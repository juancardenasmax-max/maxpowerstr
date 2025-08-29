#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Bike Deal Bot — OfferUp + Facebook + JD Power (NADA)
Focus: ensure Facebook listings have parseable titles (year/make/modelish) by enriching
from detail pages when the card label is too weak. OfferUp + NADA logic unchanged.

Deal logic recap
----------------
- Primary deal: list_price <= (NADA Low × (1 + low_margin)) AND profit >= min_profit.
- Potential: negotiated(list_price) <= target AND profit >= min_profit.
- Profit baseline selectable: avg | low | avg_or_low (default in CLI: avg).
- Cache-first NADA valuation with optional live fallback.

"""

from __future__ import annotations

import argparse, asyncio, csv, dataclasses, json, logging, math, os, random, re, threading, time
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from urllib.parse import urlencode, urlparse

from playwright.sync_api import (
    sync_playwright, BrowserContext, Page, TimeoutError as PWTimeout
)

# ============================== Logging ==============================
LOG = logging.getLogger("bike-deal-bot")
logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")

# ============================== Data ==============================
@dataclasses.dataclass
class Listing:
    title: str
    price: Optional[int]
    url: str
    location: Optional[str] = None
    source: str = "offerup"

CLEAN_SPACES = re.compile(r"\s+")
YEAR_RE  = re.compile(r"\b(19[7-9]\d|20[0-4]\d|2050)\b")
PRICE_RE = re.compile(r"\$\s*([\d,]+)")
MONEY_RE_HTML = re.compile(r"\$\s*([\d,]+)")

BRAND_ALIASES = {
    "harley davidson": "harley-davidson", "harley-davidson": "harley-davidson", "hd": "harley-davidson",
    "can am": "can-am", "can-am": "can-am", "cf moto": "cfmoto", "cfmoto": "cfmoto",
    "ktm": "ktm", "honda": "honda", "yamaha": "yamaha", "suzuki": "suzuki", "kawasaki": "kawasaki",
    "ducati": "ducati", "bmw": "bmw", "triumph": "triumph", "buell": "buell",
    "vespa": "vespa", "aprilia": "aprilia", "indian": "indian", "polaris": "polaris",
    # FB often shows this exact phrase:
    "indian motorcycle": "indian",
}

def now_str() -> str: return datetime.now().strftime("%Y-%m-%d %H:%M:%S")
_def_profile = "./playwright_profile"
def _slugify(s: str) -> str: return re.sub(r"[^a-z0-9]+", "-", (s or "").lower()).strip("-")

def parse_price_from_text(txt: str) -> Optional[int]:
    m = PRICE_RE.search(txt or "")
    try: return int(m.group(1).replace(",","")) if m else None
    except Exception: return None

def _money_to_int(txt: Optional[str]) -> Optional[int]:
    if not txt: return None
    m = MONEY_RE_HTML.search(txt)
    return int(m.group(1).replace(",","")) if m else None

# ============================== Persisted dedupe helpers ==============================
def _dedupe_load(path: str) -> Tuple[Dict[str, Optional[int]], set, set]:
    try:
        p = Path(path)
        if not p.exists():
            return {}, set()
        data = json.loads(p.read_text("utf-8"))
        seen = data.get("seen", {})
        if not isinstance(seen, dict):
            seen = {}
        notified_list = data.get("notified", [])
        if isinstance(notified_list, list):
            notified = set(str(u) for u in notified_list)
        elif isinstance(notified_list, dict):
            notified = set(notified_list.keys())
        else:
            notified = set()
        # Optional fingerprint set
        fps = data.get("notified_fps", [])
        notified_fps = set(str(x) for x in fps) if isinstance(fps, list) else set()
        # Ensure keys are strings, values are ints or None
        out_seen: Dict[str, Optional[int]] = {}
        for k, v in seen.items():
            try:
                out_seen[str(k)] = (int(v) if v is not None else None)
            except Exception:
                continue
        # Temporarily pack fingerprints into the notified set structure by attaching attribute later
        out = (out_seen, notified)
        # Attach as hidden attribute for caller to pick up
        try:
            out._notified_fps = notified_fps  # type: ignore[attr-defined]
        except Exception:
            pass
        return out_seen, notified, notified_fps
    except Exception:
        return {}, set(), set()

def _dedupe_save(path: str, seen_index: Dict[str, Optional[int]], notified_urls: set) -> None:
    try:
        data = {
            "version": 1,
            "saved_at": time.time(),
            "seen": {k: (int(v) if v is not None else None) for k, v in seen_index.items()},
            "notified": sorted(list(notified_urls)),
        }
        # If caller attached fingerprints on the function for this call, persist them
        try:
            fps = _dedupe_save._notified_fps  # type: ignore[attr-defined]
            if isinstance(fps, set):
                data["notified_fps"] = sorted(list(fps))
        except Exception:
            pass
        Path(path).write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception:
        pass

# ============================== Fingerprinting for dedupe ==============================
def listing_fingerprint(title: str, price: Optional[int]) -> Optional[str]:
    try:
        y, mk, mdl = normalize_title(title)
        if (not y and not mk and not mdl) or price is None:
            return None
        toks = _tokens_from_modelish(mdl or "")
        core = ":".join([str(y or 0), mk or "", " ".join(toks)])
        return f"{core}|{int(price)}".lower()
    except Exception:
        return None

# ============================== URL canonicalization ==============================
_RE_FB_ITEM = re.compile(r"/marketplace/item/(\d+)/?")
_RE_OU_ITEM = re.compile(r"/item/detail/([A-Za-z0-9\-]+)/?")

def canonicalize_listing_url(url: str) -> str:
    try:
        u = urlparse(url)
        host = (u.netloc or "").lower()
        path = u.path or ""
        if "facebook.com" in host:
            m = _RE_FB_ITEM.search(path)
            if m:
                return f"https://www.facebook.com/marketplace/item/{m.group(1)}"
        if "offerup.com" in host:
            m = _RE_OU_ITEM.search(path)
            if m:
                return f"https://offerup.com/item/detail/{m.group(1)}"
        # Generic: strip query/fragment
        base = (url.split("#",1)[0]).split("?",1)[0]
        return base
    except Exception:
        return url

# ============================== Telegram ==============================
def send_telegram(token: Optional[str], chat_id: Optional[str], text: str) -> bool:
    if not token or not chat_id: return False
    if len(text) > 4096: text = text[:4093] + "..."
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    payload = {"chat_id": chat_id, "text": text, "disable_web_page_preview": True}
    try:
        try:
            import requests
            r = requests.post(url, json=payload, timeout=12)
            try:
                jd = r.json()
                return bool(jd.get("ok"))
            except Exception:
                return r.status_code == 200
        except Exception:
            import urllib.parse, urllib.request, json as _json
            data = urllib.parse.urlencode(payload).encode("utf-8")
            req = urllib.request.Request(url, data=data, headers={"Content-Type":"application/x-www-form-urlencoded"})
            with urllib.request.urlopen(req, timeout=12) as resp:
                try:
                    jd = json.loads(resp.read().decode("utf-8")); return bool(jd.get("ok"))
                except Exception: return True
    except Exception as e:
        LOG.warning(f"Telegram send failed: {e}"); return False

# ============================== JD Power helpers ==============================
def jdp_strip_zip(url: str) -> str: return re.sub(r"/zip(?=/|$)", "", (url or ""))
def jdp_force_values(url: str) -> str:
    u = (url or "").rstrip("/")
    return u if u.endswith("/values") else u + "/values"
def jdp_canonical(url: str) -> str: return jdp_strip_zip(url)

# ============================== Browser manager ==============================
BLOCK_TEXT = [
    "access denied", "request unsuccessful", "verify you are a human",
    "perimeterx", "px-captcha", "cloudflare", "akamai", "reference #",
]

class BrowserMgr:
    def __init__(self, user_data_dir: Optional[str], headless: bool, allow_domains=None,
                 restart_after_navs=200, recycle_every_seconds=480, nav_timeout_ms=60000):
        self.user_data_dir = user_data_dir or _def_profile
        self.headless = headless
        self.allow_domains = set(allow_domains or [])
        self.restart_after_navs = max(50, int(restart_after_navs))
        self.recycle_every_seconds = max(120, int(recycle_every_seconds))
        self.nav_timeout_ms = nav_timeout_ms
        self.pw = None; self.context: Optional[BrowserContext] = None
        self.page: Optional[Page] = None
        self.navs = 0; self._last_recycle = 0.0

    def _route_filter(self, route):
        if not self.allow_domains: return route.continue_()
        try:
            host = (urlparse(route.request.url).hostname or "").lower()
            if any(host.endswith(d) for d in self.allow_domains): return route.continue_()
            return route.abort()
        except Exception: return route.continue_()

    def start(self):
        self.pw = sync_playwright().start()
        prof = Path(self.user_data_dir).resolve(); prof.mkdir(parents=True, exist_ok=True)
        self.context = self.pw.chromium.launch_persistent_context(
            user_data_dir=str(prof), headless=self.headless,
            viewport={"width":1366,"height":900}, args=["--disable-blink-features=AutomationControlled"]
        )
        self.context.route("**/*", self._route_filter)
        self.page = self.context.new_page(); self.page.set_default_navigation_timeout(self.nav_timeout_ms)
        self._last_recycle = time.time()

    def stop(self):
        try:
            if self.context: self.context.close()
        finally:
            if self.pw: self.pw.stop()

    def recycle(self):
        LOG.info("Recycling browser context…")
        self.stop(); self.start(); self.navs = 0; self._last_recycle = time.time()

    def _maybe_recycle(self):
        if (self.navs >= self.restart_after_navs) or (time.time()-self._last_recycle >= self.recycle_every_seconds):
            self.recycle()

    def goto(self, url: str, wait="domcontentloaded") -> bool:
        try:
            self._maybe_recycle()
            P(self).goto(url, wait_until=wait, timeout=self.nav_timeout_ms)
            P(self).wait_for_timeout(500)
            self.navs += 1
            return True
        except PWTimeout:
            LOG.warning(f"Timeout navigating to {url}"); self.recycle(); return False
        except Exception as e:
            LOG.warning(f"Navigation error: {e}"); self.recycle(); return False

    def looks_blocked(self) -> bool:
        try:
            txt = (P(self).evaluate("() => document.body ? document.body.innerText : ''") or "").lower()
            return any(p in txt for p in BLOCK_TEXT)
        except Exception: return False

def P(mgr: BrowserMgr) -> Page:
    return mgr.page

# ============================== CSV helper ==============================
def _append_csv(path: str, row: Dict[str, object]) -> None:
    p = Path(path); exists = p.exists()
    try:
        with p.open("a", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=[
                "ts","kind","source","title","price","year","make","modelish",
                "nada_low","nada_avg","nada_msrp","nada_url",
                "low_margin","negotiate_pct","profit_baseline","profit",
                "target","negotiated_price","miles","title_flags","url"
            ])
            if not exists: w.writeheader()
            w.writerow(row)
    except Exception as e:
        LOG.warning(f"CSV write failed ({path}): {e}")

# ============================== NADA extraction (unchanged logic) ==============================
def _first_dollar_after(html: str, label: str, window: int = 2500) -> Optional[int]:
    for m in re.finditer(re.escape(label), html, flags=re.I):
        seg = html[m.end(): m.end()+window]
        m2 = MONEY_RE_HTML.search(seg)
        if m2: return int(m2.group(1).replace(",",""))
    return None

def _extract_from_html_labels(html: str) -> Dict[str, Optional[int]]:
    labels = {
        "low_retail": ["Low Retail","Low Retail Value"],
        "avg_retail": ["Average Retail","Average Retail Value"],
        "msrp": ["Suggested List","Suggested List Price","MSRP","Suggested Retail"],
    }
    out = {"low_retail": None, "avg_retail": None, "msrp": None}
    for key, variants in labels.items():
        for lab in variants:
            v = _first_dollar_after(html, lab, 2500)
            if v is not None: out[key] = v; break
    return out

def _extract_from_dom(mgr: BrowserMgr) -> Dict[str, Optional[int]]:
    def val_for(label_text: str) -> Optional[int]:
        try:
            el = P(mgr).locator(
                "xpath=//*[translate(normalize-space(text()), 'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz')='" + label_text.lower() + "']"
            ).first
            if el.count() == 0: return None
            row = el.locator("xpath=ancestor::tr[1]")
            if row.count() > 0:
                price = row.locator("xpath=.//*[contains(text(),'$')]").first
                if price.count() > 0: return _money_to_int(price.text_content())
            cont = el.locator("xpath=ancestor::*[self::div or self::li][1]")
            if cont.count() > 0:
                price = cont.locator("xpath=.//*[contains(text(),'$')]").first
                if price.count() > 0: return _money_to_int(price.text_content())
            after = el.locator("xpath=following::*[contains(text(),'$')][1]")
            if after.count() > 0: return _money_to_int(after.text_content())
        except Exception: return None
        return None

    out = {"low_retail": None, "avg_retail": None, "msrp": None}
    labels = {
        "low_retail": ["Low Retail","Low Retail Value"],
        "avg_retail": ["Average Retail","Average Retail Value"],
        "msrp": ["Suggested List","Suggested List Price","MSRP","Suggested Retail"],
    }
    for key, variants in labels.items():
        for v in variants:
            x = val_for(v)
            if x is not None: out[key] = x; break
    return out

def extract_jdp_values_precise(mgr: BrowserMgr) -> Dict[str, Optional[int]]:
    out = _extract_from_dom(mgr)
    if not all(out.get(k) is not None for k in ("low_retail","avg_retail","msrp")):
        html = P(mgr).content()
        lbl = _extract_from_html_labels(html)
        for k, v in lbl.items():
            if out.get(k) is None and v is not None: out[k] = v
    if all(out.get(x) is not None for x in ("msrp","avg_retail","low_retail")):
        msrp, avg, low = out["msrp"], out["avg_retail"], out["low_retail"]
        if not (msrp >= avg >= low):
            a = sorted([msrp, avg, low], reverse=True)
            out = {"msrp": a[0], "avg_retail": a[1], "low_retail": a[2]}
    return out

# ============================== Offline cache ==============================
def nada_cache_load(path: Optional[str]) -> Dict:
    if not path: return {}
    p = Path(path)
    if not p.exists():
        LOG.error(f"NADA cache file not found: {p}")
        return {}
    try:
        data = json.loads(p.read_text("utf-8"))
        years = list(data.keys())
        if not years:
            LOG.error("NADA cache loaded but empty.")
            return {}
        total = 0
        for yr in data.values():
            for mk in yr.values():
                total += len(mk)
        LOG.info(f"NADA cache: years={len(years)} models={total} path={p}")
        return data
    except Exception as e:
        LOG.error(f"Failed to read NADA cache: {e}")
        return {}

def nada_cache_save(path: str, data: Dict):
    try:
        Path(path).write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        LOG.info(f"NADA cache saved: {path}")
    except Exception as e:
        LOG.warning(f"Failed saving NADA cache: {e}")

def _tokens_from_modelish(modelish: str) -> List[str]:
    raw = (modelish or "").lower()
    toks = [t for t in re.split(r"[^a-z0-9]+", raw) if t and len(t) >= 2]
    stop = {"for","sale","motorcycle","bike","harley","davidson","ktm","honda","kawasaki","yamaha",
            "suzuki","triumph","bmw","indian","can","am","polaris","cfmoto","vespa","aprilia"}
    # Drop obvious stopwords and 4-digit years so model tokens focus on trim/displacement
    toks = [t for t in toks if t not in stop and not re.fullmatch(r"(19[7-9]\d|20[0-4]\d|2050)", t)]
    return toks[:8]

def _pick_merge_slug(cache: Dict, year: int, make: str, title: str, suggested_slug: str) -> str:
    try:
        yr = str(year); mk = (make or "").lower()
        recs = cache.get(yr, {}).get(mk, {})
        if not isinstance(recs, dict) or not recs:
            return suggested_slug
        # Exact title match first
        norm_new = CLEAN_SPACES.sub(" ", (title or "").lower()).strip()
        tokens_new = set(_tokens_from_modelish(title))
        best_slug = None
        best_score = -1
        for slug, rec in recs.items():
            t_old = CLEAN_SPACES.sub(" ", (rec.get("title") or "").lower()).strip()
            if t_old and t_old == norm_new:
                return slug
            toks_old = set(_tokens_from_modelish(t_old))
            if not toks_old:
                continue
            overlap = len(tokens_new & toks_old)
            if overlap > best_score:
                best_score = overlap
                best_slug = slug
        # Require reasonable overlap to treat as same model
        # Threshold: at least 60% of new tokens or minimum 2 tokens
        need = max(2, math.ceil(len(tokens_new) * 0.6)) if tokens_new else 0
        if best_slug is not None and best_score >= need:
            return best_slug
        return suggested_slug
    except Exception:
        return suggested_slug

def _best_cache_match(entries: Dict[str, Dict], modelish: str) -> Optional[Dict]:
    toks = _tokens_from_modelish(modelish or "")
    if not toks:
        return None
    word_toks = [t for t in toks if not t.isdigit()]
    num_toks = [int(t) for t in toks if t.isdigit()]
    want_super = any(t in ("super","superduke","super-duke") for t in toks)

    def numbers_in(text: str) -> List[int]:
        out = []
        for m in re.finditer(r"\b(\d{2,4})\b", text):
            try:
                v = int(m.group(1))
                # Ignore obvious years
                if 1970 <= v <= 2050:
                    continue
                out.append(v)
            except Exception:
                pass
        return out

    best_rec = None
    best_score = -10**9
    for slug, rec in entries.items():
        hay = (slug + " " + (rec.get("title") or "")).lower()
        score = 0
        # Base word matches
        for w in word_toks:
            if w and w in hay:
                score += 1
        # Numeric displacement matches are highly informative
        hay_nums = numbers_in(hay)
        if num_toks:
            if hay_nums:
                diff = min(abs(a-b) for a in num_toks for b in hay_nums)
                if any(str(n) in hay for n in num_toks):
                    score += 3  # exact number present
                elif diff <= 100:
                    score += 1  # close family (e.g., 890 vs 900)
                else:
                    score -= 1
            else:
                score -= 2  # listing specifies number but candidate has none
        # Super Duke heuristic: avoid Super Duke when query doesn't say 'super'
        if ("super" in hay and "duke" in hay):
            if not want_super and ("duke" in word_toks or not word_toks):
                score -= 2
            elif want_super:
                score += 1
        # Lightweight preference for shorter, cleaner slugs (more specific models often shorter here)
        score -= 0.001 * len(slug)

        # Require at least one non-trivial overlap
        if score > best_score and (any(w in hay for w in word_toks) or (num_toks and any(str(n) in hay for n in num_toks))):
            best_score = score
            best_rec = rec

    return best_rec

def nada_lookup_offline(cache: Dict, year: int, make: str, modelish: str, *, verbose=False) -> Optional[Dict[str, int]]:
    yr = str(year); mk = (make or "").lower()
    MAKE_SYNONYMS = {"indian": "indian-motorcycle", "indian-motorcycle": "indian"}
    recs = cache.get(yr, {}).get(mk, {})
    if not recs and mk in MAKE_SYNONYMS:
        recs = cache.get(yr, {}).get(MAKE_SYNONYMS[mk], {})
    if not recs:
        if verbose: LOG.debug(f"[NADA] cache miss (no entries) for {yr}/{mk}")
        return None
    hit = _best_cache_match(recs, modelish)
    if not hit:
        if verbose:
            LOG.debug(f"[NADA] cache miss (no token match) for {yr}/{mk} :: modelish='{modelish}' tokens={_tokens_from_modelish(modelish)}")
        return None
    out = {k: v for k, v in hit.items() if k in ("low_retail","avg_retail","msrp")}
    out["source_url"] = hit.get("url")
    if verbose:
        LOG.info(f"[NADA] cache HIT {yr}/{mk} :: '{hit.get('title')}' low={out.get('low_retail')} avg={out.get('avg_retail')} msrp={out.get('msrp')}")
    return out

# ============================== JDP model list discovery (for live fallback) ==============================
def _scroll_to_bottom(mgr: BrowserMgr, max_passes: int = 16, pause_ms: int = 650):
    last_h = 0
    for _ in range(max_passes):
        try:
            h = P(mgr).evaluate("() => document.scrollingElement ? document.scrollingElement.scrollHeight : document.body.scrollHeight")
            P(mgr).mouse.wheel(0, h); P(mgr).wait_for_timeout(pause_ms)
            if h == last_h: break
            last_h = h
        except Exception: break

def _collect_model_links_js(mgr: BrowserMgr, year: int, make: str) -> List[Tuple[str, str]]:
    try:
        results = P(mgr).evaluate(r"""(y,m) => {
            const out=[]; const A=[...document.querySelectorAll('a[href]')];
            const re=new RegExp(`/motorcycles/${y}/${m}/([^/?#]+)`,'i');
            for (const a of A){ const href=a.href||a.getAttribute('href')||''; const m2=href.match(re);
                if(!m2) continue; const slug=(m2[1]||'').toLowerCase(); if(slug==='motorcycles') continue;
                const lab=(a.getAttribute('aria-label')||a.innerText||a.textContent||'').replace(/\s+/g,' ').trim();
                out.push([href, lab]); }
            return out;
        }""", year, make)
        return [(jdp_canonical(u), (txt or "").strip()) for u, txt in (results or [])]
    except Exception: return []

def _list_models_for_year_make(mgr: BrowserMgr, year: int, make: str, list_pause_ms: int) -> List[Tuple[str, str]]:
    models: List[Tuple[str, str]] = []; seen=set()
    candidates = [
        f"https://www.jdpower.com/motorcycles/{year}/{make}/motorcycles",
        f"https://www.jdpower.com/motorcycles/{year}/{make}",
        f"https://www.jdpower.com/motorcycles/{year}",
    ]
    for base in candidates:
        url = jdp_canonical(base)
        if not mgr.goto(url): continue
        P(mgr).wait_for_timeout(500)
        _scroll_to_bottom(mgr, 14, 650)
        pairs = _collect_model_links_js(mgr, year, make)

        if len(pairs) < 2:
            anchors = P(mgr).locator("a"); cnt = anchors.count()
            for i in range(min(cnt, 3500)):
                href = anchors.nth(i).get_attribute("href") or ""
                if not href: continue
                if href.startswith("/"): href = "https://www.jdpower.com" + href
                href = jdp_canonical(href)
                m = re.search(rf"/motorcycles/{year}/{make}/([^/?#]+)", href, flags=re.I)
                if not m: continue
                slug = m.group(1).lower()
                if slug == "motorcycles": continue
                txt = (anchors.nth(i).text_content() or "").strip()
                pairs.append((href, txt))

        for href, txt in pairs:
            key = href.lower().split("?")[0]
            if key in seen: continue
            seen.add(key); models.append((href, txt))
        if len(models) >= 10: break
        P(mgr).wait_for_timeout(list_pause_ms)
    return models

def _parse_jdp_url(url: str) -> Tuple[Optional[int], Optional[str], Optional[str]]:
    m = re.search(r"/motorcycles/(\d{4})/([^/]+)/([^/?#]+)", url or "")
    return (int(m.group(1)), m.group(2).lower(), m.group(3).lower()) if m else (None,None,None)

def _ensure_values_on_page(mgr: BrowserMgr):
    cur = jdp_canonical(P(mgr).url)
    if not cur.rstrip("/").endswith("/values"):
        target = jdp_force_values(cur)
        if target != P(mgr).url:
            mgr.goto(target); P(mgr).wait_for_timeout(150)

def _page_looks_like_model(mgr: BrowserMgr) -> bool:
    try:
        return P(mgr).locator("xpath=//*[contains(., 'Low Retail')]").count() > 0 and \
               P(mgr).locator("xpath=//*[contains(., 'Average Retail')]").count() > 0
    except Exception: return False

def _validate_jdp_target(mgr: BrowserMgr, year: int, make: str, model_tokens: List[str]) -> bool:
    _ensure_values_on_page(mgr)
    y, m, slug = _parse_jdp_url(P(mgr).url)
    if y != year or m != make: return False
    if not _page_looks_like_model(mgr): return False
    try: h1 = (P(mgr).locator("h1").first.text_content() or "").lower()
    except Exception: h1 = ""
    has_tok = any(t for t in model_tokens if t and (t in h1 or (slug or "")))
    return bool(has_tok or not model_tokens)

# ============================== NADA scan-once (UNCHANGED) ==============================
def save_progress(path: str, year: int, make: str, last_url: Optional[str] = None):
    try:
        payload = {"year":year, "make":make, "ts":time.time()}
        if last_url:
            payload["last_url"] = last_url
        Path(path).write_text(json.dumps(payload), encoding="utf-8")
    except Exception: pass

def load_progress(path: str) -> Tuple[Optional[int], Optional[str], Optional[str]]:
    p = Path(path)
    if not p.exists(): return None, None, None
    try:
        d = json.loads(p.read_text("utf-8"))
        return d.get("year"), d.get("make"), d.get("last_url")
    except Exception:
        return None, None, None

def nada_scan_once(mgr: BrowserMgr, years: Tuple[int,int], makes: List[str], cache_path: str,
                   list_pause_ms: int, detail_pause_ms: int, backoff_seconds: int,
                   progress_path: str, resume: bool, merge_cache: bool):
    # Load existing cache when merging; otherwise start fresh
    cache: Dict = nada_cache_load(cache_path) if merge_cache else {}
    ymin, ymax = years; total_models = 0
    resume_year, resume_make, resume_last_url = (load_progress(progress_path) if resume else (None, None, None))
    skipping = (resume_year, resume_make) if (resume and resume_year and resume_make) else None
    if not resume and Path(progress_path).exists():
        try: Path(progress_path).unlink()
        except Exception: pass

    for year in range(ymin, ymax+1):
        for make in makes:
            if skipping:
                y0, m0 = skipping
                if (year, make) < (y0, m0): continue
                skipping = None
            save_progress(progress_path, year, make)
            try:
                models = _list_models_for_year_make(mgr, year, make, list_pause_ms)
            except Exception as e:
                LOG.warning(f"List error {year}/{make}: {e}"); mgr.recycle(); continue

            LOG.info(f"Scan {year}/{make}: discovered {len(models)} model links")
            # If resuming within the same year/make, skip models up to last_url
            start_idx = 0
            if resume and resume_year == year and (resume_make or '').lower() == (make or '').lower() and resume_last_url:
                try:
                    canon_resume = jdp_canonical(resume_last_url)
                    for i, (u, _t) in enumerate(models):
                        if jdp_canonical(u) == canon_resume:
                            start_idx = i + 1
                            break
                except Exception:
                    pass
            for (url, title) in models[start_idx:]:
                try:
                    urlv = jdp_force_values(jdp_canonical(url))
                    P(mgr).wait_for_timeout(detail_pause_ms + random.randint(0, 400))
                    if not mgr.goto(urlv): continue
                    if mgr.looks_blocked():
                        LOG.warning("Detected block page. Cooling down…")
                        time.sleep(max(60, backoff_seconds))
                        mgr.recycle()
                        if not mgr.goto(urlv) or mgr.looks_blocked():
                            LOG.warning("Still blocked; skipping this model."); continue

                    tokens = _tokens_from_modelish(title)
                    if not _validate_jdp_target(mgr, year, make, tokens): continue

                    vals = extract_jdp_values_precise(mgr)
                    if not any(vals.values()): continue

                    m = re.search(r"/motorcycles/\d{4}/[^/]+/([^/]+)/?", P(mgr).url)
                    raw_slug = m.group(1) if m else _slugify(title)

                    yr = str(year); mk = make.lower()
                    cache.setdefault(yr, {}).setdefault(mk, {})
                    # If merging, try to map to an existing slug for same model title
                    use_slug = _pick_merge_slug(cache, year, mk, title, raw_slug) if merge_cache else raw_slug
                    cache[yr][mk][use_slug] = {
                        "title": title,
                        "low_retail": vals.get("low_retail"),
                        "avg_retail": vals.get("avg_retail"),
                        "msrp": vals.get("msrp"),
                        "url": P(mgr).url,
                    }
                    total_models += 1
                    # Save fine-grained progress (last processed model URL)
                    try:
                        save_progress(progress_path, year, make, P(mgr).url)
                    except Exception:
                        pass
                    if total_models % 25 == 0:
                        nada_cache_save(cache_path, cache)
                except Exception:
                    continue

    nada_cache_save(cache_path, cache)
    LOG.info(f"NADA scan complete. Models cached: {total_models}")

# ============================== Live JDP (cache-first) ==============================
def jdp_find_values_for_model(mgr: BrowserMgr, year: int, make: str, modelish: str,
                              nada_cache: Dict, list_pause_ms: int, detail_pause_ms: int,
                              allow_online_fallback: bool, explain: bool) -> Optional[Dict[str,int]]:
    if nada_cache:
        hit = nada_lookup_offline(nada_cache, year, make, modelish, verbose=explain)
        if hit: return hit
        if not allow_online_fallback:
            if explain: LOG.debug("[NADA] offline only: giving up (no cache hit)")
            return None

    models = _list_models_for_year_make(mgr, year, make, list_pause_ms)
    tokens = _tokens_from_modelish(modelish or "")
    best, score_best = None, 0
    for url, title in models:
        hay = (url.lower() + " " + (title or "").lower())
        s = sum(1 for t in tokens if t and t in hay)
        if s > score_best: score_best = s; best = (url, title)
    if not best and models: best = models[0]
    if not best: return None
    try:
        urlv = jdp_force_values(jdp_canonical(best[0]))
        P(mgr).wait_for_timeout(detail_pause_ms + random.randint(0, 250))
        if not mgr.goto(urlv): return None
        if not _validate_jdp_target(mgr, year, make, tokens): return None
        vals = extract_jdp_values_precise(mgr)
        if any(vals.values()):
            vals["source_url"] = P(mgr).url
            if explain:
                LOG.info(f"[NADA] live fallback HIT {year}/{make} '{best[1]}' low={vals.get('low_retail')} avg={vals.get('avg_retail')}")
            return {k: v for k, v in vals.items() if v is not None}
    except Exception: return None
    return None

# ============================== OfferUp (unchanged) ==============================
def fetch_offerup_price_from_detail(mgr: BrowserMgr, url: str) -> Optional[int]:
    if not mgr.goto(url): return None
    P(mgr).wait_for_timeout(600)
    scripts = P(mgr).locator("script[type='application/ld+json']")
    for i in range(min(scripts.count(), 8)):
        raw = scripts.nth(i).text_content() or ""
        try: data = json.loads(raw)
        except Exception: continue
        objs = data if isinstance(data, list) else [data]
        for obj in objs:
            try:
                offers = obj.get("offers")
                if isinstance(offers, dict) and "price" in offers:
                    p = offers["price"]
                    if isinstance(p,(int,float)) or (isinstance(p,str) and p.replace(".","",1).isdigit()):
                        return int(float(p))
            except Exception: continue
    texts = P(mgr).locator("xpath=//*[contains(text(),'$')]").all_text_contents()
    nums: List[int] = []
    for t in texts:
        for m in PRICE_RE.findall(t):
            try: nums.append(int(m.replace(",","")))
            except Exception: pass
    if nums:
        from statistics import median
        freq: Dict[int,int] = {}
        for n in nums: freq[n] = freq.get(n,0)+1
        best = max(freq.items(), key=lambda kv: kv[1])[0]
        return best if freq[best] > 1 else int(median(nums))
    return None

def fetch_offerup_detail_text(mgr: BrowserMgr, url: str) -> Optional[str]:
    try:
        if not mgr.goto(url):
            return None
        P(mgr).wait_for_timeout(700)
        try:
            head = P(mgr).get_by_role("heading").first.text_content() or ""
        except Exception:
            head = ""
        try:
            body = P(mgr).evaluate("() => document.body ? document.body.innerText : ''") or ""
        except Exception:
            body = ""
        text = (head + " \n " + body)
        text = CLEAN_SPACES.sub(" ", text).strip()
        return text[:2000] if text else None
    except Exception:
        return None

def _ou_collect_cards(mgr: BrowserMgr) -> List[Tuple[str,str]]:
    results = P(mgr).evaluate(r"""() => {
        const out=[]; const A=[...document.querySelectorAll('a[href*="/item/detail/"]')];
        for (const a of A){ const href=a.href||a.getAttribute('href')||''; if(!href) continue;
            const label=(a.getAttribute('aria-label')||a.innerText||a.textContent||'').replace(/\s+/g,' ').trim();
            out.push([href.startsWith('http')?href:('https://offerup.com'+href), label]); }
        return out;
    }""")
    results = results or []
    return [(canonicalize_listing_url(u), lbl) for (u,lbl) in results]

def _scroll_until_stable(mgr: BrowserMgr, max_rounds=14, pause_ms=800):
    prev = 0
    for _ in range(max_rounds):
        try:
            P(mgr).mouse.wheel(0, 25000); P(mgr).wait_for_timeout(pause_ms)
            cur = P(mgr).locator('a[href*="/item/detail/"]').count()
            if cur <= prev: break
            prev = cur
        except Exception: break

def scrape_offerup(mgr: BrowserMgr, price_min: int, price_max: int, endpoint: str,
                   seen_index: Optional[Dict[str, Optional[int]]] = None,
                   skip_urls: Optional[set] = None,
                   exclude_parts: bool = True) -> List[Listing]:
    items: List[Listing] = []
    endpoints: List[str] = []
    if endpoint in ("search","both"):
        endpoints.append(f"https://offerup.com/search/?q=motorcycle&price_min={price_min}&price_max={price_max}")
    if endpoint in ("explore","both"):
        endpoints.append("https://offerup.com/explore/k/5/2")
    seen=set()
    for url in endpoints:
        if not mgr.goto(url): continue
        P(mgr).wait_for_timeout(1200); _scroll_until_stable(mgr, 16, 750)
        pairs = _ou_collect_cards(mgr)
        consecutive_skips = 0
        for href, label in pairs:
            if href in seen: continue
            seen.add(href)
            canon = href  # already canonicalized by _ou_collect_cards
            if skip_urls is not None and canon in skip_urls:
                consecutive_skips += 1
                if consecutive_skips >= 40:
                    break
                continue
            else:
                consecutive_skips = 0
            price = parse_price_from_text(label)
            # Skip if we've seen the same canonical URL with the same price
            if seen_index is not None and canon in seen_index and price is not None and seen_index.get(canon) == price:
                continue
            title = re.sub(r"\$[\d,]+.*", "", label).strip() or "OfferUp Listing"
            if exclude_parts and (is_likely_parts_or_gear(title) or is_likely_parts_or_gear(label)):
                continue
            year_in_title = None; m = YEAR_RE.search(title)
            if m: year_in_title = int(m.group(1))
            # Only spend detail navigation when we haven't seen this item before
            if (price is None or (year_in_title and price == year_in_title)) and (seen_index is None or canon not in seen_index):
                detail_price = fetch_offerup_price_from_detail(mgr, href)
                if detail_price is not None:
                    price = detail_price
            if year_in_title and price == year_in_title: price = None
            if price is None: continue
            items.append(Listing(title=title, price=price, url=href, source="offerup"))
    LOG.info(f"OfferUp {len(items)} raw items (dedup will follow)")
    return items

# ============================== Facebook (FIXED: enrich weak titles) ==============================
def _fb_collect_cards(mgr: BrowserMgr) -> List[Tuple[str,str]]:
    results = P(mgr).evaluate(r"""() => {
        const out=[]; const A=[...document.querySelectorAll('a[href*="/marketplace/item/"]')];
        for (const a of A){ const href=a.href||a.getAttribute('href')||''; if(!href) continue;
            let label=a.getAttribute('aria-label')||a.innerText||a.textContent||''; label=label.replace(/\s+/g,' ').trim();
            out.push([href.startsWith('http')?href:('https://www.facebook.com'+href), label]); }
        return out;
    }""")
    results = results or []
    return [(canonicalize_listing_url(u), lbl) for (u,lbl) in results]

def is_logged_in_facebook(ctx: BrowserContext) -> bool:
    try:
        cookies = ctx.cookies()
        return any(c.get("name")=="c_user" and "facebook.com" in c.get("domain","") for c in cookies)
    except Exception: return False

def ensure_facebook_login(mgr: BrowserMgr, mode: str, wait_seconds: int) -> bool:
    if is_logged_in_facebook(P(mgr).context):
        LOG.info("Facebook login status: LOGGED IN"); return True
    LOG.warning("Facebook: not logged in. Opening login page…")
    mgr.goto("https://www.facebook.com/login"); P(mgr).wait_for_timeout(800)
    mode = (mode or "wait").lower()
    if mode == "never": return False
    if mode == "enter":
        LOG.info("Log in in the browser window, then press ENTER here…")
        try: input()
        except Exception: pass
        return is_logged_in_facebook(P(mgr).context)
    deadline = time.time() + max(10, wait_seconds)
    while time.time() < deadline:
        time.sleep(4)
        if is_logged_in_facebook(P(mgr).context):
            LOG.info("Facebook login detected."); return True
    LOG.warning("Facebook: login not detected within the wait window."); return False

def _fb_scroll_until_stable(mgr: BrowserMgr, max_rounds=18, pause_ms=900):
    prev = 0
    for _ in range(max_rounds):
        try:
            P(mgr).mouse.wheel(0, 30000); P(mgr).wait_for_timeout(pause_ms)
            cur = P(mgr).locator("a[href*='/marketplace/item/']").count()
            if cur <= prev: break
            prev = cur
        except Exception: break

def _fb_read_detail_title_and_price(mgr: BrowserMgr, href: str) -> Tuple[Optional[str], Optional[int]]:
    """Open the FB item page and try hard to get a strong, parseable title; also try price."""
    if not mgr.goto(href): return (None, None)
    P(mgr).wait_for_timeout(900)

    # Title candidates: og:title > biggest heading > document.title
    title_candidates: List[str] = []
    try:
        og = P(mgr).evaluate("""() => {
            const el = document.querySelector('meta[property="og:title"]');
            return el ? (el.getAttribute('content') || '').trim() : '';
        }""") or ""
        if og: title_candidates.append(og)
    except Exception: pass

    try:
        # Pick the longest visible heading (role-based is robust on FB)
        hs = P(mgr).get_by_role("heading")
        count = min(hs.count(), 6)
        best_h = ""
        for i in range(count):
            t = (hs.nth(i).text_content() or "").strip()
            if len(t) > len(best_h): best_h = t
        if best_h: title_candidates.append(best_h)
    except Exception: pass

    try:
        dt = (P(mgr).title() or "").strip()
        if dt: title_candidates.append(dt)
    except Exception: pass

    strong_title = None
    # Choose the first candidate that contains any known brand token; else the longest.
    lower_aliases = list(BRAND_ALIASES.keys())
    for cand in title_candidates:
        t = (cand or "").lower()
        if any(f" {alias} " in f" {t} " or t.startswith(alias + " ") for alias in lower_aliases):
            strong_title = cand
            break
    if not strong_title and title_candidates:
        strong_title = max(title_candidates, key=lambda s: len(s))

    # Price from detail if needed
    price_detail: Optional[int] = None
    try:
        snippet = ""
        try: snippet = P(mgr).get_by_role("heading").first.text_content() or ""
        except Exception: pass
        snippet += " " + " ".join(P(mgr).locator("xpath=//*[contains(text(),'$')]").all_text_contents()[:10])
        price_detail = parse_price_from_text(snippet)
        if price_detail is None:
            # sometimes price is in og:description
            ogd = P(mgr).evaluate("""() => {
                const el = document.querySelector('meta[property="og:description"]');
                return el ? (el.getAttribute('content') || '').trim() : '';
            }""") or ""
            if ogd:
                price_detail = parse_price_from_text(ogd)
    except Exception:
        pass

    return (strong_title, price_detail)

def fetch_facebook_detail_hints(mgr: BrowserMgr, url: str) -> Optional[str]:
    """Return a broader text sample from the detail page (heading + page text).
    Helps capture displacement like '390' that may be missing in the card title."""
    try:
        if not mgr.goto(url):
            return None
        P(mgr).wait_for_timeout(800)
        try:
            head = P(mgr).get_by_role("heading").first.text_content() or ""
        except Exception:
            head = ""
        try:
            body = P(mgr).evaluate("() => document.body ? document.body.innerText : ''") or ""
        except Exception:
            body = ""
        text = (head + " \n " + body)
        text = CLEAN_SPACES.sub(" ", text).strip()
        return text[:2000] if text else None
    except Exception:
        return None

# ============================== Text extraction: miles & title status ==============================
_RE_MILES = [
    re.compile(r"\b(\d{1,3}(?:[,\.]\d{3})+|\d+(?:\.\d+)?)\s*(k\+?|k\b)?\s*(miles?|mi\.?)(?!/h)\b", re.I),
    re.compile(r"\b(\d{1,3}(?:[,\.]\d{3})+|\d+(?:\.\d+)?)\s*(k\+?|k\b)?\s*(on\s+the\s+clock|odometer|odo)\b", re.I),
]
_RE_KM = [
    re.compile(r"\b(\d{1,3}(?:[,\.]\d{3})+|\d+(?:\.\d+)?)\s*(k\+?|k\b)?\s*(kilometers?|kms?|km)(?!/h)\b", re.I),
]

def extract_miles_from_text(text: Optional[str]) -> Optional[int]:
    if not text: return None
    t = (text or "").lower()
    for rx in _RE_MILES:
        m = rx.search(t)
        if not m: continue
        raw = m.group(1).replace(",", "")
        try:
            val = float(raw)
        except Exception:
            continue
        if m.group(2) and 'k' in m.group(2).lower():
            val *= 1000.0
        miles = int(round(val))
        if 0 < miles < 500000:  # sanity guard
            return miles
    # Try kilometers → convert to miles if miles weren't found
    for rx in _RE_KM:
        m = rx.search(t)
        if not m: continue
        raw = m.group(1).replace(",", "")
        try:
            val = float(raw)
        except Exception:
            continue
        if m.group(2) and 'k' in m.group(2).lower():
            val *= 1000.0
        miles = int(round(val * 0.621371))
        if 0 < miles < 500000:
            return miles
    return None

_TITLE_RED_FLAGS = [
    re.compile(r"\bsalvage(\s*title)?\b", re.I),
    re.compile(r"\b(rebuilt|rebuild|reconstructed)\s*(\w*\s*){0,2}title\b", re.I),
    re.compile(r"\bno\s*titt?le\b", re.I),
    re.compile(r"\bmissing\s*title\b", re.I),
    re.compile(r"\blost\s*title\b", re.I),
    re.compile(r"\bbonded\s*title\b", re.I),
    re.compile(r"\bbill\s*of\s*sale\s*only\b", re.I),
]

def branded_title_flags(text: Optional[str]) -> List[str]:
    if not text: return []
    t = (text or "").lower()
    # If it clearly says clean title and no other red flags, treat as clean
    if "clean title" in t:
        flags = [rx.pattern for rx in _TITLE_RED_FLAGS if rx.search(t)]
        return [] if not flags else flags
    out = []
    for rx in _TITLE_RED_FLAGS:
        if rx.search(t):
            out.append(rx.pattern)
    return out

# ============================== Parts/Gear filter ==============================
_PARTS_PHRASES = [
    # Strong phrases indicating non-vehicle listings
    r"\bfor\s+parts\b", r"\bparts\s*only\b", r"\brolling\s+chassis\b",
    r"\bengine\s*only\b", r"\bmotor\s*only\b", r"\bframe\s*only\b",
    r"\bproject\s*bike\b", r"\bpart[- ]?out\b",
    # Common part/gear nouns
    r"\bengine\s*cover\b", r"\bfairings?\b", r"\bplastics\b", r"\bfender(s)?\b",
    r"\bheadlight\b", r"\btaillight\b", r"\bwindshield|windscreen\b",
    r"\bmirror(s)?\b", r"\bseat\b", r"\bsaddlebag(s)?\b", r"\bbag(s)?\b",
    r"\bhelmet(s)?\b", r"\bjacket(s)?\b", r"\bglove(s)?\b", r"\bboot(s)?\b",
    r"\btire(s)?\b", r"\brim(s)?\b", r"\bwheel(s)?\b",
    r"\bbattery\b", r"\bstator\b", r"\bgasket\b", r"\bpiston\b", r"\bcrank\b",
    r"\bcaliper(s)?\b", r"\brotor(s)?\b", r"\b(brake\s*)?pad(s)?\b",
    r"\blever(s)?\b", r"\bhandlebar(s)?\b", r"\bfootpeg(s)?\b|\bpeg(s)?\b",
    r"\bradiator\b", r"\b(hose|hoses)\b", r"\btank\b", r"\becu\b", r"\bdash\b|\bcluster\b",
    r"\bignition\b|\bkey(s)?\b", r"\bcarb(uretor)?\b|\bthrottle\s*body\b|\binject(or|ion)\b",
    r"\bexhaust\b|\bmuffler\b|\bslip[- ]?on\b", r"\bspark\s*plug(s)?\b", r"\b(filter|air\s*filter|oil\s*filter)\b",
    r"\bfork(s)?\b", r"\bshock(s)?\b|\bspring(s)?\b|\bswingarm\b",
]

_PARTS_RE = [re.compile(p, re.I) for p in _PARTS_PHRASES]

def is_likely_parts_or_gear(text: Optional[str]) -> bool:
    if not text:
        return False
    t = (text or "").lower()
    # Strong disqualifiers
    for rx in _PARTS_RE:
        if rx.search(t):
            return True
    # Heuristic: if it lacks both year and brand but contains common single-word part terms
    has_year = bool(YEAR_RE.search(t))
    has_brand = any((f" {alias} " in f" {t} " or t.startswith(alias + " ")) for alias in BRAND_ALIASES.keys())
    weak_parts = [
        "fairing", "plastics", "fender", "mirror", "seat", "saddlebag", "helmet", "jacket",
        "gloves", "boots", "tire", "rim", "wheel", "battery", "stator", "gasket", "piston",
        "crank", "caliper", "rotor", "pads", "lever", "handlebar", "footpeg", "radiator",
        "hose", "tank", "ecu", "cluster", "ignition", "carb", "throttle", "injector",
        "exhaust", "muffler", "spark plug", "filter", "fork", "shock", "spring", "swingarm",
    ]
    if not has_year and not has_brand:
        if any(w in t for w in weak_parts):
            return True
    return False

def scrape_facebook(mgr: BrowserMgr, price_min: int, price_max: int, endpoint: str,
                    seen_index: Optional[Dict[str, Optional[int]]] = None,
                    skip_urls: Optional[set] = None,
                    exclude_parts: bool = True) -> List[Listing]:
    if not is_logged_in_facebook(P(mgr).context):
        LOG.warning("Facebook: skipping, not logged in."); return []
    items: List[Listing] = []; endpoints: List[str] = []
    if endpoint in ("search","both"):
        q = {"query":"motorcycle","minPrice":str(price_min),"maxPrice":str(price_max)}
        endpoints.append(f"https://www.facebook.com/marketplace/search/?{urlencode(q)}")
    if endpoint in ("category","both"):
        base_sorted = "https://www.facebook.com/marketplace/category/vehicles?sortBy=creation_time_descend&topLevelVehicleType=motorcycle&exact=false"
        base_unsorted = "https://www.facebook.com/marketplace/category/vehicles?topLevelVehicleType=motorcycle&exact=false"
        endpoints.append(base_sorted + f"&minPrice={price_min}&maxPrice={price_max}")
        endpoints.append(base_unsorted + f"&minPrice={price_min}&maxPrice={price_max}")
    seen=set()
    for url in endpoints:
        if not mgr.goto(url): continue
        P(mgr).wait_for_timeout(1500); _fb_scroll_until_stable(mgr, 20, 900)
        raw = _fb_collect_cards(mgr)
        consecutive_skips = 0
        for href, label in raw:
            if href in seen: continue
            seen.add(href)

            # Card values
            canon = href  # already canonical
            if skip_urls is not None and canon in skip_urls:
                consecutive_skips += 1
                if consecutive_skips >= 30:
                    break
                continue
            else:
                consecutive_skips = 0
            price = parse_price_from_text(label)
            if seen_index is not None and canon in seen_index and price is not None and seen_index.get(canon) == price:
                continue
            title = re.sub(r"\$[\d,]+.*", "", label).strip() or "Facebook Marketplace Listing"
            if exclude_parts and (is_likely_parts_or_gear(title) or is_likely_parts_or_gear(label)):
                continue

            # If title is weak (can't parse year/make/modelish) or price missing, open detail and enrich.
            y0, m0, mod0 = normalize_title(title)
            need_enrich = not (y0 and m0 and mod0)
            if (need_enrich or price is None) and (seen_index is None or canon not in seen_index):
                title2, price2 = _fb_read_detail_title_and_price(mgr, href)
                # Prefer enriched title if it exists
                if title2 and len(title2) > len(title):
                    title = CLEAN_SPACES.sub(" ", title2).strip()
                # Prefer price from detail if missing
                if price is None and price2 is not None:
                    price = price2

            if price is None:
                continue  # still no price? skip

            items.append(Listing(title=title, price=price, url=href, source="facebook"))
    LOG.info(f"Facebook {len(items)} raw items (dedup will follow)")
    return items

# ============================== Deal logic ==============================
def normalize_title(title: str) -> Tuple[Optional[int], Optional[str], Optional[str]]:
    t = (title or "").lower()
    t = t.split(" for sale in ")[0]; t = t.split(" - offerup")[0]  # harmless on FB
    t = CLEAN_SPACES.sub(" ", t).strip()
    year = None; m = YEAR_RE.search(t)
    if m: year = int(m.group(1))
    brand = None; found_alias = None
    for alias in sorted(BRAND_ALIASES, key=lambda x: -len(x)):
        if f" {alias} " in f" {t} " or t.startswith(alias + " "):
            brand = BRAND_ALIASES[alias]; found_alias = alias; break
    if not brand: return (year, None, None)
    parts = t.split(found_alias, 1)
    modelish = parts[1].strip() if len(parts) > 1 else ""
    modelish = re.sub(r"\bfor\b.*$", "", modelish).strip()
    modelish = re.sub(r"[^a-z0-9\s\-\/]", " ", modelish)
    modelish = CLEAN_SPACES.sub(" ", modelish).strip() or None
    return (year, brand, modelish)

def _profit_baseline_value(nada: Dict[str,int], mode: str) -> Optional[int]:
    if mode == "avg": return nada.get("avg_retail")
    if mode == "low": return nada.get("low_retail")
    return nada.get("avg_retail") if isinstance(nada.get("avg_retail"), int) else nada.get("low_retail")

def _deal_target_low(nada: Dict[str,int], low_margin: float) -> Optional[int]:
    low = nada.get("low_retail")
    if not isinstance(low, int) or low <= 0: return None
    return int(round(low * (1.0 + low_margin)))

def evaluate_deal(list_price: int, nada: Dict[str,int], low_margin: float, min_profit: int, profit_mode: str):
    tgt = _deal_target_low(nada, low_margin)
    if tgt is None: return (False, "no_low", None, None)
    baseline = _profit_baseline_value(nada, profit_mode)
    if not isinstance(baseline, int): return (False, "no_baseline", tgt, None)
    profit = baseline - list_price
    if list_price <= tgt and profit >= min_profit:
        return (True, f"ask ${list_price:,} ≤ target ${tgt:,} & profit ≥ ${min_profit:,}", tgt, profit)
    return (False, "threshold_miss", tgt, profit)

def evaluate_potential(list_price: int, nada: Dict[str,int], low_margin: float, negotiate_pct: float,
                       min_profit: int, profit_mode: str):
    tgt = _deal_target_low(nada, low_margin)
    if tgt is None: return (False, "no_low", None, None, None)
    negotiated = int(round(list_price * (1.0 - negotiate_pct)))
    baseline = _profit_baseline_value(nada, profit_mode)
    if not isinstance(baseline, int): return (False, "no_baseline", negotiated, tgt, None)
    profit = baseline - negotiated
    if negotiated <= tgt and profit >= min_profit:
        return (True, f"neg ${negotiated:,} ≤ target ${tgt:,} & profit ≥ ${min_profit:,}", negotiated, tgt, profit)
    return (False, "threshold_miss", negotiated, tgt, profit)

def nada_tuple_for_log(nada: Optional[Dict[str,int]]) -> str:
    if not nada: return "avg=None, low=None, msrp=None"
    fmt = lambda x: f"{x:,}" if isinstance(x,int) else "None"
    return f"avg={fmt(nada.get('avg_retail'))}, low={fmt(nada.get('low_retail'))}, msrp={fmt(nada.get('msrp'))}"

# ============================== Processing ==============================
def process_listings(mgr: BrowserMgr, listings: List[Listing], explain: bool, year_min: int,
                     telegram_token: Optional[str], telegram_chat: Optional[str], notified_urls: set,
                     nada_cache: Dict, list_pause_ms: int, detail_pause_ms: int,
                     low_margin: float, min_profit: int, profit_mode: str,
                     potential: bool, negotiate_pct: float, notify_potential: bool,
                     deals_csv: str, potentials_csv: str, allow_online_fallback: bool,
                     max_miles: int, branded_bikes: bool, include_parts: bool, notified_fps: set):
    counters = {k:0 for k in [
        "total","price_missing","too_old","parse_failed","no_low","no_baseline",
        "no_valuation","threshold_miss","deals","potential","miles_exceeded","title_branded","parts_gear"
    ]}
    for li in listings:
        counters["total"] += 1
        if li.price is None or li.price <= 0: counters["price_missing"] += 1; continue
        year, make, modelish = normalize_title(li.title)
        # Extra FB hinting: if parsing fails, mine detail page body for displacement like '390'
        if not (year and make and modelish) and li.source == "facebook":
            _h = fetch_facebook_detail_hints(mgr, li.url)
            if _h:
                yx, mx, mdx = normalize_title(_h)
                if yx and mx and mdx:
                    year, make, modelish = yx, mx, mdx
        if year is not None and year < year_min: counters["too_old"] += 1; continue
        if not (year and make and modelish): counters["parse_failed"] += 1; 
        if not (year and make and modelish):
            if explain: LOG.debug(f"Skip parse: {li.title} — ${li.price:,}")
            continue

        # Optional parts/gear filter at processing stage as a safety net
        if not include_parts:
            if is_likely_parts_or_gear(li.title):
                counters["parts_gear"] += 1
                if explain: LOG.info(f"Reject parts/gear: {li.title}")
                continue

        nada_vals = jdp_find_values_for_model(
            mgr, year, make, modelish, nada_cache,
            list_pause_ms, detail_pause_ms, allow_online_fallback, explain
        )
        if not nada_vals:
            counters["no_valuation"] += 1
            if explain: LOG.debug(f"NADA not found: {year} {make} {modelish} — {li.title}")
            continue

        ok, why, tgt, profit = evaluate_deal(li.price, nada_vals, low_margin, min_profit, profit_mode)
        if ok:
            # Fingerprint-based dedupe to avoid notifying same bike reposts
            fp = listing_fingerprint(li.title, li.price)
            if fp is not None and fp in notified_fps:
                counters["parts_gear"] += 0  # no-op; just skip silently
                if explain: LOG.info(f"Skip by fingerprint duplicate: {li.title} @ {li.price}")
                continue
            
            # Before notifying, enrich with detail text to check miles and title flags
            detail_text = fetch_facebook_detail_hints(mgr, li.url) if li.source == "facebook" else fetch_offerup_detail_text(mgr, li.url)
            miles_val = extract_miles_from_text((li.title + " \n " + (detail_text or "")).strip())
            flags = branded_title_flags(detail_text)
            if miles_val is not None and miles_val > max_miles:
                counters["miles_exceeded"] += 1
                if explain: LOG.info(f"Reject by miles: {miles_val:,} > {max_miles:,} :: {li.title}")
                continue
            if (not branded_bikes) and flags:
                counters["title_branded"] += 1
                if explain: LOG.info(f"Reject by title flags: {flags} :: {li.title}")
                continue
            msg = (f"Deal 🔥\n{li.title}\nAsk: ${li.price:,}\n"
                   f"NADA: low={nada_vals.get('low_retail')} avg={nada_vals.get('avg_retail')} msrp={nada_vals.get('msrp')}\n"
                   + (f"Miles: {miles_val:,}\n" if miles_val is not None else "") +
                   f"{why}\n{li.url}")
            LOG.info(msg); counters["deals"] += 1
            row = {"ts":now_str(),"kind":"deal","source":li.source,"title":li.title,"price":li.price,
                   "year":year,"make":make,"modelish":modelish,
                   "nada_low":nada_vals.get("low_retail"),"nada_avg":nada_vals.get("avg_retail"),
                   "nada_msrp":nada_vals.get("msrp"),"nada_url":nada_vals.get("source_url"),
                   "low_margin":low_margin,"negotiate_pct":negotiate_pct,"profit_baseline":profit_mode,
                   "profit":profit,"target":tgt,"negotiated_price":None,
                   "miles": miles_val, "title_flags": ",".join(flags) if flags else None,
                   "url":li.url}
            _append_csv(deals_csv, row)
            _key = canonicalize_listing_url(li.url)
            # Always mark as notified locally to prevent duplicates even if Telegram fails
            if _key not in notified_urls:
                try:
                    sent = send_telegram(telegram_token, telegram_chat, msg)
                except Exception:
                    sent = False
                notified_urls.add(_key)
            # Also record fingerprint to catch reposts under new URLs
            if fp is not None:
                notified_fps.add(fp)
            continue

        if potential:
            okp, why2, negotiated, tgt2, profit2 = evaluate_potential(
                li.price, nada_vals, low_margin, negotiate_pct, min_profit, profit_mode
            )
            if okp:
                fp = listing_fingerprint(li.title, li.price)
                if fp is not None and fp in notified_fps:
                    if explain: LOG.info(f"Skip potential by fingerprint duplicate: {li.title} @ {li.price}")
                    continue
                # Same miles/title gate for potentials before notifying/logging
                detail_text = fetch_facebook_detail_hints(mgr, li.url) if li.source == "facebook" else fetch_offerup_detail_text(mgr, li.url)
                miles_val = extract_miles_from_text((li.title + " \n " + (detail_text or "")).strip())
                flags = branded_title_flags(detail_text)
                if miles_val is not None and miles_val > max_miles:
                    counters["miles_exceeded"] += 1
                    if explain: LOG.info(f"Reject potential by miles: {miles_val:,} > {max_miles:,} :: {li.title}")
                    continue
                if (not branded_bikes) and flags:
                    counters["title_branded"] += 1
                    if explain: LOG.info(f"Reject potential by title flags: {flags} :: {li.title}")
                    continue
                counters["potential"] += 1
                msg = (f"Potential 🤝\n{li.title}\nAsk: ${li.price:,} → Neg: ${negotiated:,}\n"
                       f"NADA: low={nada_vals.get('low_retail')} avg={nada_vals.get('avg_retail')} msrp={nada_vals.get('msrp')}\n"
                       + (f"Miles: {miles_val:,}\n" if miles_val is not None else "") +
                       f"{why2}\n{li.url}")
                if explain: LOG.info(msg)
                row = {"ts":now_str(),"kind":"potential","source":"facebook" if li.source=="facebook" else li.source,"title":li.title,"price":li.price,
                       "year":year,"make":make,"modelish":modelish,
                       "nada_low":nada_vals.get("low_retail"),"nada_avg":nada_vals.get("avg_retail"),
                       "nada_msrp":nada_vals.get("msrp"),"nada_url":nada_vals.get("source_url"),
                       "low_margin":low_margin,"negotiate_pct":negotiate_pct,"profit_baseline":profit_mode,
                       "profit":profit2,"target":tgt2,"negotiated_price":negotiated,
                       "miles": miles_val, "title_flags": ",".join(flags) if flags else None,
                       "url":li.url}
                _append_csv(potentials_csv, row)
                _key = canonicalize_listing_url(li.url)
                if notify_potential and _key not in notified_urls:
                    try:
                        sent = send_telegram(telegram_token, telegram_chat, msg)
                    except Exception:
                        sent = False
                    notified_urls.add(_key)
                    if fp is not None:
                        notified_fps.add(fp)
                continue

        if explain: LOG.debug(f"Reject: {li.title} — reason={why} (NADA {nada_tuple_for_log(nada_vals)})")
        if why in counters: counters[why] += 1
        else: counters["threshold_miss"] += 1

    LOG.info(f"Summary: deals={counters['deals']} potential={counters['potential']} "
             f"rejects: price_missing={counters['price_missing']} parse_failed={counters['parse_failed']} "
             f"no_valuation={counters['no_valuation']} no_low={counters['no_low']} no_baseline={counters['no_baseline']} "
             f"miles_exceeded={counters['miles_exceeded']} title_branded={counters['title_branded']} parts_gear={counters['parts_gear']} "
             f"threshold_miss={counters['threshold_miss']} too_old={counters['too_old']} total={counters['total']}")
    LOG.info("Cycle complete.")

# ============================== CLI ==============================
def parse_years_span(span: str) -> Tuple[int,int]:
    m = re.match(r"^\s*(\d{4})\s*-\s*(\d{4})\s*$", span)
    if not m: raise ValueError("Invalid --nada-scan-years format. Use e.g. 2005-2025")
    a,b = int(m.group(1)), int(m.group(2))
    if a>b: a,b=b,a
    return a,b

def run_main():
    ap = argparse.ArgumentParser(description="OfferUp + Facebook + JD Power (NADA) deal finder")

    # Sources
    ap.add_argument("--offerup", action="store_true", help="enable OfferUp scraping")
    ap.add_argument("--offerup-endpoint", choices=["search","explore","both"], default="both",
                    help="OfferUp surface to scrape: search results, explore feed, or both")
    ap.add_argument("--facebook", action="store_true", help="enable Facebook Marketplace scraping")
    ap.add_argument("--fb-endpoint", choices=["search","category","both"], default="both",
                    help="Facebook: use search, category feed, or both")

    # NADA modes
    ap.add_argument("--nada", action="store_true", help="enable NADA lookups")
    ap.add_argument("--nada-cache", type=str, default=None, help="path to local NADA (JD Power) cache JSON")
    ap.add_argument("--nada-online-fallback", action="store_true", help="if cache miss, try live JD Power")
    ap.add_argument("--require-cache", action="store_true", help="fail fast if cache is empty/missing")

    # NADA scan (kept intact)
    ap.add_argument("--nada-scan-once", action="store_true", help="crawl JD Power once to build/update the local cache")
    ap.add_argument("--nada-scan-years", type=str, default="2005-2025",
                    help="year span to scan for JD Power, e.g. '2005-2025'")
    ap.add_argument("--nada-scan-makes", type=str, default="harley-davidson,honda,yamaha,suzuki,kawasaki,bmw,triumph,ducati,ktm,indian-motorcycle,aprilia,cfmoto,vespa,buell,can-am,polaris",
                    help="comma-separated list of makes for JD Power scan")
    ap.add_argument("--nada-progress", type=str, default=".nada_progress.json",
                    help="path to resume checkpoint file for long JD Power scans")
    ap.add_argument("--resume", action="store_true", help="resume NADA scan from last checkpoint")
    ap.add_argument("--nada-cache-mode", choices=["merge","overwrite"], default="merge",
                    help="when scanning, merge into existing cache or overwrite it (default: merge)")

    # NADA display helper
    ap.add_argument("--nada-display", action="store_true", help="inspect local NADA cache instead of scraping")
    ap.add_argument("--display-year", type=int, default=None, help="filter display by year")
    ap.add_argument("--display-make", type=str, default=None, help="filter display by make (lowercase)")
    ap.add_argument("--display-like", type=str, default=None, help="substring filter for model titles")
    ap.add_argument("--display-limit", type=int, default=100, help="max entries to print in display mode")

    # Pacing / backoff
    ap.add_argument("--nada-list-pace-ms", type=int, default=900, help="delay between JD Power list page scrolls (ms)")
    ap.add_argument("--nada-pace-ms", type=int, default=2200, help="delay before loading a JD Power model page (ms)")
    ap.add_argument("--backoff-seconds", type=int, default=600, help="cooldown when site blocking is detected (s)")

    # Browser
    ap.add_argument("--user-data-dir", type=str, default=None, help="Playwright profile dir (persists FB login cookies)")
    ap.add_argument("--headless", action="store_true", help="run browser without a visible window")
    ap.add_argument("--restart-after-navs", type=int, default=200, help="relaunch browser after N navigations")
    ap.add_argument("--recycle-every-seconds", type=int, default=480, help="relaunch browser after this many seconds")
    ap.add_argument("--nav-timeout-ms", type=int, default=60000, help="navigation timeout per page load in ms")

    # FB login helper
    ap.add_argument("--login-fb", action="store_true", help="open a browser window to log into Facebook")
    ap.add_argument("--fb-login-mode", type=str, default="wait", choices=["wait","enter","never"],
                    help="wait: poll for login; enter: pause for ENTER; never: do not assist login")
    ap.add_argument("--fb-wait-login-seconds", type=int, default=40, help="how long to wait for login in 'wait' mode")

    # Search params
    ap.add_argument("--price-min", type=int, default=1000, help="minimum asking price to search")
    ap.add_argument("--price-max", type=int, default=15000, help="maximum asking price to search")
    ap.add_argument("--year-min", type=int, default=2005, help="minimum model year to consider")
    ap.add_argument("--explain", action="store_true", help="log reasons for skips and matches in detail")

    # Deal tuning
    ap.add_argument("--low-margin", type=float, default=0.05, help="target = NADA Low Retail × (1+low-margin)")
    ap.add_argument("--min-profit", type=int, default=1000, help="minimum required profit vs chosen NADA baseline")
    ap.add_argument("--profit-baseline", choices=["avg","low","avg_or_low"], default="avg",
                    help="which NADA value to use when computing profit")
    ap.add_argument("--max-miles", type=int, default=25000, help="maximum acceptable mileage; if mileage is unknown, do not filter")
    ap.add_argument("--branded-bikes", action="store_true", help="include salvage/rebuilt/no-title bikes (disabled by default)")

    # Potential deals
    ap.add_argument("--potential", action="store_true", help="also surface potential deals after negotiation")
    ap.add_argument("--negotiate-pct", type=float, default=0.20, help="expected negotiation discount for potentials (0–1)")
    ap.add_argument("--notify-potential", action="store_true", help="send Telegram notifications for potential deals")
    ap.add_argument("--include-parts", action="store_true", help="include parts/gear/accessories listings (disabled by default)")

    # Persisted dedupe (skip repeats across restarts)
    ap.add_argument("--persist-dedupe", action="store_true", help="persist seen/notified URLs to a file across restarts")
    ap.add_argument("--dedupe-file", type=str, default=None, help="path to dedupe state JSON (defaults to dedupe_state.json when --persist-dedupe is set)")

    # Loop vs once
    grp = ap.add_mutually_exclusive_group(); grp.add_argument("--loop", action="store_true", help="run continuously with sleep between cycles"); grp.add_argument("--once", action="store_true", help="run a single cycle and exit")
    ap.add_argument("--sleep-seconds", type=int, default=600, help="delay between cycles when running in --loop")

    # Logs
    ap.add_argument("--deals-csv", type=str, default="deals.csv", help="CSV file to append confirmed deals")
    ap.add_argument("--potentials-csv", type=str, default="potentials.csv", help="CSV file to append potential deals")

    # Telegram
    ap.add_argument("--telegram-token", "--tg-token", dest="telegram_token", type=str, default=None,
                    help="Telegram bot token for notifications (optional)")
    ap.add_argument("--telegram-chat", "--tg-chat", dest="telegram_chat", type=str, default=None,
                    help="Telegram chat ID to receive notifications (optional)")

    args = ap.parse_args()

    LOG.info("Bike Deal Bot starting…")
    send_telegram(args.telegram_token, args.telegram_chat, f"🟢 Bike Deal Bot started at {now_str()}")

    # QoL: if a cache path is provided but --nada wasn’t set, enable valuations automatically
    if args.nada_cache and not args.nada and not args.nada_scan_once and not args.nada_display:
        LOG.info("--nada-cache provided; enabling NADA valuations.")
        args.nada = True

    # Load cache (once) and validate if required
    cache_path = args.nada_cache or "nada_cache.json"
    cache = nada_cache_load(cache_path) if (args.nada or args.nada_display or args.nada_scan_once) else {}

    if (getattr(args, "require_cache", False) or args.nada) and not args.nada_scan_once:
        if not cache:
            raise SystemExit(
                f"ERROR: NADA cache is empty or missing at '{cache_path}'. "
                f"Pass --nada-cache <path> (and build it with --nada-scan-once if needed)."
            )

    # Optional display mode for quick inspection
    if args.nada_display:
        if not cache: print("NADA cache: (empty)"); return
        like = (args.display_like or "").lower().strip() or None
        if args.display_year and args.display_make:
            yr = str(args.display_year); mk = args.display_make.lower()
            recs = cache.get(yr, {}).get(mk, {})
            print(f"NADA cache entries for {yr}/{mk}: {len(recs)}")
            shown = 0
            for slug, rec in sorted(recs.items()):
                text = f"{rec.get('title','')} [{slug}]"
                if like and like not in text.lower(): continue
                print(f" - {text} :: Low={rec.get('low_retail')} Avg={rec.get('avg_retail')} MSRP={rec.get('msrp')}  URL={rec.get('url')}")
                shown += 1
                if shown >= args.display_limit: break
        else:
            total = 0; print("NADA cache summary by year/make:")
            for yr in sorted(cache.keys()):
                makes = cache[yr]; line=[]
                for mk in sorted(makes.keys()):
                    cnt = len(makes[mk]); total += cnt; line.append(f"{mk}:{cnt}")
                print(f" {yr} :: {'  '.join(line)}")
            print(f"Total models cached: {total}")
        return

    # Start with JD Power allowlisted (we’ll toggle later)
    mgr = BrowserMgr(
        user_data_dir=args.user_data_dir, headless=bool(args.headless),
        allow_domains=["jdpower.com"], restart_after_navs=args.restart_after_navs,
        recycle_every_seconds=args.recycle_every_seconds, nav_timeout_ms=args.nav_timeout_ms
    )
    mgr.start()

    try:
        if args.login_fb:
            ensure_facebook_login(mgr, args.fb_login_mode, args.fb_wait_login_seconds); return

        if args.nada_scan_once:
            years = parse_years_span(args.nada_scan_years)
            makes = [m.strip().lower() for m in args.nada_scan_makes.split(",") if m.strip()]
            out_path = cache_path
            LOG.info(f"Starting NADA scan {years} for makes={makes} -> {out_path}")
            nada_scan_once(mgr, years, makes, out_path, args.nada_list_pace_ms, args.nada_pace_ms,
                           args.backoff_seconds, args.nada_progress, bool(args.resume), args.nada_cache_mode=="merge")
            return

        # Marketplaces need full network (drop allowlist)
        if args.offerup or args.facebook:
            mgr.allow_domains = set()

        notified_urls: set = set()
        # Track canonical URL -> last seen price for skipping in later cycles
        seen_index: Dict[str, Optional[int]] = {}
        # Track notified fingerprints across runs
        notified_fps: set = set()

        # Load persisted dedupe if enabled
        dedupe_path: Optional[str] = None
        if bool(getattr(args, "persist_dedupe", False)):
            dedupe_path = args.dedupe_file or "dedupe_state.json"
            si, nu, nfps = _dedupe_load(dedupe_path)
            if si: seen_index.update(si)
            if nu: notified_urls |= nu
            if nfps: notified_fps |= nfps

        def do_cycle():
            listings: List[Listing] = []
            if args.offerup:
                LOG.info("Scraping OfferUp…")
                try: listings += scrape_offerup(mgr, args.price_min, args.price_max, args.offerup_endpoint, seen_index, notified_urls, exclude_parts=(not args.include_parts))
                except Exception as e: LOG.warning(f"OfferUp scraping failed: {e}")
            if args.facebook:
                LOG.info("Scraping Facebook…")
                try: listings += scrape_facebook(mgr, args.price_min, args.price_max, args.fb_endpoint, seen_index, notified_urls, exclude_parts=(not args.include_parts))
                except Exception as e: LOG.warning(f"Facebook scraping failed: {e}")

            if not listings:
                LOG.info("No listings found."); return

            # Dedup by canonical URL across sources
            uniq: Dict[str, Listing] = {}
            for li in listings:
                uniq.setdefault(canonicalize_listing_url(li.url), li)
            final = list(uniq.values())
            # Drop already-notified items completely from processing to save time
            def _fp_ok(li: Listing) -> bool:
                fpv = listing_fingerprint(li.title, li.price)
                return (fpv is None) or (fpv not in notified_fps)
            final = [li for li in final if (canonicalize_listing_url(li.url) not in notified_urls) and _fp_ok(li)]
            # Update seen_index so future cycles can skip these items if price unchanged
            for li in final:
                canon = canonicalize_listing_url(li.url)
                if li.price is not None:
                    seen_index[canon] = li.price

            if args.nada:
                # Re-enable JDP allowlist during valuations (only used for fallback)
                mgr.allow_domains = {"jdpower.com"}
                process_listings(
                    mgr, final, args.explain, args.year_min,
                    args.telegram_token, args.telegram_chat, notified_urls,
                    cache, args.nada_list_pace_ms, args.nada_pace_ms,
                    args.low_margin, args.min_profit, args.profit_baseline,
                    bool(args.potential), args.negotiate_pct, bool(args.notify_potential),
                    args.deals_csv, args.potentials_csv,
                    bool(args.nada_online_fallback),
                    args.max_miles, bool(args.branded_bikes), bool(args.include_parts), notified_fps
                )
                # Drop allowlist again for next marketplace pass
                mgr.allow_domains = set()
            else:
                for li in final:
                    LOG.info(f"[{li.source}] {li.title} — ${li.price:,} — {li.url}")

        if args.once or not args.loop:
            do_cycle()
            if dedupe_path:
                # Attach fingerprints to save call via attribute
                _dedupe_save._notified_fps = notified_fps  # type: ignore[attr-defined]
                _dedupe_save(dedupe_path, seen_index, notified_urls)
        else:
            while True:
                LOG.info(f"🔁 Loop tick at {now_str()}"); do_cycle()
                if dedupe_path:
                    _dedupe_save._notified_fps = notified_fps  # type: ignore[attr-defined]
                    _dedupe_save(dedupe_path, seen_index, notified_urls)
                LOG.info(f"Sleeping {args.sleep_seconds}s…"); time.sleep(max(1, int(args.sleep_seconds)))
    finally:
        mgr.stop()

# ============================== Safe entry (sync-in-async guard) ==============================
def _run_main_safely():
    def _target():
        try: run_main()
        except SystemExit: pass
        except Exception:
            import traceback; traceback.print_exc()
    try:
        loop = asyncio.get_event_loop()
        if loop.is_running():
            t = threading.Thread(target=_target, daemon=False); t.start(); t.join(); return
    except RuntimeError: pass
    _target()

if __name__ == "__main__":
    _run_main_safely()
