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
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from urllib.parse import urlencode, urlparse

from playwright.sync_api import (
    sync_playwright, BrowserContext, Page, TimeoutError as PWTimeout
)
try:
    import requests as _requests
except Exception:
    _requests = None

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

# Display names for KBB dropdowns (slug -> site label)
KBB_MAKE_NAMES = {
    "harley-davidson": "Harley-Davidson",
    "can-am": "Can-Am",
    "cfmoto": "CFMoto",
    "ktm": "KTM",
    "honda": "Honda",
    "yamaha": "Yamaha",
    "suzuki": "Suzuki",
    "kawasaki": "Kawasaki",
    "ducati": "Ducati",
    "bmw": "BMW",
    "triumph": "Triumph",
    "buell": "Buell",
    "vespa": "Vespa",
    "aprilia": "Aprilia",
    "indian": "Indian",
    "polaris": "Polaris",
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
_RE_CL_ITEM = re.compile(r"/([a-z]{2,})/([a-z]{3})/([\w\-]+)/?(\d+)\.html", re.I)

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
        if "craigslist.org" in host:
            # Normalize to scheme://<current-host>/<cat>/<postingid>.html
            m = re.search(r"/(?:search|[a-z]{2,})/([a-z]{3})/.*?(\d+)\.html", path, flags=re.I)
            if not m:
                m2 = re.search(r"/([a-z]{2,})/([a-z]{3})/[^/]*(\d+)\.html", path, flags=re.I)
            else:
                m2 = None
            pid = None; cat = None
            if m:
                cat = m.group(1).lower(); pid = m.group(2)
            elif m2:
                cat = m2.group(2).lower(); pid = m2.group(3)
            if pid and cat:
                return f"https://{host}/{cat}/{pid}.html"
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
        launch_args = ["--disable-blink-features=AutomationControlled"]
        if self.headless:
            # Improve headless stability in CI/servers and reduce detection
            launch_args += [
                "--no-sandbox",
                "--disable-dev-shm-usage",
                "--disable-gpu",
                "--window-size=1366,900",
                "--hide-scrollbars",
            ]
        self.context = self.pw.chromium.launch_persistent_context(
            user_data_dir=str(prof), headless=self.headless,
            viewport={"width":1366,"height":900}, args=launch_args,
            user_agent=(
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/121.0.0.0 Safari/537.36"
            ),
            locale="en-US"
        )
        self.context.route("**/*", self._route_filter)
        try:
            # Light stealth: mask webdriver/language/platform hints
            self.context.add_init_script(
                """
                Object.defineProperty(navigator, 'webdriver', {get: () => undefined});
                Object.defineProperty(navigator, 'language', {get: () => 'en-US'});
                Object.defineProperty(navigator, 'languages', {get: () => ['en-US','en']});
                Object.defineProperty(navigator, 'platform', {get: () => 'Win32'});
                """
            )
        except Exception:
            pass
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

# ============================== Navigation helpers (generic settle) ==============================
def wait_until_settled(mgr: BrowserMgr, selectors: Optional[List[str]] = None,
                       timeout_ms: int = 8000, check_interval_ms: int = 250) -> bool:
    """
    Wait for the page to be reasonably "ready":
    - Try load state 'load' quickly (non-fatal on failure)
    - Until timeout: if any selector exists, return True
    - Otherwise, sample body length and return when stable for a few cycles
    """
    end = time.time() + max(0.5, timeout_ms/1000.0)
    try:
        P(mgr).wait_for_load_state('load', timeout=min(timeout_ms, 2000))
    except Exception:
        pass
    last_len = None; stable = 0
    sels = selectors or []
    while time.time() < end:
        # Abort early if page was recycled/closed
        try:
            if hasattr(P(mgr), "is_closed") and P(mgr).is_closed():
                return False
        except Exception:
            pass
        # If caller provided target nodes, check them first
        try:
            for sel in sels:
                try:
                    loc = P(mgr).locator(sel)
                    if loc.count() > 0:
                        return True
                except Exception:
                    continue
        except Exception:
            pass
        # Heuristic: body size stability
        try:
            blen = P(mgr).evaluate("() => document.body ? document.body.innerText.length : 0")
        except Exception:
            blen = None
        if isinstance(blen, int) and blen > 0:
            if last_len is not None and abs(blen - last_len) < 20:
                stable += 1
                if stable >= 3:  # ~3*interval_ms ~ settled
                    return True
            else:
                stable = 0
            last_len = blen
        P(mgr).wait_for_timeout(check_interval_ms)
    return False

def goto_and_wait(mgr: BrowserMgr, url: str, selectors: Optional[List[str]] = None,
                  wait: str = 'domcontentloaded', timeout_ms: int = 9000) -> bool:
    if not mgr.goto(url, wait=wait):
        return False
    ok = wait_until_settled(mgr, selectors, timeout_ms=timeout_ms)
    return ok

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

# ============================== KBB extraction (labels) ==============================
def _first_dollar_after_any(html: str, labels: List[str], window: int = 3000) -> Optional[int]:
    for lab in labels:
        for m in re.finditer(re.escape(lab), html, flags=re.I):
            seg = html[m.end(): m.end()+window]
            m2 = MONEY_RE_HTML.search(seg)
            if m2:
                try:
                    return int(m2.group(1).replace(",",""))
                except Exception:
                    continue
    return None

def kbb_extract_values_from_page(mgr: BrowserMgr) -> Dict[str, Optional[int]]:
    """
    Attempt to pull KBB motorcycle values from the current page.
    We look for "Trade-In" and "Typical Listing" labels in DOM or HTML fallback.
    Output keys: trade_in, retail. Also tolerate variants like "Trade In Value".
    """
    out = {"trade_in": None, "retail": None}
    # Try DOM first using label heuristics
    label_sets = {
        # Broaden synonyms as KBB text varies across flows
        "trade_in": [
            "Trade-In Value", "Trade In Value", "Trade-In", "Trade In",
            "Trade-In Range", "Trade In Range", "Trade-In Value Range", "Trade In Value Range",
            "Trade-In Pricing", "Trade In Pricing"
        ],
        "retail": [
            "Typical Listing Price", "Typical Listing", "Typical Price", "Listing Price",
            "Typical Listing Price Range", "Listing Price Range", "Typical Listing Pricing"
        ],
    }
    try:
        for key, labels in label_sets.items():
            for lab in labels:
                try:
                    el = P(mgr).locator(
                        "xpath=//*[translate(normalize-space(text()), 'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz')='" + lab.lower() + "']"
                    ).first
                    if el.count() == 0:
                        continue
                    # Look for a dollar value in the same row/container or immediately after
                    row = el.locator("xpath=ancestor::tr[1]")
                    if row.count() > 0:
                        price = row.locator("xpath=.//*[contains(text(),'$')]").first
                        if price.count() > 0:
                            v = _money_to_int(price.text_content())
                            if v is not None:
                                out[key] = v; break
                    cont = el.locator("xpath=ancestor::*[self::div or self::li][1]")
                    if cont.count() > 0:
                        price = cont.locator("xpath=.//*[contains(text(),'$')]").first
                        if price.count() > 0:
                            v = _money_to_int(price.text_content())
                            if v is not None:
                                out[key] = v; break
                    after = el.locator("xpath=following::*[contains(text(),'$')][1]")
                    if after.count() > 0:
                        v = _money_to_int(after.text_content())
                        if v is not None:
                            out[key] = v; break
                except Exception:
                    continue
    except Exception:
        pass
    # Fallback to raw HTML scan when DOM heuristics fail
    if out.get("trade_in") is None or out.get("retail") is None:
        try:
            html = P(mgr).content()
        except Exception:
            html = ""
        if html:
            if out.get("trade_in") is None:
                out["trade_in"] = _first_dollar_after_any(html, label_sets["trade_in"], 3600)
            if out.get("retail") is None:
                out["retail"] = _first_dollar_after_any(html, label_sets["retail"], 3600)
    return out

# ============================== KBB navigation helpers ==============================
def kbb_canonical(url: str) -> str:
    try:
        u = urlparse(url)
        if not u.scheme:
            return ("https://www.kbb.com" + (url if url.startswith("/") else ("/" + url)))
        return url
    except Exception:
        return url

def kbb_model_base_url(make: str, model_slug: str, year: int) -> str:
    mk = (make or "").strip().lower()
    slug = (model_slug or "").strip().lower()
    return f"https://www.kbb.com/motorcycles/{mk}/{slug}/{int(year)}/"

def kbb_normalize_model_slug(slug: str) -> str:
    """
    Normalize slugs that erroneously include style-only suffixes.
    We conservatively strip base-only markers; do NOT strip '-abs' here because some makes
    represent ABS as a separate model in certain years. We do strip obvious 'base' variants.
    """
    s = (slug or '').lower().strip('-')
    for suf in ("-base-style", "-base", "-standard", "-std"):
        if s.endswith(suf):
            s = s[: -len(suf)]
            s = s.strip('-')
    return s

# ------------------------------ KBB navigation reliability & pacing ------------------------------
_KBB_WAIT_MODE = "auto"  # auto|dom|net
_KBB_RATE_MS = 0
_KBB_JITTER_MS = 0

class _RateLimiter:
    def __init__(self, min_interval_ms: int):
        self.min_interval = max(0, int(min_interval_ms)) / 1000.0
        self._last = 0.0
        self._lock = threading.Lock()
    def acquire(self):
        if self.min_interval <= 0:
            return
        with self._lock:
            now = time.time()
            wait = self.min_interval - (now - self._last)
            if wait > 0:
                time.sleep(wait)
            self._last = time.time()

_KBB_RL: Optional[_RateLimiter] = None

def set_kbb_nav_prefs(wait_mode: str, rate_ms: int, jitter_ms: int):
    global _KBB_WAIT_MODE, _KBB_RATE_MS, _KBB_JITTER_MS, _KBB_RL
    mode = (wait_mode or "auto").strip().lower()
    if mode not in ("auto","dom","net"):
        mode = "auto"
    _KBB_WAIT_MODE = mode
    _KBB_RATE_MS = max(0, int(rate_ms or 0))
    _KBB_JITTER_MS = max(0, int(jitter_ms or 0))
    _KBB_RL = _RateLimiter(_KBB_RATE_MS) if _KBB_RATE_MS > 0 else None

def _kbb_rate_pause():
    try:
        if _KBB_RL is not None:
            _KBB_RL.acquire()
    except Exception:
        pass
    try:
        if _KBB_JITTER_MS > 0:
            time.sleep(random.uniform(0, _KBB_JITTER_MS/1000.0))
    except Exception:
        pass

def _nav_waits_for_mode() -> Tuple[str, ...]:
    if _KBB_WAIT_MODE == "dom":
        return ("domcontentloaded",)
    if _KBB_WAIT_MODE == "net":
        return ("networkidle",)
    return ("networkidle","domcontentloaded")

def _goto_kbb(mgr: BrowserMgr, url: str) -> bool:
    """KBB navigation wrapper with rate limiting, jitter, and wait-mode fallback."""
    waits = _nav_waits_for_mode()
    for w in waits:
        _kbb_rate_pause()
        if mgr.goto(url, wait=w):
            P(mgr).wait_for_timeout(300)
            if mgr.looks_blocked():
                LOG.warning(f"KBB: block/anti-bot page detected during nav to {url}; recycling…")
                time.sleep(2)
                mgr.recycle()
                continue
            return True
    return False

# ------------------------------ KBB navigation reliability ------------------------------
def _goto_with_retries(mgr: BrowserMgr, url: str, *, waits=("networkidle","domcontentloaded"), retries: int = 2, pause_ms: int = 250) -> bool:
    """Navigate with a couple of attempts and different wait strategies.
    Falls back from networkidle to domcontentloaded to avoid hangs on quiet pages.
    Also recycles the browser if a block page is detected.
    """
    for attempt in range(max(1, retries)):
        for w in (list(waits) or ["domcontentloaded"]):
            ok = mgr.goto(url, wait=w)
            P(mgr).wait_for_timeout(pause_ms)
            if not ok:
                continue
            try:
                if mgr.looks_blocked():
                    LOG.warning(f"KBB: block/anti-bot page detected during nav to {url}; recycling…")
                    time.sleep(3)
                    mgr.recycle()
                    continue
            except Exception:
                pass
            return True
        # brief backoff then retry
        P(mgr).wait_for_timeout(min(1200, 300 + attempt * 300))
    return False

def _kbb_fetch_prices_via_params(mgr: BrowserMgr, year: int, make: str, model_slug: str, detail_pause_ms: int, zip_code: Optional[str] = None) -> Dict[str, Optional[int]]:
    out: Dict[str, Optional[int]] = {"trade_in": None, "retail": None}
    base = kbb_model_base_url(make, model_slug, year)
    # Trade-In
    try:
        # Use explicit trade-in parameter (no hyphen) and include vehicle class
        url_t = base + "?pricetype=tradein&vehicleclass=motorcycles"
        P(mgr).wait_for_timeout(detail_pause_ms//2 if detail_pause_ms else 400)
        # Try networkidle then domcontentloaded to avoid long hangs
        if _goto_kbb(mgr, url_t):
            # Small settle time then extract
            P(mgr).wait_for_timeout(500)
            v = kbb_extract_values_from_page(mgr)
            # Only trust trade-in value on the trade-in page
            if v.get("trade_in") is not None:
                out["trade_in"] = v.get("trade_in")
            elif zip_code:
                # Attempt to set ZIP if value missing
                try:
                    _kbb_try_open_values(mgr, zip_code)
                    P(mgr).wait_for_timeout(350)
                    v = kbb_extract_values_from_page(mgr)
                    if v.get("trade_in") is not None:
                        out["trade_in"] = v.get("trade_in")
                except Exception:
                    pass
    except Exception:
        pass
    # Retail
    try:
        if out.get("retail") is None:
            # Typical Listing Price (aka retail)
            url_r = base + "?pricetype=retail&vehicleclass=motorcycles"
            P(mgr).wait_for_timeout(300)
            if _goto_kbb(mgr, url_r):
                P(mgr).wait_for_timeout(500)
                v = kbb_extract_values_from_page(mgr)
                if v.get("retail") is not None:
                    out["retail"] = v.get("retail")
                if out.get("trade_in") is None and v.get("trade_in") is not None:
                    out["trade_in"] = v.get("trade_in")
                elif zip_code and out.get("retail") is None:
                    try:
                        _kbb_try_open_values(mgr, zip_code)
                        P(mgr).wait_for_timeout(350)
                        v = kbb_extract_values_from_page(mgr)
                        if v.get("retail") is not None:
                            out["retail"] = v.get("retail")
                    except Exception:
                        pass
    except Exception:
        pass
    # Sanity: retail should not be lower than trade-in
    try:
        ti = out.get("trade_in"); rt = out.get("retail")
        if isinstance(ti, int) and isinstance(rt, int) and ti > rt:
            # Re-read retail once to confirm
            try:
                url_r2 = kbb_model_base_url(make, model_slug, year) + "?pricetype=retail&vehicleclass=motorcycles"
                if _goto_kbb(mgr, url_r2):
                    P(mgr).wait_for_timeout(350)
                    v2 = kbb_extract_values_from_page(mgr)
                    rt2 = v2.get("retail") if isinstance(v2.get("retail"), int) else v2.get("retail")
                    if isinstance(rt2, int):
                        rt = rt2
            except Exception:
                pass
            if isinstance(ti, int) and isinstance(rt, int) and ti > rt:
                LOG.warning("KBB: retail < trade-in after re-read; swapping values.")
                out["trade_in"], out["retail"] = rt, ti
    except Exception:
        pass
    return out

def _kbb_fetch_prices_and_styles(mgr: BrowserMgr, year: int, make: str, model_slug: str, detail_pause_ms: int, zip_code: Optional[str] = None) -> Tuple[Dict[str, Optional[int]], Dict[str, Dict[str, Optional[int]]]]:
    """
    Fetch base trade-in and retail for a model, plus per-style values when a style/trim select is present.
    Returns (base_values, styles_map) where styles_map maps style label -> {'trade_in': int|None, 'retail': int|None}.
    """
    base_vals = _kbb_fetch_prices_via_params(mgr, year, make, model_slug, detail_pause_ms, zip_code)
    styles: Dict[str, Dict[str, Optional[int]]] = {}
    try:
        base = kbb_model_base_url(make, model_slug, year)
        # Navigate to retail page (no trim) and enumerate style labels once
        url_r_base = base + "?pricetype=retail&vehicleclass=motorcycles"
        P(mgr).wait_for_timeout(250)
        style_pairs: List[Tuple[str, Optional[str]]] = []
        if _goto_kbb(mgr, url_r_base):
            P(mgr).wait_for_timeout(600)
            style_pairs = _kbb_collect_style_options(mgr)

        # Style synonyms that mean default/no trim param
        base_syn = {"base style", "base", "standard", "std"}

        for lab, trim_param in (style_pairs or []):
            lab_clean = (lab or "").strip()
            if not lab_clean:
                continue
            # Default style: values equal to base; no extra fetch needed
            if lab_clean.lower() in base_syn:
                # Ensure ordering retail >= trade_in
                rtv = base_vals.get('retail')
                tiv = base_vals.get('trade_in')
                try:
                    if isinstance(rtv, int) and isinstance(tiv, int) and tiv > rtv:
                        rtv, tiv = tiv, rtv
                except Exception:
                    pass
                styles[lab_clean] = {'retail': rtv, 'trade_in': tiv}
                continue

            # Try fast path: direct params with &trim= label
            canonical_trim = (trim_param or lab_clean).strip()
            q_trim = "&" + urlencode({"trim": canonical_trim})
            rtv: Optional[int] = None
            tiv: Optional[int] = None
            # Retail page by trim: trust only retail
            try:
                url_r = url_r_base + q_trim
                if _goto_kbb(mgr, url_r):
                    P(mgr).wait_for_timeout(550)
                    vr = kbb_extract_values_from_page(mgr)
                    rtv = vr.get('retail') if isinstance(vr.get('retail'), int) else vr.get('retail')
                    if rtv is None and zip_code:
                        try:
                            _kbb_try_open_values(mgr, zip_code)
                            P(mgr).wait_for_timeout(350)
                            vr = kbb_extract_values_from_page(mgr)
                            rtv = vr.get('retail') if isinstance(vr.get('retail'), int) else vr.get('retail')
                        except Exception:
                            pass
            except Exception:
                pass
            # Trade-in page by trim: trust only trade-in
            try:
                url_t = base + "?pricetype=tradein&vehicleclass=motorcycles" + q_trim
                if _goto_kbb(mgr, url_t):
                    P(mgr).wait_for_timeout(550)
                    vt = kbb_extract_values_from_page(mgr)
                    tiv = vt.get('trade_in') if isinstance(vt.get('trade_in'), int) else vt.get('trade_in')
                    if tiv is None and zip_code:
                        try:
                            _kbb_try_open_values(mgr, zip_code)
                            P(mgr).wait_for_timeout(350)
                            vt = kbb_extract_values_from_page(mgr)
                            tiv = vt.get('trade_in') if isinstance(vt.get('trade_in'), int) else vt.get('trade_in')
                        except Exception:
                            pass
            except Exception:
                pass

            # Sanity: swap if reversed
            try:
                if isinstance(rtv, int) and isinstance(tiv, int) and tiv > rtv:
                    rtv, tiv = tiv, rtv
            except Exception:
                pass
            styles[lab_clean] = {'retail': rtv, 'trade_in': tiv}
    except Exception:
        pass
    return base_vals, styles

def _kbb_collect_model_links_js(mgr: BrowserMgr, year: int, make: str) -> List[Tuple[str, str]]:
    try:
        results = P(mgr).evaluate(r"""(y,m) => {
            const out=[]; const A=[...document.querySelectorAll('a[href]')];
            const re=new RegExp(`/motorcycles/${m}/([^/?#]+)/${y}(?:[/?#]|$)`,'i');
            for (const a of A){ const href=a.href||a.getAttribute('href')||''; if(!href) continue;
                const lab=(a.getAttribute('aria-label')||a.innerText||a.textContent||'').replace(/\s+/g,' ').trim();
                let m1=href.match(re);
                if(!m1) continue; const slug=(m1[1]||'').toLowerCase(); if(!slug) continue;
                out.push([href, lab]); }
            return out;
        }""", year, make)
        return [(kbb_canonical(u), (txt or "").strip()) for u, txt in (results or [])]
    except Exception:
        return []

def _kbb_list_models_for_year_make(mgr: BrowserMgr, year: int, make: str, list_pause_ms: int) -> List[Tuple[str, str]]:
    models: List[Tuple[str, str]] = []; seen=set()
    candidates = [
        f"https://www.kbb.com/motorcycles/{make}/{year}/",
        f"https://www.kbb.com/motorcycles/{make}/",
        f"https://www.kbb.com/motorcycles/",
    ]
    for base in candidates:
        url = kbb_canonical(base)
        if not mgr.goto(url): continue
        P(mgr).wait_for_timeout(800)
        # Scroll a bit to trigger lazy lists
        try:
            P(mgr).mouse.wheel(0, 24000)
            P(mgr).wait_for_timeout(400)
        except Exception:
            pass
        pairs = _kbb_collect_model_links_js(mgr, year, make)
        if len(pairs) < 2:
            # Fallback: scan DOM anchors directly
            try:
                anchors = P(mgr).locator("a"); cnt = anchors.count()
                for i in range(min(cnt, 3000)):
                    href = anchors.nth(i).get_attribute("href") or ""
                    if not href: continue
                    if href.startswith("/"): href = "https://www.kbb.com" + href
                    href = kbb_canonical(href)
                    m = re.search(rf"/motorcycles/{make}/([^/?#]+)/{year}(?:[/?#]|$)", href, flags=re.I)
                    if not m: continue
                    slug = m.group(1).lower()
                    if not slug or slug == "motorcycles": continue
                    txt = (anchors.nth(i).text_content() or "").strip()
                    pairs.append((href, txt))
            except Exception:
                pass

        for href, txt in pairs:
            key = href.lower().split("?")[0]
            if key in seen: continue
            seen.add(key)
            models.append((href, txt))
        if models:
            break
        P(mgr).wait_for_timeout(list_pause_ms)
    return models

def _kbb_page_looks_like_values(mgr: BrowserMgr) -> bool:
    try:
        has_trade = P(mgr).locator("xpath=//*[contains(translate(., 'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'trade-in')] | //*[contains(translate(., 'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'trade in')]").count() > 0
    except Exception:
        has_trade = False
    try:
        has_tlp = P(mgr).locator("xpath=//*[contains(translate(., 'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'typical listing')]").count() > 0
    except Exception:
        has_tlp = False
    if not (has_trade or has_tlp):
        # Fallback: look for any $ near value-like blocks
        try:
            money_nodes = P(mgr).locator("xpath=//*[contains(text(),'$')]")
            return money_nodes.count() >= 3
        except Exception:
            return False
    return True

def _kbb_try_open_values(mgr: BrowserMgr, zip_code: Optional[str]) -> None:
    # If values already visible, nothing to do
    if _kbb_page_looks_like_values(mgr):
        return
    # Heuristic click on prominent CTAs
    try:
        # Role-based first
        pat = re.compile(r"(get|see|show).*(value|pricing|price)|trade-?in|typical listing|kbb value", re.I)
        btn = P(mgr).get_by_role("button", name=pat).first
        if btn.count() > 0:
            try: btn.scroll_into_view_if_needed(timeout=1500)
            except Exception: pass
            try:
                btn.click(timeout=2000); P(mgr).wait_for_timeout(800)
                if _kbb_page_looks_like_values(mgr): return
            except Exception: pass
        # Fallback scan
        buttons = P(mgr).locator("xpath=//a|//button")
        n = min(buttons.count(), 80)
        triggers = [
            "get", "value", "values", "pricing", "price", "trade", "trade-in", "typical", "listing",
            "kbb", "advisor", "my price", "your price", "get my", "get your", "see value"
        ]
        for i in range(n):
            t = (buttons.nth(i).text_content() or "").strip().lower()
            if any(k in t for k in triggers):
                try:
                    buttons.nth(i).click(timeout=2000)
                    P(mgr).wait_for_timeout(800)
                    if _kbb_page_looks_like_values(mgr): return
                except Exception:
                    continue
    except Exception:
        pass
    # Attempt to set ZIP if a prompt appears
    if zip_code:
        try:
            # Try common zip inputs
            inp = P(mgr).locator("xpath=//input[contains(translate(@placeholder,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'zip') or contains(translate(@aria-label,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'zip') or @name='zip' or contains(translate(@id,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'zip')] ").first
            if inp.count() > 0:
                inp.fill( str(zip_code) )
                try:
                    inp.press('Enter')
                except Exception:
                    pass
                P(mgr).wait_for_timeout(800)
        except Exception:
            pass


# ============================== KBB dropdown wizard helpers ==============================
def _kbb_click_dropdown(mgr: BrowserMgr, keywords: List[str]) -> bool:
    kw = [k for k in keywords if k]
    # Role-based (pierces shadow DOM)
    try:
        pat = re.compile("|".join(re.escape(k) for k in kw), re.I)
        dd = P(mgr).get_by_role("combobox", name=pat).first
        if dd.count() > 0:
            try: dd.scroll_into_view_if_needed(timeout=1500)
            except Exception: pass
            dd.click(timeout=2000); P(mgr).wait_for_timeout(250)
            return True
    except Exception:
        pass
    # Fallback
    try:
        btns = P(mgr).locator("xpath=(//button|//div|//span)")
        n = min(btns.count(), 180)
        for i in range(n):
            t = (btns.nth(i).text_content() or "").strip()
            aria = (btns.nth(i).get_attribute("aria-label") or "").strip()
            hay = (t + " " + aria).lower()
            if not hay: continue
            if any(k.lower() in hay for k in kw):
                try: btns.nth(i).scroll_into_view_if_needed(timeout=1500)
                except Exception: pass
                try:
                    btns.nth(i).click(timeout=2000); P(mgr).wait_for_timeout(250)
                    return True
                except Exception:
                    continue
    except Exception:
        pass
    return False

def _kbb_choose_option(mgr: BrowserMgr, value_text: str) -> bool:
    raw = (value_text or "").strip()
    if not raw:
        return False
    # Role-based exact/contains
    try:
        exact = P(mgr).get_by_role("option", name=re.compile(rf"^\s*{re.escape(raw)}\s*$", re.I)).first
        if exact.count() > 0:
            exact.scroll_into_view_if_needed(timeout=1500)
            exact.click(timeout=2000); P(mgr).wait_for_timeout(300)
            return True
        contains = P(mgr).get_by_role("option", name=re.compile(re.escape(raw), re.I)).first
        if contains.count() > 0:
            contains.scroll_into_view_if_needed(timeout=1500)
            contains.click(timeout=2000); P(mgr).wait_for_timeout(300)
            return True
    except Exception:
        pass
    # Generic options
    want = raw.lower()
    try:
        opts = P(mgr).locator("xpath=(//li|//button|//div)[@role='option' or contains(@class,'option') or contains(@class,'menu') or contains(@class,'list') or contains(@id,'option')]")
        n = min(opts.count(), 300)
        for i in range(n):
            t = (opts.nth(i).text_content() or "").strip().lower()
            if not t: continue
            if t == want or want in t:
                try: opts.nth(i).scroll_into_view_if_needed(timeout=1500)
                except Exception: pass
                try:
                    opts.nth(i).click(timeout=2000); P(mgr).wait_for_timeout(300)
                    return True
                except Exception:
                    continue
    except Exception:
        pass
    # Last resort exact-text
    try:
        el = P(mgr).locator("xpath=//*[normalize-space(translate(text(), 'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'))='" + want + "']").first
        if el.count() > 0:
            el.scroll_into_view_if_needed(timeout=1500)
            el.click(timeout=2000); P(mgr).wait_for_timeout(300)
            return True
    except Exception:
        pass
    return False

def _kbb_select_year_make(mgr: BrowserMgr, year: int, make_slug: str, zip_code: Optional[str]) -> bool:
    # Go to motorcycles home and try to use the wizard
    if not mgr.goto("https://www.kbb.com/motorcycles/"):
        return False
    P(mgr).wait_for_timeout(1000)
    # Set ZIP first if a prompt is present
    _kbb_try_open_values(mgr, zip_code)
    # Select Year
    if not _kbb_click_dropdown(mgr, ["year", "select year", "choose year"]):
        # try again after small scroll
        try:
            P(mgr).mouse.wheel(0, 10000); P(mgr).wait_for_timeout(300)
        except Exception:
            pass
        _kbb_click_dropdown(mgr, ["year", "select year"])  # best-effort
    _ = _kbb_choose_option(mgr, str(year))
    # Select Make (display name mapping)
    disp = KBB_MAKE_NAMES.get((make_slug or "").lower(), (make_slug or "").title())
    if not _kbb_click_dropdown(mgr, ["make", "select make", "choose make", disp]):
        # Sometimes the make dropdown appears only after year is chosen; wait/scroll
        P(mgr).wait_for_timeout(400)
        _kbb_click_dropdown(mgr, ["make", "select make", disp])
    ok_make = _kbb_choose_option(mgr, disp)
    return ok_make

def _kbb_open_model_dropdown(mgr: BrowserMgr) -> bool:
    # Prefer role-based selection
    try:
        dd = P(mgr).get_by_role("combobox", name=re.compile("model", re.I)).first
        if dd.count() > 0:
            dd.scroll_into_view_if_needed(timeout=1500)
            dd.click(timeout=2000); P(mgr).wait_for_timeout(250)
            return True
    except Exception:
        pass
    if _kbb_click_dropdown(mgr, ["model", "select model", "choose model"]):
        return True
    # Try again after slight scroll
    try:
        P(mgr).mouse.wheel(0, 8000); P(mgr).wait_for_timeout(300)
    except Exception:
        pass
    return _kbb_click_dropdown(mgr, ["model", "select model", "choose model"])

def _kbb_collect_style_options(mgr: BrowserMgr) -> List[Tuple[str, Optional[str]]]:
    """Enumerate style/trim options as (label, trimParam) pairs from a native select labeled 'Style'/'Trim'."""
    try:
        js = r"""
        () => {
          const sels = Array.from(document.querySelectorAll('select'));
          const isStyleSel = (s) => {
            const p=(s.getAttribute('placeholder')||'').toLowerCase();
            const a=(s.getAttribute('aria-label')||'').toLowerCase();
            const n=(s.getAttribute('name')||'').toLowerCase();
            return p.includes('style') || a.includes('style') || n.includes('style') || p.includes('trim') || a.includes('trim') || n.includes('trim');
          };
          for (const s of sels) {
            if (!isStyleSel(s)) continue;
            const out=[];
            for (const o of Array.from(s.querySelectorAll('option'))) {
              const t=(o.innerText||o.textContent||'').trim();
              if (!t) continue;
              if (o.disabled) continue;
              const tl=t.toLowerCase();
              if (tl==='style' || tl==='trim') continue; // placeholder
              let pv = (o.getAttribute('value')||'').trim();
              if (!pv) pv = (o.getAttribute('data-value')||'').trim();
              if (!pv) pv = (o.getAttribute('data-id')||'').trim();
              if (!pv) pv = (o.getAttribute('data-trim')||'').trim();
              out.push([t, pv||null]);
            }
            if (out.length) return out;
          }
          return [];
        }
        """
        arr = P(mgr).evaluate(js) or []
        pairs: List[Tuple[str, Optional[str]]] = []
        for it in arr:
            try:
                if isinstance(it, list) and len(it) >= 2:
                    lab = str(it[0]).strip()
                    pv = (str(it[1]).strip() or None)
                    if lab:
                        pairs.append((lab, pv))
                else:
                    lab = str(it).strip()
                    if lab:
                        pairs.append((lab, None))
            except Exception:
                continue
        return pairs
    except Exception:
        return []

def _kbb_select_style(mgr: BrowserMgr, style_label: str) -> bool:
    raw = (style_label or '').strip()
    if not raw:
        return False
    try:
        sel = P(mgr).locator("xpath=//select[contains(translate(@placeholder,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'style') or contains(translate(@aria-label,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'style') or contains(translate(@name,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'style') or contains(translate(@placeholder,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'trim') or contains(translate(@aria-label,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'trim') or contains(translate(@name,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'trim')]").first
        if sel.count() > 0:
            try:
                sel.select_option(label=raw)
                P(mgr).wait_for_timeout(350)
                return True
            except Exception:
                try:
                    opt = sel.locator(f"xpath=.//option[normalize-space(.)='{raw}']").first
                    if opt.count() > 0:
                        opt.click()
                        P(mgr).wait_for_timeout(350)
                        return True
                except Exception:
                    pass
    except Exception:
        pass
    return False

def _kbb_collect_models_from_dropdown(mgr: BrowserMgr) -> List[str]:
    models: List[str] = []
    try:
        # 1) Native <select placeholder="Model"> path (as in your example)
        try:
            js = r"""
            () => {
              const sels = Array.from(document.querySelectorAll('select'));
              const isModelSel = (s) => {
                const p=(s.getAttribute('placeholder')||'').toLowerCase();
                const a=(s.getAttribute('aria-label')||'').toLowerCase();
                const n=(s.getAttribute('name')||'').toLowerCase();
                return p.includes('model') || a.includes('model') || n.includes('model');
              };
              for (const s of sels) {
                if (!isModelSel(s)) continue;
                const out=[];
                for (const o of Array.from(s.querySelectorAll('option'))) {
                  const t=(o.innerText||o.textContent||'').trim();
                  if (!t) continue;
                  if (o.disabled) continue;
                  if (t.toLowerCase()==='model') continue; // placeholder
                  out.push(t);
                }
                if (out.length) return out;
              }
              return [];
            }
            """
            arr = P(mgr).evaluate(js)
            if isinstance(arr, list) and arr:
                # Preserve DOM order
                return [str(x).strip() for x in arr if str(x).strip()]
        except Exception:
            pass

        # 2) Fallback: open a custom combobox/listbox and enumerate role=option with scrolling
        if not _kbb_open_model_dropdown(mgr):
            return []

        seen: List[str] = []
        stability = 0

        def _add_visible_options() -> int:
            added = 0
            try:
                opts = P(mgr).get_by_role("option")
            except Exception:
                opts = P(mgr).locator("xpath=(//li|//button|//div)[@role='option' or contains(@class,'option') or contains(@class,'menu') or contains(@class,'list') or contains(@id,'option')]")
            count = min(getattr(opts, 'count', lambda: 0)(), 400)
            for i in range(count):
                try:
                    t = (opts.nth(i).text_content() or "").strip()
                except Exception:
                    t = ""
                if not t:
                    continue
                tl = t.lower()
                if any(x in tl for x in ["select", "choose", "all models", "see all", "filter", "model"]):
                    continue
                if t not in seen:
                    seen.append(t)
                    added += 1
            return added

        listbox = None
        try:
            lb = P(mgr).get_by_role("listbox").first
            if lb.count() > 0:
                listbox = lb
        except Exception:
            listbox = None
        if listbox is None:
            try:
                lb = P(mgr).locator("xpath=(//*[@role='listbox' or contains(@class,'menu') or contains(@class,'list')])[1]").first
                if lb.count() > 0:
                    listbox = lb
            except Exception:
                listbox = None

        _ = _add_visible_options()
        for _i in range(60):
            before = len(seen)
            did_scroll = False
            try:
                if listbox is not None:
                    try:
                        listbox.evaluate("el => { el.scrollTop = Math.min(el.scrollTop + 700, el.scrollHeight); }")
                        did_scroll = True
                    except Exception:
                        pass
            except Exception:
                pass
            if not did_scroll:
                try:
                    if listbox is not None:
                        listbox.press("PageDown")
                    else:
                        P(mgr).keyboard.press("PageDown")
                except Exception:
                    pass
            P(mgr).wait_for_timeout(160)
            _ = _add_visible_options()
            after = len(seen)
            stability = stability + 1 if after <= before else 0
            if stability >= 6:
                break

        models = seen
    except Exception:
        return []
    return models

def _kbb_collect_models_and_slugs(mgr: BrowserMgr, year: int, make: str) -> List[Tuple[str, Optional[str]]]:
    """
    Return a list of (label, slug_guess) pairs for the brand-year page.
    - Prefer native <select placeholder/name/aria-label="Model"> options.
    - Attempt to parse a slug from option value/attributes if present; else None.
    - When slug is None, caller can fall back to selecting from dropdown to discover it.
    """
    pairs: List[Tuple[str, Optional[str]]] = []
    try:
        js = r"""
        (y,m) => {
          const out=[];
          const sels = Array.from(document.querySelectorAll('select'));
          const isModelSel = (s) => {
            const p=(s.getAttribute('placeholder')||'').toLowerCase();
            const a=(s.getAttribute('aria-label')||'').toLowerCase();
            const n=(s.getAttribute('name')||'').toLowerCase();
            return p.includes('model') || a.includes('model') || n.includes('model');
          };
          const rx = new RegExp(`/motorcycles/${m}/([^/]+)/${y}(?:[/?#]|$)`, 'i');
          for (const s of sels) {
            if (!isModelSel(s)) continue;
            const opts = Array.from(s.querySelectorAll('option'));
            for (const o of opts) {
              const t=(o.innerText||o.textContent||'').trim();
              if (!t) continue;
              if (o.disabled) continue;
              if (t.toLowerCase()==='model') continue;
              let slug=null;
              const val=(o.getAttribute('value')||'');
              const attrs=[val, o.getAttribute('data-value')||'', o.getAttribute('data-href')||'', o.getAttribute('data-url')||''];
              for (const a of attrs) {
                if (!a) continue;
                let m1=a.match(rx);
                if (m1 && m1[1]) { slug=(m1[1].toLowerCase()); break; }
                // plain slug value like "yzf-r1"
                if (/^[a-z0-9\-]+$/i.test(a) && a.length <= 64 && !/^model$/i.test(a)) {
                  slug = a.toLowerCase(); break;
                }
              }
              out.push([t, slug]);
            }
            if (out.length) return out;
          }
          return out;
        }
        """
        arr = P(mgr).evaluate(js, int(year), str(make)) or []
        for it in arr:
            try:
                label = str(it[0]).strip()
                slug = (str(it[1]).strip().lower()) if (len(it) > 1 and it[1]) else None
                if label:
                    # Always provide a fallback slug guess from label and normalize to avoid style-only slugs
                    guess = slug or _slugify(label)
                    guess = kbb_normalize_model_slug(guess)
                    pairs.append((label, guess))
            except Exception:
                continue
        if pairs:
            return pairs
    except Exception:
        pass
    # Fallback to generic dropdown enumeration; provide slug guesses from labels
    names = _kbb_collect_models_from_dropdown(mgr)
    return [(n, kbb_normalize_model_slug(_slugify(n))) for n in names]

def _kbb_select_model(mgr: BrowserMgr, model_name: str) -> bool:
    # Prefer selecting on native <select> if present
    raw = (model_name or "").strip()
    if not raw:
        return False
    try:
        sel = P(mgr).locator("xpath=//select[contains(translate(@placeholder,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'model') or contains(translate(@aria-label,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'model') or contains(translate(@name,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'model')]").first
        if sel.count() > 0:
            try:
                sel.select_option(label=raw)
                P(mgr).wait_for_timeout(250)
                return True
            except Exception:
                # If select_option by label fails, try by visible option click
                try:
                    opt = sel.locator(f"xpath=.//option[normalize-space(.)='{raw}']").first
                    if opt.count() > 0:
                        opt.click()
                        P(mgr).wait_for_timeout(250)
                        return True
                except Exception:
                    pass
    except Exception:
        pass
    # Fallback to combobox/listbox selection
    if not _kbb_open_model_dropdown(mgr):
        return False
    return _kbb_choose_option(mgr, raw)

def _kbb_maybe_select_first_trim(mgr: BrowserMgr) -> None:
    # Some models require trim; attempt to pick first/"Base"
    if not _kbb_click_dropdown(mgr, ["trim", "select trim", "choose trim"]):
        return
    # Prefer "Base" if present, else first visible option
    if _kbb_choose_option(mgr, "Base"):
        return
    try:
        opts = P(mgr).locator("xpath=(//li|//button|//div)[@role='option' or contains(@class,'option')]")
        if opts.count() > 0:
            opts.nth(0).click(timeout=1500); P(mgr).wait_for_timeout(400)
    except Exception:
        pass

# Navigate to brand page and select year, then advance
def _kbb_go_to_brand(mgr: BrowserMgr, make_slug: str) -> bool:
    bases = [f"https://www.kbb.com/motorcycles/{make_slug}/"]
    for u in bases:
        if mgr.goto(kbb_canonical(u)):
            P(mgr).wait_for_timeout(700)
            return True
    return False

def _kbb_click_next(mgr: BrowserMgr) -> bool:
    try:
        pat = re.compile(r"^(next|continue)$|see (models?|results?|value|values)", re.I)
        btn = P(mgr).get_by_role("button", name=pat).first
        if btn.count() > 0:
            try: btn.scroll_into_view_if_needed(timeout=1200)
            except Exception: pass
            try:
                btn.click(timeout=2000); P(mgr).wait_for_timeout(500)
                return True
            except Exception: pass
        # fallback scan
        buttons = P(mgr).locator("xpath=//button|//a")
        n = min(buttons.count(), 80)
        for i in range(n):
            t = (buttons.nth(i).text_content() or "").strip().lower()
            if not t: continue
            if any(k in t for k in ["next","continue","see models","see model","see results","see value","see values","get value"]):
                try:
                    buttons.nth(i).click(timeout=2000); P(mgr).wait_for_timeout(500)
                    return True
                except Exception:
                    continue
    except Exception:
        pass
    return False

def _kbb_select_year_on_brand_page(mgr: BrowserMgr, year: int) -> bool:
    # Expect a year combobox on brand root
    ok = _kbb_click_dropdown(mgr, ["year","select year","choose year"])
    if not ok:
        try: P(mgr).mouse.wheel(0, 8000); P(mgr).wait_for_timeout(250)
        except Exception: pass
        ok = _kbb_click_dropdown(mgr, ["year","select year"])  # second try
    _ = _kbb_choose_option(mgr, str(year))
    # Advance
    _kbb_click_next(mgr)
    P(mgr).wait_for_timeout(600)
    return True

def _kbb_open_value_type(mgr: BrowserMgr, kind: str) -> bool:
    kind = (kind or '').lower()
    try:
        if kind.startswith('trade'):
            pat = re.compile(r"(see|get).*(trade-?in).*value", re.I)
        else:
            pat = re.compile(r"(see|get).*(typical).*listing.*price", re.I)
        btn = P(mgr).get_by_role("button", name=pat).first
        if btn.count() > 0:
            try: btn.scroll_into_view_if_needed(timeout=1500)
            except Exception: pass
            try:
                btn.click(timeout=2000); P(mgr).wait_for_timeout(900)
                return True
            except Exception:
                pass
        # Sometimes a link instead of button
        links = P(mgr).locator("xpath=//a")
        n = min(links.count(), 60)
        for i in range(n):
            t = (links.nth(i).text_content() or "").strip().lower()
            if not t: continue
            if (kind.startswith('trade') and ('trade' in t and 'value' in t)) or (not kind.startswith('trade') and ('typical' in t and 'listing' in t)):
                try:
                    links.nth(i).click(timeout=2000); P(mgr).wait_for_timeout(900)
                    return True
                except Exception:
                    continue
    except Exception:
        pass
    return False

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

# ------------------------------ KBB cache I/O ------------------------------
def kbb_cache_load(path: Optional[str]) -> Dict:
    if not path: return {}
    p = Path(path)
    if not p.exists():
        LOG.info(f"KBB cache file not found (first run is expected): {p}")
        return {}
    try:
        data = json.loads(p.read_text("utf-8"))
        years = list(data.keys())
        if not years:
            LOG.error("KBB cache loaded but empty.")
            return {}
        total = 0
        for yr in data.values():
            for mk in yr.values():
                total += len(mk)
        LOG.info(f"KBB cache: years={len(years)} models={total} path={p}")
        return data
    except Exception as e:
        LOG.error(f"Failed to read KBB cache: {e}")
        return {}

def kbb_cache_save(path: str, data: Dict):
    try:
        Path(path).write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        LOG.info(f"KBB cache saved: {path}")
    except Exception as e:
        LOG.warning(f"Failed saving KBB cache: {e}")

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

# ============================== KBB scan-once (skeleton) ==============================
def kbb_scan_once(mgr: BrowserMgr, years: Tuple[int,int], makes: List[str], cache_path: str,
                  list_pause_ms: int, detail_pause_ms: int, backoff_seconds: int,
                  progress_path: str, resume: bool, merge_cache: bool,
                  zip_code: Optional[str] = None, workers: int = 1, include_styles: bool = False):
    """
    Crawl KBB once to build the KBB cache.
    For each Year/Make: discover model links, try to open a values view,
    extract Trade-In and Typical Listing Price, and persist to cache.
    """
    cache: Dict = kbb_cache_load(cache_path) if merge_cache else {}
    ymin, ymax = years
    total_models = 0
    direct_hits = 0
    dropdown_fallbacks = 0
    resume_year, resume_make, resume_last_url = (load_progress(progress_path) if resume else (None, None, None))
    skipping = (resume_year, resume_make) if (resume and resume_year and resume_make) else None
    if not resume and Path(progress_path).exists():
        try: Path(progress_path).unlink()
        except Exception: pass

    for year in range(ymin, ymax+1):
        for make in makes:
            if skipping:
                y0, m0 = skipping
                if (year, make) < (y0, m0):
                    continue
                skipping = None
            save_progress(progress_path, year, make)
            # Prefer brand-root wizard; fallback to site wizard then anchor discovery
            try:
                models: List[Tuple[str, str]] = []
                # 1) Prefer direct brand-year page (dropdown shows models here)
                brand_year_url = f"https://www.kbb.com/motorcycles/{make}/{year}/"
                if mgr.goto(brand_year_url):
                    P(mgr).wait_for_timeout(800)
                    pairs = _kbb_collect_models_and_slugs(mgr, year, make)
                    if pairs:
                        for label, slug in pairs:
                            # Always prefer slug-first attempts; selection is last-resort
                            models.append((f"slug://{slug}", label))
                # 2) Brand wizard (brand root → pick year → models dropdown)
                if not models:
                    if _kbb_go_to_brand(mgr, make):
                        _kbb_select_year_on_brand_page(mgr, year)
                        pairs = _kbb_collect_models_and_slugs(mgr, year, make)
                        if pairs:
                            for label, slug in pairs:
                                models.append((f"slug://{slug}", label))
                # 3) Site wizard (motorcycles home → pick year/make → models dropdown)
                if not models:
                    if _kbb_select_year_make(mgr, year, make, zip_code):
                        pairs = _kbb_collect_models_and_slugs(mgr, year, make)
                        if pairs:
                            for label, slug in pairs:
                                models.append((f"slug://{slug}", label))
                # 4) Absolute fallback: try anchor discovery (rarely present on KBB)
                if not models:
                    models = _kbb_list_models_for_year_make(mgr, year, make, list_pause_ms)
            except Exception as e:
                LOG.warning(f"KBB list error {year}/{make}: {e}")
                mgr.recycle();
                continue
            LOG.info(f"KBB scan {year}/{make}: discovered {len(models)} candidate model links")

            # Resume: skip up to last URL if provided (disabled when workers>1)
            start_idx = 0
            if workers <= 1 and resume and resume_year == year and (resume_make or '').lower() == (make or '').lower() and resume_last_url:
                try:
                    canon_resume = kbb_canonical(resume_last_url)
                    for i, (u, _t) in enumerate(models):
                        if kbb_canonical(u) == canon_resume:
                            start_idx = i + 1; break
                except Exception:
                    pass

            # Parallel execution path using multiple browser workers
            if max(1, int(workers)) > 1 and models:
                jobs: List[Tuple[str, str]] = []
                for (u, label) in models[start_idx:]:
                    if not label:
                        continue
                    if u.startswith("slug://"):
                        slug_guess = u.split("slug://", 1)[1]
                    else:
                        slug_guess = _slugify(label)
                    jobs.append((label, slug_guess))

                def _do_one(idx: int, label: str, slug_guess: str) -> Optional[Tuple[str, Dict[str, Optional[int]], Dict[str, Dict[str, Optional[int]]], str, str]]:
                    wm = BrowserMgr(
                        user_data_dir=(str(mgr.user_data_dir) + f"-kbbw-{idx}" if mgr.user_data_dir else f"./playwright_profile_kbbw_{idx}"),
                        headless=mgr.headless,
                        allow_domains={"kbb.com", "kbbcdn.com"},
                        restart_after_navs=mgr.restart_after_navs,
                        recycle_every_seconds=mgr.recycle_every_seconds,
                        nav_timeout_ms=mgr.nav_timeout_ms,
                    )
                    try:
                        wm.start()
                        mslug = slug_guess or _slugify(label)
                        if include_styles:
                            vals, styles_map = _kbb_fetch_prices_and_styles(wm, year, make, mslug, detail_pause_ms, zip_code)
                        else:
                            vals = _kbb_fetch_prices_via_params(wm, year, make, mslug, detail_pause_ms, zip_code)
                            styles_map = {}
                        if not (vals.get('trade_in') or vals.get('retail')):
                            by_url = f"https://www.kbb.com/motorcycles/{make}/{year}/"
                            if wm.goto(by_url):
                                P(wm).wait_for_timeout(400)
                                if _kbb_select_model(wm, label):
                                    _kbb_maybe_select_first_trim(wm)
                                    _kbb_click_next(wm)
                                    m = re.search(r"/motorcycles/[^/]+/([^/]+)/\d{4}(?:[/?#]|$)", P(wm).url)
                                    if m:
                                        mslug = m.group(1)
                                        if include_styles:
                                            vals, styles_map = _kbb_fetch_prices_and_styles(wm, year, make, mslug, detail_pause_ms, zip_code)
                                        else:
                                            vals = _kbb_fetch_prices_via_params(wm, year, make, mslug, detail_pause_ms, zip_code)
                                            styles_map = {}
                                    else:
                                        v2 = kbb_extract_values_from_page(wm)
                                        if v2.get('trade_in') is not None and vals.get('trade_in') is None:
                                            vals['trade_in'] = v2.get('trade_in')
                                        if v2.get('retail') is not None and vals.get('retail') is None:
                                            vals['retail'] = v2.get('retail')
                        if not (vals.get('trade_in') or vals.get('retail')):
                            return None
                        base = kbb_model_base_url(make, mslug, year)
                        url_trade = base + "?pricetype=tradein&vehicleclass=motorcycles"
                        url_retail = base + "?pricetype=retail&vehicleclass=motorcycles"
                        final_url = url_retail if vals.get('retail') is not None else url_trade
                        return (mslug, vals, styles_map, label, final_url)
                    except Exception:
                        return None
                    finally:
                        try:
                            wm.stop()
                        except Exception:
                            pass

                with ThreadPoolExecutor(max_workers=max(1, int(workers))) as ex:
                    futs = []
                    for i, (label, slug_guess) in enumerate(jobs):
                        futs.append(ex.submit(_do_one, i, label, slug_guess))
                    for fut in as_completed(futs):
                        res = fut.result()
                        if not res:
                            continue
                        mslug, vals, styles_map, label, final_url = res
                        mslug = kbb_normalize_model_slug(mslug)
                        yr = str(year); mk = make.lower()
                        cache.setdefault(yr, {}).setdefault(mk, {})
                        cache[yr][mk][mslug] = {
                            "title": label or mslug.replace("-"," ").upper(),
                            "trade_in": vals.get("trade_in"),
                            "retail": vals.get("retail"),
                            "styles": styles_map if styles_map else None,
                            "url": final_url,
                        }
                        total_models += 1
                        direct_hits += 1
                        if total_models % 25 == 0:
                            kbb_cache_save(cache_path, cache)
                # Done with parallel processing for this year/make
                continue

            for (url, title) in models[start_idx:]:
                try:
                    P(mgr).wait_for_timeout(detail_pause_ms + random.randint(0, 350))
                    used_dropdown = url.startswith("dropdown://")
                    used_slug = url.startswith("slug://")
                    if used_dropdown:
                        # Ensure we are back on the brand-year page before each selection
                        brand_year_url = f"https://www.kbb.com/motorcycles/{make}/{year}/"
                        if not mgr.goto(brand_year_url):
                            continue
                        P(mgr).wait_for_timeout(400)
                        # Open dropdown and select the model by label
                        if not _kbb_select_model(mgr, title):
                            continue
                        _kbb_maybe_select_first_trim(mgr)
                        # Some flows require advancing; try but don't depend on it
                        _kbb_click_next(mgr)
                    elif used_slug:
                        # Go directly to price pages using the discovered slug
                        mslug = url.split("slug://", 1)[1]
                        # Fetch base + optional styles
                        if include_styles:
                            vals, styles_map = _kbb_fetch_prices_and_styles(mgr, year, make, mslug, detail_pause_ms, zip_code)
                        else:
                            vals = _kbb_fetch_prices_via_params(mgr, year, make, mslug, detail_pause_ms, zip_code)
                            styles_map = {}
                        if not (vals.get('trade_in') or vals.get('retail')):
                            # try a conservative slugify of the label as a fallback guess
                            guess = _slugify(title)
                            if guess and guess != mslug:
                                if include_styles:
                                    vals, styles_map = _kbb_fetch_prices_and_styles(mgr, year, make, guess, detail_pause_ms, zip_code)
                                else:
                                    vals = _kbb_fetch_prices_via_params(mgr, year, make, guess, detail_pause_ms, zip_code)
                                    styles_map = {}
                                if (vals.get('trade_in') or vals.get('retail')):
                                    mslug = guess
                        if (vals.get('trade_in') or vals.get('retail')):
                            # Fast-path: record without further navigation
                            yr = str(year); mk = make.lower()
                            cache.setdefault(yr, {}).setdefault(mk, {})
                            raw_slug = kbb_normalize_model_slug(mslug)
                            base = kbb_model_base_url(make, raw_slug, year)
                            url_trade = base + "?pricetype=tradein&vehicleclass=motorcycles"
                            url_retail = base + "?pricetype=retail&vehicleclass=motorcycles"
                            cache[yr][mk][raw_slug] = {
                                "title": title or raw_slug.replace("-"," ").upper(),
                                "trade_in": vals.get("trade_in"),
                                "retail": vals.get("retail"),
                                "styles": styles_map if styles_map else None,
                                # Prefer a retail URL when available
                                "url": url_retail if vals.get("retail") is not None else url_trade,
                            }
                            total_models += 1
                            direct_hits += 1
                            try:
                                save_progress(progress_path, year, make, cache[yr][mk][raw_slug]["url"])
                            except Exception:
                                pass
                            if total_models % 25 == 0:
                                kbb_cache_save(cache_path, cache)
                            # Skip the rest of the flow
                            continue
                        # fallback to dropdown selection if direct param failed
                        brand_year_url = f"https://www.kbb.com/motorcycles/{make}/{year}/"
                        if not mgr.goto(brand_year_url):
                            continue
                        P(mgr).wait_for_timeout(400)
                        if not _kbb_select_model(mgr, title):
                            continue
                        _kbb_maybe_select_first_trim(mgr)
                        _kbb_click_next(mgr)
                        dropdown_fallbacks += 1
                    else:
                        if not mgr.goto(kbb_canonical(url)):
                            continue
                    if mgr.looks_blocked():
                        LOG.warning("KBB: detected block page. Cooling down…")
                        time.sleep(max(60, backoff_seconds))
                        mgr.recycle()
                        if (not used_dropdown and (not mgr.goto(kbb_canonical(url)) or mgr.looks_blocked())):
                            LOG.warning("KBB: still blocked; skipping this model.");
                            continue

                    # Prefer direct price-type URLs for stability (post-selection only)
                    mslug: Optional[str] = None
                    m = re.search(r"/motorcycles/[^/]+/([^/]+)/\d{4}(?:[/?#]|$)", P(mgr).url)
                    if m: mslug = m.group(1)
                    if not mslug:
                        mslug = _slugify(title)
                    if include_styles:
                        vals, styles_map = _kbb_fetch_prices_and_styles(mgr, year, make, mslug, detail_pause_ms, zip_code)
                    else:
                        vals = _kbb_fetch_prices_via_params(mgr, year, make, mslug, detail_pause_ms, zip_code)
                        styles_map = {}
                    if not (vals.get('trade_in') or vals.get('retail')):
                        # Fallback to clicking value buttons if direct URLs didn't render
                        _kbb_open_value_type(mgr, 'trade') or _kbb_try_open_values(mgr, zip_code)
                        v1 = kbb_extract_values_from_page(mgr)
                        if v1.get('trade_in') is not None: vals['trade_in'] = v1.get('trade_in')
                        if v1.get('retail') is not None: vals['retail'] = v1.get('retail')
                        if vals.get('retail') is None:
                            _kbb_open_value_type(mgr, 'listing') or _kbb_try_open_values(mgr, zip_code)
                            v2 = kbb_extract_values_from_page(mgr)
                            if v2.get('retail') is not None: vals['retail'] = v2.get('retail')
                            if vals.get('trade_in') is None and v2.get('trade_in') is not None:
                                vals['trade_in'] = v2.get('trade_in')
                    if not (vals.get('trade_in') or vals.get('retail')):
                        continue

                    # Determine slug from URL or title
                    m = re.search(r"/motorcycles/[^/]+/([^/]+)/\d{4}(?:[/?#]|$)", P(mgr).url)
                    raw_slug = kbb_normalize_model_slug(m.group(1) if m else _slugify(title))

                    yr = str(year); mk = make.lower()
                    cache.setdefault(yr, {}).setdefault(mk, {})
                    use_slug = _pick_merge_slug(cache, year, mk, title, raw_slug) if merge_cache else raw_slug
                    cache[yr][mk][use_slug] = {
                        "title": title or use_slug.replace("-"," ").upper(),
                        "trade_in": vals.get("trade_in"),
                        "retail": vals.get("retail"),
                        "styles": styles_map if styles_map else None,
                        "url": P(mgr).url,
                    }
                    total_models += 1
                    try:
                        save_progress(progress_path, year, make, P(mgr).url)
                    except Exception:
                        pass
                    if total_models % 25 == 0:
                        kbb_cache_save(cache_path, cache)
                except Exception:
                    continue
    kbb_cache_save(cache_path, cache)
    LOG.info(f"KBB scan complete. Models cached: {total_models} (direct={direct_hits}, fallback={dropdown_fallbacks})")

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

# ============================== Craigslist ==============================
def fetch_craigslist_detail_text(mgr: BrowserMgr, url: str) -> Optional[str]:
    try:
        if not goto_and_wait(mgr, url, selectors=["h1","#titletextonly",".postingtitle","[role=heading]"], timeout_ms=8000):
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
        if not text:
            return None
        return text[:2000]
    except Exception:
        # HTTP fallback
        try:
            if _requests is None:
                return None
            headers = {
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                "Accept-Language": "en-US,en;q=0.9",
            }
            r = _requests.get(url, headers=headers, timeout=12)
            if r.status_code != 200:
                return None
            html = r.text
            txt = re.sub(r"<[^>]+>", " ", html)
            txt = CLEAN_SPACES.sub(" ", txt).strip()
            return txt[:2000] if txt else None
        except Exception:
            return None

def _cl_collect_cards(mgr: BrowserMgr) -> List[Tuple[str,str]]:
    try:
        items = P(mgr).locator("li.cl-search-result")
        out: List[Tuple[str,str]] = []
        if items.count() > 0:
            n = min(items.count(), 250)
            for i in range(n):
                try:
                    li = items.nth(i)
                    a = li.locator("a[href]").first
                    href = a.get_attribute("href") or ""
                    if not href:
                        continue
                    if href.startswith("/"):
                        href = f"https://{urlparse(P(mgr).url).netloc}{href}"
                    href = canonicalize_listing_url(href)
                    title = (li.locator("h3 a").first.text_content() or a.text_content() or "").strip()
                    try:
                        pr = (li.locator(".price").first.text_content() or "").strip()
                    except Exception:
                        pr = ""
                    label = (title + (f" {pr}" if pr else "")).strip()
                    out.append((href, label))
                except Exception:
                    continue
            return out
        items = P(mgr).locator("li.result-row")
        n = min(items.count(), 250)
        out = []
        for i in range(n):
            try:
                li = items.nth(i)
                a = li.locator("a.result-title, a[href]").first
                href = a.get_attribute("href") or ""
                if not href:
                    continue
                if href.startswith("/"):
                    href = f"https://{urlparse(P(mgr).url).netloc}{href}"
                href = canonicalize_listing_url(href)
                title = (a.text_content() or "").strip()
                try:
                    pr = (li.locator("span.result-price").first.text_content() or "").strip()
                except Exception:
                    pr = ""
                label = (title + (f" {pr}" if pr else "")).strip()
                out.append((href, label))
            except Exception:
                continue
        return out
    except Exception:
        return []

def _cl_collect_cards_html(mgr: BrowserMgr) -> List[Tuple[str,str]]:
    """Very robust fallback: scan raw HTML for posting anchors and nearby price snippets."""
    out: List[Tuple[str,str]] = []
    try:
        html = P(mgr).content() or ""
    except Exception:
        html = ""
    if not html:
        return out
    try:
        # Find posting links like /mca/<postid>.html or /<area>/<cat>/<postid>.html
        for m in re.finditer(r"href=\"([^\"]+/(?:[a-z]{3})/(\d+)\.html)\"", html, flags=re.I):
            href_rel = m.group(1)
            pid = m.group(2)
            try:
                href = href_rel
                if href.startswith("/"):
                    host = urlparse(P(mgr).url).netloc
                    href = f"https://{host}{href}"
                href = canonicalize_listing_url(href)
            except Exception:
                continue
            # Extract a simple label by looking around the link for title and price
            span = 300
            s = max(0, m.start()-span); e = min(len(html), m.end()+span)
            chunk = html[s:e]
            # Title heuristic: strip tags and compress spaces
            title = re.sub(r"<[^>]+>", " ", chunk)
            title = CLEAN_SPACES.sub(" ", title).strip()
            # Try to isolate something readable
            title = (title[:120]) if len(title) > 120 else title
            # Price if present
            pm = re.search(r"\$\s*([\d,]+)", chunk)
            label = title
            if pm:
                label = f"{title} ${pm.group(1)}"
            out.append((href, label))
    except Exception:
        return []
    # Dedup by URL
    seen=set(); uniq=[]
    for href, lab in out:
        if href in seen: continue
        seen.add(href); uniq.append((href, lab))
    return uniq

def _cl_fetch_search_http(url: str) -> List[Tuple[str,str]]:
    out: List[Tuple[str,str]] = []
    if _requests is None:
        return out
    try:
        headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
        }
        r = _requests.get(url, headers=headers, timeout=12)
        if r.status_code != 200 or not r.text:
            return out
        html = r.text
        base_host = urlparse(url).netloc
        # Find posting anchors
        for m in re.finditer(r"href=\"([^\"]+/(?:[a-z]{3})/[^\"]*(\d+)\.html)\"", html, flags=re.I):
            href = m.group(1)
            try:
                if href.startswith("/"):
                    href = f"https://{base_host}{href}"
                href = canonicalize_listing_url(href)
            except Exception:
                continue
            # Crude title/price context
            s = max(0, m.start()-240); e = min(len(html), m.end()+240)
            chunk = html[s:e]
            title = re.sub(r"<[^>]+>", " ", chunk)
            title = CLEAN_SPACES.sub(" ", title).strip()
            title = title[:120]
            pm = re.search(r"\$\s*([\d,]+)", chunk)
            label = f"{title} ${pm.group(1)}" if pm else title
            out.append((href, label))
        # Dedup
        seen=set(); uniq=[]
        for href, lab in out:
            if href in seen: continue
            seen.add(href); uniq.append((href, lab))
        return uniq
    except Exception:
        return []

def scrape_craigslist(mgr: BrowserMgr, price_min: int, price_max: int, zip_code: str, radius: int,
                      site: Optional[str] = None, endpoint: str = "mca",
                      seen_index: Optional[Dict[str, Optional[int]]] = None,
                      skip_urls: Optional[set] = None,
                      exclude_parts: bool = True) -> List[Listing]:
    items: List[Listing] = []
    bases: List[str] = []
    def _site_from_zip(z: str) -> Optional[str]:
        try:
            z = re.sub(r"\D+", "", z or "").strip()
            if len(z) < 3:
                return None
            z3 = int(z[:3])
        except Exception:
            return None
        if (750 <= z3 <= 754) or (760 <= z3 <= 764) or z3 in (761, 762):
            return "dallas"
        if 770 <= z3 <= 778:
            return "houston"
        if z3 in (733, 787) or 786 <= z3 <= 787:
            return "austin"
        if 780 <= z3 <= 782:
            return "sanantonio"
        if z3 == 767:
            return "waco"
        if z3 in (757, 759):
            return "easttexas"
        return None

    use_site = (site or "").strip().lower() or _site_from_zip(zip_code)
    if not use_site:
        LOG.warning("Craigslist: no --cl-site and no ZIP mapping available; please pass --cl-site explicitly (e.g., dallas).")
        return []
    if endpoint in ("mca", "both"):
        path = f"/search/mca?postal={zip_code}&search_distance={radius}&min_price={price_min}&max_price={price_max}&hasPic=1"
        host = f"https://{use_site}.craigslist.org"
        bases.append(host + path)
    if endpoint in ("search", "both"):
        path = f"/search/sss?query=motorcycle&postal={zip_code}&search_distance={radius}&min_price={price_min}&max_price={price_max}&hasPic=1"
        host = f"https://{use_site}.craigslist.org"
        bases.append(host + path)

    seen = set()
    for url in bases:
        if not goto_and_wait(mgr, url, selectors=["li.cl-search-result","li.result-row",".search-legend",".cl-results","#search-results"], timeout_ms=15000):
            continue
        try:
            # Nudge to trigger any lazy content
            P(mgr).mouse.wheel(0, 6000)
            P(mgr).wait_for_timeout(600)
        except Exception:
            pass
        # Optional: read totalcount if present for diagnostics
        try:
            tc = None
            legend = P(mgr).locator("css=.search-legend .totalcount").first
            if legend.count() > 0:
                tx = (legend.text_content() or "").strip()
                if tx.isdigit():
                    tc = int(tx)
            if isinstance(tc, int) and tc == 0:
                LOG.info("Craigslist reports 0 results by totalcount.")
        except Exception:
            pass
        pairs = _cl_collect_cards(mgr)
        if not pairs:
            # scroll once more and try fallback HTML scan
            try:
                P(mgr).mouse.wheel(0, 12000)
                P(mgr).wait_for_timeout(700)
            except Exception:
                pass
            pairs = _cl_collect_cards_html(mgr)
        if not pairs:
            # Last-resort: HTTP fetch of the search page (bypasses headless quirks)
            pairs = _cl_fetch_search_http(url)
        consecutive_skips = 0
        for href, label in pairs:
            if href in seen:
                continue
            seen.add(href)
            canon = href
            if skip_urls is not None and canon in skip_urls:
                consecutive_skips += 1
                if consecutive_skips >= 40:
                    break
                continue
            else:
                consecutive_skips = 0
            price = parse_price_from_text(label)
            if seen_index is not None and canon in seen_index and price is not None and seen_index.get(canon) == price:
                continue
            title = re.sub(r"\$[\d,]+.*", "", label).strip() or "Craigslist Listing"
            if exclude_parts and (is_likely_parts_or_gear(title) or is_likely_parts_or_gear(label)):
                continue
            if price is None and (seen_index is None or canon not in seen_index):
                try:
                    body = fetch_craigslist_detail_text(mgr, href) or ""
                    p2 = parse_price_from_text(body)
                    if p2 is not None:
                        price = p2
                except Exception:
                    pass
            if price is None:
                continue
            items.append(Listing(title=title, price=price, url=href, source="craigslist"))
    LOG.info(f"Craigslist {len(items)} raw items (dedup will follow)")
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
    # Ensure allowlist is open for Facebook
    try:
        mgr.allow_domains = set()
    except Exception:
        pass
    ok = goto_and_wait(mgr, "https://www.facebook.com/login",
                       selectors=["input[name='email']","input[name='pass']","[data-testid='royal_login_button']","form"],
                       timeout_ms=15000)
    if not ok:
        # Fallback to mobile login page which is often lighter
        ok = goto_and_wait(mgr, "https://m.facebook.com/login.php",
                           selectors=["input[name='email']","input[name='pass']","button[name='login']","form"],
                           timeout_ms=15000)
    if not ok:
        LOG.warning("Facebook: could not open login page (network or block).")
        return False
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
            # Source-specific detail text for miles/title checks
            if li.source == "facebook":
                detail_text = fetch_facebook_detail_hints(mgr, li.url)
            elif li.source == "offerup":
                detail_text = fetch_offerup_detail_text(mgr, li.url)
            elif li.source == "craigslist":
                detail_text = fetch_craigslist_detail_text(mgr, li.url)
            else:
                detail_text = fetch_offerup_detail_text(mgr, li.url)
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
                if li.source == "facebook":
                    detail_text = fetch_facebook_detail_hints(mgr, li.url)
                elif li.source == "offerup":
                    detail_text = fetch_offerup_detail_text(mgr, li.url)
                elif li.source == "craigslist":
                    detail_text = fetch_craigslist_detail_text(mgr, li.url)
                else:
                    detail_text = fetch_offerup_detail_text(mgr, li.url)
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

    # Craigslist
    ap.add_argument("--craigslist", action="store_true", help="enable Craigslist scraping")
    ap.add_argument("--cl-zip", type=str, default=None, help="Craigslist ZIP code for proximity search")
    ap.add_argument("--cl-radius", type=int, default=50, help="Craigslist search radius in miles")
    ap.add_argument("--cl-site", type=str, default=None, help="Craigslist site subdomain (e.g., dallas). Optional")
    ap.add_argument("--cl-endpoint", choices=["mca","search","both"], default="mca",
                    help="Craigslist surface: motorcycles category (mca), general search, or both")

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
    
    # KBB scan (new)
    ap.add_argument("--kbb-once", action="store_true", help="crawl KBB once to build/update the local cache")
    ap.add_argument("--kbb-cache", type=str, default=None, help="path to local KBB cache JSON")
    ap.add_argument("--kbb-scan-years", type=str, default="2005-2025",
                    help="year span to scan for KBB, e.g. '2005-2025'")
    ap.add_argument("--kbb-scan-makes", type=str, default="harley-davidson,honda,yamaha,suzuki,kawasaki,bmw,triumph,ducati,ktm,indian,aprilia,cfmoto,vespa,buell,can-am,polaris",
                    help="comma-separated list of makes for KBB scan")
    ap.add_argument("--kbb-progress", type=str, default=".kbb_progress.json",
                    help="path to resume checkpoint file for long KBB scans")
    ap.add_argument("--kbb-cache-mode", choices=["merge","overwrite"], default="merge",
                    help="when scanning, merge into existing KBB cache or overwrite it (default: merge)")
    ap.add_argument("--kbb-zip", type=str, default=None, help="optional ZIP code for region-specific KBB values")
    ap.add_argument("--kbb-workers", type=int, default=1, help="number of parallel browser workers for KBB scan")
    ap.add_argument("--multitread", type=int, default=None, help="alias for --kbb-workers (e.g. --multitread 2)")
    ap.add_argument("--kbb-styles", action="store_true", help="capture per-style (trim) values for each model")
    ap.add_argument("--kbb-wait-mode", choices=["auto","dom","net"], default="auto", help="page wait strategy: auto (networkidle→dom), dom, or net")
    ap.add_argument("--kbb-rate-ms", type=int, default=300, help="min milliseconds between KBB navigations across workers")
    ap.add_argument("--kbb-jitter-ms", type=int, default=300, help="max random jitter (ms) added to each KBB navigation")

    # KBB quick debug: list models for a single year/make and exit
    ap.add_argument("--kbb-list-models", action="store_true", help="list model labels and slug guesses for a single year/make and exit")
    ap.add_argument("--kbb-year", type=int, default=None, help="year to use with --kbb-list-models")
    ap.add_argument("--kbb-make", type=str, default=None, help="make (slug) to use with --kbb-list-models")

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
            # Ensure open network (no allowlist) and prefer headful for manual login
            mgr.allow_domains = set()
            if bool(args.headless):
                try:
                    LOG.info("--login-fb requested in headless mode; switching to headful for interactive login…")
                    mgr.stop(); mgr.headless = False; mgr.start()
                except Exception:
                    pass
            ensure_facebook_login(mgr, args.fb_login_mode, args.fb_wait_login_seconds); return

        # KBB: quick list-and-exit for a single year/make
        if args.kbb_list_models:
            if not (args.kbb_year and args.kbb_make):
                raise SystemExit("--kbb-list-models requires --kbb-year and --kbb-make")
            # Apply KBB pacing/nav prefs
            set_kbb_nav_prefs(args.kbb_wait_mode, args.kbb_rate_ms, args.kbb_jitter_ms)
            mgr.allow_domains = {"kbb.com", "kbbcdn.com"}
            url = f"https://www.kbb.com/motorcycles/{args.kbb_make.strip().lower()}/{int(args.kbb_year)}/"
            if not mgr.goto(url):
                raise SystemExit(f"Failed to open {url}")
            P(mgr).wait_for_timeout(1000)
            pairs = _kbb_collect_models_and_slugs(mgr, int(args.kbb_year), args.kbb_make.strip().lower())
            print(f"KBB {args.kbb_year}/{args.kbb_make.lower()} models: {len(pairs)}")
            for label, slug in pairs:
                print(f" - {label} :: slug={slug or '(unknown)'}")
            return

        if args.nada_scan_once:
            years = parse_years_span(args.nada_scan_years)
            makes = [m.strip().lower() for m in args.nada_scan_makes.split(",") if m.strip()]
            out_path = cache_path
            LOG.info(f"Starting NADA scan {years} for makes={makes} -> {out_path}")
            nada_scan_once(mgr, years, makes, out_path, args.nada_list_pace_ms, args.nada_pace_ms,
                           args.backoff_seconds, args.nada_progress, bool(args.resume), args.nada_cache_mode=="merge")
            return

        # KBB scan-once (scaffold)
        if args.kbb_once:
            kbb_years = parse_years_span(args.kbb_scan_years)
            kbb_makes = [m.strip().lower() for m in args.kbb_scan_makes.split(",") if m.strip()]
            kbb_path = args.kbb_cache or "kbb-cache.json"
            # Allow KBB network (include CDN)
            mgr.allow_domains = {"kbb.com", "kbbcdn.com"}
            # Apply KBB pacing/nav prefs
            set_kbb_nav_prefs(args.kbb_wait_mode, args.kbb_rate_ms, args.kbb_jitter_ms)
            LOG.info(f"Starting KBB scan (scaffold) {kbb_years} for makes={kbb_makes} -> {kbb_path}")
            workers = args.kbb_workers if args.kbb_workers and args.kbb_workers>0 else 1
            if args.multitread and args.multitread>0:
                workers = args.multitread
            if workers > 1 and args.resume:
                LOG.warning("--resume is disabled when using multiple workers; proceeding without resume.")
            kbb_scan_once(mgr, kbb_years, kbb_makes, kbb_path, args.nada_list_pace_ms, args.nada_pace_ms,
                          args.backoff_seconds, args.kbb_progress, False, args.kbb_cache_mode=="merge", args.kbb_zip, workers, bool(args.kbb_styles))
            return

        # Marketplaces need full network (drop allowlist)
        if args.offerup or args.facebook or getattr(args, "craigslist", False):
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
            if getattr(args, "craigslist", False):
                if not args.cl_zip:
                    LOG.warning("Craigslist: --cl-zip is required; skipping")
                else:
                    LOG.info("Scraping Craigslist…")
                    try:
                        listings += scrape_craigslist(
                            mgr, args.price_min, args.price_max,
                            str(args.cl_zip), int(args.cl_radius or 50), args.cl_site, args.cl_endpoint,
                            seen_index, notified_urls, exclude_parts=(not args.include_parts)
                        )
                    except Exception as e:
                        LOG.warning(f"Craigslist scraping failed: {e}")

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
