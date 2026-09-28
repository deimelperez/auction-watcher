#!/usr/bin/env python3
"""
RealAuction watcher (realtaxdeed / realforeclose).

Pulls the auction list for upcoming sale dates, filters it, and sends a
Telegram and/or email alert for items it hasn't seen before.

Usage:
    python auction_watcher.py                   # live run
    python auction_watcher.py --sample x.json   # parse a saved response (no network, no alerts)
    python auction_watcher.py --dry-run         # live fetch, print instead of alerting
    python auction_watcher.py --folio 28-2202-029-2320   # test the land-use lookup

Alerts: one when a listing first appears, then reminders REMIND_DAYS before the sale (default 7 and 1).

Config comes from environment variables (see CONFIG below).
"""
import argparse
import html
import json
import os
import re
import smtplib
import sys
import time
from datetime import date, datetime, timedelta
from email.message import EmailMessage
from pathlib import Path

import requests

# ----------------------------------------------------------------------------
# CONFIG (environment variables)
# ----------------------------------------------------------------------------
# RealAuction sites, comma-separated, each as URL|AUCT_TYPE|REPORT_ID
# (AUCT_TYPE 2 = tax deed; REPORT_ID = the quick-search page's Report_id).
# Miami-Dade tax deeds are listed on its realforeclose site; Broward uses realtaxdeed.
BASE_URLS = [u.strip().rstrip("/") for u in os.getenv(
    "BASE_URL", "https://www.miamidade.realforeclose.com|2|33,https://broward.realtaxdeed.com|2|33").split(",") if u.strip()]
# The site's "quick search" report: FilterData sets the date range in the session, LoadData returns rows.
# The quick-search page itself. Opening it registers a report id (REPID) in the session;
# FilterData/LoadData only work with that id, otherwise the site answers "report expired".
SEARCH_PAGE_PATH = os.getenv("SEARCH_PAGE_PATH", "/index.cfm?zaction=admin&zmethod=REPORT&Report_id={report_id}")
FILTER_PATH = ("/index.cfm?&AUCT_TYPE={auct_type}&CaseNumber=&view_ssdate={start}&view_sedate={end}"
               "&ParcelID=&PrimaryPlaintiffTD=&Address=&City=&Zip=&My_bids=null&CaseStatus=0,1,2,3,4,5,6"
               "&zaction=AJAX&zmethod=COM&process=REPVIEW&FUNC=FilterData&SHOWJSON=false&REPID={repid}&_={ms}")
LOAD_PATH = ("/index.cfm?zaction=AJAX&zmethod=COM&Process=REPVIEW&SHOWJSON=FALSE&REPID={repid}"
             "&func=LoadData&page={page}&rows=100&_={ms}")
# Links to open in your browser: the listing itself ({aid} = auction item id), and its sale-date page.
DETAIL_PATH = os.getenv("DETAIL_PATH", "/index.cfm?zaction=AUCTION&Zmethod=DETAILS&AID={aid}&bypassPage=1")
PREVIEW_PATH = "/index.cfm?zaction=AUCTION&Zmethod=PREVIEW&AUCTIONDATE={date}"
# Optional login (your own bidder account) to use the quick-search report, which includes
# each sale's status. Set RA_USER/RA_PASS as GitHub secrets; per-county overrides like
# RA_USER_BROWARD/RA_PASS_BROWARD win if the county uses a different account.
# Without them, the public calendar is used instead.
def creds_for(county: str) -> tuple[str, str] | None:
    u = os.getenv(f"RA_USER_{county.upper()}") or os.getenv("RA_USER", "")
    p = os.getenv(f"RA_PASS_{county.upper()}") or os.getenv("RA_PASS", "")
    return (u, p) if u and p else None


# Public calendar + per-day listing (no login needed)
CALENDAR_PATH = os.getenv("CALENDAR_PATH", "/index.cfm?zaction=USER&zmethod=CALENDAR")
DAY_LOAD_PATH = ("/index.cfm?zaction=AUCTION&Zmethod=UPDATE&FNC=LOAD&AREA=W&PageDir={page_dir}"
                 "&doR=1&bypassPage=1&test=1&tx={ms}&_={ms}")

# Report column positions (from the site's quick-search results)
COL = {"sale_date": 0, "case": 2, "status": 3, "bid": 5, "assessed": 6,
       "address": 9, "city": 10, "zip": 11, "parcel": 12}
SKIP_STATUSES = {s.strip().upper() for s in os.getenv("SKIP_STATUSES", "CANCELED,CANCELLED").split(",") if s.strip()}
MAX_PAGES = int(os.getenv("MAX_PAGES", "10"))
DATE_FORMAT = os.getenv("DATE_FORMAT", "%m/%d/%Y")
DAYS_AHEAD = int(os.getenv("DAYS_AHEAD", "45"))

AUCTION_TYPES = {t.strip().upper() for t in os.getenv("AUCTION_TYPES", "TAXDEED").split(",") if t.strip()}
MAX_BID = float(os.getenv("MAX_BID", "0") or 0)          # 0 = no limit
ZIPS = {z.strip() for z in os.getenv("ZIPS", "").split(",") if z.strip()}  # empty = any

SEEN_FILE = Path(os.getenv("SEEN_FILE", "seen.json"))
# Reminder alerts: days before the sale (default: a week before and a day before).
REMIND_DAYS = sorted({int(d) for d in os.getenv("REMIND_DAYS", "7,1").split(",") if d.strip()}, reverse=True)

TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN", "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")
SMTP_USER = os.getenv("SMTP_USER", "")        # e.g. you@gmail.com
SMTP_PASS = os.getenv("SMTP_PASS", "")        # Gmail app password
EMAIL_TO = os.getenv("EMAIL_TO", SMTP_USER)

# Land-use lookup (Miami-Dade parcel layer, public ArcGIS REST, no key needed)
PA_LAYER_URL = os.getenv(
    "PA_LAYER_URL",
    "https://gisweb.miamidade.gov/arcgis/rest/services/MD_LandInformation/MapServer/26",
)
# Alert only if the land-use description contains one of these words.
# Empty = no land-use filter. Parcels whose land use can't be found are still alerted.
# Broward (and any non-Miami-Dade county): Florida DOR statewide parcel layer.
STATEWIDE_LAYER_URL = os.getenv(
    "STATEWIDE_LAYER_URL",
    "https://services9.arcgis.com/Gh9awoU677aKree0/arcgis/rest/services/Florida_Statewide_Cadastral/FeatureServer/0",
)
# FDOR county numbers used by the statewide layer.
FDOR_COUNTY_NO = {"miamidade": 23, "broward": 16}
# Standard Florida DOR land-use codes (the statewide layer gives codes, not descriptions).
DOR_CODES = {
    0: "VACANT RESIDENTIAL", 1: "SINGLE FAMILY", 2: "MOBILE HOMES", 3: "MULTI-FAMILY 10+ UNITS",
    4: "CONDOMINIUM", 5: "COOPERATIVES", 8: "MULTI-FAMILY <10 UNITS", 9: "RESIDENTIAL COMMON AREAS",
    10: "VACANT COMMERCIAL", 40: "VACANT INDUSTRIAL", 70: "VACANT INSTITUTIONAL", 80: "VACANT GOVERNMENTAL",
}

# Comparable sales (from the statewide layer): vacant residential lots sold nearby.
COMP_RADIUS_FT = float(os.getenv("COMP_RADIUS_FT", "2640"))   # half a mile
COMP_YEARS = int(os.getenv("COMP_YEARS", "3"))                 # sales in the last N years
COMP_MIN = int(os.getenv("COMP_MIN", "3"))                     # widen to 2x radius if fewer found
COMP_MIN_PRICE = float(os.getenv("COMP_MIN_PRICE", "5000"))    # ignore token/family transfers

# Comma = OR, plus = AND. Default: vacant land zoned/used residential (i.e. land to build a house on).
LAND_USE_KEYWORDS = [
    [w.strip().upper() for w in k.split("+") if w.strip()]
    for k in os.getenv("LAND_USE_KEYWORDS", "VACANT+RESIDENTIAL").split(",") if k.strip()
]
# Never alert on these land uses (matched anywhere in the land-use description).
EXCLUDE_LAND_USE = [k.strip().upper() for k in os.getenv("EXCLUDE_LAND_USE", "CONDOMINIUM,CONDO").split(",") if k.strip()]
# Minimum lot size in square feet (0 = no minimum). Screens out slivers and too-small lots.
MIN_LOT_SQFT = float(os.getenv("MIN_LOT_SQFT", "5000") or 0)
# Florida East State Plane (US survey feet), so geometry areas come back in sq ft.
AREA_SR = os.getenv("AREA_SR", "2236")

HEADERS = {"User-Agent": "Mozilla/5.0 (personal auction watcher; 1 run/day)"}

# ----------------------------------------------------------------------------
# PARSING
# The site ships compressed HTML: tokens like @A @B @F @G stand in for tags and
# are expanded client-side. We don't expand them; we read label/value pairs.
#   "Parcel ID:@F tabindex="0" @CAD_DTA">28-2202-029-2320@G"
# ----------------------------------------------------------------------------
ITEM_SPLIT = re.compile(r'id="AITEM_(\d+)"')
FIELD_RE = re.compile(r'>\s*([^<>@:]+?):@F[^>]*?@CAD_DTA[^"]*">(.*?)@G', re.S)
CITY_RE = re.compile(r'scope="row">@F[^>]*?@CAD_DTA[^"]*">(.*?)@G', re.S)
TAG_RE = re.compile(r"<[^>]+>")
MONEY_RE = re.compile(r"[-\d,]+\.?\d*")


def clean(s: str) -> str:
    return html.unescape(TAG_RE.sub("", s)).strip()


def money(s: str | None) -> float | None:
    if not s:
        return None
    m = MONEY_RE.search(s.replace("$", ""))
    try:
        return float(m.group().replace(",", "")) if m else None
    except ValueError:
        return None


def parse_response(text: str, sale_date: str = "") -> list[dict]:
    data = json.loads(text, strict=False)  # strict=False tolerates raw newlines
    body = data.get("retHTML", "")
    parts = ITEM_SPLIT.split(body)
    # parts = [prefix, id1, chunk1, id2, chunk2, ...]
    items = []
    for i in range(1, len(parts) - 1, 2):
        aid, chunk = parts[i], parts[i + 1]
        fields = {k.strip(): clean(v) for k, v in FIELD_RE.findall(chunk)}
        city = CITY_RE.search(chunk)
        city_line = clean(city.group(1)) if city else ""
        zip_m = re.search(r"\b(\d{5})\b", city_line)
        items.append({
            "id": aid,
            "sale_date": sale_date,
            "type": fields.get("Auction Type", "").upper(),
            "case": fields.get("Case #", ""),
            "parcel": fields.get("Parcel ID", ""),
            "address": fields.get("Property Address", ""),
            "city": city_line,
            "zip": zip_m.group(1) if zip_m else "",
            # tax deed lists show Opening Bid; foreclosures show Final Judgment Amount
            "bid": money(fields.get("Opening Bid")) or money(fields.get("Final Judgment Amount")),
            "assessed": money(fields.get("Assessed Value")),
            "raw": fields,
        })
    return items


# ----------------------------------------------------------------------------
# FILTERING
# ----------------------------------------------------------------------------
def keep(item: dict) -> bool:
    if AUCTION_TYPES and item["type"].replace(" ", "") not in {t.replace(" ", "") for t in AUCTION_TYPES}:
        return False
    if MAX_BID and item["bid"] is not None and item["bid"] > MAX_BID:
        return False
    if ZIPS and item["zip"] and item["zip"] not in ZIPS:
        return False
    return True


def tags(item: dict) -> list[str]:
    t = []
    if not item["address"]:
        t.append("no street address (often vacant land)")
    if item["parcel"].upper().startswith("MULTIPLE"):
        t.append("multiple parcels")
    if item["assessed"] is not None and item["assessed"] < 5000:
        t.append("very low assessed value (possible sliver)")
    return t


# ----------------------------------------------------------------------------
# FETCHING
# ----------------------------------------------------------------------------
def sale_dates(days: int):
    d = date.today()
    for _ in range(days):
        d += timedelta(days=1)
        if d.weekday() < 5:  # sales run Mon-Fri
            yield d


def county_of(base: str) -> str:
    """'https://broward.realtaxdeed.com' -> 'broward'"""
    host = re.sub(r"^https?://(www\.)?", "", base)
    return host.split(".")[0].lower()


def parse_report(text: str, base: str) -> tuple[list[dict], int]:
    """Parse one page of the quick-search report. Returns (items, total_pages)."""
    data = json.loads(text, strict=False)
    err = ((data.get("userdata") or {}).get("errorMSG") or "").strip()
    if err:
        print(f"[warn] {county_of(base)}: site says: {err}", file=sys.stderr)
    items = []
    for row in data.get("rows") or []:
        c = row.get("cell") or []
        get = lambda k: (c[COL[k]] if COL[k] < len(c) else "") or ""
        # skip anything that isn't a real listing (error rows, headers, blank rows)
        if not re.fullmatch(r"\d{1,2}/\d{1,2}/\d{4}", get("sale_date").strip()) or not get("case").strip():
            print(f"[warn] {county_of(base)}: skipped odd row id={row.get('id')}: {c[:6]}", file=sys.stderr)
            continue
        zip5 = get("zip")[:5]
        items.append({
            "id": f"{county_of(base)}:{row.get('id')}",  # ids are per site, so prefix the county
            "sale_date": get("sale_date").strip(),
            "type": "TAXDEED",
            "status": get("status").strip(),
            "case": get("case").strip(),
            "parcel": get("parcel").strip(),
            "address": get("address").strip(),
            "city": f"{get('city').strip().upper()}, FL- {zip5}".strip(", -"),
            "zip": zip5 if zip5.isdigit() else "",
            "bid": money(get("bid")),
            "assessed": money(get("assessed")),
            "county": county_of(base),
            "aid": str(row.get("id")),
            "link": base + DETAIL_PATH.format(aid=row.get("id")),
            "day_link": base + PREVIEW_PATH.format(date=get("sale_date").strip()),
            "raw": c,
        })
    try:
        total = int(data.get("total") or 1)
    except ValueError:
        total = 1
    return items, total


def login(s: requests.Session, base: str, user: str, pw: str) -> bool:
    """Log in the same way the site's login form does. Never logs the password or the full reply."""
    r = s.post(base + "/index.cfm",
               data={"ZACTION": "AJAX", "ZMETHOD": "LOGIN", "func": "LOGIN", "USERNAME": user, "USERPASS": pw},
               timeout=30, headers={"X-Requested-With": "XMLHttpRequest"})
    r.raise_for_status()
    reply = re.sub(r"<[^>]+>", " ", r.text)
    if re.search(r"invalid|incorrect|not found|locked|captcha|verif|fail", reply, re.I):
        print(f"[warn] {county_of(base)}: login refused: {reply.strip()[:120]!r}", file=sys.stderr)
        return False
    return True


# Notices that mean accepting terms are left for you to accept in the browser.
TERMS_WORDS = re.compile(r"\bi agree\b|user agreement|terms (and|&) conditions|terms of (use|service)|"
                         r"license agreement|agree to (be )?(legally )?bound", re.I)


def find_notices(page_text: str) -> dict[str, str]:
    """NID -> short notice text, from any page the site returns after login."""
    found = {}
    for m in re.finditer(r"\bNID\W{0,6}(?:value\W{0,3})?(\d{3,})|Notice\w*\(\s*['\"]?(\d{3,})", page_text, re.I):
        nid = m.group(1) or m.group(2)
        around = page_text[max(0, m.start() - 1500): m.end() + 1500]
        text = re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", around)).strip()
        found.setdefault(nid, text)
    return found


def accept_notices(s: requests.Session, base: str, pages: list[str]) -> bool:
    """Acknowledge informational notices (like clicking OK). Returns False if a terms notice blocks us."""
    county, handled = county_of(base), set()
    for _ in range(5):  # accepting one can reveal the next
        notices = {k: v for p in pages for k, v in find_notices(p).items() if k not in handled}
        if not notices:
            return True
        for nid, text in notices.items():
            handled.add(nid)
            if TERMS_WORDS.search(text):
                print(f"[warn] {county}: notice {nid} looks like terms to accept. Please log in and accept it "
                      f"yourself in the browser; the script won't accept terms for you. ({text[:120]!r})",
                      file=sys.stderr)
                return False
            time.sleep(1)
            r = s.post(base + "/index.cfm", data={"zaction": "AJAX", "zmethod": "COM", "process": "NOTICE",
                                                  "func": "ACCEPT", "showjson": "false", "NID": nid},
                       timeout=30, headers={"X-Requested-With": "XMLHttpRequest"})
            r.raise_for_status()
            print(f"[notice] {county}: acknowledged notice {nid}")
        time.sleep(2)
        pages = [s.get(base + "/index.cfm", timeout=30).text]  # look again for any further notices
    return True


def fetch_report(s: requests.Session, base: str, auct_type: str, report_id: str) -> list[dict] | None:
    """Quick-search report (needs login). Returns None if the site won't give us the report."""
    county = county_of(base)
    start, end = date.today(), date.today() + timedelta(days=DAYS_AHEAD)
    fmt_d = lambda d: f"{d.month}/{d.day}/{d.year}"
    time.sleep(2)
    page = s.get(base + SEARCH_PAGE_PATH.format(report_id=report_id), timeout=30)
    page.raise_for_status()
    if find_notices(page.text):
        if not accept_notices(s, base, [page.text]):
            return None
        time.sleep(2)
        page = s.get(base + SEARCH_PAGE_PATH.format(report_id=report_id), timeout=30)
        page.raise_for_status()
    if re.search(r"type=.?password", page.text, re.I):
        print(f"[warn] {county}: still seeing a login form after logging in", file=sys.stderr)
        return None
    m = re.search(r"REPID\W{0,5}(\d{6,})", page.text, re.I)
    repid = m.group(1) if m else str(int(time.time() * 1000))  # the page's script may generate it
    time.sleep(2)
    f = s.get(base + FILTER_PATH.format(auct_type=auct_type, start=fmt_d(start), end=fmt_d(end),
                                        repid=repid, ms=int(time.time() * 1000)),
              timeout=30, headers={"X-Requested-With": "XMLHttpRequest"})
    f.raise_for_status()
    items, ids = [], set()
    for pg in range(1, MAX_PAGES + 1):
        time.sleep(2)
        r = s.get(base + LOAD_PATH.format(repid=repid, page=pg, ms=int(time.time() * 1000)),
                  timeout=30, headers={"X-Requested-With": "XMLHttpRequest"})
        r.raise_for_status()
        if "expired" in r.text.lower():
            print(f"[warn] {county}: report expired even after login", file=sys.stderr)
            return None
        batch, total = parse_report(r.text, base)
        new = [i for i in batch if i["id"] not in ids]
        ids.update(i["id"] for i in new)
        items.extend(new)
        if not new or pg >= total:
            break
    print(f"[fetch] {county}: {len(items)} listings via quick search (logged in) {fmt_d(start)}-{fmt_d(end)}")
    return items


def calendar_day_wanted(box: str) -> bool:
    """Keep a calendar day if it has sales scheduled of a type we watch (tax deed by default)."""
    text = re.sub(r"<[^>]+>", " ", box).upper()
    sch = re.search(r'CALSCH[^>]*>\s*(\d+)', box, re.I)
    if sch and int(sch.group(1)) == 0:
        return False
    kinds = {"TAXDEED": ("TAX DEED", "TAXDEED", " TD"), "FORECLOSURE": ("FORECLOSURE", " FC")}
    watched = [w for t in AUCTION_TYPES for w in kinds.get(t.replace(" ", ""), (t,))]
    if not watched or not any(k in " " + text for k in watched):
        # unknown label: keep the day rather than miss sales (listings are filtered by type anyway)
        return not any(k in " " + text for ks in kinds.values() for k in ks)
    return True


def auction_days(s: requests.Session, base: str) -> list[str]:
    """Days with auctions, from the public calendar. Falls back to every weekday if it can't be read."""
    start, end = date.today(), date.today() + timedelta(days=DAYS_AHEAD)
    found = set()
    try:
        # the calendar shows a month at a time; look at this month and the next ones in range
        months = {(start.year, start.month)}
        d = start
        while d <= end:
            months.add((d.year, d.month)); d += timedelta(days=28)
        for y, m in sorted(months):
            r = s.get(base + CALENDAR_PATH + f"&selCalDate={m}/1/{y}", timeout=30)
            r.raise_for_status()
            # each day: <div class="CALBOX ..." dayid="09/01/2026"> ... Foreclosure ... CALSCH">4</span> FC ...</div>
            for ds, box in re.findall(r'dayid="(\d{2}/\d{2}/\d{4})"(.*?)</div>', r.text, re.I | re.S):
                try:
                    dd = datetime.strptime(ds, "%m/%d/%Y").date()
                except ValueError:
                    continue
                if not (start <= dd <= end) or not calendar_day_wanted(box):
                    continue
                found.add(dd)
            time.sleep(2)
    except Exception as e:
        print(f"[warn] {county_of(base)}: calendar: {e}", file=sys.stderr)
    if found:
        print(f"[fetch] {county_of(base)}: calendar has {len(found)} auction day(s) in range")
        return [d.strftime(DATE_FORMAT) for d in sorted(found)]
    print(f"[warn] {county_of(base)}: couldn't read auction days from the calendar; checking every weekday",
          file=sys.stderr)
    return [d.strftime(DATE_FORMAT) for d in sale_dates(DAYS_AHEAD)]


def fetch_site(site: str) -> list[dict]:
    base, auct_type, report_id = (site.split("|") + ["", ""])[:3]
    base, auct_type, report_id = base.rstrip("/"), (auct_type or "2"), (report_id or "33")
    county = county_of(base)
    s = requests.Session()
    s.headers.update(HEADERS)
    s.get(base, timeout=30).raise_for_status()  # session cookies

    creds = creds_for(county)
    if creds:
        try:
            if login(s, base, *creds) and accept_notices(s, base, [s.get(base + "/index.cfm", timeout=30).text]):
                items = fetch_report(s, base, auct_type, report_id)
                if items is not None:
                    return items
        except Exception as e:
            print(f"[warn] {county}: logged-in search failed ({type(e).__name__})", file=sys.stderr)
        print(f"[fetch] {county}: falling back to the public calendar")
        s = requests.Session()
        s.headers.update(HEADERS)
        s.get(base, timeout=30).raise_for_status()
    items, ids = [], set()
    for ds in auction_days(s, base):
        try:
            time.sleep(2)
            s.get(base + PREVIEW_PATH.format(date=ds), timeout=30).raise_for_status()  # select the day
            day_new = 0
            for page in range(MAX_PAGES):
                time.sleep(2)
                ms = int(time.time() * 1000)
                r = s.get(base + DAY_LOAD_PATH.format(page_dir=0 if page == 0 else 1, ms=ms),
                          timeout=30, headers={"X-Requested-With": "XMLHttpRequest"})
                r.raise_for_status()
                if '"retHTML"' not in r.text:
                    break
                batch = parse_response(r.text, ds)
                fresh = [i for i in batch if f"{county}:{i['id']}" not in ids]
                if not fresh:  # nothing new: empty day, last page, or a repeat of an earlier day
                    break
                for i in fresh:
                    aid = i["id"]
                    i.update({"id": f"{county}:{aid}", "aid": aid, "county": county,
                              "link": base + DETAIL_PATH.format(aid=aid),
                              "day_link": base + PREVIEW_PATH.format(date=ds)})
                    ids.add(i["id"])
                items.extend(fresh)
                day_new += len(fresh)
            print(f"[fetch] {county} {ds}: {day_new} listing(s)")
        except Exception as e:  # one bad day shouldn't kill the run
            print(f"[warn] {county} {ds}: {e}", file=sys.stderr)
    return items


def fetch_all() -> list[dict]:
    items = []
    for site in BASE_URLS:
        try:
            items.extend(fetch_site(site))
        except Exception as e:  # one unreachable site shouldn't stop the others
            print(f"[error] {site}: {e}", file=sys.stderr)
    active = [i for i in items if i.get("status", "").upper() not in SKIP_STATUSES]
    print(f"[fetch] {len(items)} total, {len(items) - len(active)} skipped (canceled)")
    return active


# ----------------------------------------------------------------------------
# LAND USE (Property Appraiser parcel data)
# ----------------------------------------------------------------------------
def folio_of(item: dict) -> str:
    digits = re.sub(r"\D", "", item["parcel"])
    return digits if len(digits) == 13 else ""


def lookup_land_use(session: requests.Session, folio: str) -> dict | None:
    """Return the parcel's attributes (plus _geom_sqft) from the county layer, or None."""
    r = session.get(
        f"{PA_LAYER_URL}/query",
        params={"where": f"FOLIO='{folio}'", "outFields": "*", "returnGeometry": "true",
                "outSR": AREA_SR, "f": "json"},
        timeout=30,
    )
    r.raise_for_status()
    data = r.json()
    if "error" in data:
        raise RuntimeError(data["error"])
    feats = data.get("features") or []
    if not feats:
        return None
    attrs = dict(feats[0].get("attributes") or {})
    attrs["_geom_sqft"] = polygon_area(feats[0].get("geometry") or {})
    attrs["_centroid"] = centroid(feats[0].get("geometry") or {})
    return attrs


def lookup_statewide(session: requests.Session, county: str, parcel: str) -> dict | None:
    """Look up a parcel in the Florida DOR statewide layer and map it to the same keys
    the Miami-Dade layer uses, so the rest of the script doesn't care which county it is."""
    co = FDOR_COUNTY_NO.get(county)
    pid = re.sub(r"[^0-9A-Za-z]", "", parcel).upper()
    if co is None or not pid:
        return None
    feats, last_err = [], None
    for co_expr in (f"CO_NO={co}", f"CO_NO='{co}'"):  # field may be numeric or text
        r = session.get(
            f"{STATEWIDE_LAYER_URL}/query",
            params={"where": f"{co_expr} AND PARCEL_ID='{pid}'", "outFields": "*",
                    "returnGeometry": "true", "outSR": AREA_SR, "f": "json"},
            timeout=30,
        )
        r.raise_for_status()
        data = r.json()
        if "error" in data:
            last_err = data["error"]
            continue
        feats = data.get("features") or []
        break
    else:
        raise RuntimeError(last_err)
    if not feats:
        return None
    a = dict(feats[0].get("attributes") or {})
    try:
        code = int(str(a.get("DOR_UC")).strip())
    except (TypeError, ValueError):
        code = None
    return {
        "DOR_CODE_CUR": a.get("DOR_UC"),
        "DOR_DESC": DOR_CODES.get(code, f"DOR USE CODE {a.get('DOR_UC')}") if code is not None else "",
        "LAND_VAL_CUR": a.get("LND_VAL"),
        "TOTAL_VAL_CUR": a.get("JV"),
        "LND_SQFOOT": a.get("LND_SQFOOT"),  # land sq ft, if the layer carries it
        "_geom_sqft": polygon_area(feats[0].get("geometry") or {}),
        "_centroid": centroid(feats[0].get("geometry") or {}),
        "_pid": a.get("PARCEL_ID"),
    }


def polygon_area(geom: dict) -> float | None:
    """Area of an ArcGIS polygon in the units of its spatial reference (sq ft here).
    Outer rings and holes have opposite winding, so signed areas net out correctly."""
    rings = geom.get("rings") or []
    total = 0.0
    for ring in rings:
        a = 0.0
        for (x1, y1), (x2, y2) in zip(ring, ring[1:] + ring[:1]):
            a += x1 * y2 - x2 * y1
        total += a / 2
    return abs(total) or None


def centroid(geom: dict) -> tuple[float, float] | None:
    """Rough centre of a parcel (average of its outer ring's vertices); fine for a radius search."""
    rings = geom.get("rings") or []
    if not rings or not rings[0]:
        return None
    pts = rings[0][:-1] if rings[0][0] == rings[0][-1] else rings[0]
    return sum(p[0] for p in pts) / len(pts), sum(p[1] for p in pts) / len(pts)


def lot_sqft(attrs: dict) -> tuple[float | None, str]:
    """Lot size in sq ft: a lot-size field if the layer has one, else the parcel polygon's area."""
    for k, v in attrs.items():
        ku = k.upper()
        if not isinstance(v, (int, float)) or v <= 0:
            continue
        if "ACRE" in ku:
            return float(v) * 43560, k
        if ("LOT" in ku and ("SIZE" in ku or "SQ" in ku or "AREA" in ku)) or ku in ("LND_SQFOOT", "LAND_SQFT"):
            return float(v), k
    g = attrs.get("_geom_sqft")
    return (g, "parcel shape") if g else (None, "")


def query_statewide(session: requests.Session, wheres: list[str], extra: dict) -> list[dict]:
    """Try WHERE variants (numeric vs text fields differ between layers) until one is accepted."""
    last_err = None
    for where in wheres:
        r = session.get(f"{STATEWIDE_LAYER_URL}/query",
                        params={"where": where, "outFields": "*", "f": "json", **extra}, timeout=60)
        r.raise_for_status()
        data = r.json()
        if "error" in data:
            last_err = data["error"]
            continue
        return data.get("features") or []
    raise RuntimeError(last_err)


def find_comps(session: requests.Session, county: str, xy: tuple[float, float], exclude_pid: str = "") -> dict | None:
    """Vacant residential lots sold near a point. Returns a summary with median $/sq ft."""
    co = FDOR_COUNTY_NO.get(county)
    if co is None or not xy:
        return None
    since = date.today().year - COMP_YEARS + 1
    wheres = [
        f"{c} AND {u} AND SALE_YR1 >= {since} AND SALE_PRC1 >= {COMP_MIN_PRICE:.0f}"
        for c in (f"CO_NO={co}", f"CO_NO='{co}'")
        for u in ("DOR_UC IN ('000','00','0')", "DOR_UC=0")
    ]
    for radius in (COMP_RADIUS_FT, COMP_RADIUS_FT * 2):
        feats = query_statewide(session, wheres, {
            "geometry": f"{xy[0]},{xy[1]}", "geometryType": "esriGeometryPoint", "inSR": AREA_SR,
            "distance": radius, "units": "esriSRUnit_Foot", "spatialRel": "esriSpatialRelIntersects",
            "returnGeometry": "true", "outSR": AREA_SR,
        })
        sales = []
        for f in feats:
            a = f.get("attributes") or {}
            if exclude_pid and re.sub(r"[^0-9A-Za-z]", "", str(a.get("PARCEL_ID"))).upper() == exclude_pid.upper():
                continue
            price = a.get("SALE_PRC1") or 0
            if price < COMP_MIN_PRICE:
                continue
            sqft = a.get("LND_SQFOOT") or polygon_area(f.get("geometry") or {})
            if price and sqft and sqft > 500:
                sales.append({"price": float(price), "sqft": float(sqft), "ppsf": float(price) / float(sqft),
                              "year": a.get("SALE_YR1"), "month": a.get("SALE_MO1")})
        if len(sales) >= COMP_MIN or radius != COMP_RADIUS_FT:
            break
    if not sales:
        return {"n": 0, "radius_ft": radius}
    ppsf = sorted(x["ppsf"] for x in sales)
    mid = len(ppsf) // 2
    median = ppsf[mid] if len(ppsf) % 2 else (ppsf[mid - 1] + ppsf[mid]) / 2
    return {"n": len(sales), "radius_ft": radius, "median_ppsf": round(median, 2),
            "low_ppsf": round(ppsf[0], 2), "high_ppsf": round(ppsf[-1], 2)}


def enrich(items: list[dict]) -> None:
    s = requests.Session()
    s.headers.update(HEADERS)
    for item in items:
        item["land_use"] = None
        county = item.get("county", "miamidade")
        if county == "miamidade":
            folio = folio_of(item)
            if not folio:
                continue
        else:
            folio = re.sub(r"[^0-9A-Za-z]", "", item["parcel"]).upper()
            if not folio or item["parcel"].upper().startswith("MULTIPLE"):
                continue
        try:
            if county == "miamidade":
                a = lookup_land_use(s, folio)
            else:
                a = lookup_statewide(s, county, item["parcel"])
        except Exception as e:
            print(f"[warn] land use {county} {folio}: {e}", file=sys.stderr)
            continue
        if not a:
            print(f"[land use] {county} {folio}: not found")
        if a:
            sqft, src = lot_sqft(a)
            item["land_use"] = {
                "code": a.get("DOR_CODE_CUR"),
                "desc": (a.get("DOR_DESC") or "").strip(),
                "land_val": a.get("LAND_VAL_CUR"),
                "total_val": a.get("TOTAL_VAL_CUR"),
                "lot_sqft": round(sqft) if sqft else None,
                "lot_src": src,
            }
            # comparable sales only for lots that pass the filter (keeps requests low)
            if land_use_ok(item):
                try:
                    item["land_use"]["comps"] = find_comps(s, county, a.get("_centroid"), a.get("_pid") or folio)
                except Exception as e:
                    print(f"[warn] comps {county} {folio}: {e}", file=sys.stderr)
            # shows in the Actions log so you can see the county's real descriptions
            print(f"[land use] {county} {folio}: {item['land_use']['code']} {item['land_use']['desc']!r}, "
                  f"lot {item['land_use']['lot_sqft']} sq ft ({src or 'unknown'})")
        time.sleep(1)


def land_use_ok(item: dict) -> bool:
    """Buildable-residential screen. Unknown values pass, so a human can take a look."""
    lu = item.get("land_use")
    if not lu:
        return True
    desc = (lu.get("desc") or "").upper()
    if any(x in desc for x in EXCLUDE_LAND_USE):
        return False
    if LAND_USE_KEYWORDS and desc and not any(all(w in desc for w in group) for group in LAND_USE_KEYWORDS):
        return False
    sqft = lu.get("lot_sqft")
    if MIN_LOT_SQFT and sqft and sqft < MIN_LOT_SQFT:
        return False
    return True


# ----------------------------------------------------------------------------
# STATE + ALERTS
# ----------------------------------------------------------------------------
def load_seen() -> dict:
    """State per auction item id: {"sale_date", "ok" (passed land-use filter), "land_use", "reminded": [days]}."""
    try:
        data = json.loads(SEEN_FILE.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}
    if isinstance(data, dict):
        data.pop("_tg", None)  # leftover from the checklist version
    if isinstance(data, list):  # old format: plain list of ids -> treat as seen, no reminders sent yet
        return {i: {"sale_date": "", "ok": True, "land_use": None, "reminded": []} for i in data}
    return data


def save_seen(seen: dict) -> None:
    today = date.today()
    # drop items whose sale date has passed so the file doesn't grow forever
    keep_ = {k: v for k, v in seen.items()
             if k.startswith("_") or (days_until(v.get("sale_date", ""), today) or 0) >= 0}
    SEEN_FILE.write_text(json.dumps(keep_, indent=1, sort_keys=True))


def days_until(sale_date: str, today: date) -> int | None:
    try:
        return (datetime.strptime(sale_date, DATE_FORMAT).date() - today).days
    except ValueError:
        return None


def fmt(item: dict) -> str:
    bid = f"${item['bid']:,.2f}" if item["bid"] is not None else "n/a"
    assessed = f"${item['assessed']:,.0f}" if item["assessed"] is not None else "n/a"
    lines = [
        f"{item['sale_date']}  {item.get('county', '').upper()}  {item['type']}  #{item['case']}"
        + (f"  [{item['status']}]" if item.get("status") else ""),
        f"Parcel: {item['parcel']}",
        f"Address: {item['address'] or '(none)'} {item['city']}".rstrip(),
        f"Bid: {bid}   Assessed: {assessed}",
    ]
    lu = item.get("land_use")
    if lu:
        lines.append(f"Land use: {lu['code']} {lu['desc']}".rstrip())
        vals = []
        if lu["land_val"] is not None:
            vals.append(f"land ${lu['land_val']:,.0f}")
        if lu["total_val"] is not None:
            vals.append(f"total ${lu['total_val']:,.0f}")
        if lu.get("lot_sqft"):
            acres = lu["lot_sqft"] / 43560
            vals.append(f"lot {lu['lot_sqft']:,} sq ft ({acres:.2f} ac)")
        if vals:
            lines.append("PA values: " + ", ".join(vals))
    elif folio_of(item):
        lines.append("Land use: not found, check manually")
    comps = (lu or {}).get("comps")
    if comps is not None:
        miles = comps["radius_ft"] / 5280
        if comps["n"]:
            line = (f"Comps: {comps['n']} vacant residential sales within {miles:.1f} mi "
                    f"(last {COMP_YEARS}y): median ${comps['median_ppsf']:,.2f}/sq ft "
                    f"(${comps['low_ppsf']:,.2f}-${comps['high_ppsf']:,.2f})")
            lines.append(line)
            if lu.get("lot_sqft"):
                est = comps["median_ppsf"] * lu["lot_sqft"]
                pct = f", bid = {item['bid'] / est:.0%} of that" if item.get("bid") and est else ""
                lines.append(f"Est. land value ≈ ${est:,.0f}{pct}")
        else:
            lines.append(f"Comps: no vacant residential sales within {miles:.1f} mi in the last {COMP_YEARS}y")
    if t := tags(item):
        lines.append("Note: " + "; ".join(t))
    for name, url in links_of(item):
        lines.append(f"{name}: {url}")
    return "\n".join(lines)


def links_of(item: dict) -> list[tuple[str, str]]:
    out = []
    if item.get("link"):
        out.append(("Listing", item["link"]))
    if item.get("day_link"):
        out.append(("Sale day", item["day_link"]))
    if item.get("county", "miamidade") == "miamidade":
        if folio := folio_of(item):
            out.append(("Property", f"https://apps.miamidadepa.gov/propertysearch/#/?folio={folio}"))
    elif item.get("county") == "broward" and item["parcel"] and not item["parcel"].upper().startswith("MULTIPLE"):
        out.append(("Property", "https://web.bcpa.net/BcpaClient/"))
    return out


def fmt_html(item: dict) -> str:
    """Compact Telegram version of one listing (HTML)."""
    e = html.escape
    lu = item.get("land_use") or {}
    head = f"<b>{e(item['sale_date'][:5])} · {e(item.get('county', '').upper())} · #{e(item['case'])}</b>"
    addr = f"{item['address'] or 'no address'}, {item['city']}".strip(", ")
    bid = f"${item['bid']:,.0f}" if item.get("bid") is not None else "n/a"
    lines = [head, e(addr), f"Opening bid <b>{bid}</b> · parcel <code>{e(item['parcel'])}</code>"]
    bits = []
    if lu.get("desc"):
        bits.append(e(lu["desc"].title()))
    if lu.get("lot_sqft"):
        bits.append(f"{lu['lot_sqft']:,} sq ft")
    if bits:
        lines.append(" · ".join(bits))
    c = lu.get("comps")
    if c and c.get("n") and lu.get("lot_sqft"):
        est = c["median_ppsf"] * lu["lot_sqft"]
        pct = f" (bid {item['bid'] / est:.0%})" if item.get("bid") and est else ""
        lines.append(f"Comps: {c['n']} sales, ${c['median_ppsf']:,.2f}/sq ft → ≈${est:,.0f}{pct}")
    elif c is not None and not c.get("n"):
        lines.append("Comps: none nearby")
    if t := tags(item):
        lines.append("<i>" + e("; ".join(t)) + "</i>")
    ls = links_of(item)
    if ls:
        lines.append(" | ".join(f'<a href="{e(u, quote=True)}">{e(n)}</a>' for n, u in ls))
    return "\n".join(lines)


def tg(method: str, **payload) -> dict:
    r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/{method}", json=payload, timeout=30)
    data = r.json()
    if not data.get("ok"):
        raise RuntimeError(f"Telegram {method}: {data.get('description')}")
    return data.get("result")


def send_telegram_html(items: list[dict], subject: str) -> None:
    """Send listings as compact HTML messages (split to stay under Telegram's 4096-char limit)."""
    blocks = [fmt_html(i) for i in items]
    chunks, cur = [], []
    for b in blocks:
        if cur and (sum(len(x) for x in cur) + len(b) > 3500 or len(cur) >= 10):
            chunks.append(cur); cur = []
        cur.append(b)
    if cur:
        chunks.append(cur)
    for k, ch in enumerate(chunks, 1):
        subj = subject + (f" ({k}/{len(chunks)})" if len(chunks) > 1 else "")
        text = f"<b>{html.escape(subj)}</b>\n\n" + "\n\n".join(ch)
        tg("sendMessage", chat_id=TELEGRAM_CHAT_ID, text=text, parse_mode="HTML", disable_web_page_preview=True)


def send_telegram(text: str) -> None:
    for i in range(0, len(text), 3900):  # Telegram message limit is 4096
        requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
            data={"chat_id": TELEGRAM_CHAT_ID, "text": text[i:i + 3900], "disable_web_page_preview": True},
            timeout=30,
        ).raise_for_status()


def send_email(subject: str, text: str) -> None:
    msg = EmailMessage()
    msg["Subject"], msg["From"], msg["To"] = subject, SMTP_USER, EMAIL_TO
    msg.set_content(text)
    with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
        smtp.login(SMTP_USER, SMTP_PASS)
        smtp.send_message(msg)


def notify(items: list[dict], subject: str, dry_run: bool, seen: dict | None = None) -> None:
    body = "\n\n".join(fmt(i) for i in items)
    if dry_run or not (TELEGRAM_TOKEN or SMTP_USER):
        print(f"--- {subject} ---\n{body}")
        return
    if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID:
        send_telegram_html(items, subject)
    if SMTP_USER and SMTP_PASS:
        send_email(subject, body)


# ----------------------------------------------------------------------------
def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sample", help="parse a saved JSON response instead of fetching")
    ap.add_argument("--dry-run", action="store_true", help="print alerts instead of sending")
    ap.add_argument("--folio", help="test the land-use lookup for one folio and exit")
    args = ap.parse_args()

    if args.folio:
        s = requests.Session()
        s.headers.update(HEADERS)
        a = lookup_land_use(s, re.sub(r"\D", "", args.folio))
        print(json.dumps(a, indent=2, default=str) if a else "not found")
        return

    if args.sample:
        text = Path(args.sample).read_text()
        if '"rows"' in text:
            items, _ = parse_report(text, "https://sample.local")
        else:
            items = parse_response(text, "sample")
        for i in items:
            print(json.dumps({k: v for k, v in i.items() if k != "raw"}), "KEEP" if keep(i) else "skip")
        return

    items = [i for i in fetch_all() if keep(i)]
    seen = load_seen()
    today = date.today()

    # 1) New listings: look up land use once, alert if they pass the filter
    new = [i for i in items if i["id"] not in seen]
    enrich(new)  # only look up parcels we haven't seen, to keep requests low
    new_alerts = [i for i in new if land_use_ok(i)]
    for i in new:
        d = days_until(i["sale_date"], today)
        seen[i["id"]] = {
            "sale_date": i["sale_date"],
            "ok": land_use_ok(i),
            "land_use": i.get("land_use"),
            # a listing first found inside a reminder window already got the "new" alert
            "reminded": [r for r in REMIND_DAYS if d is not None and d <= r],
        }

    # 2) Reminders: still-listed items (so cancelled sales drop out) whose sale is N days away
    reminders: dict[int, list[dict]] = {r: [] for r in REMIND_DAYS}
    for i in items:
        st = seen.get(i["id"])
        if not st or not st.get("ok") or i["id"] in {n["id"] for n in new}:
            continue
        st["sale_date"] = i["sale_date"]  # the sale may have been rescheduled
        i["land_use"] = st.get("land_use")
        d = days_until(i["sale_date"], today)
        if d is None:
            continue
        # smallest window reached that hasn't been sent (a missed run still gets caught up)
        due = [r for r in REMIND_DAYS if d <= r and r not in st["reminded"]]
        if due:
            reminders[min(due)].append(i)
            st["reminded"] = sorted(set(st["reminded"]) | set(due), reverse=True)

    print(f"{len(items)} matching, {len(new)} new, {len(new_alerts)} new alerts, "
          + ", ".join(f"{len(v)} reminders at {k}d" for k, v in reminders.items()))

    if new_alerts:
        notify(new_alerts, f"🆕 {len(new_alerts)} new auction listing(s)", args.dry_run, seen)
    for r, group in sorted(reminders.items(), reverse=True):
        if group:
            when = "tomorrow" if r == 1 else f"in {r} days"
            notify(group, f"⏰ {len(group)} auction(s) {when}", args.dry_run, seen)

    if not args.dry_run:
        save_seen(seen)

if __name__ == "__main__":
    main()
