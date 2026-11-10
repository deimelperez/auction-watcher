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
import csv
import html
import json
import math
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
# RealAuction sites, comma-separated. Miami-Dade's tax deeds are on its realforeclose calendar.
# Miami-Dade tax deeds are listed on its realforeclose site; Broward uses realtaxdeed.
BASE_URLS = [u.strip().rstrip("/") for u in os.getenv(
    "BASE_URL", "https://www.miamidade.realforeclose.com,https://broward.realtaxdeed.com").split(",") if u.strip()]
# The site's "quick search" report: FilterData sets the date range in the session, LoadData returns rows.
# Links to open in your browser: the listing itself ({aid} = auction item id), and its sale-date page.
DETAIL_PATH = os.getenv("DETAIL_PATH", "/index.cfm?zaction=AUCTION&Zmethod=DETAILS&AID={aid}&bypassPage=1")
PREVIEW_PATH = "/index.cfm?zaction=AUCTION&Zmethod=PREVIEW&AUCTIONDATE={date}"
# Public calendar + per-day listing (no login needed)
CALENDAR_PATH = os.getenv("CALENDAR_PATH", "/index.cfm?zaction=USER&zmethod=CALENDAR")
# How to ask the calendar for a given month ({m}, {y}); confirm from the site's "next month" link.
# The site's own "next month" link uses a ColdFusion timestamp: selCalDate={ts '2026-10-01 00:00:00'}
CALENDAR_MONTH_PARAM = os.getenv("CALENDAR_MONTH_PARAM",
                                 "&selCalDate=%7Bts%20%27{y}%2D{m:02d}%2D01%2000%3A00%3A00%27%7D")
# Page 1: PageDir=0&doR=1&bypassPage=1. Next pages: PageDir=1&doR=0&bypassPage=0
# (with bypassPage=1 the site just returns page 1 again).
# AREA: W = waiting (upcoming), R = running, C = closed (sold / redeemed / canceled).
DAY_LOAD_PATH = ("/index.cfm?zaction=AUCTION&Zmethod=UPDATE&FNC=LOAD&AREA={area}&PageDir={page_dir}"
                 "&doR={dor}&bypassPage={bypass}&test=1&tx={ms}&_={ms}")
# Status of the items on the current page (sold amount, sold to, redeemed, canceled...)
STATUS_PATH = "/index.cfm?zaction=AUCTION&ZMETHOD=UPDATE&FNC=UPDATE&ref={ids},&tx={ms}"


def day_page_url(area: str, page: int, ms: int) -> str:
    if page == 0:
        return DAY_LOAD_PATH.format(area=area, page_dir=0, dor=1, bypass=1, ms=ms)
    return DAY_LOAD_PATH.format(area=area, page_dir=1, dor=0, bypass=0, ms=ms)

SKIP_STATUSES = {s.strip().upper() for s in os.getenv("SKIP_STATUSES", "CANCELED,CANCELLED").split(",") if s.strip()}
MAX_PAGES = int(os.getenv("MAX_PAGES", "10"))
DATE_FORMAT = os.getenv("DATE_FORMAT", "%m/%d/%Y")
DAYS_AHEAD = int(os.getenv("DAYS_AHEAD", "45"))

AUCTION_TYPES = {t.strip().upper() for t in os.getenv("AUCTION_TYPES", "TAXDEED").split(",") if t.strip()}
MAX_BID = float(os.getenv("MAX_BID", "0") or 0)          # max opening bid for vacant lots; 0 = no limit
# Second search: any non-condo property (houses, townhouses, duplexes, lots, commercial...)
# with an opening bid at or under this. 0 = turn this search off.
PROPERTY_MAX_BID = float(os.getenv("PROPERTY_MAX_BID", "100000") or 0)
ZIPS = {z.strip() for z in os.getenv("ZIPS", "").split(",") if z.strip()}  # empty = any

SEEN_FILE = Path(os.getenv("SEEN_FILE", "seen.json"))
# Sale results (one row per tax deed listing, every listing, not just alerted ones)
RESULTS_FILE = Path(os.getenv("RESULTS_FILE", "results.csv"))
# Send a short Telegram/email summary of the day's results (sold items) after collecting them
RESULTS_NOTIFY = os.getenv("RESULTS_NOTIFY", "0") not in ("0", "", "false", "no")  # 0 = Saturday report only
# Each results run re-checks sale days this far back, so a missed run is caught up.
RESULTS_DAYS_BACK = int(os.getenv("RESULTS_DAYS_BACK", "7"))
# Reminder alerts: days before the sale (default: a week before and a day before).
REMIND_DAYS = sorted({int(d) for d in os.getenv("REMIND_DAYS", "7,1").split(",") if d.strip()}, reverse=True)

TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN", "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")
SMTP_USER = os.getenv("SMTP_USER", "")        # e.g. you@gmail.com
SMTP_PASS = os.getenv("SMTP_PASS", "")        # Gmail app password
EMAIL_TO = os.getenv("EMAIL_TO", SMTP_USER)

# Land-use lookup (Miami-Dade parcel layer, public ArcGIS REST, no key needed)
MD_SERVICE_URL = os.getenv(
    "MD_SERVICE_URL", "https://gisweb.miamidade.gov/arcgis/rest/services/MD_LandInformation/MapServer")
PA_LAYER_URL = os.getenv("PA_LAYER_URL", f"{MD_SERVICE_URL}/26")     # parcels (polygons)
PA_POINTS_URL = os.getenv("PA_POINTS_URL", f"{MD_SERVICE_URL}/24")   # every folio, condo units included
# FEMA national flood hazard layer (flood zone at a point), both counties
FEMA_NFHL_URL = os.getenv("FEMA_NFHL_URL", "https://hazards.fema.gov/arcgis/rest/services/public/NFHL/MapServer/28")
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
    4: "CONDOMINIUM", 5: "COOPERATIVES", 6: "RETIREMENT HOMES", 7: "MISCELLANEOUS RESIDENTIAL",
    8: "MULTI-FAMILY <10 UNITS", 9: "RESIDENTIAL COMMON AREAS",
    10: "VACANT COMMERCIAL", 11: "STORES", 12: "MIXED USE STORE/OFFICE", 13: "DEPARTMENT STORES",
    14: "SUPERMARKETS", 15: "REGIONAL SHOPPING CENTERS", 16: "COMMUNITY SHOPPING CENTERS",
    17: "OFFICE BUILDINGS", 18: "OFFICE BUILDINGS (MULTI-STORY)", 19: "PROFESSIONAL SERVICE BUILDINGS",
    20: "AIRPORTS, TERMINALS, MARINAS", 21: "RESTAURANTS", 22: "DRIVE-IN RESTAURANTS",
    23: "FINANCIAL INSTITUTIONS", 24: "INSURANCE COMPANY OFFICES", 25: "REPAIR SERVICE SHOPS",
    26: "SERVICE STATIONS", 27: "AUTO SALES AND REPAIR", 28: "PARKING LOTS, MOBILE HOME PARKS",
    29: "WHOLESALE OUTLETS", 30: "FLORISTS, GREENHOUSES", 31: "DRIVE-IN THEATERS, OPEN STADIUMS",
    32: "ENCLOSED THEATERS", 33: "NIGHTCLUBS, BARS", 34: "BOWLING ALLEYS, SKATING RINKS",
    35: "TOURIST ATTRACTIONS", 36: "CAMPS", 37: "RACE TRACKS", 38: "GOLF COURSES", 39: "HOTELS, MOTELS",
    40: "VACANT INDUSTRIAL", 41: "LIGHT MANUFACTURING", 42: "HEAVY INDUSTRIAL", 43: "LUMBER YARDS",
    44: "PACKING PLANTS", 45: "CANNERIES, BOTTLERS", 46: "OTHER FOOD PROCESSING", 47: "MINERAL PROCESSING",
    48: "WAREHOUSING", 49: "OPEN STORAGE",
    **{c: "AGRICULTURAL" for c in range(50, 70)},
    70: "VACANT INSTITUTIONAL", 71: "CHURCHES", 72: "PRIVATE SCHOOLS", 73: "PRIVATE HOSPITALS",
    74: "HOMES FOR THE AGED", 75: "NON-PROFIT SERVICES", 76: "MORTUARIES, CEMETERIES", 77: "CLUBS, LODGES",
    78: "REST HOMES", 79: "CULTURAL ORGANIZATIONS",
    80: "VACANT GOVERNMENTAL", 81: "MILITARY", 82: "FOREST, PARKS, RECREATION", 83: "PUBLIC SCHOOLS",
    84: "COLLEGES", 85: "HOSPITALS", 86: "COUNTY PROPERTY", 87: "STATE PROPERTY", 88: "FEDERAL PROPERTY",
    89: "MUNICIPAL PROPERTY", 90: "LEASEHOLD INTERESTS", 91: "UTILITIES", 92: "MINING",
    93: "SUBSURFACE RIGHTS", 94: "RIGHT-OF-WAY (STREETS, ROADS, CANALS)",
    95: "RIVERS, LAKES, SUBMERGED LAND", 96: "WASTE LAND, MARSH, DRAINAGE", 97: "OUTDOOR RECREATION, PARK LAND",
    98: "CENTRALLY ASSESSED", 99: "ACREAGE NOT ZONED AGRICULTURAL",
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
EXCLUDE_LAND_USE = [k.strip().upper() for k in os.getenv("EXCLUDE_LAND_USE", "CONDOMINIUM,CONDO,COOPERATIVE").split(",") if k.strip()]
# Never alert on these Florida DOR use codes: 4 condo, 5 co-op, 9 common areas, 94 roads and canals,
# 95 lakes and submerged land, 96 waste land and marsh, 97 park land, 98 centrally assessed.
SKIP_DOR_CODES = {int(c) for c in os.getenv("SKIP_DOR_CODES", "4,5,9,94,95,96,97,98").split(",") if c.strip()}
# Minimum lot size in square feet (0 = no minimum). Screens out slivers and too-small lots.
MIN_LOT_SQFT = float(os.getenv("MIN_LOT_SQFT", "5000") or 0)
# Florida East State Plane (US survey feet), so geometry areas come back in sq ft.
AREA_SR = os.getenv("AREA_SR", "2236")
# Vacant land is flagged as probably unbuildable when it is narrower than this...
MIN_LOT_WIDTH_FT = float(os.getenv("MIN_LOT_WIDTH_FT", "40"))
# ...or when the county values the land below this many dollars per square foot.
LOW_LAND_VALUE_PSF = float(os.getenv("LOW_LAND_VALUE_PSF", "2"))
# Reminders go only to listings graded "worth a look"; 1 = remind about every match.
REMIND_ALL = os.getenv("REMIND_ALL", "0") not in ("0", "", "false", "no")
COMP_FIELDS = "PARCEL_ID,SALE_PRC1,SALE_YR1,SALE_MO1,LND_SQFOOT,VI_CD1,QUAL_CD1,M_PAR_SAL1"
STATE_VERSION = 2   # listings saved by an older version are re-checked once

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
        address = fields.get("Property Address", "")
        if not city_line and re.search(r",\s*FL\b", address, re.I):
            city_line, address = address, ""
        zip_m = re.search(r"\b(\d{5})\b", city_line)
        items.append({
            "id": aid,
            "sale_date": sale_date,
            "type": fields.get("Auction Type", "").upper(),
            "case": fields.get("Case #", ""),
            "parcel": fields.get("Parcel ID", ""),
            "address": address,
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
    limit = max(MAX_BID, PROPERTY_MAX_BID) if MAX_BID else 0  # 0 = lots have no limit, so none here
    if limit and item["bid"] is not None and item["bid"] > limit:
        return False
    if ZIPS and item["zip"] and item["zip"] not in ZIPS:
        return False
    return True


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
            r = s.get(base + CALENDAR_PATH + CALENDAR_MONTH_PARAM.format(m=m, y=y), timeout=30)
            r.raise_for_status()
            shown = {(int(y2), int(m2)) for m2, _, y2 in re.findall(r'dayid=["\'](\d{2})/(\d{2})/(\d{4})["\']', r.text)}
            if shown and (y, m) not in shown:
                print(f"[warn] {county_of(base)}: asked the calendar for {m}/{y} but it showed "
                      f"{sorted(shown)}; the month parameter isn't right yet", file=sys.stderr)
            # each day: <div class="CALBOX ..." dayid="09/01/2026"> ... Foreclosure ... CALSCH">4</span> FC ...</div>
            for ds, box in re.findall(r'dayid=["\'](\d{2}/\d{2}/\d{4})["\'](.*?)</div>', r.text, re.I | re.S):
                try:
                    dd = datetime.strptime(ds, "%m/%d/%Y").date()
                except ValueError:
                    continue
                if not (start <= dd <= end) or not calendar_day_wanted(box):
                    continue
                found.add(dd)
                act = re.search(r'CALACT[^>]*>\s*(\d+)', box, re.I)
                CAL_ACTIVE[(county_of(base), dd.strftime(DATE_FORMAT))] = int(act.group(1)) if act else 0
            time.sleep(2)
    except Exception as e:
        print(f"[warn] {county_of(base)}: calendar: {e}", file=sys.stderr)
        CAL_NOTE[county_of(base)] = f"could not read the auction calendar ({str(e)[:100]})"
    if found:
        print(f"[fetch] {county_of(base)}: calendar has {len(found)} auction day(s) in range")
        return [d.strftime(DATE_FORMAT) for d in sorted(found)]
    # Don't guess: opening a day with no sale makes the site show another day's list,
    # which would put the wrong sale date on listings.
    print(f"[warn] {county_of(base)}: no tax deed sale days found on the calendar in the next "
          f"{DAYS_AHEAD} days", file=sys.stderr)
    CAL_NOTE.setdefault(county_of(base), f"no tax deed sale days found on the calendar for the next {DAYS_AHEAD} days")
    return []


def fetch_site(site: str) -> list[dict]:
    base = site.split("|")[0].rstrip("/")
    county = county_of(base)
    s = requests.Session()
    s.headers.update(HEADERS)
    s.get(base, timeout=30).raise_for_status()  # session cookies

    items, ids = [], set()
    days = auction_days(s, base)
    for ds in days:
        try:
            time.sleep(2)
            s.get(base + PREVIEW_PATH.format(date=ds), timeout=30).raise_for_status()  # select the day
            day_new = 0
            for page in range(MAX_PAGES):
                time.sleep(2)
                ms = int(time.time() * 1000)
                r = s.get(base + day_page_url("W", page, ms),
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
    HEALTH[county] = {"expected": sum(CAL_ACTIVE.get((county, ds), 0) for ds in days), "parsed": len(items),
                      "note": CAL_NOTE.get(county)}
    return items


def fetch_all() -> list[dict]:
    items = []
    for site in BASE_URLS:
        try:
            items.extend(fetch_site(site))
        except Exception as e:  # one unreachable site shouldn't stop the others
            print(f"[error] {site}: {e}", file=sys.stderr)
            HEALTH[county_of(site.split("|")[0])] = {"error": str(e)}
    active = [i for i in items if i.get("status", "").upper() not in SKIP_STATUSES]
    print(f"[fetch] {len(items)} total, {len(items) - len(active)} skipped (canceled)")
    return active


# ----------------------------------------------------------------------------
# PARCEL RESEARCH (Property Appraiser data, lot shape, zoning, flood zone, wetlands)
# ----------------------------------------------------------------------------
def folio_of(item: dict) -> str:
    digits = re.sub(r"\D", "", item["parcel"])
    return digits if len(digits) == 13 else ""


def dor2(code) -> int | None:
    """Standard 2-digit Florida DOR use code. Miami-Dade gives 4 digits ('0081' -> 0, '9981' -> 99),
    the statewide layer gives 3 ('000' -> 0, '094' -> 94)."""
    s = re.sub(r"\D", "", str(code if code is not None else ""))
    if not s:
        return None
    return int(s[:2]) if len(s) == 4 else int(s)


def _arc(session: requests.Session, url: str, params: dict, timeout: int = 40) -> list[dict]:
    r = session.get(url, params={"f": "json", **params}, timeout=timeout)
    r.raise_for_status()
    data = r.json()
    if "error" in data:
        raise RuntimeError(data["error"])
    return data.get("features") or []


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


def lot_dims(geom: dict) -> tuple[int, int] | None:
    """(short side, long side) in feet of the tightest rectangle around the parcel."""
    rings = geom.get("rings") or []
    if not rings or len(rings[0]) < 4:
        return None
    pts, best = rings[0], None
    for (x1, y1), (x2, y2) in zip(pts, pts[1:]):
        length = math.hypot(x2 - x1, y2 - y1)
        if length < 1:
            continue
        ux, uy = (x2 - x1) / length, (y2 - y1) / length
        a = [p[0] * ux + p[1] * uy for p in pts]
        b = [-p[0] * uy + p[1] * ux for p in pts]
        w, h = max(a) - min(a), max(b) - min(b)
        if best is None or w * h < best[0] * best[1]:
            best = (w, h)
    return (round(min(best)), round(max(best))) if best else None


def lookup_land_use(session: requests.Session, folio: str) -> dict | None:
    """Miami-Dade parcel attributes (plus _geom_sqft, _centroid, _dims), or None.
    Condo units have no polygon of their own, so they're looked up in the property-points layer."""
    feats = _arc(session, f"{PA_LAYER_URL}/query",
                 {"where": f"FOLIO='{folio}'", "outFields": "*", "returnGeometry": "true", "outSR": AREA_SR})
    if feats:
        attrs = dict(feats[0].get("attributes") or {})
        geom = feats[0].get("geometry") or {}
        attrs["_geom_sqft"] = polygon_area(geom)
        attrs["_centroid"] = centroid(geom)
        attrs["_dims"] = lot_dims(geom)
        return attrs
    feats = _arc(session, f"{PA_POINTS_URL}/query",
                 {"where": f"FOLIO='{folio}'", "outFields": "*", "returnGeometry": "false"})
    if not feats:
        return None
    attrs = dict(feats[0].get("attributes") or {})
    x, y = attrs.get("X_COORD"), attrs.get("Y_COORD")
    attrs.update({"_geom_sqft": None, "_centroid": (x, y) if x and y else None, "_dims": None})
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
        try:
            feats = _arc(session, f"{STATEWIDE_LAYER_URL}/query",
                         {"where": f"{co_expr} AND PARCEL_ID='{pid}'", "outFields": "*",
                          "returnGeometry": "true", "outSR": AREA_SR})
            break
        except RuntimeError as e:
            last_err = e
    else:
        raise RuntimeError(last_err)
    if not feats:
        return None
    a = dict(feats[0].get("attributes") or {})
    geom = feats[0].get("geometry") or {}
    code = dor2(a.get("DOR_UC"))
    return {
        "DOR_CODE_CUR": a.get("DOR_UC"),
        "DOR_DESC": DOR_CODES.get(code, f"DOR USE CODE {a.get('DOR_UC')}") if code is not None else "",
        "LAND_VAL_CUR": a.get("LND_VAL"),
        "TOTAL_VAL_CUR": a.get("JV"),
        "LND_SQFOOT": a.get("LND_SQFOOT"),  # land sq ft, if the layer carries it
        "TRUE_OWNER1": a.get("OWN_NAME"),
        "TRUE_SITE_ADDR": a.get("PHY_ADDR1"),
        "TRUE_SITE_CITY": a.get("PHY_CITY"),
        "TRUE_SITE_ZIP_CODE": a.get("PHY_ZIPCD"),
        "YEAR_BUILT": a.get("ACT_YR_BLT"),
        "BUILDING_HEATED_AREA": a.get("TOT_LVG_AR"),
        "UNIT_COUNT": a.get("NO_RES_UNT"),
        "_geom_sqft": polygon_area(geom),
        "_centroid": centroid(geom),
        "_dims": lot_dims(geom),
        "_pid": a.get("PARCEL_ID"),
    }


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


def _txt(v) -> str:
    return str(v).strip() if v not in (None, "") else ""


def _pos(v):
    """Positive number or None (the county layers use 0 for 'none')."""
    try:
        return v if v and float(v) > 0 else None
    except (TypeError, ValueError):
        return None


def land_use_record(a: dict) -> dict:
    """The parcel facts we keep (in seen.json) and show in alerts."""
    sqft, src = lot_sqft(a)
    zip_m = re.search(r"\d{5}", _txt(a.get("TRUE_SITE_ZIP_CODE")))
    c = a.get("_centroid")
    return {
        "code": a.get("DOR_CODE_CUR"),
        "desc": _txt(a.get("DOR_DESC")),
        "land_val": a.get("LAND_VAL_CUR"),
        "total_val": a.get("TOTAL_VAL_CUR"),
        "lot_sqft": round(sqft) if sqft else None,
        "lot_src": src,
        "dims": list(a["_dims"]) if a.get("_dims") else None,
        "owner": _txt(a.get("TRUE_OWNER1")),
        "site_addr": _txt(a.get("TRUE_SITE_ADDR")),
        "site_city": _txt(a.get("TRUE_SITE_CITY")).title(),
        "site_zip": zip_m.group() if zip_m else "",
        "year_built": int(a["YEAR_BUILT"]) if _pos(a.get("YEAR_BUILT")) else None,
        "living_sqft": round(a["BUILDING_HEATED_AREA"]) if _pos(a.get("BUILDING_HEATED_AREA")) else None,
        "beds": _pos(a.get("BEDROOM_COUNT")),
        "baths": _pos(a.get("BATHROOM_COUNT")),
        "units": _pos(a.get("UNIT_COUNT")),
        "condo": _txt(a.get("CONDO_FLAG")).upper() == "Y",
        "xy": [round(c[0], 1), round(c[1], 1)] if c else None,
    }


def query_statewide(session: requests.Session, wheres: list[str], extra: dict) -> list[dict]:
    """Try WHERE variants (numeric vs text fields differ between layers) until one is accepted."""
    last_err = None
    for where in wheres:
        r = session.get(f"{STATEWIDE_LAYER_URL}/query",
                        params={"where": where, "outFields": COMP_FIELDS, "f": "json", **extra}, timeout=75)
        r.raise_for_status()
        data = r.json()
        if "error" in data:
            last_err = data["error"]
            continue
        return data.get("features") or []
    raise RuntimeError(last_err)


def find_comps(session: requests.Session, county: str, xy: tuple[float, float], exclude_pid: str = "") -> dict | None:
    """Vacant residential lots sold near a point. Returns a summary with median $/sq ft.
    Only land that was vacant when it sold counts: a lot sold with a new house on it still
    shows as 'vacant' on the tax roll and would otherwise inflate the number."""
    co = FDOR_COUNTY_NO.get(county)
    if co is None or not xy:
        return None
    since = date.today().year - COMP_YEARS + 1
    wheres = [
        f"{c} AND {u} AND SALE_YR1 >= {since} AND SALE_PRC1 >= {COMP_MIN_PRICE:.0f}"
        for c in (f"CO_NO={co}", f"CO_NO='{co}'")
        for u in ("DOR_UC IN ('000','00','0')", "DOR_UC=0")
    ]
    sales, radius = [], COMP_RADIUS_FT
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
                              "vi": _txt(a.get("VI_CD1")).upper(), "qual": _txt(a.get("QUAL_CD1")),
                              "multi": _txt(a.get("M_PAR_SAL1"))})
        if any(x["vi"] in ("V", "I") for x in sales):      # vacant/improved-at-sale code is filled in
            sales = [x for x in sales if x["vi"] == "V"]
        sales = [x for x in sales if not x["multi"]]        # one price for several parcels: skip
        qualified = [x for x in sales if x["qual"] in ("01", "02")]  # arm's-length sales
        if len(qualified) >= COMP_MIN:
            sales = qualified
        if len(sales) >= COMP_MIN or radius != COMP_RADIUS_FT:
            break
    if not sales:
        return {"n": 0, "radius_ft": radius}
    ppsf = sorted(x["ppsf"] for x in sales)
    mid = len(ppsf) // 2
    median = ppsf[mid] if len(ppsf) % 2 else (ppsf[mid - 1] + ppsf[mid]) / 2
    return {"n": len(sales), "radius_ft": radius, "median_ppsf": round(median, 2),
            "low_ppsf": round(ppsf[0], 2), "high_ppsf": round(ppsf[-1], 2)}


LOOKUPS: dict[str, list[int]] = {}   # county -> [tried, found]; used by the health check


def enrich(items: list[dict]) -> None:
    """Look up each parcel's county record (land use, size, value, owner...)."""
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
        stat = LOOKUPS.setdefault(county, [0, 0])
        stat[0] += 1
        try:
            a = lookup_land_use(s, folio) if county == "miamidade" else lookup_statewide(s, county, item["parcel"])
        except Exception as e:
            print(f"[warn] land use {county} {folio}: {e}", file=sys.stderr)
            continue
        if not a:
            print(f"[land use] {county} {folio}: not found")
            continue
        stat[1] += 1
        lu = item["land_use"] = land_use_record(a)
        lu["_pid"] = a.get("_pid") or folio
        # the auction site leaves the address blank for land with no house number
        if not item.get("city") and lu["site_city"]:
            item["city"] = lu["site_city"] + (f", FL- {lu['site_zip']}" if lu["site_zip"] else "")
        if not item.get("zip") and lu["site_zip"]:
            item["zip"] = lu["site_zip"]
        print(f"[land use] {county} {folio}: {lu['code']} {lu['desc']!r}, lot {lu['lot_sqft']} sq ft")
        time.sleep(0.7)


def research(items: list[dict]) -> None:
    """Extra checks for listings that will be alerted: map location, zoning, wetlands,
    flood zone, and (for vacant lots) nearby lot sales. Every check is optional."""
    s = requests.Session()
    s.headers.update(HEADERS)
    for item in items:
        lu = item.get("land_use")
        if not lu:
            continue
        county, pid = item.get("county", "miamidade"), lu.get("_pid")
        try:  # latitude / longitude for the map links
            if county == "miamidade":
                g = _arc(s, f"{PA_POINTS_URL}/query", {"where": f"FOLIO='{pid}'", "outFields": "FOLIO",
                                                        "returnGeometry": "true", "outSR": "4326"})
                lon, lat = (g[0]["geometry"]["x"], g[0]["geometry"]["y"]) if g else (None, None)
            else:
                g = _arc(s, f"{STATEWIDE_LAYER_URL}/query",
                         {"where": f"CO_NO={FDOR_COUNTY_NO[county]} AND PARCEL_ID='{pid}'",
                          "outFields": "PARCEL_ID", "returnGeometry": "true", "outSR": "4326"})
                lon, lat = centroid(g[0].get("geometry") or {}) if g else (None, None)
            if lat and lon:
                lu["lat"], lu["lon"] = round(lat, 6), round(lon, 6)
        except Exception as e:
            print(f"[warn] location {county} {pid}: {e}", file=sys.stderr)
        xy = lu.get("xy")
        if county == "miamidade" and xy:  # county GIS: zoning and wetlands at the parcel
            pt = {"geometry": f"{xy[0]},{xy[1]}", "geometryType": "esriGeometryPoint", "inSR": AREA_SR,
                  "spatialRel": "esriSpatialRelIntersects", "returnGeometry": "false"}
            try:
                z = _arc(s, f"{MD_SERVICE_URL}/19/query", {**pt, "outFields": "ZONE,ZONEDESC,MUNICNAME"})
                za = (z[0]["attributes"] if z else {})
                if _txt(za.get("ZONE")).upper() not in ("", "NONE"):
                    lu["zone"], lu["zone_desc"] = _txt(za.get("ZONE")), _txt(za.get("ZONEDESC"))
                    lu["muni"] = _txt(za.get("MUNICNAME")).title()
                else:  # unincorporated: county zoning
                    z = _arc(s, f"{MD_SERVICE_URL}/18/query", {**pt, "outFields": "ZONE,ZONE_DESC"})
                    if z:
                        lu["zone"] = _txt(z[0]["attributes"].get("ZONE"))
                        lu["zone_desc"] = _txt(z[0]["attributes"].get("ZONE_DESC"))
                    lu["muni"] = "Unincorporated Miami-Dade"
            except Exception as e:
                print(f"[warn] zoning {pid}: {e}", file=sys.stderr)
            try:
                w = _arc(s, f"{MD_SERVICE_URL}/36/query", {**pt, "outFields": "TYPE"})
                if w:
                    lu["wetland"] = _txt(w[0]["attributes"].get("TYPE")) or "yes"
            except Exception as e:
                print(f"[warn] wetlands {pid}: {e}", file=sys.stderr)
        if lu.get("lat"):
            try:  # FEMA flood zone (national flood hazard layer)
                fz = _arc(s, f"{FEMA_NFHL_URL}/query",
                          {"geometry": f"{lu['lon']},{lu['lat']}", "geometryType": "esriGeometryPoint", "inSR": "4326",
                           "spatialRel": "esriSpatialRelIntersects", "outFields": "FLD_ZONE,ZONE_SUBTY",
                           "returnGeometry": "false"}, timeout=30)
                if fz:
                    lu["flood"] = _txt(fz[0]["attributes"].get("FLD_ZONE"))
            except Exception as e:
                print(f"[warn] flood zone {pid}: {e}", file=sys.stderr)
        if item.get("cat") == "lot" and xy:
            try:
                lu["comps"] = find_comps(s, county, tuple(xy), pid)
            except Exception as e:
                print(f"[warn] comps {county} {pid}: {e}", file=sys.stderr)
        time.sleep(0.7)


# ----------------------------------------------------------------------------
# MATCHING: which listings are alerted, and how good each one looks
# ----------------------------------------------------------------------------
def bid_under(item: dict, limit: float) -> bool:
    return not limit or item.get("bid") is None or item["bid"] <= limit


def is_vacant(lu: dict) -> bool:
    if lu.get("living_sqft") or lu.get("year_built"):
        return False
    return dor2(lu.get("code")) in (0, 10, 40, 70, 80, 99) or "VACANT" in (lu.get("desc") or "").upper()


def is_excluded(item: dict) -> bool:
    """Condos, co-ops and land that can't hold a building (roads, canals, lakes, common areas)."""
    lu = item.get("land_use") or {}
    desc = (lu.get("desc") or "").upper()
    return bool(lu.get("condo")) or dor2(lu.get("code")) in SKIP_DOR_CODES or any(x in desc for x in EXCLUDE_LAND_USE)


def land_use_ok(item: dict) -> bool:
    """A vacant residential lot big enough to build on."""
    lu = item.get("land_use")
    if not lu or is_excluded(item):
        return False
    desc = (lu.get("desc") or "").upper()
    by_words = bool(LAND_USE_KEYWORDS) and any(all(w in desc for w in group) for group in LAND_USE_KEYWORDS)
    if not (by_words or (dor2(lu.get("code")) == 0 and is_vacant(lu)) or not LAND_USE_KEYWORDS):
        return False
    sqft = lu.get("lot_sqft")
    return not (MIN_LOT_SQFT and sqft and sqft < MIN_LOT_SQFT)


def category(item: dict) -> str | None:
    """'lot' = vacant residential lot to build on, 'property' = any other non-condo
    property with an opening bid under PROPERTY_MAX_BID, None = no alert."""
    if is_excluded(item):
        return None
    if land_use_ok(item) and bid_under(item, MAX_BID):
        return "lot"
    if PROPERTY_MAX_BID and bid_under(item, PROPERTY_MAX_BID):
        return "property"
    return None


CAT_LABEL = {"lot": "🌱 Vacant lot", "property": f"🏠 Property under ${PROPERTY_MAX_BID:,.0f}"}


def red_flags(item: dict) -> list[str]:
    """Reasons a piece of vacant land probably can't be built on."""
    lu = item.get("land_use") or {}
    if not lu or not is_vacant(lu):
        return []
    f = []
    sqft, land, dims = lu.get("lot_sqft"), lu.get("land_val"), lu.get("dims")
    if sqft and MIN_LOT_SQFT and sqft < MIN_LOT_SQFT:
        f.append(f"small lot ({sqft:,} sq ft)")
    if sqft and dims and dims[1] and sqft / dims[1] < MIN_LOT_WIDTH_FT:
        f.append(f"narrow strip, about {sqft / dims[1]:.0f} ft wide")
    low_value = bool(sqft and land is not None and land / sqft < LOW_LAND_VALUE_PSF)
    if low_value:
        f.append(f"county values the land at only ${land / sqft:,.2f}/sq ft, which usually means it can't be built on")
    if dor2(lu.get("code")) == 99:
        f.append("raw acreage outside the developed area")
    if lu.get("wetland"):
        f.append("in a county wetland area of concern")
    c = lu.get("comps") or {}
    if not low_value and c.get("n", 0) >= COMP_MIN and sqft and land and land / sqft < 0.25 * c["median_ppsf"]:
        f.append("county value is far below nearby lot sales")
    return f


def notes(item: dict) -> list[str]:
    """Things worth knowing that don't rule a listing out."""
    lu = item.get("land_use") or {}
    n = []
    if not item.get("land_use"):
        n.append("county record not found, check it by hand")
    if item["parcel"].upper().startswith("MULTIPLE"):
        n.append("several parcels sold together")
    if not item.get("address") and not lu.get("site_addr"):
        n.append("no street address, check road access on the map")
    if (lu.get("flood") or "").upper().startswith(("A", "V")):
        n.append(f"flood zone {lu['flood']} (flood insurance and a raised floor are required)")
    return n


_RATIO: tuple[float, float, int] | None = None


def price_ratio() -> tuple[float, float, int]:
    """What outside bidders have paid as a share of the county's market value, learned from
    results.csv (25th-75th percentile). Until there are 5 sales, a 70-90% assumption."""
    global _RATIO
    if _RATIO is None:
        r = []
        for row in load_results().values():
            try:
                amt, val = float(row.get("sold_amount") or 0), float(row.get("pa_total_val") or 0)
            except ValueError:
                continue
            if row.get("status") == "Sold" and "3RD PARTY" in (row.get("sold_to") or "").upper() and val >= 50000 and amt:
                r.append(amt / val)
        r.sort()
        if len(r) >= 5:
            q = lambda p: r[int(round((len(r) - 1) * p))]
            _RATIO = (round(q(.25), 2), round(q(.75), 2), len(r))
        else:
            _RATIO = (0.70, 0.90, len(r))
    return _RATIO


def estimate(item: dict) -> list[float] | None:
    """[low, high] likely winning price, from the county's market value of this parcel."""
    lu = item.get("land_use") or {}
    lo, hi, _ = price_ratio()
    value = lu.get("land_val") if is_vacant(lu) else lu.get("total_val")
    if not value or value < 20000 or red_flags(item):
        return None
    return [round(lo * value, -2), round(hi * value, -2)]


def grade(item: dict) -> None:
    """Sets item['flags'], item['est'] and item['tier']:
    'A' = worth a look, 'B' = matches the search but probably not for you."""
    item["flags"], item["est"] = red_flags(item), estimate(item)
    over = item["cat"] == "property" and item["est"] and item["est"][0] > PROPERTY_MAX_BID
    item["tier"] = "B" if item["flags"] or over else "A"
    if over:
        item["why"] = f"likely to sell for {_k(item['est'][0])}–{_k(item['est'][1])}"
    elif item["flags"]:
        item["why"] = item["flags"][0]
    else:
        item["why"] = ""


def _k(v: float) -> str:
    """$4,200 / $235K / $1.2M"""
    if v >= 1_000_000:
        return f"${v / 1_000_000:.1f}M"
    return f"${v / 1000:,.0f}K" if v >= 10_000 else f"${v:,.0f}"


# ----------------------------------------------------------------------------
# SALE RESULTS
# Past auction days disappear from the site's calendar, so results are collected
# the same day, after the sale closes (the evening run: --results).
# ----------------------------------------------------------------------------
RESULT_FIELDS = [
    "sale_date", "county", "aid", "case", "certificate", "parcel", "address", "city", "zip",
    "land_use_code", "land_use", "lot_sqft", "pa_land_val", "pa_total_val", "assessed",
    "opening_bid", "status", "sold_to", "sold_amount", "sold_time", "x_opening",
    "comps_n", "comps_median_ppsf", "est_land_value", "x_est_value", "listing", "property_link", "collected_at",
]


def parse_status(a: dict) -> dict | None:
    """One item from the site's status JSON -> {status, sold_to, sold_amount, sold_time}.
    None if the sale isn't final yet (not started / running)."""
    A, B = (a.get("A") or "").strip(), (a.get("B") or "").strip()
    if A == "Auction Sold":
        return {"status": "Sold", "sold_to": (a.get("ST") or "").strip(),
                "sold_amount": money(a.get("D")), "sold_time": B}
    if A == "B":  # template "Auction Status": B holds the status text (Redeemed, Canceled...)
        return {"status": B, "sold_to": "", "sold_amount": None, "sold_time": ""} if B else None
    if A in ("A", "Time Remaining", ""):  # "Auction Starts" / running
        return None
    return {"status": A, "sold_to": (a.get("ST") or "").strip(), "sold_amount": money(a.get("D")),
            "sold_time": B}


def sale_days_between(s: requests.Session, base: str, start: date, end: date) -> list[date]:
    """Days between start and end (inclusive) that the calendar shows a watched sale on."""
    months, d = set(), start.replace(day=1)
    while d <= end:
        months.add((d.year, d.month))
        d = (d + timedelta(days=32)).replace(day=1)
    days = set()
    for y, m in sorted(months):
        r = s.get(base + CALENDAR_PATH + CALENDAR_MONTH_PARAM.format(m=m, y=y), timeout=30)
        r.raise_for_status()
        for ds, box in re.findall(r'dayid=["\'](\d{2}/\d{2}/\d{4})["\'](.*?)</div>', r.text, re.I | re.S):
            dd = datetime.strptime(ds, "%m/%d/%Y").date()
            if start <= dd <= end and calendar_day_wanted(box):
                days.add(dd)
        time.sleep(2)
    return sorted(days)


def fetch_results_site(site: str, start: date, end: date) -> list[dict]:
    base = site.split("|")[0].rstrip("/")
    county = county_of(base)
    s = requests.Session()
    s.headers.update(HEADERS)
    s.get(base, timeout=30).raise_for_status()
    days = sale_days_between(s, base, start, end)
    print(f"[results] {county}: sale days {start:%m/%d}–{end:%m/%d}: "
          + (", ".join(f"{d:%m/%d}" for d in days) or "none"))
    out = []
    for day in days:
        try:
            out.extend(fetch_results_day(s, base, county, day))
        except Exception as e:
            print(f"[warn] results {county} {day:%m/%d/%Y}: {e}", file=sys.stderr)
    return out


def fetch_results_day(s: requests.Session, base: str, county: str, day: date) -> list[dict]:
    ds = day.strftime(DATE_FORMAT)
    time.sleep(2)
    s.get(base + PREVIEW_PATH.format(date=ds), timeout=30).raise_for_status()  # select the day
    out, ids, pending = [], set(), 0
    for page in range(MAX_PAGES * 3):
        time.sleep(2)
        ms = int(time.time() * 1000)
        r = s.get(base + day_page_url("C", page, ms), timeout=30,
                  headers={"X-Requested-With": "XMLHttpRequest"})
        r.raise_for_status()
        if '"retHTML"' not in r.text:
            break
        batch = [i for i in parse_response(r.text, ds) if f"{county}:{i['id']}" not in ids]
        if not batch:
            break
        time.sleep(1)
        st = s.get(base + STATUS_PATH.format(ids=",".join(i["id"] for i in batch), ms=int(time.time() * 1000)),
                   timeout=30, headers={"X-Requested-With": "XMLHttpRequest"})
        st.raise_for_status()
        status = {a.get("AID"): a for a in (json.loads(st.text.strip(), strict=False).get("ADATA") or {}).get("AITEM", [])}
        for i in batch:
            aid = i["id"]
            ids.add(f"{county}:{aid}")
            res = parse_status(status.get(aid) or {})
            if not res:
                pending += 1
                continue
            i.update({"id": f"{county}:{aid}", "aid": aid, "county": county,
                      "link": base + DETAIL_PATH.format(aid=aid), **res})
            out.append(i)
    print(f"[results] {county} {ds}: {len(out)} final, {pending} not final yet")
    return out


def load_results() -> dict:
    try:
        with RESULTS_FILE.open(newline="") as f:
            return {f"{r['county']}:{r['aid']}": r for r in csv.DictReader(f)}
    except FileNotFoundError:
        return {}


def result_row(i: dict) -> dict:
    lu = i.get("land_use") or {}
    c = lu.get("comps") or {}
    est = c.get("median_ppsf") * lu["lot_sqft"] if c.get("n") and lu.get("lot_sqft") else None
    amt, bid = i.get("sold_amount"), i.get("bid")
    r2 = lambda x: "" if x is None else round(x, 2)
    return {
        "sale_date": i["sale_date"], "county": i["county"], "aid": i["aid"], "case": i["case"],
        "certificate": i["raw"].get("Certificate #", ""), "parcel": i["parcel"],
        "address": i["address"] or lu.get("site_addr") or "",
        "city": i["city"] or lu.get("site_city") or "", "zip": i["zip"] or lu.get("site_zip") or "",
        "land_use_code": lu.get("code", ""), "land_use": lu.get("desc", ""), "lot_sqft": lu.get("lot_sqft") or "",
        "pa_land_val": r2(lu.get("land_val")), "pa_total_val": r2(lu.get("total_val")), "assessed": r2(i.get("assessed")),
        "opening_bid": r2(bid), "status": i["status"], "sold_to": i["sold_to"], "sold_amount": r2(amt),
        "sold_time": i["sold_time"],
        "x_opening": r2(amt / bid) if amt and bid else "",
        "comps_n": c.get("n", ""), "comps_median_ppsf": c.get("median_ppsf", ""),
        "est_land_value": r2(est), "x_est_value": r2(amt / est) if amt and est else "",
        "listing": i["link"],
        "property_link": next((u for n, u in property_links(i["county"], i["parcel"]) if n == "Property"), ""),
        "collected_at": datetime.now().isoformat(timespec="minutes"),
    }


def collect_results(start: date, end: date, dry_run: bool) -> None:
    rows = load_results()
    found = []
    for site in BASE_URLS:
        try:
            found.extend(fetch_results_site(site, start, end))
        except Exception as e:
            print(f"[error] results {site}: {e}", file=sys.stderr)
    types = {t.replace(" ", "") for t in AUCTION_TYPES}
    new = [i for i in found if i["id"] not in rows and (not types or i["type"].replace(" ", "") in types)]
    # land use: reuse what the morning run already looked up, look up the rest
    seen = load_seen()
    todo = []
    for i in new:
        lu = (seen.get(i["id"]) or {}).get("land_use")
        if lu:
            i["land_use"] = lu
        else:
            todo.append(i)
    enrich(todo)
    for i in new:
        rows[i["id"]] = result_row(i)
    # rows saved before the county lookup covered condo units: fill them in, a few per run
    blank = [r for r in rows.values() if not r.get("land_use") and not r["parcel"].upper().startswith("MULTIPLE")][:40]
    fix = [{"county": r["county"], "parcel": r["parcel"], "city": r.get("city"), "zip": r.get("zip"), "_row": r} for r in blank]
    enrich(fix)
    for f in fix:
        lu = f.get("land_use")
        if lu:
            f["_row"].update({"land_use_code": lu.get("code") or "", "land_use": lu.get("desc") or "",
                              "lot_sqft": lu.get("lot_sqft") or "",
                              "pa_land_val": "" if lu.get("land_val") is None else lu["land_val"],
                              "pa_total_val": "" if lu.get("total_val") is None else lu["total_val"],
                              "address": f["_row"].get("address") or lu.get("site_addr") or "",
                              "city": f["_row"].get("city") or lu.get("site_city") or ""})
    print(f"[results] {len(new)} new result(s), {len(rows)} total in {RESULTS_FILE}"
          + (f", {sum(1 for f in fix if f.get('land_use'))} older row(s) completed" if fix else ""))
    if not dry_run:
        ordered = sorted(rows.values(), key=lambda r: (datetime.strptime(r["sale_date"], DATE_FORMAT), r["county"], r["case"]))
        with RESULTS_FILE.open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=RESULT_FIELDS, extrasaction="ignore")
            w.writeheader()
            for r in ordered:  # rows saved before this column existed
                if not r.get("property_link") or (r["county"] == "broward" and re.search(r"[A-Za-z]", r["parcel"])):
                    r["property_link"] = next((u for n, u in property_links(r["county"], r["parcel"]) if n == "Property"), "")
            w.writerows(ordered)
    sold = [i for i in new if i["status"] == "Sold"]
    if new and RESULTS_NOTIFY:
        lines = []
        for county in sorted({i["county"] for i in new}):
            c_new = [i for i in new if i["county"] == county]
            c_sold = [i for i in sold if i["county"] == county]
            counts = {}
            for i in c_new:
                counts[i["status"]] = counts.get(i["status"], 0) + 1
            lines.append(f"{county.upper()}: " + ", ".join(f"{n} {k.lower()}" for k, n in sorted(counts.items(), key=lambda x: -x[1])))
            for i in sorted(c_sold, key=lambda x: -(x.get("sold_amount") or 0)):
                lu = (i.get("land_use") or {}).get("desc", "")
                x = f" ({i['sold_amount'] / i['bid']:.1f}x opening)" if i.get("sold_amount") and i.get("bid") else ""
                amt = f"${i['sold_amount']:,.0f}" if i.get("sold_amount") is not None else "n/a"
                lines.append(f"  #{i['case']} {i['address'] or 'no address'} {i['city']} · {lu.title()} · "
                             f"opened ${i['bid'] or 0:,.0f} → sold {amt}{x} to {i['sold_to']}")
        text = f"📊 Auction results {end:%m/%d}\n" + "\n".join(lines)
        if dry_run or not (TELEGRAM_TOKEN or SMTP_USER):
            print(text)
        else:
            if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID:
                send_telegram(text)
            if SMTP_USER and SMTP_PASS:
                send_email(f"📊 Auction results {end:%m/%d}", text)


# ----------------------------------------------------------------------------
# WEEKLY REPORT (Saturdays): what sold this week, what it means for bidding,
# and which of your matches come up next week.
# ----------------------------------------------------------------------------
def _f(x) -> float | None:
    try:
        return float(x) if x not in (None, "") else None
    except ValueError:
        return None


def _median(v: list[float]) -> float | None:
    v = sorted(v)
    if not v:
        return None
    m = len(v) // 2
    return v[m] if len(v) % 2 else (v[m - 1] + v[m]) / 2


def _pct(v: list[float], q: float) -> float | None:
    v = sorted(v)
    if not v:
        return None
    k = (len(v) - 1) * q
    lo, hi = int(k), min(int(k) + 1, len(v) - 1)
    return v[lo] + (v[hi] - v[lo]) * (k - lo)


GROUPS = ("Vacant residential lots", "Small vacant lots", "Raw acreage", "Other vacant land", "Single family",
          "Multi-family", "Mobile home", "Condo / co-op", "Other")


def _group(desc: str, sqft: float | None = None) -> str:
    d = (desc or "").upper()
    if not d:
        return "Unknown"
    if "CONDO" in d or "COOPERATIVE" in d:
        return "Condo / co-op"
    if any(w in d for w in ("RIGHT-OF-WAY", "RIVERS, LAKES", "WASTE LAND", "COMMON AREAS", "PARK LAND", "DOR USE CODE 09")):
        return "Roads, canals, lakes"
    if "ACREAGE" in d:
        return "Raw acreage"
    if "VACANT" in d and ("RESIDENTIAL" in d or "TOWNHOUSE" in d):
        return "Small vacant lots" if sqft and MIN_LOT_SQFT and sqft < MIN_LOT_SQFT else "Vacant residential lots"
    if "VACANT" in d:
        return "Other vacant land"
    if "SINGLE FAMILY" in d:
        return "Single family"
    if "MOBILE" in d:
        return "Mobile home"
    if "MULTI" in d:
        return "Multi-family"
    return "Other"


def _city(r: dict) -> str:
    return (r.get("city") or "").split(",")[0].strip().title() or "Unincorporated"


COUNTY_NAME = {"miamidade": "Miami-Dade", "broward": "Broward"}


def property_links(county: str, parcel: str) -> list[tuple[str, str]]:
    """Property Appraiser links for a parcel (Miami-Dade: property search; Broward: record + map)."""
    parcel = parcel or ""
    if not parcel or parcel.upper().startswith("MULTIPLE"):
        return []
    digits = re.sub(r"\D", "", parcel)
    if county == "miamidade" and len(digits) == 13:
        return [("Property", f"https://apps.miamidadepa.gov/propertysearch/#/?folio={digits}")]
    folio = re.sub(r"[^0-9A-Za-z]", "", parcel).upper()   # Broward folios can contain letters (484134-AB-0200)
    if county == "broward" and folio:
        return [("Property", f"https://bcpa.net/RecInfo.asp?URL_Folio={folio}"),
                ("Map", f"https://gisweb-adapters.bcpa.net/bcpawebmap_ex/bcpawebmap.aspx?FOLIO={folio}")]
    return []


# Chart colors (validated reference palette, light mode): fixed slots, never cycled.
C_BLUE, C_ORANGE, C_AQUA = "#2a78d6", "#eb6834", "#1baf7a"
C_GRAY, C_GRAY_DARK = "#c3c2b7", "#8a8983"
C_SURFACE, C_TEXT, C_TEXT2, C_GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e7e6e1"


def weekly_data(today: date) -> dict:
    rows = list(load_results().values())
    for r in rows:
        r["_d"] = datetime.strptime(r["sale_date"], DATE_FORMAT).date()
        r["_amt"], r["_bid"] = _f(r.get("sold_amount")), _f(r.get("opening_bid"))
        r["_x"], r["_xe"] = _f(r.get("x_opening")), _f(r.get("x_est_value"))
        r["_sq"] = _f(r.get("lot_sqft"))
        r["_g"] = _group(r.get("land_use"), r["_sq"])
        pa = _f(r.get("pa_total_val"))
        r["_pv"] = r["_amt"] / pa if r["_amt"] and pa and pa >= 20000 else None  # paid vs county value
        r["_3p"] = "3RD PARTY" in (r.get("sold_to") or "").upper()
        r["_sold"] = r["status"] == "Sold"
        r["_links"] = property_links(r["county"], r.get("parcel"))
    start = today - timedelta(days=7)
    d = {"today": today, "start": start, "end": today - timedelta(days=1), "rows": rows,
         "week": [r for r in rows if start <= r["_d"] < today]}
    d["third_all"] = [r for r in rows if r["_sold"] and r["_3p"] and r["_x"]]

    # per county, this week
    d["counties"] = []
    for county in sorted({r["county"] for r in d["week"]}):
        c = [r for r in d["week"] if r["county"] == county]
        sold = [r for r in c if r["_sold"]]
        third = [r["_x"] for r in sold if r["_3p"] and r["_x"]]
        red = sum(1 for r in c if r["status"].upper().startswith("REDEEM"))
        d["counties"].append({"name": COUNTY_NAME.get(county, county.title()), "n": len(c),
                              "days": len({r["_d"] for r in c}), "sold": len(sold),
                              "third": sum(1 for r in sold if r["_3p"]), "redeemed": red,
                              "median_x": _median(third)})
    w = d["week"]
    xs_w = [r["_x"] for r in w if r["_sold"] and r["_3p"] and r["_x"]]
    d["kpi"] = {"listings": len(w), "sold": sum(1 for r in w if r["_sold"]),
                "third": sum(1 for r in w if r["_sold"] and r["_3p"]),
                "median_x": _median(xs_w),
                "redeemed_pct": (sum(1 for r in w if r["status"].upper().startswith("REDEEM")) / len(w)) if w else None,
                "volume": sum(r["_amt"] or 0 for r in w if r["_sold"])}
    d["sold_week"] = sorted([r for r in w if r["_sold"]], key=lambda r: -(r["_amt"] or 0))

    # bidding guide (all data)
    guide = []
    for g in GROUPS:
        sales = [r for r in d["third_all"] if r["_g"] == g]
        if not sales:
            continue
        xs = [r["_x"] for r in sales]
        pv = [r["_pv"] for r in sales if r["_pv"]]
        ppsf = [r["_amt"] / r["_sq"] for r in sales if r["_amt"] and r["_sq"]]
        guide.append({"type": g, "n": len(xs), "median": _median(xs), "p75": _pct(xs, .75),
                      "pv": _median(pv), "pv_n": len(pv),
                      "ppsf": _median(ppsf) if g == "Vacant residential lots" and ppsf else None})
    d["guide"] = guide
    pv_all = [r["_pv"] for r in d["third_all"] if r["_pv"]]
    d["pv"] = (_median(pv_all), len(pv_all)) if pv_all else None
    by_city: dict[str, list[float]] = {}
    for r in d["third_all"]:
        if r.get("city"):
            by_city.setdefault(_city(r), []).append(r["_x"])
    d["cities"] = sorted(((c, _median(v), len(v)) for c, v in by_city.items() if len(v) >= 3),
                         key=lambda t: -t[1])[:5]
    d["county_rates"] = []
    for county in sorted({r["county"] for r in rows}):
        c = [r for r in rows if r["county"] == county]
        d["county_rates"].append({
            "name": COUNTY_NAME.get(county, county.title()), "n": len(c),
            "redeemed": sum(1 for r in c if r["status"].upper().startswith("REDEEM")) / len(c),
            "cert": sum(1 for r in c if r["_sold"] and not r["_3p"]) / len(c),
            "third": sum(1 for r in c if r["_sold"] and r["_3p"]) / len(c)})

    # your matches in the next 7 days (still on the list, graded "worth a look")
    up, others = [], 0
    for k, v in load_seen().items():
        if k.startswith("_") or not v.get("ok") or v.get("gone") or v.get("v") != STATE_VERSION:
            continue
        dd = days_until(v.get("sale_date", ""), today)
        if dd is None or not 0 <= dd <= 7:
            continue
        if v.get("last_seen") and (today - date.fromisoformat(v["last_seen"])).days > 3:
            continue  # dropped off the auction list
        if v.get("tier") != "A":
            others += 1
            continue
        county = k.split(":")[0]
        it = {**v, "county": county}
        up.append({"days": dd, "date": v["sale_date"], "county": COUNTY_NAME.get(county, county),
                   "cat": v.get("cat"), "where": where(it), "type": what(v.get("land_use") or {}),
                   "bid": v.get("bid"), "est": v.get("est"), "links": links_of(it)})
    d["upcoming_other"] = others
    d["upcoming"] = sorted(up, key=lambda u: u["days"])
    return d


def weekly_charts(d: dict) -> dict[str, bytes]:
    """PNG charts (matplotlib). Returns {} if matplotlib isn't installed or there's no data."""
    try:
        import io
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.ticker import FuncFormatter
    except ImportError:
        print("[weekly] matplotlib not installed; sending the report without charts", file=sys.stderr)
        return {}

    def style(ax, title):
        ax.set_facecolor(C_SURFACE)
        for s in ("top", "right", "left"):
            ax.spines[s].set_visible(False)
        ax.spines["bottom"].set_color(C_GRID)
        ax.tick_params(colors=C_TEXT2, labelsize=9, length=0)
        ax.set_title(title, loc="left", fontsize=12, color=C_TEXT, fontweight="bold", pad=24)

    def png(fig):
        buf = io.BytesIO()
        fig.savefig(buf, format="png", dpi=160, facecolor=C_SURFACE, bbox_inches="tight")
        plt.close(fig)
        return buf.getvalue()

    money_fmt = FuncFormatter(lambda v, _: f"${v / 1000:,.0f}K" if v >= 1000 else f"${v:,.0f}")
    out = {}
    rows = d["rows"]

    # 1) outcome of every sale day (stacked bars)
    days = sorted({(r["_d"], r["county"]) for r in rows})[-12:]
    if days:
        cats = [("Sold to outside bidder", C_BLUE, lambda r: r["_sold"] and r["_3p"]),
                ("Sold to cert holder", C_ORANGE, lambda r: r["_sold"] and not r["_3p"]),
                ("Redeemed", C_GRAY, lambda r: r["status"].upper().startswith("REDEEM")),
                ("Canceled / other", C_GRAY_DARK, lambda r: not r["_sold"] and not r["status"].upper().startswith("REDEEM"))]
        fig, ax = plt.subplots(figsize=(7.2, 3.4))
        labels = [f"{dt:%m/%d}\n{'BRW' if c == 'broward' else 'MDC'}" for dt, c in days]
        bottom = [0] * len(days)
        for name, color, f in cats:
            vals = [sum(1 for r in rows if (r["_d"], r["county"]) == k and f(r)) for k in days]
            ax.bar(labels, vals, bottom=bottom, color=color, label=name, width=0.6,
                   edgecolor=C_SURFACE, linewidth=2)
            bottom = [b + v for b, v in zip(bottom, vals)]
        for x, t in enumerate(bottom):
            ax.text(x, t + max(bottom) * 0.02, str(t), ha="center", va="bottom", fontsize=8, color=C_TEXT2)
        ax.set_ylim(0, max(bottom) * 1.12)
        ax.yaxis.grid(True, color=C_GRID, linewidth=0.8)
        ax.set_axisbelow(True)
        ax.set_ylabel("Listings", color=C_TEXT2, fontsize=9)
        ax.legend(ncol=4, fontsize=8, frameon=False, loc="lower left", bbox_to_anchor=(0, 1.02),
                  labelcolor=C_TEXT2, handlelength=1, columnspacing=1.2, borderaxespad=0)
        style(ax, "What happened on each sale day")
        out["outcomes"] = png(fig)

    # 2) opening bid vs price paid (outside bidders), log-log
    pts = [r for r in d["third_all"] if r["_bid"] and r["_amt"]]
    if pts:
        groups = [("Vacant land", C_BLUE), ("Single family", C_ORANGE), ("Other", C_AQUA)]
        gof = lambda r: ("Vacant land" if "vacant" in r["_g"].lower() or r["_g"] == "Raw acreage"
                         else r["_g"] if r["_g"] == "Single family" else "Other")
        fig, ax = plt.subplots(figsize=(7.2, 4.0))
        xlo, xhi = min(r["_bid"] for r in pts) * 0.7, max(r["_bid"] for r in pts) * 1.4
        ylo = min(min(r["_amt"] for r in pts), min(r["_bid"] for r in pts)) * 0.7
        yhi = max(r["_amt"] for r in pts) * 1.4
        for m in (1, 2, 5, 10):
            x0, x1 = max(xlo, ylo / m), min(xhi, yhi / m)
            if x0 >= x1:
                continue
            ax.plot([x0, x1], [x0 * m, x1 * m], color="#cfcec8", linewidth=1, linestyle="--", zorder=1)
            ax.text(x1, x1 * m, f" {m}×", color=C_TEXT2, fontsize=8,
                    va="bottom" if x1 < xhi else "center", ha="right" if x1 < xhi else "left")
        for name, color in groups:
            g = [r for r in pts if gof(r) == name]
            if g:
                ax.scatter([r["_bid"] for r in g], [r["_amt"] for r in g], s=55, color=color,
                           edgecolors=C_SURFACE, linewidths=1.5, label=f"{name} ({len(g)})", zorder=3)
        ax.set_xscale("log"); ax.set_yscale("log")
        ax.set_xlim(xlo, xhi); ax.set_ylim(ylo, yhi)
        ax.tick_params(which="minor", length=0)
        ax.minorticks_off()
        ax.xaxis.set_major_formatter(money_fmt); ax.yaxis.set_major_formatter(money_fmt)
        ax.set_xlabel("Opening bid", color=C_TEXT2, fontsize=9)
        ax.set_ylabel("Price paid", color=C_TEXT2, fontsize=9)
        ax.grid(True, color=C_GRID, linewidth=0.6, which="major")
        ax.set_axisbelow(True)
        ax.legend(ncol=3, fontsize=8, frameon=False, loc="lower left", bbox_to_anchor=(0, 1.02),
                  labelcolor=C_TEXT2, handletextpad=0.3, borderaxespad=0)
        style(ax, "Outside-bidder sales: opening bid vs. price paid (all data)")
        out["scatter"] = png(fig)

    # 3) median multiple by property type
    guide = [g for g in d["guide"] if g["n"] >= 2]
    if guide:
        fig, ax = plt.subplots(figsize=(7.2, 0.55 * len(guide) + 1.1))
        names = [f"{g['type']}  (n={g['n']})" for g in guide][::-1]
        vals = [g["median"] for g in guide][::-1]
        ax.barh(names, vals, color=C_BLUE, height=0.55, edgecolor=C_SURFACE, linewidth=2)
        for y, v in enumerate(vals):
            ax.text(v + max(vals) * 0.015, y, f"{v:.1f}×", va="center", fontsize=9, color=C_TEXT)
        ax.axvline(1, color=C_TEXT2, linewidth=1, linestyle="--")
        ax.xaxis.grid(True, color=C_GRID, linewidth=0.8)
        ax.set_axisbelow(True)
        ax.set_xlim(0, max(vals) * 1.15)
        ax.xaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:.0f}×"))
        style(ax, "Typical price paid, as a multiple of the opening bid")
        ax.text(0, 1.04, "Median of outside-bidder sales · dashed line = opening bid", transform=ax.transAxes,
                fontsize=8, color=C_TEXT2)
        out["multiples"] = png(fig)
    return out


def _m(v) -> str:
    return "—" if v is None else f"${v:,.0f}"


def weekly_html(d: dict, chart_src: dict[str, str]) -> str:
    """Email-safe HTML report. chart_src maps chart name -> img src (cid:... or data:...)."""
    e = lambda s: html.escape(str(s))
    td = 'style="padding:7px 8px;border-bottom:1px solid #ecebe6;font-size:13px;vertical-align:top"'
    tdr = 'style="padding:7px 8px;border-bottom:1px solid #ecebe6;font-size:13px;text-align:right;white-space:nowrap;vertical-align:top"'
    th = 'style="padding:7px 8px;border-bottom:2px solid #d6d5cf;font-size:11px;text-transform:uppercase;letter-spacing:.04em;color:#52514e;text-align:left"'
    thr = th.replace("text-align:left", "text-align:right")
    h2 = 'style="font-size:17px;margin:30px 0 4px;color:#0b0b0b"'
    sub = 'style="font-size:13px;color:#52514e;margin:0 0 12px"'
    links = lambda ls: " · ".join(f'<a href="{e(u)}" style="color:#2a78d6;text-decoration:none">{e(n)}</a>' for n, u in ls)
    img = lambda k: (f'<img src="{chart_src[k]}" width="680" style="width:100%;max-width:680px;height:auto;display:block;margin:8px 0 4px" alt="">'
                     if k in chart_src else "")
    k = d["kpi"]
    P = []
    P.append(f'''<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Auction report {d["today"]:%m/%d/%Y}</title><meta name="color-scheme" content="light"></head>
<body style="margin:0;background:#f1f0ec;font-family:-apple-system,Segoe UI,Roboto,Helvetica,Arial,sans-serif;color:#0b0b0b">
<div style="max-width:760px;margin:0 auto;padding:16px">
<div style="background:#fcfcfb;border-radius:12px;padding:24px 22px">
<div style="font-size:12px;color:#52514e;text-transform:uppercase;letter-spacing:.06em">Tax deed auctions · Miami-Dade &amp; Broward</div>
<h1 style="font-size:24px;margin:4px 0 2px">Weekly report</h1>
<div style="font-size:14px;color:#52514e">{d["start"]:%b %d} – {d["end"]:%b %d, %Y}</div>''')

    if not d["rows"]:
        P.append('<p style="margin-top:24px">No results saved yet. Check that the <b>auction-results</b> Action is '
                 'running and committing <code>results.csv</code>.</p></div></div></body></html>')
        return "".join(P)

    # KPI tiles
    tiles = [("Listings", f'{k["listings"]}'), ("Sold", f'{k["sold"]}'),
             ("To outside bidders", f'{k["third"]}'),
             ("Median × opening", f'{k["median_x"]:.1f}×' if k["median_x"] else "—"),
             ("Redeemed", f'{k["redeemed_pct"]:.0%}' if k["redeemed_pct"] is not None else "—")]
    P.append('<table role="presentation" width="100%" cellspacing="0" cellpadding="0" style="margin-top:18px;border-collapse:separate;border-spacing:6px 0"><tr>')
    for label, val in tiles:
        P.append(f'<td style="background:#f4f3ef;border-radius:8px;padding:10px 10px;width:20%;vertical-align:top">'
                 f'<div style="font-size:11px;color:#52514e">{e(label)}</div>'
                 f'<div style="font-size:18px;font-weight:700;margin-top:2px">{e(val)}</div></td>')
    P.append("</tr></table>")
    if not d["week"]:
        P.append('<p style="font-size:14px;color:#52514e;margin:14px 0 0">No tax deed sales this week. '
                 'The guide below uses all data saved so far.</p>')
    for c in d["counties"]:
        mx = f', outside bidders paid a median <b>{c["median_x"]:.1f}×</b> the opening bid' if c["median_x"] else ""
        P.append(f'<p style="font-size:14px;margin:12px 0 0"><b>{e(c["name"])}</b>: {c["n"]} listings on {c["days"]} sale day(s) · '
                 f'{c["sold"]} sold ({c["third"]} to outside bidders) · {c["redeemed"]} redeemed{mx}.</p>')

    # this week's sales
    if d["sold_week"]:
        P.append(f'<h2 {h2}>What sold this week</h2><p {sub}>Sorted by price. Open the Property link to see what was sold.</p>')
        P.append('<table width="100%" cellspacing="0" cellpadding="0" style="border-collapse:collapse">')
        P.append(f'<tr><th {th}>Date</th><th {th}>Property</th><th {thr}>Opening</th><th {thr}>Paid</th></tr>')
        for r in d["sold_week"]:
            lot = f" · {int(r['_sq']):,} sq ft" if r["_sq"] else ""
            pa = _f(r.get("pa_total_val"))
            pav = f" · PA value {_m(pa)}" if pa else ""
            ls = r["_links"] + ([("Listing", r["listing"])] if r.get("listing") else [])
            buyer = "outside bidder" if r["_3p"] else "cert holder"
            if r["_pv"]:
                buyer += f" · {r['_pv']:.0%} of county value"
            mult = f"{r['_x']:.1f}× · " if r["_x"] else ""
            P.append(f'<tr><td {td}>{r["_d"]:%m/%d}<br><span style="color:#52514e;font-size:11px">{e(COUNTY_NAME.get(r["county"], r["county"]))}</span></td>'
                     f'<td {td}><b>{e(r["address"] or "No address")}</b>, {e(_city(r))}<br>'
                     f'<span style="color:#52514e;font-size:12px">{e(r["_g"])}{lot}{pav}</span><br>'
                     f'<span style="font-size:12px">{links(ls)}</span></td>'
                     f'<td {tdr}>{_m(r["_bid"])}</td><td {td.replace("vertical-align:top", "vertical-align:top;text-align:right")}><b style="white-space:nowrap">{_m(r["_amt"])}</b><br>'
                     f'<span style="color:#52514e;font-size:11px">{mult}{buyer}</span></td></tr>')
        P.append("</table>")

    # charts
    if chart_src:
        P.append(f'<h2 {h2}>Charts</h2>')
        P.append(img("outcomes"))
        P.append(img("scatter"))
        P.append(img("multiples"))

    # bidding guide
    P.append(f'<h2 {h2}>Bidding guide</h2><p {sub}>All {len(d["rows"])} results saved since '
             f'{min(r["_d"] for r in d["rows"]):%b %d}. Based on sales to outside bidders, where there was real competition.</p>')
    if len(d["third_all"]) < 5:
        P.append(f'<p style="font-size:13px;color:#52514e">Only {len(d["third_all"])} outside-bidder sale(s) so far. '
                 'These numbers become reliable after about 20.</p>')
    if d["guide"]:
        P.append('<table width="100%" cellspacing="0" cellpadding="0" style="border-collapse:collapse">')
        P.append(f'<tr><th {th}>Property type</th><th {thr}>Sales</th><th {thr}>Median × opening</th>'
                 f'<th {thr}>Paid vs county value</th><th {thr}>$/sq ft</th></tr>')
        for g in d["guide"]:
            ppsf = f"${g['ppsf']:,.2f}" if g["ppsf"] else "—"
            pv = f"{g['pv']:.0%}" if g["pv"] else "—"
            P.append(f'<tr><td {td}>{e(g["type"])}</td><td {tdr}>{g["n"]}</td><td {tdr}><b>{g["median"]:.1f}×</b></td>'
                     f'<td {tdr}>{pv}</td><td {tdr}>{ppsf}</td></tr>')
        P.append("</table>")
    notes = []
    if d["pv"]:
        notes.append(f'Outside bidders have paid a median <b>{d["pv"][0]:.0%}</b> of the county\'s market value '
                     f'(n={d["pv"][1]}, properties the county values at $20K or more). The opening bid is only the '
                     f'unpaid taxes, so it says little about the final price.')
    if d["cities"]:
        notes.append("Most competitive cities: " + ", ".join(f'{e(c)} <b>{m:.1f}×</b> (n={n})' for c, m, n in d["cities"]) + ".")
    for c in d["county_rates"]:
        notes.append(f'{e(c["name"])}: {c["redeemed"]:.0%} redeemed before the sale, {c["cert"]:.0%} went to the cert holder '
                     f'with no bids, {c["third"]:.0%} sold to outside bidders (n={c["n"]}).')
    if notes:
        P.append('<ul style="font-size:13px;padding-left:18px;margin:12px 0 0">' + "".join(f"<li style='margin:4px 0'>{n}</li>" for n in notes) + "</ul>")

    # upcoming
    P.append(f'<h2 {h2}>Your matches in the next 7 days</h2>')
    if not d["upcoming"]:
        P.append(f'<p {sub}>No listing graded "worth a look" goes to sale in the next 7 days.</p>')
    else:
        P.append(f'<p {sub}>Still on the auction list and graded "worth a look". Likely price is based on the county\'s value of each property.</p>')
        P.append('<table width="100%" cellspacing="0" cellpadding="0" style="border-collapse:collapse">')
        P.append(f'<tr><th {th}>Sale</th><th {th}>Property</th><th {thr}>Opening</th><th {thr}>Likely price</th></tr>')
        for u in d["upcoming"]:
            icon = "🌱" if u["cat"] == "lot" else "🏠"
            est = f'{_k(u["est"][0])} – {_k(u["est"][1])}' if u["est"] else '<span style="color:#52514e">—</span>'
            P.append(f'<tr><td {td}>{e(u["date"][:5])}<br><span style="color:#52514e;font-size:11px">{e(u["county"])}</span></td>'
                     f'<td {td}>{icon} <b>{e(u["where"])}</b><br><span style="color:#52514e;font-size:12px">{e(u["type"])}</span><br>'
                     f'<span style="font-size:12px">{links(u["links"])}</span></td>'
                     f'<td {tdr}>{_m(u["bid"])}</td><td {tdr}>{est}</td></tr>')
        P.append("</table>")
    if d.get("upcoming_other"):
        P.append(f'<p style="font-size:13px;color:#52514e;margin:10px 0 0">{d["upcoming_other"]} other '
                 f'match(es) go to sale in the next 7 days but were graded "probably not for you" '
                 f'(unbuildable land, or likely to sell above your limit).</p>')
    P.append('<p style="font-size:11px;color:#8a8983;margin-top:26px">Generated by auction-watcher from the public auction '
             'calendars. For your own bidding decisions only.</p></div></div></body></html>')
    return "".join(P)


def weekly_telegram(d: dict) -> str:
    """Short Telegram summary (HTML parse mode); the full report goes as an attached file."""
    e = html.escape
    k = d["kpi"]
    L = [f"<b>📈 Weekly auction report</b>", f"<i>{d['start']:%b %d} – {d['end']:%b %d}</i>", ""]
    if not d["rows"]:
        L.append("No results saved yet. Check that the auction-results Action is running.")
        return "\n".join(L)
    if d["week"]:
        mx = f" · median <b>{k['median_x']:.1f}×</b> opening" if k["median_x"] else ""
        L.append(f"<b>{k['listings']}</b> listings · <b>{k['sold']}</b> sold ({k['third']} to outside bidders) · "
                 f"{k['redeemed_pct']:.0%} redeemed{mx}")
    else:
        L.append("No tax deed sales this week.")
    if d["sold_week"]:
        L += ["", "<b>Top sales</b>"]
        short = {"Vacant residential lots": "Lot", "Small vacant lots": "Small lot", "Raw acreage": "Acreage",
                 "Other vacant land": "Land", "Single family": "House", "Multi-family": "Multi",
                 "Mobile home": "Mobile", "Condo / co-op": "Condo", "Roads, canals, lakes": "Road/canal"}
        rows = [(_city(r)[:12], short.get(r["_g"], "Other"), _m(r["_amt"]),
                 f"{r['_x']:.1f}x" if r["_x"] else "cert") for r in d["sold_week"][:6]]
        table = [("City", "Type", "Paid", "x open")] + rows
        w = [max(len(r[i]) for r in table) for i in range(4)]
        fmt = lambda r: f"{r[0]:<{w[0]}} {r[1]:<{w[1]}} {r[2]:>{w[2]}} {r[3]:>{w[3]}}"
        L.append("<pre>" + e("\n".join(fmt(r) for r in table)) + "</pre>")
    if d["upcoming"]:
        L += ["", f"<b>Next 7 days: {len(d['upcoming'])} worth a look</b>"]
        for u in d["upcoming"][:5]:
            icon = "🌱" if u["cat"] == "lot" else "🏠"
            est = f" → likely {_k(u['est'][0])}–{_k(u['est'][1])}" if u["est"] else ""
            L.append(f"{icon} {e(u['date'][:5])} {e(u['where'])} · opens {_m(u['bid'])}{est}")
    L += ["", "Full report with tables, charts and Property Appraiser links attached ⬇️"]
    return "\n".join(L)


def send_weekly(today: date, dry_run: bool) -> None:
    import base64
    d = weekly_data(today)
    charts = weekly_charts(d) if d["rows"] else {}
    file_html = weekly_html(d, {k: "data:image/png;base64," + base64.b64encode(v).decode() for k, v in charts.items()})
    name = f"auction-report-{today:%Y-%m-%d}.html"
    if dry_run or not (TELEGRAM_TOKEN or SMTP_USER):
        Path(name).write_text(file_html, encoding="utf-8")
        for k, v in charts.items():
            Path(f"chart-{k}.png").write_bytes(v)
        print(weekly_telegram(d))
        print(f"\n[weekly] wrote {name} and {len(charts)} chart(s)")
        return
    if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID:
        tg("sendMessage", chat_id=TELEGRAM_CHAT_ID, text=weekly_telegram(d), parse_mode="HTML",
           disable_web_page_preview=True)
        if charts:
            media = [{"type": "photo", "media": f"attach://{k}"} for k in charts]
            r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMediaGroup",
                              data={"chat_id": TELEGRAM_CHAT_ID, "media": json.dumps(media)},
                              files={k: (f"{k}.png", v, "image/png") for k, v in charts.items()}, timeout=60)
            if not r.json().get("ok"):
                print(f"[warn] Telegram charts: {r.text[:200]}", file=sys.stderr)
        r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendDocument",
                          data={"chat_id": TELEGRAM_CHAT_ID, "caption": "Full weekly report (open in your browser)"},
                          files={"document": (name, file_html.encode("utf-8"), "text/html")}, timeout=60)
        if not r.json().get("ok"):
            print(f"[warn] Telegram report file: {r.text[:200]}", file=sys.stderr)
    if SMTP_USER and SMTP_PASS:
        msg = EmailMessage()
        msg["Subject"] = f"📈 Weekly auction report · {d['start']:%b %d} – {d['end']:%b %d}"
        msg["From"], msg["To"] = SMTP_USER, EMAIL_TO
        msg.set_content(re.sub(r"<[^>]+>", "", weekly_telegram(d)))
        msg.add_alternative(weekly_html(d, {k: f"cid:{k}" for k in charts}), subtype="html")
        body = msg.get_payload()[1]
        for k, v in charts.items():
            body.add_related(v, "image", "png", cid=f"<{k}>")
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
            smtp.login(SMTP_USER, SMTP_PASS)
            smtp.send_message(msg)


# ----------------------------------------------------------------------------
# HEALTH CHECK: tell the user when the watcher can't read a site, instead of going quiet
# ----------------------------------------------------------------------------
HEALTH: dict[str, dict] = {}      # county -> {"error"} or {"expected", "parsed", "note"}
CAL_ACTIVE: dict[tuple[str, str], int] = {}   # (county, sale date) -> active listings shown on the calendar
CAL_NOTE: dict[str, str] = {}
GONE_WHY = {"REDEEMED": "redeemed: the owner paid the taxes", "NO": "no longer on the list", "SOLD": "already sold"}


def health_problems() -> list[tuple[str, str]]:
    out = []
    for site in BASE_URLS:
        county = county_of(site.split("|")[0])
        name, h = COUNTY_NAME.get(county, county.title()), HEALTH.get(county) or {}
        if h.get("error"):
            out.append((county, f"{name}: could not open the auction site ({h['error'][:120]})"))
        elif h.get("note"):
            out.append((county, f"{name}: {h['note']}"))
        elif h.get("expected", 0) > 0 and not h.get("parsed"):
            out.append((county, f"{name}: the calendar shows {h['expected']} active listing(s) but none could "
                                f"be read. The site's page format may have changed."))
        tried, found = LOOKUPS.get(county, [0, 0])
        if tried >= 3 and not found:
            out.append((county, f"{name}: none of {tried} county property records could be looked up."))
    return out


def closed_statuses(pairs: set[tuple[str, str]]) -> dict[str, str]:
    """Final status (Redeemed, Canceled...) of the listings on the given (county, sale date) days."""
    bases = {county_of(b.split("|")[0]): b.split("|")[0].rstrip("/") for b in BASE_URLS}
    out = {}
    for county, ds in sorted(pairs):
        if county not in bases:
            continue
        try:
            s = requests.Session()
            s.headers.update(HEADERS)
            s.get(bases[county], timeout=30).raise_for_status()
            for r in fetch_results_day(s, bases[county], county, datetime.strptime(ds, DATE_FORMAT).date()):
                out[r["id"]] = r["status"]
        except Exception as e:
            print(f"[warn] status {county} {ds}: {e}", file=sys.stderr)
    return out


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


def place(item: dict) -> tuple[str, str]:
    """(street address, city), falling back to the county record when the listing has none."""
    lu = item.get("land_use") or {}
    addr = item.get("address") or lu.get("site_addr") or ""
    city = (item.get("city") or "").split(",")[0].strip().title() or lu.get("site_city") or lu.get("muni") or ""
    return addr, city


def where(item: dict) -> str:
    addr, city = place(item)
    return ", ".join(x for x in (addr or "No street address", city) if x)


def what(lu: dict, short: bool = False) -> str:
    """'Single Family · 3 bd/2 ba · 1,450 sq ft · built 1962 · lot 7,130 sq ft'"""
    if not lu:
        return ""
    bits = [(lu.get("desc") or "").split(" : ")[0].title()]
    if short:
        return bits[0]
    if lu.get("beds"):
        bits.append(f"{lu['beds']:g} bd" + (f"/{lu['baths']:g} ba" if lu.get("baths") else ""))
    if lu.get("living_sqft"):
        bits.append(f"{lu['living_sqft']:,} sq ft")
    if lu.get("year_built"):
        bits.append(f"built {lu['year_built']}")
    if lu.get("lot_sqft"):
        lot = f"{lu['lot_sqft']:,} sq ft"
        if lu.get("living_sqft"):
            lot = "lot " + lot
        elif lu.get("dims"):
            lot += f" (about {lu['dims'][0]} × {lu['dims'][1]} ft)"
        bits.append(lot)
    return " · ".join(b for b in bits if b)


def detail_lines(item: dict) -> list[str]:
    """The research lines of an alert, in plain text."""
    lu = item.get("land_use") or {}
    out = []
    if lu:
        out.append(what(lu))
        land, total, sqft = lu.get("land_val"), lu.get("total_val"), lu.get("lot_sqft")
        if is_vacant(lu) and land is not None:
            out.append(f"County value: {_k(land)}" + (f" (${land / sqft:,.2f}/sq ft)" if sqft else ""))
        elif total:
            out.append(f"County value: {_k(total)}" + (f" (land {_k(land)})" if land else ""))
    est = item.get("est")
    if est:
        lo, hi, n = price_ratio()
        basis = f"from {n} past sales" if n >= 5 else "a starting assumption until more sales are saved"
        out.append(f"Likely price: {_k(est[0])}–{_k(est[1])} ({lo:.0%}–{hi:.0%} of county value, {basis})")
    c = lu.get("comps")
    if c and c.get("n"):
        out.append(f"Nearby lot sales: {c['n']} within {c['radius_ft'] / 5280:.1f} mi, median ${c['median_ppsf']:,.2f}/sq ft"
                   + (f" (this lot ≈ {_k(c['median_ppsf'] * lu['lot_sqft'])} at that rate)" if lu.get("lot_sqft") else ""))
    facts = []
    if lu.get("zone"):
        desc = re.sub(r"\s+", " ", lu.get("zone_desc") or "").strip().capitalize()
        facts.append(f"Zoning {lu['zone']}" + (f" ({desc[:70]})" if desc else ""))
    if lu.get("flood") and not lu["flood"].upper().startswith(("A", "V")):  # A and V zones get a note instead
        facts.append(f"flood zone {lu['flood']}")
    if lu.get("owner"):
        facts.append(f"owner {lu['owner']}")
    if facts:
        out.append(" · ".join(facts)[0].upper() + " · ".join(facts)[1:])
    if item.get("flags"):
        out.append("⚠️ " + "; ".join(item["flags"]).capitalize())
    n = notes(item)
    if n:
        out.append("Note: " + "; ".join(n))
    return out


def links_of(item: dict) -> list[tuple[str, str]]:
    out = []
    if item.get("link"):
        out.append(("Listing", item["link"]))
    if item.get("day_link"):
        out.append(("Sale day", item["day_link"]))
    out.extend(property_links(item.get("county", "miamidade"), item.get("parcel")))
    lu = item.get("land_use") or {}
    if lu.get("lat"):
        ll = f"{lu['lat']},{lu['lon']}"
        out.append(("Google Maps", f"https://www.google.com/maps/search/?api=1&query={ll}"))
        out.append(("Street View", f"https://www.google.com/maps/@?api=1&map_action=pano&viewpoint={ll}"))
    return out


def _icon(item: dict) -> str:
    return "🌱" if item.get("cat") == "lot" else "🏠"


def _county(item: dict) -> str:
    c = item.get("county", "")
    return COUNTY_NAME.get(c, c.title()).upper()


def fmt(item: dict) -> str:
    """Full alert for one listing, plain text (email and logs)."""
    bid = f"${item['bid']:,.2f}" if item.get("bid") is not None else "n/a"
    lines = [f"{_icon(item)} {item['sale_date']}  {_county(item)}  #{item.get('case', '')}",
             where(item),
             f"Opening bid: {bid}   Parcel: {item.get('parcel', '')}"]
    lines += detail_lines(item)
    lines += [f"{name}: {url}" for name, url in links_of(item)]
    return "\n".join(lines)


def fmt_html(item: dict) -> str:
    """Full alert for one listing (Telegram HTML)."""
    e = html.escape
    bid = f"${item['bid']:,.0f}" if item.get("bid") is not None else "n/a"
    lines = [f"{_icon(item)} <b>{e(item['sale_date'][:5])} · {e(_county(item))} · #{e(item.get('case', ''))}</b>",
             e(where(item)),
             f"Opening bid <b>{bid}</b> · parcel <code>{e(item.get('parcel', ''))}</code>"]
    for ln in detail_lines(item):
        if ln.startswith("Likely price"):
            lines.append(f"<b>{e(ln)}</b>")
        elif ln.startswith(("⚠️", "Note:")):
            lines.append(f"<i>{e(ln)}</i>")
        else:
            lines.append(e(ln))
    ls = links_of(item)
    if ls:
        lines.append(" | ".join(f'<a href="{e(u, quote=True)}">{e(n)}</a>' for n, u in ls))
    return "\n".join(lines)


def _line_parts(item: dict) -> list[str]:
    bid = f"opens {_k(item['bid'])}" if item.get("bid") is not None else ""
    return [p for p in (f"{item['sale_date'][:5]} {_county(item)}", where(item),
                        what(item.get("land_use") or {}, short=True), bid) if p]


def fmt_line(item: dict) -> str:
    """One-line version, for listings that match the search but probably aren't for you."""
    why = f" ({item['why']})" if item.get("why") else ""
    link = next((u for n, u in links_of(item) if n == "Property"), item.get("link", ""))
    return "• " + " · ".join(_line_parts(item)) + why + (f"\n  {link}" if link else "")


def fmt_line_html(item: dict) -> str:
    e = html.escape
    why = f" <i>({e(item['why'])})</i>" if item.get("why") else ""
    ls = [(n, u) for n, u in links_of(item) if n in ("Listing", "Property")]
    links = " " + " ".join(f'<a href="{e(u, quote=True)}">{e(n)}</a>' for n, u in ls) if ls else ""
    return "• " + e(" · ".join(_line_parts(item))) + why + links


def tg(method: str, **payload) -> dict:
    r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/{method}", json=payload, timeout=30)
    data = r.json()
    if not data.get("ok"):
        raise RuntimeError(f"Telegram {method}: {data.get('description')}")
    return data.get("result")


def send_telegram_blocks(blocks: list[str], subject: str, sep: str = "\n\n") -> None:
    """Send HTML blocks as one or more messages (split to stay under Telegram's 4096-char limit)."""
    chunks, cur = [], []
    for b in blocks:
        if cur and sum(len(x) + len(sep) for x in cur) + len(b) > 3300:
            chunks.append(cur); cur = []
        cur.append(b)
    if cur:
        chunks.append(cur)
    for k, ch in enumerate(chunks, 1):
        subj = subject + (f" ({k}/{len(chunks)})" if len(chunks) > 1 else "")
        text = f"<b>{html.escape(subj)}</b>\n\n" + sep.join(ch)
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


def notify(items: list[dict], subject: str, dry_run: bool, compact: bool = False) -> None:
    """Send one alert message: full cards, or one line per listing when compact."""
    body = ("\n" if compact else "\n\n").join((fmt_line if compact else fmt)(i) for i in items)
    send_message(subject, body, [(fmt_line_html if compact else fmt_html)(i) for i in items], dry_run,
                 sep="\n" if compact else "\n\n")


def send_message(subject: str, text: str, html_blocks: list[str], dry_run: bool, sep: str = "\n\n") -> None:
    if dry_run or not (TELEGRAM_TOKEN or SMTP_USER):
        print(f"--- {subject} ---\n{text}\n")
        return
    if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID:
        send_telegram_blocks(html_blocks, subject, sep)
    if SMTP_USER and SMTP_PASS:
        send_email(subject, text)


# ----------------------------------------------------------------------------
def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sample", help="parse a saved JSON response instead of fetching")
    ap.add_argument("--dry-run", action="store_true", help="print alerts instead of sending")
    ap.add_argument("--folio", help="test the land-use lookup for one folio and exit")
    ap.add_argument("--weekly", action="store_true", help="send the weekly results report")
    ap.add_argument("--results", action="store_true",
                    help="collect today's sale results into results.csv (run after the sales close)")
    ap.add_argument("--since", help="with --results: collect every sale day from MM/DD/YYYY to today "
                                    f"(default: the last {RESULTS_DAYS_BACK} days)")
    args = ap.parse_args()

    if args.weekly:
        send_weekly(date.today(), args.dry_run)
        return

    if args.results:
        end = date.today()
        start = (datetime.strptime(args.since, "%m/%d/%Y").date() if args.since
                 else end - timedelta(days=RESULTS_DAYS_BACK))
        collect_results(start, end, args.dry_run)
        return

    if args.folio:
        s = requests.Session()
        s.headers.update(HEADERS)
        a = lookup_land_use(s, re.sub(r"\D", "", args.folio))
        print(json.dumps(a, indent=2, default=str) if a else "not found")
        return

    if args.sample:
        items = parse_response(Path(args.sample).read_text(), "sample")
        for i in items:
            print(json.dumps({k: v for k, v in i.items() if k != "raw"}), "KEEP" if keep(i) else "skip")
        return

    fetched = fetch_all()
    items = [i for i in fetched if keep(i)]
    present = {i["id"] for i in fetched}
    seen = load_seen()
    today = date.today()

    # 1) New listings (plus ones saved by an older version of this script, which are
    #    re-checked once with the current rules): look up the parcel, decide if it matches.
    new = [i for i in items if (seen.get(i["id"]) or {}).get("v") != STATE_VERSION]
    enrich(new)
    for i in new:
        i["cat"] = category(i)
    matched = sorted((i for i in new if i["cat"]), key=lambda i: datetime.strptime(i["sale_date"], DATE_FORMAT))
    research(matched)  # zoning, flood zone, map location, nearby sales: only for matches
    for i in matched:
        grade(i)
    for i in new:
        old = seen.get(i["id"]) or {}
        d = days_until(i["sale_date"], today)
        seen[i["id"]] = {
            "v": STATE_VERSION,
            "sale_date": i["sale_date"],
            "ok": bool(i["cat"]),
            "cat": i["cat"],
            "tier": i.get("tier"), "flags": i.get("flags", []), "est": i.get("est"), "why": i.get("why", ""),
            "land_use": i.get("land_use"),
            # a listing first found inside a reminder window already got the "new" alert
            "reminded": old["reminded"] if old.get("ok") and "reminded" in old
            else [r for r in REMIND_DAYS if d is not None and d <= r],
        }

    # 2) Keep the details of every listing that is still up for sale current
    new_ids = {i["id"] for i in new}
    for i in items:
        st = seen[i["id"]]
        st.update({"sale_date": i["sale_date"],  # the sale may have been rescheduled
                   "bid": i.get("bid"), "case": i.get("case"), "parcel": i.get("parcel"), "link": i.get("link"),
                   "address": i.get("address") or st.get("address"), "city": i.get("city") or st.get("city"),
                   "last_seen": today.isoformat()})
        st.pop("gone", None)

    # 3) Reminders: good matches still up for sale, N days before the sale
    reminders: dict[int, list[dict]] = {r: [] for r in REMIND_DAYS}
    for i in items:
        st = seen[i["id"]]
        if i["id"] in new_ids or not st.get("ok") or (st.get("tier") != "A" and not REMIND_ALL):
            continue
        i.update({k: st.get(k) for k in ("land_use", "cat", "tier", "flags", "est", "why")})
        d = days_until(i["sale_date"], today)
        if d is None:
            continue
        # smallest window reached that hasn't been sent (a missed run still gets caught up)
        due = [r for r in REMIND_DAYS if d <= r and r not in st["reminded"]]
        if due:
            reminders[min(due)].append(i)
            st["reminded"] = sorted(set(st["reminded"]) | set(due), reverse=True)

    # 4) Good matches that left the list before their sale (redeemed, canceled...)
    problems = health_problems()
    sick = {c for c, _ in problems}
    gone = []
    for k, st in seen.items():
        if k.startswith("_") or k in present or not st.get("ok") or st.get("tier") != "A" or st.get("gone"):
            continue
        d = days_until(st.get("sale_date", ""), today)
        if d is not None and d >= 1 and k.split(":")[0] not in sick:
            gone.append((k, st))
    if gone:
        status = closed_statuses({(k.split(":")[0], st["sale_date"]) for k, st in gone})
        for k, st in gone:
            st["gone"] = status.get(k, "No longer listed")

    a_new = [i for i in matched if i["tier"] == "A"]
    b_new = [i for i in matched if i["tier"] != "A"]
    print(f"{len(items)} listings, {len(new)} new, {len(a_new)} worth a look, {len(b_new)} other matches, "
          + ", ".join(f"{len(v)} reminders at {k}d" for k, v in reminders.items()) + f", {len(gone)} gone")

    plural = lambda n, one, many: one if n == 1 else many
    lots = [i for i in a_new if i["cat"] == "lot"]
    props = [i for i in a_new if i["cat"] != "lot"]
    if lots:
        notify(lots, f"🌱 {len(lots)} new vacant {plural(len(lots), 'lot', 'lots')} worth a look", args.dry_run)
    if props:
        notify(props, f"🏠 {len(props)} new {plural(len(props), 'property', 'properties')} that could sell "
                      f"under ${PROPERTY_MAX_BID:,.0f}", args.dry_run)
    if b_new:
        notify(b_new, f"ℹ️ {len(b_new)} more new {plural(len(b_new), 'listing', 'listings')} that match your "
                      f"search but probably aren't for you", args.dry_run, compact=True)
    for r, group in sorted(reminders.items(), reverse=True):
        if group:
            when = "tomorrow" if r == 1 else f"in {r} days"
            notify(group, f"⏰ {len(group)} {plural(len(group), 'auction', 'auctions')} {when}", args.dry_run)
    if gone:
        rows = [{**st, "id": k, "county": k.split(":")[0], "why": GONE_WHY.get(st["gone"].split()[0].upper(), st["gone"])}
                for k, st in gone]
        send_message(f"❌ {len(rows)} {plural(len(rows), 'listing', 'listings')} you were watching "
                     f"{plural(len(rows), 'is', 'are')} off the list",
                     "\n".join(fmt_line(r) for r in rows), [fmt_line_html(r) for r in rows], args.dry_run, sep="\n")
    if problems and (seen.get("_health") or {}).get("date") != today.isoformat():
        text = "\n".join(f"• {msg}" for _, msg in problems)
        send_message("⚠️ Auction watcher needs attention", text + "\n\nAlerts may be incomplete until this is fixed.",
                     [html.escape(text), "Alerts may be incomplete until this is fixed."], args.dry_run)
        seen["_health"] = {"date": today.isoformat(), "problems": [m for _, m in problems]}

    if not args.dry_run:
        save_seen(seen)

if __name__ == "__main__":
    main()
