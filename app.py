from flask import (
    Flask, request, redirect, url_for, session, flash,
    render_template_string, send_file, abort, jsonify
)
import sqlite3
import os
import re
import io
import csv
import html
import math
import secrets
import warnings
import time
import json
import urllib.request
import urllib.parse
from datetime import datetime, date, timedelta
from functools import wraps
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename

# Optional PDF export
PDF_ENABLED = True
try:
    from reportlab.lib.pagesizes import letter
    from reportlab.pdfgen import canvas
except Exception:
    PDF_ENABLED = False

# ----------------------------------------------------------
# STRIPE — read env vars immediately after imports, before
# anything else runs, so Render vars are guaranteed available.
# To switch to live: update the four env vars. No code changes.
# ----------------------------------------------------------
STRIPE_SECRET_KEY     = os.getenv("STRIPE_SECRET_KEY")
STRIPE_PRICE_STARTER  = os.getenv("STRIPE_PRICE_STARTER")
STRIPE_PRICE_PRO      = os.getenv("STRIPE_PRICE_PRO")
STRIPE_WEBHOOK_SECRET = os.getenv("STRIPE_WEBHOOK_SECRET")

STRIPE_ENABLED = True
try:
    import stripe
    stripe.api_key = STRIPE_SECRET_KEY
except ImportError:
    STRIPE_ENABLED = False

stripe_configured = all([
    STRIPE_SECRET_KEY,
    STRIPE_PRICE_STARTER,
    STRIPE_PRICE_PRO,
])

STRIPE_PRICE_IDS = {
    "starter": STRIPE_PRICE_STARTER or "",
    "pro":     STRIPE_PRICE_PRO     or "",
}

STRIPE_PLAN_LIMITS       = {"starter": 10, "pro": 30}
STRIPE_PURCHASABLE_PLANS = {"starter", "pro"}

# ----------------------------------------------------------
app = Flask(__name__)
_secret_key = os.environ.get("SECRET_KEY", "")
if not _secret_key:
    warnings.warn(
        "SECRET_KEY env var not set — using an insecure default. Set SECRET_KEY before deploying.",
        stacklevel=2,
    )
    _secret_key = "haultra-super-secret-key-change-me"
app.secret_key = _secret_key

# DATABASE_PATH must be set explicitly — no fallbacks, no hidden paths.
_db_env = os.environ.get("DATABASE_PATH", "").strip()
_on_render = bool(os.environ.get("RENDER", ""))
print(f"DATABASE_PATH={_db_env!r}  on_render={_on_render}", flush=True)
if not _db_env:
    raise RuntimeError("DATABASE_PATH is not set. Add it as an environment variable.")
DATABASE = _db_env
print("Using database:", DATABASE, flush=True)
UPLOAD_FOLDER = os.environ.get("UPLOAD_FOLDER", os.path.join("static", "uploads"))
ALLOWED_EXTENSIONS = {"png", "jpg", "jpeg", "webp", "pdf"}
os.makedirs(UPLOAD_FOLDER, exist_ok=True)
app.config["UPLOAD_FOLDER"] = UPLOAD_FOLDER
app.config["MAX_CONTENT_LENGTH"] = 32 * 1024 * 1024  # 32 MB upload limit


# =========================================================
# HELPERS
# =========================================================
def e(value):
    return html.escape("" if value is None else str(value))


try:
    from zoneinfo import ZoneInfo as _ZoneInfo
    _EASTERN = _ZoneInfo("America/New_York")
except Exception:
    _EASTERN = None

def now_ts():
    if _EASTERN:
        return datetime.now(_EASTERN).strftime("%Y-%m-%d %H:%M:%S")
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def today_str():
    return date.today().strftime("%Y-%m-%d")


def _fmt_12h(ts):
    """
    Convert a stored timestamp (YYYY-MM-DD HH:MM:SS) or bare HH:MM string
    to 12-hour AM/PM format with no leading zero on the hour.

    Examples:
        "2026-04-10 00:05:00"  →  "12:05 AM"
        "2026-04-10 11:20:00"  →  "11:20 AM"
        "2026-04-10 13:05:00"  →  "1:05 PM"
        "2026-04-10 23:36:00"  →  "11:36 PM"
        "12:00"                →  "12:00 PM"
    Returns "" on any failure so callers can substitute a dash.
    """
    if not ts:
        return ""
    try:
        hhmm = str(ts)[11:16]   # slice "HH:MM" from full timestamp
        if ":" not in hhmm:     # already bare "HH:MM" with no date prefix
            hhmm = str(ts)[:5]
        h_str, m_str = hhmm.split(":")
        h = int(h_str)
        meridian = "AM" if h < 12 else "PM"
        if h == 0:
            h = 12
        elif h > 12:
            h -= 12
        return "%d:%s %s" % (h, m_str, meridian)
    except Exception:
        return ""


def allowed_file(filename):
    return "." in filename and filename.rsplit(".", 1)[1].lower() in ALLOWED_EXTENSIONS


# ── Abbreviation expansion ───────────────────────────────────────────────────
_ABBREV_MAP = {
    "dom":  "Dominion",
    "wat":  "Waterway",
    "vb":   "Virginia Beach",
    "ches": "Chesapeake",
    "norf": "Norfolk",
}

def expand_abbrev(value):
    """Expand a known abbreviation only when the whole trimmed value matches (case-insensitive).
    Full values are returned unchanged — 'Virginia Beach' stays 'Virginia Beach'.
    None / empty strings are returned as-is.
    """
    if not value:
        return value
    stripped = value.strip()
    expanded = _ABBREV_MAP.get(stripped.lower())
    return expanded if expanded else stripped


# ── Route text paste parser ───────────────────────────────────────────────────
# Ordered most-specific → least-specific; first match wins.
_ACTION_PATTERNS = [
    # Most specific multi-word variants first
    (re.compile(r'\b(?:pickup\s*(?:and|&)\s*return|p\s*[&/]\s*r)\b',    re.I), "Pickup and Return"),
    (re.compile(r'\b(?:pull\s*(?:and|&)\s*return)\b',                    re.I), "Pickup and Return"),
    (re.compile(r'\b(?:dump\s*(?:and|&)\s*return)\b',                    re.I), "Pickup and Return"),
    (re.compile(r'\b(?:p\s+and\s+r)\b',                                  re.I), "Pickup and Return"),
    (re.compile(r'\bpr\b',                                                re.I), "Pickup and Return"),
    (re.compile(r'\bswap\b',                                              re.I), "Swap"),
    # Relocate checked before bare "move" so "move can" wins
    (re.compile(r'\b(?:relocate|reloc|move\s+can)\b',                    re.I), "Relocate"),
    (re.compile(r'\bpull\b',                                              re.I), "Pull"),
    (re.compile(r'\b(?:pick\s+up|pickup)\b',                              re.I), "Pull"),
    (re.compile(r'\bmove\b',                                              re.I), "Move"),
    (re.compile(r'\b(?:drop\s*off)\b',                                    re.I), "Delivery"),
    (re.compile(r'\b(?:delivery|deliver|del)\b',                          re.I), "Delivery"),
    # Bare single-letter tokens (must be at word boundary, not inside words)
    (re.compile(r'(?:(?<=\s)|^)p(?=\s|$)',                                re.I), "Pull"),
    (re.compile(r'(?:(?<=\s)|^)d(?=\s|$)',                                re.I), "Delivery"),
    (re.compile(r'(?:(?<=\s)|^)r(?=\s|$)',                                re.I), "Relocate"),
]
_CONTAINER_RE = re.compile(r'\b(\d+)\s*(?:yds?|yards?)\b', re.I)
# Ticket / reference number: "TKT#1234", "#1234", "ticket 55", "ref 999", "order 77"
_TICKET_RE = re.compile(
    r'\b(?:tkt|ticket|ref|reference|ord|order)\s*#?\s*(\w+)\b'
    r'|#(\d{3,})',
    re.I,
)
# Two-word dump phrases — checked BEFORE the single-token loop in _parse_one_line
_TWO_WORD_DUMP_MAP = {
    "sb cox": "SB Cox",
}
_PARSE_DUMP_MAP = {
    "dom":      "Dominion",
    "dominion": "Dominion",
    "wat":      "Waterway",
    "waterway": "Waterway",
    "bay":      "Bay",
    "spsa":     "SPSA Landfill",
    "holland":  "Holland",
    "spivey":   "Spivey",
    "cox":      "SB Cox",
    "sb":       "SB Cox",
    "united":   "United",
    "sykes":    "Sykes",
}
_PARSE_CITY_MAP = {
    "vb":           "Virginia Beach",
    "ches":         "Chesapeake",
    "norf":         "Norfolk",
    "norfolk":      "Norfolk",
    "chesapeake":   "Chesapeake",
    "smithfield":   "Smithfield",
    "suffolk":      "Suffolk",
    "suff":         "Suffolk",
    "hampton":      "Hampton",
    "nn":           "Newport News",
    "portsmouth":   "Portsmouth",
    "ports":        "Portsmouth",
    "port":         "Portsmouth",
    "prt":          "Portsmouth",
    "williamsburg": "Williamsburg",
    "hamp":         "Hampton",
}


def parse_route_text(text, conn, company_id):
    """Parse pasted multi-line route text. Each non-blank line → one stop attempt.
    Returns a list of stop dicts with confidence scores.
    Does NOT write to the database.
    """
    results = []
    for raw in text.splitlines():
        raw = raw.strip()
        if not raw:
            continue
        parsed = _parse_one_line(raw, conn, company_id)
        if parsed:
            results.append(parsed)
    return results


def _parse_pipe_line(raw, conn, company_id):
    """
    Parse a pipe-delimited line: Customer | Address | Service Type | Can Size
    Fields are classified by content — order does not matter.
    """
    parts = [p.strip() for p in raw.split("|") if p.strip()]
    result = {
        "original_line":    raw,
        "customer_name":    "",
        "address":          "",
        "city":             "",
        "state":            "",
        "zip_code":         "",
        "action":           "",
        "container_size":   "",
        "dump_location":    "",
        "notes":            "",
        "confidence":       20,
        "confidence_label": "low",
        "matched_saved":    False,
    }
    unclassified = []
    for part in parts:
        # Container size?
        size_m = _CONTAINER_RE.search(part)
        if size_m and not result["container_size"]:
            result["container_size"] = size_m.group(1) + "yd"
            result["confidence"] += 10
            continue
        # Action keyword?
        found_action = ""
        for pat, canonical in _ACTION_PATTERNS:
            if pat.search(part):
                found_action = canonical
                break
        if found_action and not result["action"]:
            result["action"] = found_action
            result["confidence"] += 20
            continue
        # Two-word dump phrase?
        found_dump = ""
        for phrase, fullname in _TWO_WORD_DUMP_MAP.items():
            if re.search(r'(?:^|\s)' + re.escape(phrase) + r'(?:\s|$)', part, re.I):
                found_dump = fullname
                break
        if not found_dump:
            for token, fullname in _PARSE_DUMP_MAP.items():
                tok_pat = re.compile(r'(?:(?<=\s)|^)' + re.escape(token) + r'(?=\s|$)', re.I)
                if tok_pat.search(part) and len(part.split()) <= 2:
                    found_dump = fullname
                    break
        if found_dump and not result["dump_location"]:
            result["dump_location"] = found_dump
            result["confidence"] += 10
            continue
        # Address? (starts with a house number)
        if re.match(r'^\d+\s+\w', part) and not result["address"]:
            from_structured = _parse_structured_addr(part)
            result["address"]  = from_structured[0] or part
            result["city"]     = result["city"]     or from_structured[1]
            result["state"]    = result["state"]    or from_structured[2]
            result["zip_code"] = result["zip_code"] or from_structured[3]
            result["confidence"] += 15
            continue
        # City abbreviation?
        found_city = ""
        part_lo = part.strip().lower()
        if part_lo in _PARSE_CITY_MAP:
            found_city = _PARSE_CITY_MAP[part_lo]
        if found_city and not result["city"]:
            result["city"]  = found_city
            result["state"] = "VA"
            result["confidence"] += 5
            continue
        # Customer name (first unclassified segment)
        if not result["customer_name"]:
            result["customer_name"] = part
            result["confidence"] += 10
        else:
            unclassified.append(part)
    if unclassified:
        result["notes"] = "; ".join(unclassified)
    result["confidence"] = min(100, result["confidence"])
    result["confidence_label"] = (
        "high" if result["confidence"] >= 75 else
        ("medium" if result["confidence"] >= 45 else "low")
    )
    return result


def _parse_one_line(raw, conn, company_id):
    """Parse one text line into a structured stop dict. Returns None for blank lines."""
    work = raw.strip()
    if not work:
        return None

    # ── Pipe-delimited format: Customer | Address | Service | Size ───────────
    if raw.count("|") >= 2:
        return _parse_pipe_line(raw, conn, company_id)

    # ── Relocate from/to format ───────────────────────────────────────────────
    rel = _parse_relocate_line(work, order_num=1)
    if rel:
        rel["original_line"] = raw
        return rel

    conf = 10
    conf_reasons = []

    # ── normalize separators: " - ", "|", "\" → space; "/" only when not between digits
    work = re.sub(r'\s*[|\\]\s*', ' ', work)
    work = re.sub(r'(?<!\d)/(?!\d)', ' ', work)
    work = re.sub(r'\s+-\s+', ' ', work)
    work = re.sub(r'\s+', ' ', work).strip()

    # ── 0. extract ticket / reference number ─────────────────────────────────
    ticket_number = ""
    tm = _TICKET_RE.search(work)
    if tm:
        ticket_number = (tm.group(1) or tm.group(2) or "").strip()
        work = re.sub(r'\s+', ' ', work[:tm.start()] + " " + work[tm.end():]).strip()
        conf += 5
        conf_reasons.append("ticket")

    # ── 1. extract action ────────────────────────────────────────────────────
    action = ""
    for pat, canonical in _ACTION_PATTERNS:
        m = pat.search(work)
        if m:
            action = canonical
            work = (work[:m.start()] + " " + work[m.end():])
            work = re.sub(r'\s+', ' ', work).strip()
            conf += 20
            conf_reasons.append("action")
            break

    # ── 2. extract container size (Nyd / N yd / N yard) ─────────────────────
    container_size = ""
    m = _CONTAINER_RE.search(work)
    if m:
        container_size = m.group(1) + "yd"
        work = work[:m.start()] + " " + work[m.end():]
        work = re.sub(r'\s+', ' ', work).strip()
        conf += 10
        conf_reasons.append("container")

    # ── 3. extract dump location ─────────────────────────────────────────────
    # Check two-word phrases first (e.g. "sb cox") before single-token loop
    dump_location = ""
    for phrase, fullname in _TWO_WORD_DUMP_MAP.items():
        pat = re.compile(r'(?:(?<=\s)|^)' + re.escape(phrase) + r'(?=\s|$)', re.I)
        m = pat.search(work)
        if m:
            dump_location = fullname
            work = work[:m.start()] + " " + work[m.end():]
            work = re.sub(r'\s+', ' ', work).strip()
            conf += 10
            conf_reasons.append("dump")
            break
    if not dump_location:
        for token, fullname in _PARSE_DUMP_MAP.items():
            pat = re.compile(r'(?:(?<=\s)|^)' + re.escape(token) + r'(?=\s|$)', re.I)
            m = pat.search(work)
            if m:
                dump_location = fullname
                work = work[:m.start()] + " " + work[m.end():]
                work = re.sub(r'\s+', ' ', work).strip()
                conf += 10
                conf_reasons.append("dump")
                break

    # ── 4. extract city abbreviation/name ────────────────────────────────────
    city = ""
    for token, fullname in _PARSE_CITY_MAP.items():
        pat = re.compile(r'(?:(?<=\s)|^)' + re.escape(token) + r'(?=\s|$)', re.I)
        m = pat.search(work)
        if m:
            city = fullname
            work = work[:m.start()] + " " + work[m.end():]
            work = re.sub(r'\s+', ' ', work).strip()
            conf += 5
            conf_reasons.append("city")
            break
    state = "VA" if city else ""

    # ── 5. split remaining into customer name + address ──────────────────────
    work = work.strip()
    customer_name = ""
    address = ""
    notes   = ""

    if "," in work:
        # "Customer Name, 123 Street" explicit CSV split
        parts = work.split(",", 1)
        customer_name = parts[0].strip()
        address = parts[1].strip()
        conf += 15
        conf_reasons.append("csv-split")
    else:
        # Find first occurrence of a street number (digit(s) + space + word)
        m = re.search(r'(?:(?<=\s)|^)(\d+\s+\w)', work)
        if m:
            pos = m.start() if work[m.start()].isdigit() else m.start() + 1
            customer_name = work[:pos].strip()
            address = work[pos:].strip()
            conf += 10
            conf_reasons.append("addr-num")
            # If address contains trailing words past a street suffix, split to notes
            sfx_m = None
            for sfx_hit in _STREET_SFX_RE.finditer(address):
                sfx_m = sfx_hit
            if sfx_m and sfx_m.end() < len(address):
                trailing = address[sfx_m.end():].strip()
                address  = address[:sfx_m.end()].strip()
                # Only promote to notes if it looks like free text, not a unit/apt
                if trailing and not re.match(r'^(?:apt|unit|ste|#)\s*\w+', trailing, re.I):
                    notes = trailing
        else:
            customer_name = work
            conf += 5
            conf_reasons.append("name-only")

    # ── 6. saved addresses lookup ─────────────────────────────────────────────
    zip_code = ""
    matched_saved = False
    if conn and company_id:
        try:
            saved = None
            if customer_name:
                saved = conn.execute(
                    """SELECT * FROM saved_addresses
                       WHERE company_id=? AND LOWER(customer_name) LIKE ?
                       ORDER BY times_used DESC LIMIT 1""",
                    (company_id, "%" + customer_name.lower() + "%")
                ).fetchone()
            if not saved and address:
                saved = conn.execute(
                    """SELECT * FROM saved_addresses
                       WHERE company_id=? AND LOWER(address) LIKE ?
                       ORDER BY times_used DESC LIMIT 1""",
                    (company_id, "%" + address.lower() + "%")
                ).fetchone()
            if saved:
                matched_saved = True
                conf += 20
                conf_reasons.append("saved")
                if not city:
                    city  = saved["city"]  or ""
                    state = saved["state"] or ""
                zip_code = saved["zip"] or ""
                if not customer_name and saved["customer_name"]:
                    customer_name = saved["customer_name"]
                if not address and saved["address"]:
                    address = saved["address"]
                if not action and saved["default_action"]:
                    action = saved["default_action"]
                    conf_reasons.append("saved-action")
                if not container_size and saved["default_container_size"]:
                    container_size = saved["default_container_size"]
                    conf_reasons.append("saved-container")
                if not dump_location and saved["default_dump_location"]:
                    dump_location = saved["default_dump_location"]
                    conf_reasons.append("saved-dump")
        except Exception:
            pass

    conf = min(100, conf)
    conf_label = "high" if conf >= 75 else ("medium" if conf >= 45 else "low")

    return {
        "original_line":         raw,
        "customer_name":         customer_name,
        "address":               address,
        "city":                  city,
        "state":                 state,
        "zip_code":              zip_code,
        "action":                action,
        "container_size":        container_size,
        "dump_location":         dump_location,
        "notes":                 notes,
        "ticket_number":         ticket_number,
        "reference_number":      "",
        "relocate_from_address": "",
        "relocate_to_address":   "",
        "confidence":            conf,
        "confidence_label":      conf_label,
        "matched_saved":         matched_saved,
        "conf_reasons":          conf_reasons,
    }


def get_db():
    db_dir = os.path.dirname(DATABASE)
    if db_dir:
        os.makedirs(db_dir, exist_ok=True)
    conn = sqlite3.connect(DATABASE)
    conn.row_factory = sqlite3.Row
    return conn


def get_csrf_token():
    if "_csrf_token" not in session:
        session["_csrf_token"] = secrets.token_hex(32)
    return session["_csrf_token"]


# Endpoints that legitimately receive POST from external servers (no session/CSRF)
_CSRF_EXEMPT_ENDPOINTS = {"stripe_webhook"}

@app.before_request
def csrf_protect():
    if request.method == "POST":
        if request.endpoint in _CSRF_EXEMPT_ENDPOINTS:
            return
        token = session.get("_csrf_token")
        # Support form data, JSON body, or explicit header
        if request.is_json:
            form_token = (request.get_json(silent=True) or {}).get("_csrf_token") \
                         or request.headers.get("X-CSRF-Token")
        else:
            form_token = request.form.get("_csrf_token")
        if not token or token != form_token:
            abort(403)


# Routes that are always accessible regardless of subscription status
_SUBSCRIPTION_EXEMPT = {
    "login", "logout", "company_register", "static",
    "subscription_blocked", "subscription_success", "billing",
    "company_subscription", "stripe_webhook",
    "privacy_policy", "terms_of_service",
}

@app.before_request
def subscription_enforce():
    """
    Auto-suspend expired trials, then block suspended/cancelled accounts.
    Runs on every request after login.
    """
    if request.endpoint in _SUBSCRIPTION_EXEMPT or not session.get("company_id"):
        return

    company_id = session["company_id"]
    conn = get_db()
    co = conn.execute(
        "SELECT subscription_plan, subscription_status, trial_ends_at FROM companies WHERE id=?",
        (company_id,)
    ).fetchone()
    conn.close()

    if not co:
        return

    # Auto-expire trial if past end date
    if (co["subscription_plan"] == "trial"
            and co["subscription_status"] == "active"
            and co["trial_ends_at"]):
        try:
            ends = datetime.strptime(co["trial_ends_at"], "%Y-%m-%d %H:%M:%S")
        except ValueError:
            ends = None
        if ends and datetime.now() > ends:
            _conn = get_db()
            _conn.execute(
                "UPDATE companies SET subscription_status='suspended' WHERE id=?",
                (company_id,)
            )
            _conn.execute(
                """INSERT INTO subscriptions (company_id, plan, status, started_at, notes, created_at)
                   VALUES (?,?,?,?,?,?)""",
                (company_id, "trial", "suspended", now_ts(),
                 "Auto-suspended: trial period expired", now_ts())
            )
            _conn.commit()
            _conn.close()
            co = {"subscription_status": "suspended", "subscription_plan": "trial"}

    if co["subscription_status"] in ("suspended", "cancelled"):
        # Allow boss to view subscription page so they can act
        if request.endpoint in ("company_subscription", "company_settings"):
            return
        return redirect(url_for("subscription_blocked"))


def col_exists(conn, table_name, column_name):
    rows = conn.execute(f"PRAGMA table_info({table_name})").fetchall()
    return any(r[1] == column_name for r in rows)


def safe_add_column(conn, table_name, ddl):
    try:
        conn.execute(f"ALTER TABLE {table_name} ADD COLUMN {ddl}")
        conn.commit()
    except sqlite3.OperationalError:
        pass


def _haversine_mi(lat1, lon1, lat2, lon2):
    """Straight-line distance in miles between two lat/lng points."""
    R = 3958.8
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    a = (math.sin(dlat / 2) ** 2
         + math.cos(math.radians(lat1)) * math.cos(math.radians(lat2))
         * math.sin(dlon / 2) ** 2)
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))


def _geocode_server(address):
    """Geocode an address with Nominatim. Returns (lat, lng) or None."""
    url = ("https://nominatim.openstreetmap.org/search?format=json&limit=1&q="
           + urllib.parse.quote_plus(address))
    req = urllib.request.Request(url, headers={
        "User-Agent": "HaultraAISystems/1.0 route-optimizer",
        "Accept-Language": "en",
    })
    try:
        with urllib.request.urlopen(req, timeout=6) as resp:
            data = json.loads(resp.read().decode())
            if data:
                return float(data[0]["lat"]), float(data[0]["lon"])
    except Exception:
        pass
    return None


# Actions that require a dump trip after the customer stop
_DUMP_ACTIONS = frozenset({"pickup and return", "pull", "swap"})
# Notes keywords that pin a stop to the very beginning of the route
_FIRST_KEYWORDS = ("do this first", "first stop", "start here", "start with this")
# Notes keywords that pin a stop to the very end (already used in optimize_route)
_EOD_KEYWORDS_SET = frozenset(("end of day", "return to yard", "take to yard", "back to yard", "eod"))


def _nearest_neighbor(stops_coords, origin=None):
    """
    Simple greedy nearest-neighbor (kept for internal reuse).
    stops_coords: list of (stop_id, lat, lng)
    Returns stop_ids in optimized order.
    """
    if not stops_coords:
        return []
    remaining = list(stops_coords)
    visited   = []
    if origin:
        first = min(remaining,
                    key=lambda s: _haversine_mi(origin[0], origin[1], s[1], s[2]))
    else:
        first = remaining[0]
    visited.append(first)
    remaining.remove(first)
    while remaining:
        last = visited[-1]
        nearest = min(remaining,
                      key=lambda s: _haversine_mi(last[1], last[2], s[1], s[2]))
        visited.append(nearest)
        remaining.remove(nearest)
    return [s[0] for s in visited]


def _can_flow_valid(action_lower, can_state):
    """Return True if a stop with this action is valid given the current simulated can state.

    Rules (physical truck constraints):
      PR       — valid in ANY can state; mode is determined at runtime:
                   empty_can → swap mode (bring empty, take full, dump)
                   no_can    → return-same-can mode (take full, dump, return empty)
      Delivery — needs an empty can on the truck to drop off → requires empty_can
      Pull     — truck must be empty to pick up a can       → requires no_can
      Dump/unknown — always valid (no can-state constraint)
    """
    is_delivery = "delivery" in action_lower
    is_pull     = "pull" in action_lower and "return" not in action_lower
    if is_delivery:
        return can_state == "empty_can"
    if is_pull:
        return can_state == "no_can"
    return True  # PR (either mode), dump run, or unrecognised — no constraint


def _next_can_state(action_lower, can_state):
    """
    Simulate the truck can-state after completing a stop (including its dump run).

    Pull (return-same-can):
      no_can → pick up full → dump → return empty to customer → no_can

    PR swap mode (truck arrives with empty_can):
      empty_can → drop off empty → pick up full → dump → truck now holds empty → empty_can

    PR return-same-can mode (truck arrives with no_can):
      no_can → pick up full → dump → return empty to customer → no_can

    Delivery:
      empty_can → drop off empty → no_can (truck is empty)
    """
    is_pr = (
        "pickup and return" in action_lower
        or ("swap" in action_lower and "pull" not in action_lower)
    )
    is_delivery = "delivery" in action_lower
    is_pull     = "pull" in action_lower and "return" not in action_lower

    if is_delivery:
        return "no_can"   # left the can at the site; truck is empty

    if is_pull:
        # Truck returns same dumped-empty can to customer — truck leaves empty
        return "no_can"

    if is_pr:
        if can_state == "empty_can":
            # Swap mode: dropped off empty, dumped full → truck holds empty after dump
            return "empty_can"
        else:
            # Return-same-can mode: dumped full, returned empty to customer → truck empty
            return "no_can"

    return can_state   # dump run or unrecognised — no change


def _stop_trip_cost(pos, s):
    """
    True routing cost from current position to a stop, including the dump leg
    when the stop requires one.

    For Delivery stops (is_dump=False) or stops with no dump coords:
        cost = dist(current → customer)

    For Pull / PR stops with a known dump location:
        cost = dist(current → customer) + dist(customer → dump)

    This prevents the greedy selector from choosing a Pull whose dump site is
    far off-route simply because the customer address is nearby.
    """
    cost = _haversine_mi(pos[0], pos[1], s["lat"], s["lng"])
    if s["is_dump"] and s["dump_lat"] is not None:
        cost += _haversine_mi(s["lat"], s["lng"], s["dump_lat"], s["dump_lng"])
    return cost


def _dump_aware_order(stops_data, origin=None, action_map=None, starts_with_can=False):
    """
    Dump-aware greedy nearest-neighbor with optional can-flow constraints.

    stops_data: list of dicts
        {
            "id":       stop_id (int),
            "lat":      float,
            "lng":      float,
            "is_dump":  bool,        # True for PR / Pull / Swap stops
            "dump_lat": float|None,  # dump site coords if known
            "dump_lng": float|None,
        }
    origin:          (lat, lng) or None — yard / base start position.
    action_map:      dict of {stop_id: action_string} — when supplied, only
                     physically valid stops are candidates at each step.
    starts_with_can: whether the truck starts the day with an empty can loaded.

    Logic
    -----
    Current position starts at origin (yard) or first stop.
    At each step we pick the nearest unvisited stop that is VALID for the
    current simulated can state.  If no valid stop exists the algorithm is
    stuck; remaining stops are appended in their original dispatcher order and
    a constrained=True flag is returned so the caller can warn the boss.

    Returns (list_of_stop_ids_in_order, constrained: bool).
    """
    if not stops_data:
        return [], False

    remaining  = list(stops_data)   # preserves original dispatcher order
    ordered    = []
    constrained = False
    can_state  = "empty_can" if starts_with_can else "no_can"

    if origin:
        pos = origin
    else:
        pos = (stops_data[0]["lat"], stops_data[0]["lng"])

    while remaining:
        # When action_map is provided, filter to can-flow-valid candidates
        if action_map:
            valid = [
                s for s in remaining
                if _can_flow_valid(
                    (action_map.get(s["id"]) or "").lower().strip(),
                    can_state,
                )
            ]
            if not valid:
                # Stuck — no valid next stop; preserve original order for remainder
                constrained = True
                ordered.extend(remaining)
                remaining = []
                break
        else:
            valid = remaining

        # Score by full trip leg: customer distance + dump-run distance when applicable.
        # Delivery stops score by customer distance only (no dump leg).
        best = min(valid, key=lambda s: _stop_trip_cost(pos, s))
        ordered.append(best)
        remaining.remove(best)

        # Advance position to dump exit (truck ends at dump, not at customer)
        if best["is_dump"] and best["dump_lat"] is not None:
            pos = (best["dump_lat"], best["dump_lng"])
        else:
            pos = (best["lat"], best["lng"])

        # Simulate can state after this stop
        if action_map:
            action_lower = (action_map.get(best["id"]) or "").lower().strip()
            can_state = _next_can_state(action_lower, can_state)

    return [s["id"] for s in ordered], constrained


def compute_can_flow(conn, route_id, starts_with_can=False):
    """
    Walk ordered stops, stamp can_state_before, and derive swap_with_prev_pull.

    States
    ------
    "no_can"    — truck is empty, no container loaded
    "empty_can" — truck carries a clean empty container

    (Loaded-can is transient while driving to dump; not persisted.)

    Stop-type transitions
    ---------------------
    Pull      : requires no_can    → dumps + returns same can → after: no_can
    Delivery  : requires empty_can → drops can at site        → after: no_can
    PR / Swap : valid in any state → mode derived from can_state_before:
                  empty_can → swap mode        → dump full, keep empty → after: empty_can
                  no_can    → return-same-can  → dump full, return same → after: no_can
    Other     : no change to can state

    swap_with_prev_pull is set to 1 for PR/Swap stops when can_state_before
    is "empty_can" (swap mode). Value is sequence-derived, not manually set.

    Call after ordering stops so the sequence reflects actual drive order.
    Caller is responsible for conn.commit().
    """
    stops = conn.execute(
        "SELECT id, action FROM stops WHERE route_id=? ORDER BY stop_order ASC, id ASC",
        (route_id,)
    ).fetchall()

    can_state = "empty_can" if starts_with_can else "no_can"

    for s in stops:
        action_lower = (s["action"] or "").lower().strip()

        # Is this a PR-type stop (Pickup and Return or Swap-only)?
        is_pr = (
            "pickup and return" in action_lower
            or ("swap" in action_lower and "pull" not in action_lower)
        )

        if is_pr:
            # Derive swap from whether truck arrives carrying an empty can
            derived_swap = 1 if can_state == "empty_can" else 0
            conn.execute(
                "UPDATE stops SET can_state_before=?, swap_with_prev_pull=? WHERE id=?",
                (can_state, derived_swap, s["id"])
            )
            # PR swap (empty_can): dropped off empty, dumped full → truck holds empty
            # PR return-same (no_can): dumped full, returned empty to customer → truck empty
            can_state = _next_can_state(action_lower, can_state)
        else:
            conn.execute(
                "UPDATE stops SET can_state_before=? WHERE id=?",
                (can_state, s["id"])
            )
            # Compute state AFTER this stop using shared helper
            can_state = _next_can_state(action_lower, can_state)


# =============================================================
# PHASE 5A — CONTAINER FLOW ENGINE
# Set to True to activate automatic per-stop container tracking.
# False = tables are created but no writes happen.
# =============================================================
ENABLE_CONTAINER_TRACKING = False


def update_container_flow(conn, stop_id):
    """
    Update container inventory records when a stop is completed.

    Rules:
      Delivery  → insert customer_containers row (on_site)
      Pull      → close existing on_site row for that address
      PR swap   → close existing row + insert new on_site row
      PR return → close existing row + insert new on_site row
                  (same can goes back; treated identically to swap at record level)

    This function is always safe to call:
      - wrapped in try/except so a tracking failure never aborts a stop completion
      - only runs if ENABLE_CONTAINER_TRACKING is True
      - never touches parser, can-flow, or optimization code
    """
    if not ENABLE_CONTAINER_TRACKING:
        return

    try:
        stop = conn.execute(
            """SELECT s.*, r.company_id
               FROM stops s JOIN routes r ON s.route_id = r.id
               WHERE s.id = ?""",
            (stop_id,)
        ).fetchone()
        if not stop:
            return

        s       = dict(stop)
        co_id   = s.get("company_id")
        addr    = (s.get("address") or "").strip()
        city    = (s.get("city")    or "").strip()
        state   = (s.get("state")   or "").strip()
        size    = (s.get("container_size") or "").strip()
        ts      = now_ts()
        action  = (s.get("action") or "").lower()

        is_delivery = "delivery" in action
        is_pull     = "pull" in action and "return" not in action
        is_pr       = "pickup and return" in action or ("swap" in action and "pull" not in action)

        if not addr:
            return

        if is_delivery:
            # Drop off an empty can — truck leaves empty
            conn.execute(
                """INSERT INTO customer_containers
                   (company_id, address, city, state, size,
                    delivered_stop_id, delivered_at, status, created_at)
                   VALUES (?,?,?,?,?,?,?,'on_site',?)""",
                (co_id, addr, city, state, size, stop_id, ts, ts)
            )

        elif is_pull or is_pr:
            # Pull  — box out full, dump, return SAME empty can to customer (cycle)
            # PR    — same physical cycle (swap or return-same; both close + reopen)
            # Close the full can that was on-site
            conn.execute(
                """UPDATE customer_containers
                   SET pulled_stop_id=?, pulled_at=?, status='pulled'
                   WHERE company_id=? AND LOWER(address)=LOWER(?) AND status='on_site'""",
                (stop_id, ts, co_id, addr)
            )
            # Return the now-empty can to the customer
            conn.execute(
                """INSERT INTO customer_containers
                   (company_id, address, city, state, size,
                    delivered_stop_id, delivered_at, status, created_at)
                   VALUES (?,?,?,?,?,?,?,'on_site',?)""",
                (co_id, addr, city, state, size, stop_id, ts, ts)
            )
    except Exception:
        pass  # Never abort a driver completion due to tracking failure


# =============================================================
# PHASE 5B — DRIVER HOURS / PAY CYCLE HELPERS
# =============================================================

def get_pay_period_bounds(company_settings, as_of_date_str=None):
    """
    Return (period_start, period_end) as 'YYYY-MM-DD' strings.

    Uses the company's configured timezone to determine 'today' so the
    displayed pay period matches the company's local calendar, not UTC.

    company_settings: dict with keys pay_period_type, pay_period_end_day, timezone.
    as_of_date_str:   'YYYY-MM-DD' override; when given, timezone is ignored.

    pay_period_end_day: lowercase weekday name, e.g. 'thursday'.
    pay_period_type:    'weekly' (7-day) | 'biweekly' (14-day).

    Example — settings: timezone=America/New_York, pay_period_end_day=thursday,
              pay_period_type=weekly.  On a Monday local date 2026-04-13:
              end   = 2026-04-09  (most recent Thursday on/before today)
              start = 2026-04-03  (end - 6 days = Friday)
    """
    DAYS = ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"]

    if as_of_date_str:
        as_of = date.fromisoformat(as_of_date_str)
    else:
        tz_name = (company_settings.get("timezone") or "America/New_York").strip()
        try:
            from zoneinfo import ZoneInfo
            as_of = datetime.now(ZoneInfo(tz_name)).date()
        except Exception:
            as_of = date.today()

    ptype  = (company_settings.get("pay_period_type") or "weekly").lower()
    endday = (company_settings.get("pay_period_end_day") or "sunday").lower()

    try:
        target_wd = DAYS.index(endday)  # 0=Mon … 6=Sun
    except ValueError:
        target_wd = 6  # default Sunday

    # Find the end of the CURRENT pay period:
    # advance forward to the next occurrence of target_wd (0 days if today IS target_wd).
    # This gives the period that contains today, not the one that just ended.
    # Example: pay_period_end_day=thursday, today=Monday 2026-04-13
    #   days_forward = (3 - 0) % 7 = 3  →  period_end = 2026-04-16 (Thu)
    #   period_start = 2026-04-16 - 6   = 2026-04-10 (Fri)
    days_forward = (target_wd - as_of.weekday()) % 7
    period_end = as_of + timedelta(days=days_forward)

    span = 6 if ptype == "weekly" else 13
    period_start = period_end - timedelta(days=span)

    return period_start.isoformat(), period_end.isoformat()


def get_driver_day_hours(conn, driver_id, date_str, company_settings):
    """
    Return (start_ts, end_ts, hours_float) for a driver on a given calendar date.

    Manual clock entries always override auto (stop-based) times for any date
    on which they exist, regardless of the configured start/end rules.

    company_settings: dict with driver_day_start_rule / driver_day_end_rule.
    date_str: 'YYYY-MM-DD' in the company's local time.
    Returns (None, None, None) if insufficient data or any query fails.
    """
    try:
        start_rule = (company_settings.get("driver_day_start_rule") or "first_action").lower()
        end_rule   = (company_settings.get("driver_day_end_rule")   or "last_action").lower()

        # Manual entry takes priority over any auto (stop-based) time
        manual_ci = manual_co = None
        try:
            mrow = conn.execute(
                "SELECT clock_in_at, clock_out_at FROM driver_clock_entries "
                "WHERE driver_id=? AND date=?",
                (driver_id, date_str)
            ).fetchone()
            if mrow:
                manual_ci = mrow["clock_in_at"] or None
                manual_co = mrow["clock_out_at"] or None
        except Exception:
            pass

        # ── start timestamp ──────────────────────────────────────────────────
        if manual_ci:
            start_ts = manual_ci                         # manual always wins
        elif start_rule == "first_action":
            row = conn.execute(
                """SELECT MIN(COALESCE(arrived_at, completed_at)) AS t
                   FROM stops s
                   JOIN routes r ON s.route_id = r.id
                   WHERE r.assigned_to = ?
                     AND COALESCE(arrived_at, completed_at) >= ?
                     AND COALESCE(arrived_at, completed_at) < date(?, '+1 day')
                     AND s.status = 'completed'""",
                (driver_id, date_str, date_str)
            ).fetchone()
            start_ts = row["t"] if row else None
        else:
            start_ts = None                              # manual rule, no entry yet

        # ── end timestamp ────────────────────────────────────────────────────
        if manual_co:
            end_ts = manual_co                           # manual always wins
        elif end_rule == "last_action":
            row = conn.execute(
                """SELECT MAX(completed_at) AS t
                   FROM stops s
                   JOIN routes r ON s.route_id = r.id
                   WHERE r.assigned_to = ?
                     AND s.completed_at >= ?
                     AND s.completed_at < date(?, '+1 day')
                     AND s.status = 'completed'""",
                (driver_id, date_str, date_str)
            ).fetchone()
            end_ts = row["t"] if row else None
        else:
            end_ts = None                                # manual rule, no entry yet

        if not start_ts or not end_ts:
            return None, None, None

        from datetime import datetime
        fmt = "%Y-%m-%d %H:%M:%S"
        s  = datetime.strptime(start_ts[:19], fmt)
        e_ = datetime.strptime(end_ts[:19], fmt)
        hours = max(0.0, (e_ - s).total_seconds() / 3600)
        return start_ts, end_ts, round(hours, 2)

    except Exception:
        return None, None, None


def load_stop_photos(conn, stop_ids):
    """Return dict {stop_id: [photo_row, ...]} for the given stop IDs."""
    if not stop_ids:
        return {}
    placeholders = ",".join("?" * len(stop_ids))
    rows = conn.execute(f"""
        SELECT rp.id, rp.stop_id, rp.file_path, rp.uploaded_at,
               COALESCE(u.username, 'Unknown') AS uploader
        FROM route_photos rp
        LEFT JOIN users u ON rp.uploaded_by = u.id
        WHERE rp.stop_id IN ({placeholders})
        ORDER BY rp.stop_id, rp.uploaded_at ASC
    """, stop_ids).fetchall()
    result = {}
    for r in rows:
        result.setdefault(r["stop_id"], []).append(r)
    return result


def build_photo_gallery_html(photos):
    """Render a gallery of uploaded photos with uploader name and timestamp."""
    if not photos:
        return ""
    items = []
    for p in photos:
        path = "/" + p["file_path"].replace("\\", "/")
        ext = p["file_path"].rsplit(".", 1)[-1].lower() if "." in p["file_path"] else ""
        if ext == "pdf":
            media = f'<a class="photo-pdf-link" href="{e(path)}" target="_blank">&#128196; PDF Document</a>'
        else:
            media = f'<a href="{e(path)}" target="_blank"><img class="photo-thumb" src="{e(path)}" alt="stop photo" loading="lazy"></a>'
        items.append(
            f'<div class="photo-item">'
            f'{media}'
            f'<div class="photo-meta">{e(p["uploader"])}<br>{e(p["uploaded_at"])}</div>'
            f'</div>'
        )
    return '<div class="photo-gallery">' + "".join(items) + "</div>"


def init_db():
    conn = get_db()
    cur = conn.cursor()

    cur.execute("""
    CREATE TABLE IF NOT EXISTS users (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        username TEXT UNIQUE NOT NULL,
        password_hash TEXT NOT NULL,
        role TEXT NOT NULL CHECK(role IN ('boss', 'driver')),
        full_name TEXT,
        phone TEXT,
        created_at TEXT NOT NULL
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS routes (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        route_date TEXT NOT NULL,
        route_name TEXT NOT NULL,
        raw_text TEXT,
        assigned_to INTEGER,
        created_by INTEGER NOT NULL,
        status TEXT NOT NULL DEFAULT 'open' CHECK(status IN ('open','in_progress','completed')),
        notes TEXT,
        started_at TEXT,
        completed_at TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY (assigned_to) REFERENCES users(id),
        FOREIGN KEY (created_by) REFERENCES users(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS stops (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        route_id INTEGER NOT NULL,
        stop_order INTEGER NOT NULL,
        customer_name TEXT,
        address TEXT,
        city TEXT,
        state TEXT,
        zip_code TEXT,
        action TEXT,
        container_size TEXT,
        ticket_number TEXT,
        reference_number TEXT,
        dump_location TEXT,
        notes TEXT,
        status TEXT NOT NULL DEFAULT 'open' CHECK(status IN ('open','completed')),
        completed_at TEXT,
        driver_signature TEXT,
        photo_path TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY (route_id) REFERENCES routes(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS route_photos (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        stop_id INTEGER NOT NULL,
        file_path TEXT NOT NULL,
        uploaded_at TEXT NOT NULL,
        FOREIGN KEY (stop_id) REFERENCES stops(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS load_scores (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        origin TEXT,
        destination TEXT,
        pickup_time TEXT,
        payout REAL DEFAULT 0,
        miles REAL DEFAULT 0,
        estimated_profit REAL DEFAULT 0,
        score REAL DEFAULT 0,
        notes TEXT,
        created_by INTEGER,
        created_at TEXT NOT NULL,
        FOREIGN KEY (created_by) REFERENCES users(id)
    )
    """)
    cur.execute("""
    CREATE TABLE IF NOT EXISTS orders (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        customer_name TEXT NOT NULL,
        phone TEXT,
        email TEXT,
        address TEXT NOT NULL,
        city TEXT,
        state TEXT,
        zip_code TEXT,
        service_type TEXT NOT NULL,
        container_size TEXT,
        notes TEXT,
        requested_date TEXT,
        status TEXT NOT NULL DEFAULT 'new' CHECK(status IN ('new','converted','closed')),
        company_id INTEGER,
        created_at TEXT NOT NULL
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS companies (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL,
        slug TEXT UNIQUE NOT NULL,
        owner_id INTEGER,
        subscription_plan TEXT NOT NULL DEFAULT 'trial'
            CHECK(subscription_plan IN ('trial','starter','pro','enterprise')),
        subscription_status TEXT NOT NULL DEFAULT 'active'
            CHECK(subscription_status IN ('active','suspended','cancelled')),
        max_drivers INTEGER NOT NULL DEFAULT 5,
        trial_ends_at TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY (owner_id) REFERENCES users(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS subscriptions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id INTEGER NOT NULL,
        plan TEXT NOT NULL,
        status TEXT NOT NULL DEFAULT 'active',
        started_at TEXT NOT NULL,
        ends_at TEXT,
        notes TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY (company_id) REFERENCES companies(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS dump_locations (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL,
        address TEXT,
        city TEXT,
        state TEXT,
        zip_code TEXT,
        notes TEXT,
        active INTEGER NOT NULL DEFAULT 1,
        created_at TEXT NOT NULL
    )
    """)

    # Seed dump locations if table is empty
    if cur.execute("SELECT COUNT(*) FROM dump_locations").fetchone()[0] == 0:
        _seed_dumps = [
            ("Bay",         "83 Pagan Ave",          "Smithfield",    "VA", "23430", ""),
            ("SPSA Landfill","1 Bob Foeller Dr",      "Suffolk",       "VA", "",      ""),
            ("Holland",     "4801 Nansemond Pkwy",   "Suffolk",       "VA", "",      ""),
            ("Spivey",      "228 Salters Creek Rd",  "Hampton",       "VA", "",      ""),
            ("SB Cox",      "217 Cox Dr",            "Yorktown",      "VA", "",      ""),
            ("United",      "161 Wellman St",        "Norfolk",       "VA", "",      ""),
            ("Waterway",    "1431 Precon Dr",        "Chesapeake",    "VA", "",      ""),
            ("Dominion",    "5444 Bainbridge Blvd",  "Chesapeake",    "VA", "",      ""),
            ("Sykes",       "124 Sykes Ave",         "Virginia Beach","VA", "",      ""),
            ("MM GU2737",   "Seaboard Rd",           "",              "VA", "",      "Verify full city and ZIP before production"),
        ]
        _ts = now_ts()
        for _n, _a, _c, _s, _z, _notes in _seed_dumps:
            cur.execute(
                "INSERT INTO dump_locations (name, address, city, state, zip_code, notes, active, created_at) VALUES (?,?,?,?,?,?,1,?)",
                (_n, _a, _c, _s, _z, _notes, _ts)
            )

    # --- column migrations (safe, idempotent) ---
    safe_add_column(conn, "users", "full_name TEXT")
    safe_add_column(conn, "users", "phone TEXT")
    safe_add_column(conn, "users", "company_id INTEGER")
    safe_add_column(conn, "users", "is_superadmin INTEGER NOT NULL DEFAULT 0")
    safe_add_column(conn, "routes", "started_at TEXT")
    safe_add_column(conn, "routes", "company_id INTEGER")
    safe_add_column(conn, "orders", "email TEXT")
    safe_add_column(conn, "orders", "city TEXT")
    safe_add_column(conn, "orders", "state TEXT")
    safe_add_column(conn, "orders", "zip_code TEXT")
    safe_add_column(conn, "orders", "container_size TEXT")
    safe_add_column(conn, "orders", "requested_date TEXT")
    safe_add_column(conn, "orders", "company_id INTEGER")
    safe_add_column(conn, "load_scores", "company_id INTEGER")
    safe_add_column(conn, "route_photos", "uploaded_by INTEGER")
    safe_add_column(conn, "routes", "dump_location_id INTEGER")
    safe_add_column(conn, "stops", "phone TEXT")

    # --- dump tickets table ---
    cur.execute("""
    CREATE TABLE IF NOT EXISTS dump_tickets (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        stop_id INTEGER NOT NULL,
        route_id INTEGER NOT NULL,
        company_id INTEGER,
        dump_site TEXT,
        arrival_time TEXT,
        departure_time TEXT,
        can_number TEXT,
        scale_in_weight REAL,
        scale_out_weight REAL,
        net_tons REAL,
        ticket_number TEXT,
        notes TEXT,
        photo_path TEXT,
        created_at TEXT NOT NULL,
        created_by INTEGER,
        FOREIGN KEY (stop_id) REFERENCES stops(id),
        FOREIGN KEY (route_id) REFERENCES routes(id)
    )
    """)
    # --- Phase 5A: container fleet tracking ---
    cur.execute("""
    CREATE TABLE IF NOT EXISTS containers (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id  INTEGER NOT NULL,
        size        TEXT NOT NULL,
        label       TEXT,
        status      TEXT NOT NULL DEFAULT 'yard'
                    CHECK(status IN ('yard','deployed','lost','retired')),
        notes       TEXT,
        created_at  TEXT NOT NULL
    )
    """)
    cur.execute("""
    CREATE TABLE IF NOT EXISTS customer_containers (
        id               INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id       INTEGER NOT NULL,
        address          TEXT NOT NULL,
        city             TEXT,
        state            TEXT,
        size             TEXT,
        container_id     INTEGER,
        delivered_stop_id INTEGER,
        delivered_at     TEXT,
        pulled_stop_id   INTEGER,
        pulled_at        TEXT,
        status           TEXT NOT NULL DEFAULT 'on_site'
                         CHECK(status IN ('on_site','pulled','transferred')),
        created_at       TEXT NOT NULL,
        FOREIGN KEY (container_id)      REFERENCES containers(id),
        FOREIGN KEY (delivered_stop_id) REFERENCES stops(id),
        FOREIGN KEY (pulled_stop_id)    REFERENCES stops(id)
    )
    """)

    # --- driver workflow columns on stops ---
    safe_add_column(conn, "stops", "driver_status TEXT NOT NULL DEFAULT 'pending'")
    safe_add_column(conn, "stops", "arrived_at TEXT")
    safe_add_column(conn, "stops", "box_in_at TEXT")
    safe_add_column(conn, "stops", "box_out_at TEXT")
    safe_add_column(conn, "stops", "go_to_dump_at TEXT")
    safe_add_column(conn, "stops", "wo_type TEXT")
    safe_add_column(conn, "stops", "dump_location TEXT")
    safe_add_column(conn, "stops", "swap_with_prev_pull INTEGER NOT NULL DEFAULT 0")
    safe_add_column(conn, "companies", "stripe_customer_id TEXT")
    safe_add_column(conn, "companies", "stripe_subscription_id TEXT")
    safe_add_column(conn, "users", "email TEXT")
    safe_add_column(conn, "companies", "yard_address TEXT")
    safe_add_column(conn, "companies", "yard_city TEXT")
    safe_add_column(conn, "companies", "yard_state TEXT")
    safe_add_column(conn, "companies", "yard_zip TEXT")
    safe_add_column(conn, "stops", "can_state_before TEXT")

    # --- Phase 5B: company work hours / pay cycle ---
    safe_add_column(conn, "companies", "timezone TEXT")
    safe_add_column(conn, "companies", "workweek_start_day TEXT")
    safe_add_column(conn, "companies", "workweek_reset_day TEXT")
    safe_add_column(conn, "companies", "pay_period_type TEXT")
    safe_add_column(conn, "companies", "pay_period_end_day TEXT")
    safe_add_column(conn, "companies", "payday TEXT")
    safe_add_column(conn, "companies", "driver_day_start_rule TEXT")
    safe_add_column(conn, "companies", "driver_day_end_rule TEXT")

    cur.execute("""
    CREATE TABLE IF NOT EXISTS driver_clock_entries (
        id           INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id   INTEGER NOT NULL,
        driver_id    INTEGER NOT NULL,
        date         TEXT NOT NULL,
        clock_in_at  TEXT,
        clock_out_at TEXT,
        notes        TEXT,
        created_at   TEXT NOT NULL,
        FOREIGN KEY (driver_id) REFERENCES users(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS saved_addresses (
        id                     INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id             INTEGER NOT NULL,
        customer_name          TEXT,
        address                TEXT,
        city                   TEXT,
        state                  TEXT,
        zip                    TEXT,
        full_address           TEXT,
        lat                    REAL,
        lng                    REAL,
        default_action         TEXT,
        default_container_size TEXT,
        default_dump_location  TEXT,
        times_used             INTEGER NOT NULL DEFAULT 1,
        last_used_at           TEXT NOT NULL,
        created_at             TEXT NOT NULL,
        UNIQUE(company_id, customer_name, address)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS saved_address_details (
        id               INTEGER PRIMARY KEY AUTOINCREMENT,
        saved_address_id INTEGER NOT NULL,
        action           TEXT NOT NULL DEFAULT '',
        container_size   TEXT NOT NULL DEFAULT '',
        dump_location    TEXT NOT NULL DEFAULT '',
        times_used       INTEGER NOT NULL DEFAULT 1,
        last_used_at     TEXT NOT NULL,
        UNIQUE(saved_address_id, action, container_size, dump_location),
        FOREIGN KEY (saved_address_id) REFERENCES saved_addresses(id)
    )
    """)

    # --- default company bootstrap ---
    default_co = conn.execute("SELECT id FROM companies LIMIT 1").fetchone()
    if not default_co:
        conn.execute(
            """INSERT INTO companies (name, slug, subscription_plan, subscription_status,
               max_drivers, trial_ends_at, created_at)
               VALUES (?,?,?,?,?,?,?)""",
            ("Default Company", "default", "trial", "active", 10, None, now_ts())
        )
        conn.commit()
    default_co_id = conn.execute("SELECT id FROM companies LIMIT 1").fetchone()["id"]

    # migrate orphaned rows to the default company
    conn.execute("UPDATE users SET company_id=? WHERE company_id IS NULL", (default_co_id,))
    conn.execute("UPDATE routes SET company_id=? WHERE company_id IS NULL", (default_co_id,))
    conn.execute("UPDATE orders SET company_id=? WHERE company_id IS NULL", (default_co_id,))
    conn.execute("UPDATE load_scores SET company_id=? WHERE company_id IS NULL", (default_co_id,))
    conn.commit()

    existing_boss = cur.execute("SELECT id FROM users WHERE role='boss' LIMIT 1").fetchone()
    if not existing_boss:
        cur.execute(
            """INSERT INTO users (username, password_hash, role, full_name, phone,
               company_id, created_at) VALUES (?, ?, ?, ?, ?, ?, ?)""",
            ("boss", generate_password_hash("boss123"), "boss", "Boss", "", default_co_id, now_ts())
        )
        conn.commit()
        # make the default boss the company owner
        boss_id = cur.lastrowid
        conn.execute("UPDATE companies SET owner_id=? WHERE id=?", (boss_id, default_co_id))
        conn.commit()

    conn.close()


# =========================================================
# AUTH / SESSION
# =========================================================
def login_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if "user_id" not in session:
            flash("Login required.", "error")
            return redirect(url_for("login"))
        return fn(*args, **kwargs)
    return wrapper


def boss_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if "user_id" not in session:
            flash("Login required.", "error")
            return redirect(url_for("login"))
        if session.get("role") != "boss":
            flash("Boss access only.", "error")
            return redirect(url_for("dashboard"))
        return fn(*args, **kwargs)
    return wrapper

def driver_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if "user_id" not in session:
            flash("Login required.", "error")
            return redirect(url_for("login"))
        if session.get("role") != "driver":
            flash("Driver access only.", "error")
            return redirect(url_for("dashboard"))
        return fn(*args, **kwargs)
    return wrapper

def superadmin_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if "user_id" not in session:
            flash("Login required.", "error")
            return redirect(url_for("login"))
        if not session.get("is_superadmin"):
            flash("Superadmin access only.", "error")
            return redirect(url_for("dashboard"))
        return fn(*args, **kwargs)
    return wrapper


def get_current_user():
    if "user_id" not in session:
        return None
    conn = get_db()
    user = conn.execute("SELECT * FROM users WHERE id = ?", (session["user_id"],)).fetchone()
    conn.close()
    return user


def cid():
    """Return the current session's company_id (None if not logged in)."""
    return session.get("company_id")


def get_company_route(conn, route_id):
    """Fetch a route only if it belongs to the current company. Returns None otherwise."""
    return conn.execute(
        "SELECT * FROM routes WHERE id=? AND company_id=?",
        (route_id, cid())
    ).fetchone()


def get_company_stop(conn, stop_id):
    """Fetch a stop (with route fields) only if it belongs to the current company."""
    return conn.execute(
        """SELECT s.*, r.assigned_to, r.company_id, r.id AS route_id_int
           FROM stops s JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()


# =========================================================
# ROUTE PARSER
# =========================================================
def clean_line(line):
    line = line.replace("\t", " ").replace("•", " ").replace("–", "-")
    line = re.sub(r"\s+", " ", line).strip()
    return line


def looks_like_address(line):
    line = line.strip()

    if not re.match(r"^\d{1,6}\s+", line):
        return False

    lower = line.lower()
    bad_starts = [
        "ticket", "tkt", "job", "ref", "load",
        "notes", "note",
        "pickup", "pick up",
        "drop", "swap", "dump",
        "service", "remove", "deliver", "delivery"
    ]

    if any(lower.startswith(x) for x in bad_starts):
        return False

    return True

def extract_city_state_zip(line):
    m = re.search(r"([A-Za-z .'-]+),\s*([A-Z]{2})\s*(\d{5})?", line)
    if m:
        return m.group(1).strip(), m.group(2).strip(), (m.group(3) or "").strip()
    return "", "", ""


def extract_ticket(line):
    patterns = [
        r"(?:ticket|tkt|job|ref|load)\s*#?:?\s*([A-Za-z0-9\-\/]+)",
        r"#\s*([A-Za-z0-9\-\/]+)"
    ]
    for p in patterns:
        m = re.search(p, line, re.IGNORECASE)
        if m:
            return m.group(1).strip()
    return ""


def extract_container_size(line):
    patterns = [
        r"\b(\d{1,2})\s*(?:yd|yard|yards)\b",
        r"\b(\d{1,2})\b"
    ]
    for p in patterns:
        m = re.search(p, line, re.IGNORECASE)
        if m:
            return m.group(1).strip()
    return ""


# Action tokens that may appear as the first field in a dash-delimited line
_ACTION_TOKENS = {
    "P":    "Pickup",
    "D":    "Drop",
    "PR":   "Pickup and Return",
    "DUMP": "Dump",
    "PULL": "Pull",
}


def extract_action(line):
    # Check short token at start of line first (e.g. "P - ", "D - ", "PR - ")
    stripped = re.sub(r"^\d{1,3}[).\-:]\s*", "", line).strip()
    first_token = stripped.split(" - ")[0].strip().upper()
    if first_token in _ACTION_TOKENS:
        return _ACTION_TOKENS[first_token]

    lower = line.lower()
    action_map = [
        ("pickup and return", "Pickup and Return"),
        ("swap",     "Swap"),
        ("switch",   "Swap"),
        ("remove",   "Remove"),
        ("pickup",   "Pickup"),
        ("pick up",  "Pickup"),
        ("drop",     "Drop"),
        ("delivery", "Drop"),
        ("deliver",  "Drop"),
        ("dump",     "Dump"),
        ("empty",    "Dump"),
        ("final",    "Final"),
        ("relocate", "Relocate"),
        ("service",  "Service"),
    ]
    for key, label in action_map:
        if key in lower:
            return label
    return ""

def _is_dash_delimited(line):
    """Return True if a line is a complete one-line dash-delimited stop.

    Requires at least 3 parts (>= 2 separators) for both action-prefixed and
    plain formats.  This prevents multiline first-lines like "P - John Smith"
    (only 2 parts) from being mistaken for one-line stops.
    """
    stripped = re.sub(r"^\d{1,3}[).\-:]\s*", "", line).strip()
    if not stripped:
        return False
    parts = [p.strip() for p in stripped.split(" - ")]
    if len(parts) < 3:
        return False
    first_token = parts[0].upper()
    # Action-prefixed one-liner: P/D/PR/DUMP - ADDRESS - ... (>= 3 parts confirmed above)
    if first_token in _ACTION_TOKENS:
        return True
    # Plain format: ADDRESS - CONTAINER - NAME  (first part must look like a street)
    return bool(re.match(r"^\d", parts[0]))


# Words that identify a line as a route/day title rather than a stop
_ROUTE_TITLE_WORDS = {
    "MONDAY", "TUESDAY", "WEDNESDAY", "THURSDAY", "FRIDAY", "SATURDAY", "SUNDAY",
    "ROUTE", "DRIVER", "RUN", "AM", "PM",
}


def _is_route_header(line):
    """Return True if line looks like a route title and should be skipped.

    Matches lines like: MONDAY ROUTE, TUESDAY ROUTE, DRIVER TIM, ROUTE, WEDNESDAY
    Does NOT match customer names, addresses, actions, or city/state lines.
    """
    stripped = re.sub(r"^\d+[\).\-\s]+", "", line).strip()
    if not stripped:
        return False
    # Must contain only letters and spaces (no digits, dashes, commas, etc.)
    if not re.match(r"^[A-Za-z\s]+$", stripped):
        return False
    # Must be entirely uppercase
    if stripped != stripped.upper():
        return False
    words = stripped.split()
    # Single word: only skip if it is a known route-title word
    if len(words) == 1:
        return words[0] in _ROUTE_TITLE_WORDS
    # Multi-word: skip if at least one word is a route-title keyword
    return any(w in _ROUTE_TITLE_WORDS for w in words)


def split_into_stop_blocks(raw_text):
    lines = [clean_line(x) for x in raw_text.splitlines()]
    lines = [x for x in lines if x]
    if not lines:
        return []

    # Numbered-stop detector: 1–3 digits followed by a separator ( . ) : - ) then
    # at least one space.  Intentionally NOT matching street addresses:
    #   "1. "  "2) "  "3- "  → numbered stop  ✓
    #   "5678 Tidewater"      → address, 4 digits, no separator  ✗
    #   "123 Main St"         → address, digits+space, no separator  ✗
    _NUMBERED = re.compile(r"^\d{1,3}[).\-:]\s")

    # Dash-delimited: one true one-line stop per line (>= 3 parts)
    dash_lines = sum(1 for l in lines if _is_dash_delimited(l))
    if dash_lines >= max(1, len(lines) // 2):
        return [[line] for line in lines if not _is_route_header(line)]

    # Numbered multi-line format: each numbered line starts a new block.
    # Lines before the first numbered stop (route headers, driver names) are skipped.
    has_numbered = any(_NUMBERED.match(line) for line in lines)
    if has_numbered:
        blocks = []
        current = []
        seen_first_stop = False
        for line in lines:
            if _NUMBERED.match(line):
                if current:
                    blocks.append(current)
                current = [line]
                seen_first_stop = True
            elif not seen_first_stop:
                # Pre-stop line (route header, driver label, etc.) — skip
                continue
            else:
                current.append(line)
        if current:
            blocks.append(current)
        return blocks

    # Fallback: each non-header line is its own block
    return [[line] for line in lines if not _is_route_header(line)]


# Street-type suffixes used to split "STREET CITY STATE" without commas.
_STREET_SFX_RE = re.compile(
    r"\b(rd|st|ave|blvd|dr|ln|ct|way|pl|cir|hwy|pkwy|trl|ter|row|loop|run|pass|pt)\b",
    re.IGNORECASE,
)


def _parse_structured_addr(addr_str):
    """
    Parse an address that may contain city and state without commas.

    Handles both:
      "4100 Holland Rd, Virginia Beach VA"   (comma form)
      "4100 Holland Rd Virginia Beach VA"    (space form)

    Returns (street, city, state, zip_code).
    Falls back to (addr_str, "", "", "") if not parseable.
    """
    addr = addr_str.strip()

    # ── Comma form ────────────────────────────────────────────────────────────
    m = re.search(r",\s*(.+?)\s+([A-Z]{2})\s*(\d{5})?\s*$", addr)
    if m:
        return (
            addr[:m.start()].strip(),
            m.group(1).strip(),
            m.group(2),
            (m.group(3) or "").strip(),
        )

    # ── Space form: locate state code at end, then city before it ────────────
    m_state = re.search(r"\s+([A-Z]{2})\s*(\d{5})?\s*$", addr)
    if not m_state:
        return addr, "", "", ""

    state    = m_state.group(1)
    zip_code = (m_state.group(2) or "").strip()
    before   = addr[:m_state.start()].strip()

    # Find the last street-type abbreviation; city starts after it
    last_sfx = None
    for m_sfx in _STREET_SFX_RE.finditer(before):
        last_sfx = m_sfx

    if last_sfx:
        street = before[:last_sfx.end()].strip()
        city   = before[last_sfx.end():].strip()
    else:
        # No suffix found — split at last two words as city
        words = before.rsplit(None, 2)
        if len(words) >= 3:
            street = words[0].strip()
            city   = " ".join(words[1:]).strip()
        else:
            street, city = before, ""

    return street, city, state, zip_code


def parse_stop_block(lines, order_num):
    cleaned_lines = [x.strip() for x in lines if x.strip()]

    _empty = {
        "stop_order":       order_num,
        "customer_name":    "",
        "address":          "",
        "city":             "",
        "state":            "",
        "zip_code":         "",
        "action":           "Service",
        "container_size":   "",
        "ticket_number":    "",
        "reference_number": "",
        "phone":            "",
        "dump_location":    "",
        "notes":            "",
    }

    if not cleaned_lines:
        return _empty

    first_line = cleaned_lines[0]
    # Strip leading number prefix ("1. ", "2) ", "4. ", etc.)
    stripped_first = re.sub(r"^\d{1,3}[).\-:]\s*", "", first_line).strip()

    # ── Dash-delimited ONE-LINE format ────────────────────────────────────────
    # Only enter this branch when there are >= 3 dash-separated parts.
    # A line like "P - John Smith" has only 2 parts and is the start of a
    # multiline stop — it falls through to the multiline section below.
    #
    # Supported one-line layouts:
    #   P  - ADDRESS - SIZE - NAME [- PHONE]
    #   D  - ADDRESS - SIZE - NAME [- PHONE]
    #   PR - ADDRESS - SIZE - NAME [- PHONE]
    #   DUMP - LOCATION_NAME - ADDRESS
    #   ADDRESS - SIZE - NAME [- PHONE]        (plain, no action prefix)
    if " - " in stripped_first:
        parts = [p.strip() for p in stripped_first.split(" - ")]
        first_token = parts[0].upper() if parts else ""
        action_from_token = _ACTION_TOKENS.get(first_token, "")

        # DUMP is always a one-liner regardless of part count
        if action_from_token == "Dump":
            location_name = parts[1] if len(parts) > 1 else ""
            dump_address  = parts[2] if len(parts) > 2 else ""
            if not dump_address:
                dump_address, location_name = location_name, ""
            return {
                "stop_order":       order_num,
                "customer_name":    location_name,
                "address":          dump_address,
                "city":             "",
                "state":            "",
                "zip_code":         "",
                "action":           "Dump",
                "container_size":   "",
                "ticket_number":    "",
                "reference_number": "",
                "phone":            "",
                "dump_location":    "",
                "notes":            "",
            }

        if len(parts) >= 3:
            # ── Detect structured format: CUSTOMER - ADDRESS - ACTION - SIZE [- DUMP: SITE]
            # Signature: parts[0] is NOT a known action, but parts[2] IS.
            # Example: "Smith Demo - 4100 Holland Rd Virginia Beach VA - P - 30yd - Dump: Dominion"
            _p2_action = _ACTION_TOKENS.get(parts[2].strip().upper(), "")
            if not action_from_token and _p2_action and len(parts) >= 4:
                _cust  = parts[0].strip()
                _addr  = parts[1].strip()
                _act   = _p2_action
                _size  = parts[3].strip()
                _dump  = ""
                for _pt in parts[4:]:
                    if re.match(r"dump\s*:\s*", _pt.strip(), re.IGNORECASE):
                        _dump = re.sub(r"^dump\s*:\s*", "", _pt.strip(),
                                       flags=re.IGNORECASE).strip()
                        break
                _street, _city, _state, _zip = _parse_structured_addr(_addr)
                _csz = extract_container_size(_size) or _size
                return {
                    "stop_order":       order_num,
                    "customer_name":    _cust,
                    "address":          _street,
                    "city":             _city,
                    "state":            _state,
                    "zip_code":         _zip,
                    "action":           _act,
                    "container_size":   _csz,
                    "ticket_number":    "",
                    "reference_number": "",
                    "phone":            "",
                    "dump_location":    _dump,
                    "notes":            "",
                }

            # ── Existing one-line formats ────────────────────────────────────
            # ACTION - ADDRESS - SIZE - NAME [- PHONE]
            # ADDRESS - SIZE - NAME [- PHONE]  (no action prefix)
            if action_from_token:
                raw_address   = parts[1]
                raw_size      = parts[2] if len(parts) > 2 else ""
                customer_name = parts[3] if len(parts) > 3 else ""
                phone         = parts[4] if len(parts) > 4 else ""
                action        = action_from_token
            else:
                raw_address   = parts[0]
                raw_size      = parts[1]
                customer_name = parts[2] if len(parts) > 2 else ""
                phone         = parts[3] if len(parts) > 3 else ""
                action        = extract_action(stripped_first) or "Service"

            container_size = extract_container_size(raw_size) or raw_size
            return {
                "stop_order":       order_num,
                "customer_name":    customer_name,
                "address":          raw_address,
                "city":             "",
                "state":            "",
                "zip_code":         "",
                "action":           action,
                "container_size":   container_size,
                "ticket_number":    "",
                "reference_number": "",
                "phone":            phone,
                "dump_location":    "",
                "notes":            "",
            }

        # < 3 parts (e.g. "P - John Smith") — fall through to multiline

    # ── Multiline format ──────────────────────────────────────────────────────
    # The first line carries the action token and customer name.
    # Subsequent lines carry address, city/state, container size, etc.
    #
    # Examples handled:
    #   ["4. P - John Smith",  "5678 Tidewater Dr, Virginia Beach VA", "10yd"]
    #   ["1. D - Mary Jones",  "123 Main St, Norfolk, VA 23510",       "20yd"]
    #   ["John Smith",         "5678 Tidewater Dr",                    "10yd"]
    parts_ml   = [p.strip() for p in stripped_first.split(" - ")]
    first_tok  = parts_ml[0].upper() if parts_ml else ""
    action_tok = _ACTION_TOKENS.get(first_tok, "")

    if action_tok:
        # "P - John Smith" → action=Pickup, customer_name="John Smith"
        customer_name = " - ".join(parts_ml[1:]).strip() if len(parts_ml) > 1 else ""
    else:
        customer_name = stripped_first

    address          = ""
    address_line_raw = ""          # original line as it appears in cleaned_lines
    city = state = zip_code = ""
    action           = action_tok or ""
    container_size   = ""
    ticket_number    = ""
    reference_number = ""

    # Find the first subsequent line that looks like a street address
    address_index = None
    for i in range(1, len(cleaned_lines)):
        if looks_like_address(cleaned_lines[i]):
            address_line_raw = cleaned_lines[i]
            address          = cleaned_lines[i]
            address_index    = i
            break

    # Try city/state/zip from the address line itself
    if address:
        csz = extract_city_state_zip(address)
        if any(csz):
            city, state, zip_code = csz
        else:
            # Handle "5678 Main St, Virginia Beach VA" where state has no leading comma
            m = re.search(r",\s*(.+?)\s+([A-Z]{2})\s*(\d{5})?$", address)
            if m:
                city     = m.group(1).strip()
                state    = m.group(2).strip()
                zip_code = (m.group(3) or "").strip()
                address  = address[:m.start()].strip()

    # Also check the line immediately after the address for standalone city/state
    if address_index is not None and not city:
        nxt = address_index + 1
        if nxt < len(cleaned_lines):
            csz = extract_city_state_zip(cleaned_lines[nxt])
            if any(csz):
                city, state, zip_code = csz

    # Scan all continuation lines for action, size, ticket, ref
    for line in cleaned_lines[1:]:
        if not action:
            found_action = extract_action(line)
            if found_action:
                action = found_action
        if not container_size:
            found_size = extract_container_size(line)
            if found_size:
                container_size = found_size
        if not ticket_number:
            found_ticket = extract_ticket(line)
            if found_ticket:
                ticket_number = found_ticket
        if not reference_number:
            mo = re.search(r"(?:po|ref)\s*#?:?\s*([A-Za-z0-9\-\/]+)", line, re.IGNORECASE)
            if mo:
                reference_number = mo.group(1).strip()

    if not action:
        action = "Service"

    # Notes: only lines that are genuinely extra (not address, not pure size/action)
    extra_lines = []
    for line in cleaned_lines[1:]:
        # Skip the original address line (before or after city stripping)
        if line == address_line_raw or line == address:
            continue
        # Skip standalone city/state/zip lines
        if city and state and city.lower() in line.lower() and state in line:
            continue
        # Skip lines that are only a container size ("10yd", "10", "20 yd")
        if re.match(r"^\d{1,2}\s*(?:yd|yard|yards)?$", line, re.IGNORECASE):
            continue
        # Skip bare action tokens
        if line.upper() in _ACTION_TOKENS:
            continue
        extra_lines.append(line)

    notes = "\n".join(extra_lines).strip()

    # Confidence scoring for legacy block stops
    _conf = 10  # base: we had to guess at stop boundaries
    _conf += 20 if address        else 0
    _conf += 15 if city           else 0
    _conf += 10 if customer_name  else 0
    _conf += 15 if container_size else 0
    _conf += 10 if action and action != "Service" else 0
    _conf  = min(100, _conf)
    _conf_label = "high" if _conf >= 75 else ("medium" if _conf >= 45 else "low")

    return {
        "stop_order":            order_num,
        "original_line":         cleaned_lines[0] if cleaned_lines else "",
        "customer_name":         customer_name,
        "address":               address,
        "city":                  city,
        "state":                 state,
        "zip_code":              zip_code,
        "action":                action,
        "container_size":        container_size,
        "ticket_number":         ticket_number,
        "reference_number":      reference_number,
        "phone":                 "",
        "dump_location":         "",
        "notes":                 notes,
        "relocate_from_address": "",
        "relocate_to_address":   "",
        "confidence":            _conf,
        "confidence_label":      _conf_label,
    }


# ─── Work-order format parser (PR / P / D prefix lines) ───────────────────────

# Maps work-order code → dumpster action
_WO_ACTION = {"PR": "Pickup and Return", "P": "Pull", "D": "Delivery"}


def _is_wo_line(line):
    """Return 'PR', 'P', or 'D' if line starts with a work-order prefix, else None.

    Work-order lines look like: 'P 1233 Westover Ave, Norfolk, VA, ...'
    They do NOT look like dash-delimited: 'P - John Smith' or '4. P - John Smith'.
    The (?!-) lookahead guards against the dash-delimited case.
    """
    m = re.match(r"^(PR|P|D)\s+(?!-)", line, re.IGNORECASE)
    return m.group(1).upper() if m else None


def _parse_wo_line(line, order_num):
    """
    Parse one work-order / boss-style stop line.

    Supports two variants:
      Boss format (no state field):
        TYPE ADDRESS, CITY, CUSTOMER SIZEyd [dump SITE]
        D 2431 Southern Pines Dr, Chesapeake, Roof Joe 20yd
        P 211 Marcella Rd, Hampton, Marlyn 30yd dump spivey
        PR 2434 Cromwell Rd, Norfolk, Beck 30yd dump dominion

      WO format (explicit state):
        TYPE ADDRESS, CITY, STATE, CUSTOMER SIZEyd [dump SITE]
        PR 1233 Westover Ave, Norfolk, VA, ringen 30yd dump dominion

    Detection: if the third comma-field is a bare two-letter state code (e.g. "VA")
    treat it as the state and take the fourth field as customer+rest.
    Otherwise there is no state field and the third field is customer+rest directly.
    """
    wo_type = _is_wo_line(line)
    if not wo_type:
        return None

    # Remove the type prefix
    body = re.sub(r"^(PR|P|D)\s+", "", line, flags=re.IGNORECASE).strip()

    # Split on ", " — up to 3 splits → at most 4 parts
    parts   = body.split(", ", 3)
    address = parts[0].strip() if len(parts) > 0 else ""
    city    = parts[1].strip() if len(parts) > 1 else ""

    # Detect whether parts[2] is a bare state code or already the customer+rest
    _p2 = parts[2].strip() if len(parts) > 2 else ""
    if re.match(r"^[A-Z]{2}$", _p2):
        # Explicit state: ADDRESS, CITY, STATE, CUSTOMER+rest
        state = _p2
        rest  = parts[3].strip() if len(parts) > 3 else ""
    else:
        # Boss format (no state): ADDRESS, CITY, CUSTOMER+rest
        state = ""
        rest  = _p2

    customer_name  = ""
    container_size = ""
    dump_location  = ""
    notes          = ""

    if rest:
        # Extract container size first (e.g. "30yd" or "20 yd")
        size_m = re.search(r"\b(\d{1,2})\s*yd\b", rest, re.IGNORECASE)
        if size_m:
            container_size = size_m.group(1)
            # Customer name = everything before the size match (handles multi-word names)
            customer_name = rest[:size_m.start()].strip()
        else:
            # No size — strip dump phrase and use the remainder as name
            customer_name = re.sub(
                r"\bdump\s+\w+\b", "", rest, flags=re.IGNORECASE
            ).strip()

        # Extract dump location into dump_location field
        dump_m = re.search(r"\bdump\s+(\w+)", rest, re.IGNORECASE)
        if dump_m:
            dump_key      = dump_m.group(1).lower()
            dump_location = _DUMP_SITES.get(dump_key, dump_m.group(1).title())

        # Notes = remainder after stripping customer name, size, and dump phrase
        notes_body = rest[len(customer_name):].strip()
        notes_body = re.sub(r"\b\d{1,2}\s*yd\b",    "", notes_body, flags=re.IGNORECASE)
        notes_body = re.sub(r"\bdump\s+\w+\b",       "", notes_body, flags=re.IGNORECASE)
        notes      = re.sub(r"\s+", " ", notes_body).strip()

    # Confidence scoring for work-order stops
    _conf = 30  # base: structured format gives us action implicitly
    _conf += 20 if address        else 0
    _conf += 15 if city           else 0
    _conf += 10 if customer_name  else 0
    _conf += 15 if container_size else 0
    _conf += 10 if dump_location  else 0
    _conf = min(100, _conf)
    _conf_label = "high" if _conf >= 75 else ("medium" if _conf >= 45 else "low")

    return {
        "stop_order":            order_num,
        "original_line":         None,
        "wo_type":               wo_type,
        "customer_name":         customer_name,
        "address":               address,
        "city":                  city,
        "state":                 state,
        "zip_code":              "",
        "action":                _WO_ACTION.get(wo_type, "Service"),
        "container_size":        container_size,
        "ticket_number":         "",
        "reference_number":      "",
        "dump_location":         dump_location,
        "notes":                 notes,
        "relocate_from_address": "",
        "relocate_to_address":   "",
        "confidence":            _conf,
        "confidence_label":      _conf_label,
    }


def _parse_workorder_format(lines):
    """
    Parse lines in PR/P/D work-order format.
    Returns (stops_list, dump_site_str).
    - Lines starting with PR/P/D become stops.
    - 'Dump: <name>' sets the route-level dump site.
    - All other lines (driver name, blank headers) are ignored.
    """
    stops     = []
    dump_site = ""
    order_num = 1

    for line in lines:
        if not line:
            continue

        # "Dump: Dominion Landfill" → route-level dump site, not a stop
        dm = re.match(r"^dump\s*:\s*(.+)$", line, re.IGNORECASE)
        if dm:
            dump_site = dm.group(1).strip()
            continue

        wo_type = _is_wo_line(line)
        if wo_type:
            stop = _parse_wo_line(line, order_num)
            if stop:
                stops.append(stop)
                order_num += 1
        # else: non-stop header line (driver name, notes, etc.) → skip

    return stops, dump_site


# ─── Roll-off shorthand dispatch parser ───────────────────────────────────────
#
# Handles the boss's compressed single-line format, e.g.:
#   Pr 5660 lowery rd,orf, jaswal
#   30yd dump dominion
#
#   Pull 280 benton rd,suff, power bolt 20yd dump dominion and take to yard empty
#   Del  2008 seafarer cove,vb, decor 20yd place on right hand side of driveway
#   Pr   4333 Indian river rd,ches, Doyle 30yd dump dominion then do the two at lowery

# Roll-off action prefix → canonical action label
_ROLLOFF_PREFIXES = {
    "PR":       "Pickup and Return",
    "PULL":     "Pull",
    "DEL":      "Delivery",
    "DELIVERY": "Delivery",
    "D":        "Delivery",
    "P":        "Pull",
    "RELOCATE": "Relocate",
    "RELOC":    "Relocate",
    "R":        "Relocate",
}

# City shorthand codes (Hampton Roads / Tidewater Virginia)
_CITY_CODES = {
    "orf":   ("Norfolk",        "VA"),
    "norf":  ("Norfolk",        "VA"),
    "vb":    ("Virginia Beach", "VA"),
    "nb":    ("Virginia Beach", "VA"),
    "suff":  ("Suffolk",        "VA"),
    "ches":  ("Chesapeake",     "VA"),
    "port":  ("Portsmouth",     "VA"),
    "ports": ("Portsmouth",     "VA"),
    "prt":   ("Portsmouth",     "VA"),
    "smith": ("Smithfield",     "VA"),
    "hamp":  ("Hampton",        "VA"),
    "nn":    ("Newport News",   "VA"),
    "york":  ("Yorktown",       "VA"),
    "isle":  ("Isle of Wight",  "VA"),
}

# Dump site short names → canonical display names
_DUMP_SITES = {
    "dominion": "Dominion",
    "dom":      "Dominion",
    "bay":      "Bay",
    "holland":  "Holland",
    "holl":     "Holland",
    "spsa":     "SPSA",
    "spivey":   "Spivey",
    "cox":      "SB Cox",
    "sb":       "SB Cox",
    "united":   "United",
    "waterway": "Waterway",
    "wat":      "Waterway",
    "sykes":    "Sykes",
    "mm":       "MM GU2737",
}

# Canonical dump site display name → full street address for navigation.


# Matches a new roll-off stop line: action prefix followed by a house number.
# Uses (?=\d) lookahead so the digit is NOT consumed — m.end() lands right
# before the house number and body = merged[m.end():] keeps the full address.
_ROLLOFF_LINE_RE = re.compile(r"^(PR|PULL|DEL|DELIVERY|RELOCATE|RELOC|D|P|R)\s+(?=\d)", re.IGNORECASE)

# Matches the city-shorthand pattern that confirms roll-off format
_ROLLOFF_CITY_RE = re.compile(
    r",\s*(orf|norf|vb|nb|suff|ches|port|ports|prt|smith|hamp|nn|york|isle)\s*,",
    re.IGNORECASE
)

# Instruction phrases that signal the start of driver notes (not customer name)
_ROLLOFF_NOTES_RE = re.compile(
    r"\b(?:"
    r"take\s+to"
    r"|and\s+take"
    r"|place\s+on"
    r"|place\s+in"
    r"|put\s+on"
    r"|put\s+in"
    r"|then\s+do"
    r"|then\s+go"
    r"|then\b"
    r"|with\s+enough"
    r"|with\s+room"
    r"|empty\s+to"
    r"|to\s+end\s+the"
    r"|do\s+the\s+two"
    r"|leave\s"
    r")\b",
    re.IGNORECASE
)


def _is_rolloff_format(lines):
    """Return True if any line looks like a roll-off shorthand stop.

    Requires BOTH an action prefix (Pr/Pull/Del/D/P + house number)
    AND a city shorthand code in comma position (,orf, / ,vb, etc.).
    Both conditions must match the same line.
    """
    for line in lines:
        if _ROLLOFF_LINE_RE.match(line) and _ROLLOFF_CITY_RE.search(line):
            return True
    return False


def _extract_rolloff_dump(text):
    """Find and extract 'dump <site>' from text.
    Returns (canonical_site_name, text_with_phrase_removed).
    """
    m = re.search(r"\bdump\s+(\w+)", text, re.IGNORECASE)
    if not m:
        return "", text
    key  = m.group(1).lower()
    site = _DUMP_SITES.get(key, m.group(1).title())
    cleaned = (text[:m.start()] + " " + text[m.end():]).strip()
    cleaned = re.sub(r"\s+", " ", cleaned)
    return site, cleaned


def _split_rolloff_customer_notes(text):
    """Split 'CustomerName [driver notes]' into (customer_name, notes_text).

    Customer name ends at the first instruction-trigger phrase.
    Examples:
      "jaswal"                                 → ("jaswal", "")
      "power bolt and take to yard empty..."   → ("power bolt", "take to yard empty...")
      "decor place on right hand side..."      → ("decor", "place on right hand side...")
      "Doyle then do the two at lowery..."     → ("Doyle", "then do the two at lowery...")
    """
    text = text.strip()
    if not text:
        return "", ""

    m = _ROLLOFF_NOTES_RE.search(text)
    if not m:
        return text, ""

    customer = text[:m.start()].strip()
    # Strip a trailing " and" connector that bridges to the note
    customer = re.sub(r"\s+and\s*$", "", customer, flags=re.IGNORECASE).strip()

    # Notes begin at trigger; drop a leading "and " if trigger started with it
    notes = text[m.start():].strip()
    notes = re.sub(r"^and\s+", "", notes, flags=re.IGNORECASE)

    return customer, notes


def _parse_rolloff_stop(block_lines, order_num):
    """Parse one roll-off shorthand stop (one or more lines merged).

    Structure after action prefix is stripped:
        STREET_ADDRESS, CITY_CODE, CUSTOMER [SIZEyd] [dump SITE] [notes]

    Returns a stop dict or None if the block can't be parsed.
    """
    # Merge all lines of this block into one string
    merged = " ".join(clean_line(l) for l in block_lines if clean_line(l))

    m = _ROLLOFF_LINE_RE.match(merged)
    if not m:
        return None

    prefix = m.group(1).upper()
    action = _ROLLOFF_PREFIXES.get(prefix, "Service")
    body   = merged[m.end():].strip()
    # body: "5660 lowery rd,orf, jaswal 30yd dump dominion and take to yard..."

    # Split at the first two commas to isolate: [street, city_code, customer+rest]
    parts     = body.split(",", 2)
    address   = parts[0].strip()
    city_code = parts[1].strip().lower() if len(parts) > 1 else ""
    rest      = parts[2].strip()         if len(parts) > 2 else ""

    city, state = _CITY_CODES.get(city_code, (city_code.title(), "VA"))

    # Extract container size first (before dump extraction changes text positions)
    container_size = ""
    size_m = re.search(r"\b(\d{1,2})\s*yd\b", rest, re.IGNORECASE)
    if size_m:
        container_size = size_m.group(1)
        rest = (rest[:size_m.start()] + " " + rest[size_m.end():]).strip()
        rest = re.sub(r"\s+", " ", rest)

    # Extract dump site
    dump_site, rest = _extract_rolloff_dump(rest)

    # Split remaining text into customer name and driver notes
    customer_name, instruction_notes = _split_rolloff_customer_notes(rest)

    # Confidence scoring for rolloff stops
    _conf = 30  # base: we know action+address from the line structure
    _conf += 20 if address   else 0
    _conf += 15 if city      else 0
    _conf += 15 if container_size else 0
    _conf += 10 if customer_name  else 0
    _conf += 10 if dump_site      else 0
    _conf = min(100, _conf)
    _conf_label = "high" if _conf >= 75 else ("medium" if _conf >= 45 else "low")

    return {
        "stop_order":            order_num,
        "original_line":         " ".join(block_lines),
        "customer_name":         customer_name,
        "address":               address,
        "city":                  city,
        "state":                 state,
        "zip_code":              "",
        "action":                action,
        "container_size":        container_size,
        "ticket_number":         "",
        "reference_number":      "",
        "phone":                 "",
        "dump_location":         dump_site,
        "notes":                 instruction_notes,
        "relocate_from_address": "",
        "relocate_to_address":   "",
        "confidence":            _conf,
        "confidence_label":      _conf_label,
    }


def _parse_rolloff_shorthand(lines):
    """Parse a full roll-off shorthand dispatch text.

    Returns (stops_list, dump_site_str).
    Each stop begins with an action-prefix line (Pr/Pull/Del/D/P + house number).
    Continuation lines (e.g. '30yd dump dominion') are merged into the preceding stop.
    Blank lines and new action lines both flush the current stop block.
    """
    stops       = []
    order_num   = 1
    current_block = []

    for line in lines:
        if not line:
            # Blank line: flush current block
            if current_block:
                stop = _parse_rolloff_stop(current_block, order_num)
                if stop:
                    stops.append(stop)
                    order_num += 1
                current_block = []
            continue

        if _ROLLOFF_LINE_RE.match(line):
            # New action line: flush previous block
            if current_block:
                stop = _parse_rolloff_stop(current_block, order_num)
                if stop:
                    stops.append(stop)
                    order_num += 1
            current_block = [line]
        elif current_block:
            # Continuation line (size / dump info) — belongs to current stop
            current_block.append(line)
        # Lines before any stop (header text) are dropped

    # Flush final block
    if current_block:
        stop = _parse_rolloff_stop(current_block, order_num)
        if stop:
            stops.append(stop)

    return stops, ""


# ─── Inline shorthand (freeform, no commas) ───────────────────────────────────
#
# Handles: ACTION HOUSE_NUM STREET [CITY_CODE] [CUSTOMER] [SIZEyd] [dump SITE]
# Example: Pull 4915 Broad St vb rhr 30yd dump dominion
#          R 7801 Shore Dr norf smith 20yd dump dominion
#
# Differs from roll-off: NO commas required. City code is space-separated.

_INLINE_PREFIX_RE = re.compile(
    r"^(PR|PULL|DEL|DELIVERY|RELOCATE|RELOC|P|D|R)\s+(?=\d)",
    re.IGNORECASE,
)


def _is_inline_shorthand(lines):
    """Return True when any line has an action prefix + house number, no commas, and
    a known city shorthand code somewhere on the line."""
    for line in lines:
        if _INLINE_PREFIX_RE.match(line) and "," not in line:
            for code in _CITY_CODES:
                if re.search(r'\b' + re.escape(code) + r'\b', line, re.IGNORECASE):
                    return True
    return False


def _parse_inline_stop(line, order_num):
    """
    Parse one inline-shorthand line.
    Structure: ACTION  HOUSE_NUM STREET [CITY_CODE] [CUSTOMER] [SIZEyd] [dump SITE] [notes]
    """
    m = _INLINE_PREFIX_RE.match(line)
    if not m:
        return None
    prefix = m.group(1).upper()
    action = _ROLLOFF_PREFIXES.get(prefix, "Service")
    body   = line[m.end():].strip()

    # 1. Extract container size
    container_size = ""
    sz = re.search(r'\b(\d{1,2})\s*yd\b', body, re.IGNORECASE)
    if sz:
        container_size = sz.group(1)
        body = re.sub(r'\s+', ' ', (body[:sz.start()] + " " + body[sz.end():])).strip()

    # 2. Extract dump site
    dump_location = ""
    dm = re.search(r'\bdump\s+(\w+)', body, re.IGNORECASE)
    if dm:
        key = dm.group(1).lower()
        dump_location = _DUMP_SITES.get(key, dm.group(1).title())
        body = re.sub(r'\s+', ' ', (body[:dm.start()] + " " + body[dm.end():])).strip()

    # 3. Find and remove city code
    city = state = ""
    for code, (city_name, state_code) in _CITY_CODES.items():
        mc = re.search(r'\b' + re.escape(code) + r'\b', body, re.IGNORECASE)
        if mc:
            city  = city_name
            state = state_code
            body  = re.sub(r'\s+', ' ', (body[:mc.start()] + " " + body[mc.end():])).strip()
            break

    # 4. Split remaining "HOUSE_NUM STREET [CUSTOMER notes]" at last street suffix
    address = customer_name = notes = ""
    house_m = re.match(r'\d+\s+', body)
    if house_m:
        sfx_m = None
        for sfx in _STREET_SFX_RE.finditer(body):
            sfx_m = sfx
        if sfx_m:
            address = body[:sfx_m.end()].strip()
            rest    = body[sfx_m.end():].strip()
        else:
            # No street suffix: first 4 tokens → address, rest → customer
            words   = body.split()
            n       = min(4, len(words))
            address = " ".join(words[:n])
            rest    = " ".join(words[n:])
        customer_name, notes = _split_rolloff_customer_notes(rest)
    else:
        customer_name = body

    # Confidence scoring for inline-shorthand stops
    _addr    = address.strip()
    _cust    = customer_name.strip()
    _conf    = 30  # base: action prefix detected
    _conf   += 20 if _addr          else 0
    _conf   += 15 if city           else 0
    _conf   += 15 if container_size else 0
    _conf   += 10 if _cust          else 0
    _conf   += 10 if dump_location  else 0
    _conf    = min(100, _conf)
    _conf_label = "high" if _conf >= 75 else ("medium" if _conf >= 45 else "low")

    return {
        "stop_order":            order_num,
        "original_line":         None,
        "customer_name":         _cust,
        "address":               _addr,
        "city":                  city,
        "state":                 state,
        "zip_code":              "",
        "action":                action,
        "container_size":        container_size,
        "ticket_number":         "",
        "reference_number":      "",
        "dump_location":         dump_location,
        "notes":                 notes.strip(),
        "relocate_from_address": "",
        "relocate_to_address":   "",
        "confidence":            _conf,
        "confidence_label":      _conf_label,
    }


def _parse_inline_shorthand(lines):
    """Parse all inline-shorthand stops from a line list. Returns (stops, "")."""
    stops     = []
    order_num = 1
    for line in lines:
        if not line:
            continue
        stop = _parse_inline_stop(line, order_num)
        if stop and (stop["address"] or stop["customer_name"]):
            stops.append(stop)
            order_num += 1
    return stops, ""


# ─── Relocate from/to parser ──────────────────────────────────────────────────
# Matches: "relocate [can] <from_address> to <to_address> [size] [dump site]"
_RELOCATE_TO_RE = re.compile(
    r"^(?:relocate|reloc|move\s+can)\s+(.+?)\s+to\s+(.+)$",
    re.IGNORECASE,
)


def _parse_relocate_line(raw, order_num=1):
    """
    Parse a relocate-style line:
      relocate can 222 industrial rd norf to 333 yard st norf 30yd
      relocate 100 main st vb to 200 back lot vb 20yd dump dominion

    Returns a stop dict with:
      - action = "Relocate"
      - address = from_address (primary, shown on stop card)
      - relocate_from_address = same as address
      - relocate_to_address  = destination address
      - can_size, dump_location, city/state from from_address side
      - notes = "From: <from> → To: <to>" for driver reference
    Returns None if the pattern does not match.
    """
    work = raw.strip()
    # Strip leading "can" after relocate keyword so the address starts at house #
    work = re.sub(r"^(relocate|reloc|move\s+can)\s+can\s+", r"\1 ", work, flags=re.I)
    m = _RELOCATE_TO_RE.match(work)
    if not m:
        return None

    from_raw = m.group(1).strip()
    to_raw   = m.group(2).strip()

    def _extract_fields(text):
        """Pull size, dump site, and city from an address fragment."""
        sz = ""
        sz_m = re.search(r"\b(\d{1,2})\s*yd\b", text, re.I)
        if sz_m:
            sz   = sz_m.group(1)
            text = re.sub(r"\s+", " ", text[:sz_m.start()] + " " + text[sz_m.end():]).strip()

        dump = ""
        # Two-word dump first
        for phrase, fullname in _TWO_WORD_DUMP_MAP.items():
            if re.search(r"(?:^|\s)" + re.escape(phrase) + r"(?:\s|$)", text, re.I):
                dump = fullname
                text = re.sub(re.escape(phrase), "", text, flags=re.I)
                text = re.sub(r"\s+", " ", text).strip()
                break
        if not dump:
            dm = re.search(r"\bdump\s+(\w+)", text, re.I)
            if dm:
                dump = _DUMP_SITES.get(dm.group(1).lower(), dm.group(1).title())
                text = re.sub(r"\s+", " ", text[:dm.start()] + " " + text[dm.end():]).strip()

        city = state = ""
        for code, (city_name, state_code) in _CITY_CODES.items():
            mc = re.search(r"(?:(?<=\s)|^)" + re.escape(code) + r"(?=\s|$)", text, re.I)
            if mc:
                city  = city_name
                state = state_code
                text  = re.sub(r"\s+", " ", text[:mc.start()] + " " + text[mc.end():]).strip()
                break
        return text.strip(), sz, dump, city, state

    from_addr, from_sz, from_dump, from_city, from_state = _extract_fields(from_raw)
    to_addr,   to_sz,   to_dump,   to_city,   _          = _extract_fields(to_raw)

    # Prefer size / dump from whichever side had them; from-side wins ties
    container_size = from_sz   or to_sz
    dump_location  = from_dump or to_dump
    city           = from_city or to_city
    state          = from_state

    # Build driver-facing note
    notes = f"From: {from_addr} → To: {to_addr}"
    if to_city:
        notes = f"From: {from_addr} ({from_city}) → To: {to_addr} ({to_city})"

    return {
        "stop_order":            order_num,
        "original_line":         raw,
        "customer_name":         "",
        "address":               from_addr,
        "city":                  city,
        "state":                 state,
        "zip_code":              "",
        "action":                "Relocate",
        "container_size":        container_size,
        "ticket_number":         "",
        "reference_number":      "",
        "dump_location":         dump_location,
        "notes":                 notes,
        "relocate_from_address": from_addr,
        "relocate_to_address":   to_addr,
        "confidence":            75,
        "confidence_label":      "high",
    }


# ─── Top-level parser dispatcher ──────────────────────────────────────────────

def _is_relocate_format(lines):
    """Return True when ALL non-empty lines are relocate-style (relocate X to Y)."""
    return (
        lines
        and all(_RELOCATE_TO_RE.match(l) for l in lines)
    )


def parse_boss_text(raw_text):
    """
    Parse pasted route text into (stops_list, dump_site_str).

    Format detection priority:
      1. Roll-off shorthand  — boss compressed format (Pr/Pull/Del + comma city code)
      2. Work-order format   — PR/P/D with full address, city, state, customer
      3. Relocate from/to    — "relocate can X to Y"
      4. Inline shorthand    — action + house number + space-separated city code (no commas)
      5. Numbered/dash-delimited legacy format
    """
    lines          = [clean_line(x) for x in raw_text.splitlines()]
    lines_nonempty = [l for l in lines if l]

    detected_format = "unknown"

    if _is_rolloff_format(lines_nonempty):
        detected_format = "rolloff"
        stops, dump = _parse_rolloff_shorthand(lines)
    elif any(_is_wo_line(l) for l in lines_nonempty):
        detected_format = "workorder"
        stops, dump = _parse_workorder_format(lines_nonempty)
    elif _is_relocate_format(lines_nonempty):
        detected_format = "relocate"
        stops = []
        for idx, line in enumerate(lines_nonempty, start=1):
            stop = _parse_relocate_line(line, idx)
            if stop:
                stops.append(stop)
        dump = ""
    elif _is_inline_shorthand(lines_nonempty):
        detected_format = "inline"
        stops, dump = _parse_inline_shorthand(lines_nonempty)
    else:
        # Legacy numbered-list / dash-delimited fallback.
        # Also try per-line relocate detection inside mixed text.
        detected_format = "legacy"
        blocks = split_into_stop_blocks(raw_text)
        stops  = []
        for idx, block in enumerate(blocks, start=1):
            merged = " ".join(block).strip()
            rel = _parse_relocate_line(merged, idx)
            if rel:
                stops.append(rel)
                continue
            stop = parse_stop_block(block, idx)
            if stop["customer_name"] or stop["address"]:
                stops.append(stop)
        dump = ""

    # ── Debug logging (visible in Flask dev logs / gunicorn stderr) ──────────
    app.logger.debug(
        "[parse_boss_text] format=%s  stops=%d",
        detected_format, len(stops)
    )
    for i, s in enumerate(stops, start=1):
        unmatched = []
        if not s.get("address"):
            unmatched.append("address")
        if not s.get("action"):
            unmatched.append("action")
        if not s.get("container_size"):
            unmatched.append("size")
        app.logger.debug(
            "  stop %d | conf=%s(%s) | cust=%r addr=%r city=%r "
            "action=%r size=%r dump=%r | unmatched=%s | raw=%r",
            i,
            s.get("confidence", "?"),
            s.get("confidence_label", "?"),
            s.get("customer_name", ""),
            s.get("address", ""),
            s.get("city", ""),
            s.get("action", ""),
            s.get("container_size", ""),
            s.get("dump_location", ""),
            unmatched or "none",
            (s.get("original_line") or "")[:80],
        )

    return stops, dump

# =========================================================
# LOAD SCORING / AI SIDE
# =========================================================
def parse_money(value):
    value = (value or "").replace(",", "").replace("$", "").strip()
    if not value:
        return 0.0
    try:
        return float(value)
    except ValueError:
        return 0.0


def estimate_miles(origin, destination):
    # lightweight placeholder estimation when miles are not provided
    text = f"{origin} {destination}".lower()
    base = 120
    if "virginia beach" in text and "richmond" in text:
        return 110
    if "norfolk" in text and "atlanta" in text:
        return 560
    if "chesapeake" in text and "charlotte" in text:
        return 330
    if origin and destination:
        token_count = len((origin + " " + destination).split())
        return max(base, token_count * 35)
    return 0


def score_load_record(origin, destination, pickup_time, payout, miles):
    if not miles or miles <= 0:
        miles = estimate_miles(origin, destination)

    rpm = payout / miles if miles > 0 else 0
    estimated_cost = miles * 1.35
    estimated_profit = payout - estimated_cost

    score = 0
    score += min(rpm * 25, 50)
    score += 20 if estimated_profit > 500 else max(estimated_profit / 25, 0)

    pickup_bonus = 0
    pickup_lower = (pickup_time or "").lower()
    if "am" in pickup_lower:
        pickup_bonus += 8
    elif "pm" in pickup_lower:
        pickup_bonus += 4
    score += pickup_bonus

    if miles <= 200:
        score += 18
    elif miles <= 400:
        score += 12
    elif miles <= 650:
        score += 7
    else:
        score += 2

    score = round(min(score, 100), 1)
    return {
        "miles": round(miles, 1),
        "estimated_profit": round(estimated_profit, 2),
        "score": score,
        "rpm": round(rpm, 2)
    }


def parse_load_input_line(line):
    raw = line.strip()
    if not raw:
        return None

    parts = [x.strip() for x in raw.split("/")]
    route_part = parts[0] if parts else ""
    pickup_time = parts[1] if len(parts) > 1 else ""
    payout = parse_money(parts[2]) if len(parts) > 2 else 0.0
    miles = parse_money(parts[3]) if len(parts) > 3 else 0.0

    if ">" in route_part:
        origin, destination = [x.strip() for x in route_part.split(">", 1)]
    elif " to " in route_part.lower():
        split_match = re.split(r"\bto\b", route_part, maxsplit=1, flags=re.IGNORECASE)
        origin = split_match[0].strip()
        destination = split_match[1].strip() if len(split_match) > 1 else ""
    else:
        origin, destination = route_part.strip(), ""

    calc = score_load_record(origin, destination, pickup_time, payout, miles)

    return {
        "origin": origin,
        "destination": destination,
        "pickup_time": pickup_time,
        "payout": payout,
        "miles": calc["miles"],
        "estimated_profit": calc["estimated_profit"],
        "score": calc["score"],
        "notes": f"RPM: {calc['rpm']}"
    }


# =========================================================
# UI SHELL
# =========================================================
def nav_link(href, label, current_path):
    active = "active" if current_path == href else ""
    return f'<a class="nav-item {active}" href="{href}">{label}</a>'


def shell_page(title, body, extra_head=""):
    user = get_current_user()
    path = request.path

    sidebar = ""
    if user:
        # resolve company name for sidebar display
        _co_name = ""
        if user["company_id"]:
            _co_conn = get_db()
            _co_row = _co_conn.execute(
                "SELECT name, subscription_plan FROM companies WHERE id=?",
                (user["company_id"],)
            ).fetchone()
            _co_conn.close()
            if _co_row:
                _co_name = _co_row["name"]
                _co_plan = _co_row["subscription_plan"].title()

        boss_only = ""
        if user["role"] == "boss":
            boss_only = """
    {boss_panel}
    {orders}
    {users}
    {dump_locs}
    {containers}
    {driver_hours}
    {co_settings}
    {subscription}
""".format(
    boss_panel=nav_link(url_for("boss_dashboard"), "📊 Boss Panel", path),
    orders=nav_link(url_for("orders_page"), "🧾 Orders", path),
    users=nav_link(url_for("manage_users"), "👥 Users", path),
    dump_locs=nav_link(url_for("dump_locations_page"), "🗑 Dump Locations", path),
    containers=nav_link(url_for("containers_page"), "📦 Containers", path),
    driver_hours=nav_link(url_for("driver_hours_page"), "⏱ Driver Hours", path),
    co_settings=nav_link(url_for("company_settings"), "⚙ Company Settings", path),
    subscription=nav_link(url_for("company_subscription"), "💳 Subscription", path),
)

        superadmin_link = nav_link(url_for("superadmin_panel"), "🔧 Superadmin", path) \
            if session.get("is_superadmin") else ""

        co_badge = (f'<div class="muted small" style="margin-bottom:4px;">'
                    f'{e(_co_name)}</div>') if _co_name else ""

        sidebar = f"""
        <aside class="sidebar">
            <div class="logo-card">
                <div class="logo-wordmark">
                    <span class="logo-h">H</span><span class="logo-rest">AULTRA</span>
                </div>
                <div class="logo-sub">AI DISPATCH SYSTEMS</div>
            </div>
            {co_badge}
            <div class="sidebar-user">
                <span class="sidebar-user-dot"></span>
                {e(user['username'] if user else '')}
                <span class="sidebar-role-badge">{e(user['role'] if user else '')}</span>
            </div>
            <nav class="nav-stack">
                {nav_link(url_for('dashboard'), '⬡ Dashboard', path)}
                {nav_link(url_for('driver_dashboard'), '◈ My Routes', path) if user['role'] == 'driver' else ''}
                {nav_link(url_for('driver_clock'), '⏱ Clock In/Out', path) if user['role'] == 'driver' else ''}
                {nav_link(url_for('routes_page'), '◈ Routes', path) if user['role'] == 'boss' else ''}
                {nav_link(url_for('drivers_page'), '◉ Drivers', path) if user['role'] == 'boss' else ''}
                {boss_only}
                {superadmin_link}
                <form method="POST" action="{url_for('logout')}" style="margin:0;padding:0;margin-top:8px;">
                    <button type="submit" class="nav-item nav-logout">⏻ Logout</button>
                </form>
            </nav>
        </aside>
        """

    from flask import get_flashed_messages
    flashes = get_flashed_messages(with_categories=True)
    messages_html = "".join(
        f'<div class="flash {e(category)}">{e(msg)}</div>' for category, msg in flashes
    )

    csrf_token = get_csrf_token()

    return f"""
    <!doctype html>
    <html>
   <head>
    <title>{e(title)}</title>
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <meta name="csrf-token" content="{csrf_token}">

    <link rel="apple-touch-icon" href="/static/logo.png">

    {extra_head}
     <style>
/* ═══════════════════════════════════════════════════════════
   HAULTRA AI — ROCKKSTAAR COMMAND CENTER THEME
   ═══════════════════════════════════════════════════════════ */

/* ── Reset ─────────────────────────────────────────────────*/
*, *::before, *::after {{ box-sizing: border-box; margin: 0; padding: 0; }}

/* ── Design Tokens ─────────────────────────────────────────*/
:root {{
  --bg:          #02040a;
  --bg-card:     rgba(6,11,22,0.92);
  --bg-sidebar:  #040710;
  --border:      rgba(0,160,255,0.10);
  --border-glow: rgba(0,200,255,0.28);
  --cyan:        #00ccff;
  --cyan-dim:    rgba(0,200,255,0.12);
  --gold:        #ff9d00;
  --gold-dim:    rgba(255,157,0,0.12);
  --green:       #00e87d;
  --red:         #ff3b5c;
  --text:        #e8f2ff;
  --text-muted:  #3d5a74;
  --text-soft:   #7a9ab8;
  --radius:      12px;
  --radius-lg:   16px;
}}

/* ── Base ───────────────────────────────────────────────────*/
html {{ background: var(--bg); scroll-behavior: smooth; }}

html, body {{
    width: 100%; min-height: 100%; overflow-x: hidden;
}}

body {{
    font-family: 'Inter', 'SF Pro Display', -apple-system, 'Segoe UI', Arial, sans-serif;
    font-size: 14px;
    line-height: 1.5;
    color: var(--text);
    background: var(--bg);
    /* cinematic deep-space backdrop */
    background-image:
        radial-gradient(ellipse 100% 60% at 20% -5%,  rgba(0,140,255,0.055) 0%, transparent 65%),
        radial-gradient(ellipse  60% 40% at 85% 100%, rgba(255,120,0,0.030) 0%, transparent 65%),
        radial-gradient(ellipse  40% 30% at 50%  50%, rgba(0,0,20,0.8) 0%, transparent 100%);
    background-attachment: fixed;
}}

a {{ color: var(--cyan); text-decoration: none; transition: color .15s; }}
a:hover {{ color: #66dfff; }}

/* ── App Shell ──────────────────────────────────────────────*/
.app-shell {{ display: flex; min-height: 100vh; width: 100%; }}

/* ══════════════════════════════════════════════════════════
   SIDEBAR
   ══════════════════════════════════════════════════════════*/
.sidebar {{
    width: 234px;
    min-width: 234px;
    background: var(--bg-sidebar);
    border-right: 1px solid var(--border);
    display: flex;
    flex-direction: column;
    position: sticky;
    top: 0;
    height: 100vh;
    overflow-y: auto;
    /* inner glow column */
    box-shadow: inset -1px 0 0 rgba(0,180,255,0.05), 1px 0 20px rgba(0,0,0,0.4);
}}

/* ── Logo ───────────────────────────────────────────────────*/
.logo-card {{
    padding: 22px 20px 16px;
    border-bottom: 1px solid rgba(0,160,255,0.07);
}}

.logo-wordmark {{
    display: flex;
    align-items: baseline;
    gap: 1px;
    line-height: 1;
}}

.logo-icon {{
    font-size: 11px;
    font-weight: 900;
    letter-spacing: 1px;
    color: var(--gold);
    background: linear-gradient(135deg, #ff9d00, #ffcc44);
    -webkit-background-clip: text;
    -webkit-text-fill-color: transparent;
    background-clip: text;
    margin-right: 6px;
    opacity: 0.85;
}}

.logo-h {{
    font-size: 20px;
    font-weight: 900;
    letter-spacing: 3px;
    background: linear-gradient(130deg, #ffffff 0%, #7dd3fc 60%, #00ccff 100%);
    -webkit-background-clip: text;
    -webkit-text-fill-color: transparent;
    background-clip: text;
    text-shadow: none;
    filter: drop-shadow(0 0 12px rgba(0,200,255,0.35));
}}

.logo-rest {{
    font-size: 20px;
    font-weight: 900;
    letter-spacing: 3px;
    color: #c8dff4;
    background: linear-gradient(130deg, #ffffff 0%, #7dd3fc 60%, #00ccff 100%);
    -webkit-background-clip: text;
    -webkit-text-fill-color: transparent;
    background-clip: text;
}}

.logo-sub {{
    font-size: 8.5px;
    font-weight: 700;
    letter-spacing: 3.5px;
    color: #1e3a52;
    margin-top: 5px;
    text-transform: uppercase;
}}

/* ── Sidebar user pill ──────────────────────────────────────*/
.sidebar-user {{
    display: flex;
    align-items: center;
    gap: 8px;
    padding: 10px 20px 12px;
    font-size: 12px;
    color: var(--text-soft);
    font-weight: 600;
    border-bottom: 1px solid rgba(0,150,255,0.06);
}}

.sidebar-user-dot {{
    width: 6px; height: 6px;
    border-radius: 50%;
    background: var(--green);
    box-shadow: 0 0 8px var(--green);
    flex-shrink: 0;
}}

.sidebar-role-badge {{
    margin-left: auto;
    font-size: 9.5px;
    font-weight: 700;
    letter-spacing: .6px;
    padding: 2px 8px;
    border-radius: 20px;
    background: var(--cyan-dim);
    border: 1px solid rgba(0,200,255,0.16);
    color: var(--cyan);
    text-transform: uppercase;
}}

/* ── Nav stack ──────────────────────────────────────────────*/
.nav-stack {{
    display: flex;
    flex-direction: column;
    gap: 2px;
    padding: 12px 10px;
    flex: 1;
}}

.nav-item {{
    display: block;
    width: 100%;
    padding: 10px 13px;
    border-radius: 9px;
    background: transparent;
    border: 1px solid transparent;
    color: #4a6880;
    font-weight: 600;
    font-size: 13px;
    letter-spacing: .15px;
    text-decoration: none;
    cursor: pointer;
    text-align: left;
    transition: background .13s, color .13s, border-color .13s;
    position: relative;
}}

.nav-item:hover {{
    background: rgba(0,180,255,0.06);
    border-color: rgba(0,200,255,0.12);
    color: #9ac8e8;
    text-decoration: none;
}}

.nav-item.active {{
    background: linear-gradient(90deg, rgba(0,180,255,0.13) 0%, rgba(0,180,255,0.04) 100%);
    border-color: rgba(0,200,255,0.25);
    color: var(--cyan);
    font-weight: 700;
}}

/* left accent bar on active */
.nav-item.active::before {{
    content: '';
    position: absolute;
    left: 0; top: 20%; bottom: 20%;
    width: 2px;
    border-radius: 2px;
    background: var(--cyan);
    box-shadow: 0 0 8px var(--cyan);
}}

.nav-logout {{
    color: #2e3f50 !important;
    margin-top: 6px;
    border-top: 1px solid rgba(0,150,255,0.05);
    padding-top: 14px !important;
}}

.nav-logout:hover {{
    background: rgba(255,50,50,0.06) !important;
    border-color: rgba(255,60,60,0.12) !important;
    color: #ff6b6b !important;
}}

/* ══════════════════════════════════════════════════════════
   MAIN CONTENT
   ══════════════════════════════════════════════════════════*/
.content {{ flex: 1; padding: 28px 32px; min-width: 0; }}

/* ── Utilities ──────────────────────────────────────────────*/
.muted  {{ color: var(--text-muted); }}
.small  {{ font-size: 12px; }}
.row    {{ display: flex; gap: 10px; flex-wrap: wrap; align-items: center; }}
.between {{ justify-content: space-between; }}

/* ══════════════════════════════════════════════════════════
   HERO SECTION — command center header
   ══════════════════════════════════════════════════════════*/
.hero {{
    position: relative;
    border: 1px solid rgba(0,180,255,0.14);
    border-radius: var(--radius-lg);
    padding: 28px 30px;
    margin-bottom: 22px;
    background: linear-gradient(145deg, rgba(0,14,32,0.97) 0%, rgba(2,6,14,0.99) 100%);
    box-shadow: 0 4px 40px rgba(0,0,0,0.5), inset 0 1px 0 rgba(255,255,255,0.035);
    overflow: hidden;
}}

/* top edge — dual-tone stripe (cyan → gold) */
.hero::before {{
    content: '';
    position: absolute;
    top: 0; left: 0; right: 0;
    height: 1.5px;
    background: linear-gradient(90deg,
        transparent 0%,
        rgba(0,200,255,0.7) 25%,
        rgba(0,200,255,0.9) 45%,
        rgba(255,157,0,0.9) 65%,
        rgba(255,157,0,0.5) 80%,
        transparent 100%);
}}

/* subtle corner glow */
.hero::after {{
    content: '';
    position: absolute;
    top: -40px; right: -40px;
    width: 200px; height: 200px;
    background: radial-gradient(circle, rgba(0,180,255,0.06) 0%, transparent 70%);
    pointer-events: none;
}}

.hero h1 {{
    font-size: 21px;
    font-weight: 800;
    color: #e8f4ff;
    letter-spacing: -.3px;
    margin-bottom: 5px;
    line-height: 1.2;
}}

.hero p {{
    color: var(--text-muted);
    font-size: 13px;
    line-height: 1.55;
}}

/* ══════════════════════════════════════════════════════════
   CARDS
   ══════════════════════════════════════════════════════════*/
.card {{
    background: var(--bg-card);
    border: 1px solid rgba(0,150,255,0.10);
    border-radius: var(--radius-lg);
    padding: 22px;
    margin-bottom: 16px;
    box-shadow: 0 2px 24px rgba(0,0,0,0.35);
}}

.card h2 {{
    font-size: 14px;
    font-weight: 700;
    letter-spacing: .2px;
    color: #7a9ab8;
    text-transform: uppercase;
    margin-bottom: 16px;
}}

/* ── Stat grid ──────────────────────────────────────────────*/
.grid {{
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
    gap: 12px;
    margin-bottom: 20px;
}}

.stat {{
    position: relative;
    background: rgba(0,10,24,0.70);
    border: 1px solid rgba(0,150,255,0.12);
    border-radius: var(--radius);
    padding: 18px 20px 16px;
    overflow: hidden;
    transition: border-color .2s, box-shadow .2s;
}}

.stat:hover {{
    border-color: rgba(0,200,255,0.22);
    box-shadow: 0 0 20px rgba(0,180,255,0.05);
}}

/* bottom cyan underline */
.stat::after {{
    content: '';
    position: absolute;
    bottom: 0; left: 0; right: 0;
    height: 1.5px;
    background: linear-gradient(90deg, transparent, var(--cyan), transparent);
    opacity: 0.30;
}}

.stat .label {{
    font-size: 10px;
    font-weight: 700;
    letter-spacing: 1px;
    text-transform: uppercase;
    color: var(--text-muted);
}}

.stat .num {{
    font-size: 32px;
    font-weight: 800;
    color: #e8f4ff;
    line-height: 1.1;
    margin-top: 6px;
    letter-spacing: -1px;
}}

/* ══════════════════════════════════════════════════════════
   BUTTONS
   ══════════════════════════════════════════════════════════*/
.btn,
button:not(.nav-item):not(.btn-reassign):not([class*="btn-driver"]):not(.compact-select) {{
    display: inline-block;
    border: none;
    cursor: pointer;
    padding: 10px 20px;
    border-radius: 9px;
    font-weight: 700;
    font-size: 13px;
    letter-spacing: .15px;
    text-decoration: none;
    transition: filter .15s, transform .1s, box-shadow .15s;
    /* default = electric cyan */
    color: #020d18;
    background: linear-gradient(135deg, #00d8ff 0%, #0098e8 100%);
    box-shadow: 0 0 18px rgba(0,180,255,0.18);
}}

.btn:hover,
button:not(.nav-item):not(.btn-reassign):not([class*="btn-driver"]):not(.compact-select):hover {{
    filter: brightness(1.1);
    transform: translateY(-1px);
    text-decoration: none;
    color: #020d18;
    box-shadow: 0 0 24px rgba(0,200,255,0.28);
}}

/* secondary — dark glass */
.btn.secondary {{
    background: rgba(10,22,42,0.90);
    border: 1px solid rgba(0,160,255,0.20);
    color: #6ea8cc;
    box-shadow: none;
}}
.btn.secondary:hover {{ color: #a8d8f0; filter: none; border-color: rgba(0,200,255,0.35); }}

/* gold — priority actions */
.btn.gold, .btn.orange {{
    background: linear-gradient(135deg, #ffb830 0%, #ff7d00 100%);
    color: #120800;
    box-shadow: 0 0 18px rgba(255,140,0,0.20);
}}
.btn.gold:hover, .btn.orange:hover {{
    filter: brightness(1.08);
    box-shadow: 0 0 28px rgba(255,140,0,0.32);
    color: #120800;
}}

/* green */
.btn.green {{
    background: linear-gradient(135deg, #00e87d 0%, #00b85e 100%);
    color: #011a0b;
    box-shadow: 0 0 14px rgba(0,232,125,0.16);
}}
.btn.green:hover {{ filter: brightness(1.08); color: #011a0b; }}

/* red / danger */
.btn.red {{
    background: linear-gradient(135deg, #ff3b5c 0%, #cc1a34 100%);
    color: #1a0009;
    box-shadow: none;
}}
.btn.red:hover {{ filter: brightness(1.1); color: #1a0009; }}

/* ── Forms ──────────────────────────────────────────────────*/
form.inline {{ display: inline; }}

label {{
    display: block;
    font-weight: 600;
    font-size: 11px;
    letter-spacing: .5px;
    text-transform: uppercase;
    color: #2e4a62;
    margin-top: 14px;
    margin-bottom: 6px;
}}

input, textarea, select {{
    width: 100%;
    padding: 11px 14px;
    border-radius: 9px;
    border: 1px solid rgba(0,150,255,0.14);
    background: rgba(2,7,18,0.80);
    color: var(--text);
    font-size: 13px;
    font-family: inherit;
    transition: border-color .15s, box-shadow .15s;
}}

input:focus, textarea:focus, select:focus {{
    outline: none;
    border-color: rgba(0,200,255,0.40);
    box-shadow: 0 0 0 3px rgba(0,180,255,0.07);
}}

textarea {{ min-height: 130px; resize: vertical; }}

/* ── Tables ─────────────────────────────────────────────────*/
table {{ width: 100%; border-collapse: collapse; }}

th {{
    padding: 9px 12px;
    border-bottom: 1px solid rgba(0,150,255,0.10);
    text-align: left;
    font-size: 10px;
    font-weight: 700;
    letter-spacing: 1px;
    text-transform: uppercase;
    color: #1e3a52;
}}

td {{
    padding: 12px 12px;
    border-bottom: 1px solid rgba(255,255,255,0.033);
    vertical-align: middle;
    font-size: 13px;
    color: #a8c4dc;
}}

td a {{ color: #7dd3fc; font-weight: 600; }}
td a:hover {{ color: #b8e8ff; }}

tr:hover td {{ background: rgba(0,150,255,0.025); }}
.table-wrap {{ overflow-x: auto; }}

/* ── Badges ─────────────────────────────────────────────────*/
.badge {{
    display: inline-block;
    padding: 3px 10px;
    border-radius: 999px;
    font-size: 10px;
    font-weight: 700;
    letter-spacing: .6px;
    text-transform: uppercase;
}}

.badge.open {{
    background: rgba(0,140,255,0.12);
    border: 1px solid rgba(0,180,255,0.22);
    color: #40b8ff;
}}

.badge.in_progress {{
    background: rgba(255,140,0,0.10);
    border: 1px solid rgba(255,160,0,0.22);
    color: #ffa830;
}}

.badge.completed {{
    background: rgba(0,232,125,0.10);
    border: 1px solid rgba(0,232,125,0.22);
    color: #00e87d;
}}

/* ── Flash messages ─────────────────────────────────────────*/
.flash {{
    padding: 12px 16px;
    border-radius: 9px;
    margin-bottom: 14px;
    font-weight: 600;
    font-size: 13px;
}}
.flash.success {{
    background: rgba(0,80,36,0.38);
    border: 1px solid rgba(0,232,125,0.20);
    color: #5cffa7;
}}
.flash.error {{
    background: rgba(100,10,20,0.45);
    border: 1px solid rgba(255,60,80,0.22);
    color: #ff8a9a;
}}

/* ── Stop cards (boss route view) ───────────────────────────*/
.stop-card {{
    background: rgba(4,10,22,0.82);
    border: 1px solid rgba(0,150,255,0.12);
    border-radius: var(--radius);
    padding: 16px;
    margin-bottom: 10px;
}}

.next-stop-glow {{
    border-color: rgba(0,220,255,0.42);
    box-shadow: 0 0 22px rgba(0,200,255,0.09);
}}

.stop-handle {{
    cursor: grab;
    background: rgba(0,70,140,0.28);
    border: 1px solid rgba(0,160,255,0.16);
    border-radius: 7px;
    padding: 4px 10px;
    display: inline-block;
    margin-right: 8px;
    font-weight: 700;
    font-size: 11px;
    color: var(--cyan);
}}

/* ── Photos ─────────────────────────────────────────────────*/
.photo-thumb {{
    max-width: 160px; max-height: 160px; width: 100%;
    object-fit: cover; border-radius: 8px;
    border: 1px solid rgba(0,160,255,0.18); display: block;
}}
.photo-gallery {{ display: flex; flex-wrap: wrap; gap: 10px; margin-top: 10px; }}
.photo-item {{
    display: flex; flex-direction: column; align-items: center;
    background: rgba(255,255,255,0.025);
    border: 1px solid rgba(0,150,255,0.10);
    border-radius: 9px; padding: 8px; width: 160px;
}}
.photo-meta {{ font-size: 11px; color: #2e4a62; text-align: center; margin-top: 5px; line-height: 1.4; word-break: break-all; }}
.photo-pdf-link {{
    display: flex; align-items: center; justify-content: center;
    width: 140px; height: 80px;
    background: var(--cyan-dim); border: 1px solid rgba(0,200,255,0.18);
    border-radius: 8px; color: var(--cyan); text-decoration: none;
    font-size: 13px; font-weight: 600; gap: 6px;
}}
.photo-pdf-link:hover {{ background: rgba(0,200,255,0.18); }}

/* ── Progress mini bar ──────────────────────────────────────*/
.mini-prog-track {{
    width: 80px; height: 5px;
    background: rgba(255,255,255,0.06);
    border-radius: 3px; overflow: hidden; flex-shrink: 0;
}}
.mini-prog-fill {{
    height: 100%;
    background: linear-gradient(90deg, #0098e8, #00ccff);
    border-radius: 3px; transition: width .4s;
}}

/* ── Inline reassign ────────────────────────────────────────*/
.inline-reassign {{ display: flex; align-items: center; gap: 6px; flex-wrap: nowrap; }}
.compact-select {{
    font-size: 12px; padding: 4px 8px; border-radius: 6px;
    background: rgba(2,7,18,0.82); border: 1px solid rgba(0,150,255,0.16);
    color: #7aa8c8; max-width: 130px;
}}
.btn-reassign {{
    font-size: 12px; padding: 4px 10px; border-radius: 6px;
    background: rgba(0,90,180,0.22); border: 1px solid rgba(0,160,255,0.20);
    color: #7aa8c8; cursor: pointer; white-space: nowrap;
    transition: background .13s;
}}
.btn-reassign:hover {{ background: rgba(0,120,220,0.38); }}
tr.status-in-progress td {{ background: rgba(255,140,0,0.03); }}

/* ── Footer ─────────────────────────────────────────────────*/
.footer-note {{
    text-align: center; color: #162636; font-size: 11px;
    margin-top: 40px; padding: 16px 0 6px;
    border-top: 1px solid rgba(0,150,255,0.05); line-height: 2;
}}
.footer-note a {{ color: #162636; margin: 0 6px; }}
.footer-note a:hover {{ color: var(--cyan); }}
.footer-trust {{ display: flex; justify-content: center; gap: 12px; flex-wrap: wrap; margin-bottom: 8px; }}
.footer-badge {{
    display: inline-flex; align-items: center; gap: 4px;
    font-size: 10px; color: #1a3040;
    background: rgba(255,255,255,0.015);
    border: 1px solid rgba(0,150,255,0.06);
    border-radius: 20px; padding: 3px 10px;
}}

/* ══════════════════════════════════════════════════════════
   RESPONSIVE
   ══════════════════════════════════════════════════════════*/
@media (max-width: 900px) {{
    .app-shell {{ flex-direction: column; }}
    .sidebar {{
        width: 100%; min-width: unset;
        height: auto; position: static;
        border-right: none;
        border-bottom: 1px solid rgba(0,160,255,0.08);
    }}
    .content {{ padding: 16px; }}
    .nav-stack {{
        flex-direction: row; flex-wrap: wrap;
        gap: 4px; padding: 8px 10px;
    }}
    .nav-item {{
        width: auto; padding: 8px 12px;
        font-size: 12px;
    }}
    .nav-item.active::before {{ display: none; }}
    .logo-card {{ padding: 14px 16px 10px; }}
    .sidebar-user {{ padding: 6px 16px 10px; }}
    .grid {{ grid-template-columns: repeat(2, 1fr); }}
}}
</style>
    </head>
    <body>
        <div class="app-shell">
            {sidebar}
            <main class="content">
                {messages_html}
                {body}
                <div class="footer-note">
                    <div class="footer-trust">
                        <span class="footer-badge">&#128274; SSL Encrypted</span>
                        <span class="footer-badge">&#9989; SOC 2 Ready</span>
                        <span class="footer-badge">&#128100; Role-Based Access</span>
                        <span class="footer-badge">&#127968; US-Based Data</span>
                    </div>
                    <div>
                        <a href="/privacy">Privacy Policy</a>
                        &middot;
                        <a href="/terms">Terms of Service</a>
                        &middot;
                        <a href="mailto:info@haultraai.com">Support</a>
                    </div>
                    <div style="margin-top:4px;">&copy; {datetime.now().year} HAULTRA AI SYSTEMS &mdash; Built for the hauling industry.</div>
                </div>
            </main>
        </div>

                <script>
        // Auto-inject CSRF token into every POST form
        (function() {{
            var csrfToken = document.querySelector('meta[name="csrf-token"]').getAttribute('content');
            document.addEventListener("DOMContentLoaded", function() {{
                document.querySelectorAll("form").forEach(function(form) {{
                    if (form.method.toLowerCase() === "post") {{
                        var input = document.createElement("input");
                        input.type = "hidden";
                        input.name = "_csrf_token";
                        input.value = csrfToken;
                        form.appendChild(input);
                    }}
                }});
            }});
        }})();

        document.addEventListener("DOMContentLoaded", function () {{
            const isIOS =
                /iPad|iPhone|iPod/.test(navigator.userAgent) ||
                (navigator.platform === "MacIntel" && navigator.maxTouchPoints > 1);

            document.querySelectorAll(".map-btn").forEach(function (btn) {{
                const googleUrl = btn.dataset.google;
                const appleUrl = btn.dataset.apple;

                if (isIOS && appleUrl) {{
                    btn.href = appleUrl;
                }} else if (googleUrl) {{
                    btn.href = googleUrl;
                }}
            }});
        const nextStopBtn = document.getElementById("next-stop-btn");
    const nextStopCard = document.getElementById("next-stop-card");

    if (nextStopBtn && nextStopCard) {{
        nextStopBtn.addEventListener("click", function (e) {{
            e.preventDefault();
            nextStopCard.scrollIntoView({{
                behavior: "smooth",
                block: "center"
            }});
        }});
    }}

}});
</script>

<script>
/* ── HAULTRA auto-save: persist & restore form inputs via localStorage ── */
(function(){{
  var PAGE = window.location.pathname;
  var SKIP = {{password:1,hidden:1,submit:1,reset:1,button:1,file:1,image:1}};

  function saveable(el) {{
    if (SKIP[el.type]) return false;
    var tag = el.tagName.toLowerCase();
    if (tag === 'select') {{
      /* skip navigation selects that auto-submit the form on change */
      var oc = el.getAttribute('onchange') || '';
      if (oc.indexOf('submit') !== -1) return false;
    }}
    return tag === 'input' || tag === 'textarea' || tag === 'select';
  }}

  function mkKey(formIdx, el, elIdx) {{
    return 'haultra:' + PAGE + ':f' + formIdx + ':' + (el.name || el.id || ('i' + elIdx));
  }}

  function getVal(el) {{
    if (el.type === 'checkbox' || el.type === 'radio') return el.checked ? '1' : '0';
    return el.value;
  }}

  function setVal(el, v) {{
    if (el.type === 'checkbox' || el.type === 'radio') {{
      el.checked = (v === '1');
    }} else if (el.tagName.toLowerCase() === 'select') {{
      for (var i = 0; i < el.options.length; i++) {{
        if (el.options[i].value === v) {{ el.selectedIndex = i; break; }}
      }}
    }} else {{
      el.value = v;
    }}
  }}

  document.addEventListener('DOMContentLoaded', function() {{
    document.querySelectorAll('form').forEach(function(form, fi) {{
      var els = form.querySelectorAll('input,textarea,select');

      /* restore */
      els.forEach(function(el, ei) {{
        if (!saveable(el)) return;
        var v = localStorage.getItem(mkKey(fi, el, ei));
        if (v !== null) setVal(el, v);
      }});

      /* save on every keystroke / change */
      els.forEach(function(el, ei) {{
        if (!saveable(el)) return;
        var k = mkKey(fi, el, ei);
        var ev = (el.tagName.toLowerCase() === 'select' ||
                  el.type === 'checkbox' || el.type === 'radio') ? 'change' : 'input';
        el.addEventListener(ev, function() {{
          try {{ localStorage.setItem(k, getVal(el)); }} catch(ex) {{}}
        }});
      }});

      /* clear this form's keys on successful submit */
      form.addEventListener('submit', function() {{
        els.forEach(function(el, ei) {{
          if (!saveable(el)) return;
          localStorage.removeItem(mkKey(fi, el, ei));
        }});
      }});
    }});
  }});
}})();
</script>

<script>
/* ── HAULTRA offline support: SW registration, queue, sync ─────────── */
(function(){{

  /* 1 ── Register service worker ──────────────────────────────────── */
  if ('serviceWorker' in navigator) {{
    navigator.serviceWorker.register('/sw.js', {{scope: '/'}}).catch(function() {{}});
  }}

  var QUEUE_KEY   = 'haultra_offline_queue';
  var _SYNCED_KEY = 'haultra_synced_uids';   /* sessionStorage: dedup across reloads */

  /* Routes queued when offline (toggle is handled by the AJAX handler directly) */
  var QUEUE_PAT = [
    /^\\/stop\\/\\d+\\/driver-action$/,
    /^\\/driver\\/clock$/
  ];

  /* ── State ──────────────────────────────────────────────────────── */
  var _syncState       = 'idle'; /* idle | syncing | success | error | session */
  var _retryTimer      = null;
  var _lastSyncTime    = null;   /* ISO string of last attempt */
  var _lastSyncResult  = null;   /* human-readable result */
  var _lastSyncSuccess = null;   /* HH:MM of last clean sync, shown in banner */

  /* ── Style constants ─────────────────────────────────────────────── */
  var _BTN_STYLE = (
    'background:none;border:1px solid currentColor;border-radius:6px;' +
    'padding:4px 12px;cursor:pointer;font-size:12px;font-weight:700;' +
    'color:inherit;flex-shrink:0;'
  );
  var _BASE_CSS = (
    'position:fixed;top:0;left:0;right:0;z-index:10000;' +
    'padding:10px 20px;display:flex;align-items:center;' +
    'justify-content:space-between;gap:12px;' +
    'font-size:13px;font-weight:600;'
  );
  var _COLORS = {{
    warn:  'background:#1a0a00;border-bottom:1px solid rgba(255,157,0,.35);color:#fbbf24;',
    ok:    'background:#001810;border-bottom:1px solid rgba(0,232,125,.30);color:#56f0b7;',
    error: 'background:#200010;border-bottom:1px solid rgba(255,60,60,.40);color:#ff9a9a;'
  }};

  /* ── Banner + conflict-box DOM ───────────────────────────────────── */
  var banner = document.createElement('div');
  banner.id  = 'haultra-offline-banner';
  document.body.insertBefore(banner, document.body.firstChild);

  /* Conflict strip: per-action Dismiss buttons; sits just below the banner */
  var _conflictBox = document.createElement('div');
  _conflictBox.id  = 'haul-conflict-box';
  _conflictBox.style.cssText = (
    'display:none;position:fixed;top:44px;left:0;right:0;z-index:9998;' +
    'background:#1a0010;border-bottom:2px solid rgba(255,60,60,.4);' +
    'padding:8px 20px;font-size:12px;color:#ff9a9a;line-height:1.8;'
  );
  document.body.appendChild(_conflictBox);

  /* ── Queue helpers ───────────────────────────────────────────────── */
  function _mkUid() {{
    return Date.now().toString(36) + Math.random().toString(36).slice(2, 7);
  }}

  function queueLen() {{
    return JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]').length;
  }}

  /* Remove one item by uid — safe to call mid-sync */
  function _removeFromQueue(uid) {{
    var q = JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]');
    localStorage.setItem(QUEUE_KEY, JSON.stringify(
      q.filter(function(i) {{ return i.uid !== uid; }})
    ));
  }}

  /* Patch one item in-place by uid */
  function _updateQueueItem(uid, updates) {{
    var q = JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]').map(function(i) {{
      return i.uid === uid ? Object.assign({{}}, i, updates) : i;
    }});
    localStorage.setItem(QUEUE_KEY, JSON.stringify(q));
  }}

  /* sessionStorage-backed set of already-synced uids — survives reload, not tab-close */
  function _getSyncedUids() {{
    try {{ return new Set(JSON.parse(sessionStorage.getItem(_SYNCED_KEY) || '[]')); }}
    catch(ex) {{ return new Set(); }}
  }}
  function _markSyncedUid(uid) {{
    try {{
      var arr = JSON.parse(sessionStorage.getItem(_SYNCED_KEY) || '[]');
      if (!arr.includes(uid)) {{
        arr.push(uid);
        if (arr.length > 300) arr = arr.slice(-300);
        sessionStorage.setItem(_SYNCED_KEY, JSON.stringify(arr));
      }}
    }} catch(ex) {{}}
  }}

  /* ── Banner render ───────────────────────────────────────────────── */
  function _setBanner(type, msgHtml, actionHtml) {{
    banner.style.cssText = _BASE_CSS + (_COLORS[type] || _COLORS.warn);
    banner.innerHTML = '<span>' + msgHtml + '</span>' + (actionHtml || '');
  }}

  function updateBanner() {{
    var qlen = queueLen();
    if (!navigator.onLine) {{
      _setBanner('warn',
        '&#9888;&nbsp;Offline &mdash; ' +
        (qlen
          ? qlen + ' action' + (qlen !== 1 ? 's' : '') + ' pending sync'
          : 'actions will be saved and synced on reconnect')
      );
    }} else if (_syncState === 'session') {{
      _setBanner('error',
        '&#9888;&nbsp;Login expired &mdash; ' +
        qlen + ' action' + (qlen !== 1 ? 's' : '') + ' still queued',
        '<a href="/login" style="' + _BTN_STYLE + 'text-decoration:none;">Log In to Sync</a>'
      );
    }} else if (_syncState === 'success') {{
      _setBanner('ok',
        '&#10003;&nbsp;Sync complete' +
        (_lastSyncSuccess ? ' at ' + _lastSyncSuccess : '')
      );
    }} else if (_syncState === 'error') {{
      var _eq   = JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]');
      var _conf = _eq.filter(function(i) {{ return i.conflict; }}).length;
      var _ret  = _eq.filter(function(i) {{ return !i.conflict; }}).length;
      var _msg  = '&#10007;&nbsp;Sync failed &mdash; ' +
        _eq.length + ' action' + (_eq.length !== 1 ? 's' : '') + ' pending';
      if (_conf > 0) _msg += ' &bull; ' + _conf + ' conflict' + (_conf !== 1 ? 's' : '');
      if (_ret  > 0) _msg += ' &bull; retrying in 15 s';
      _setBanner('error', _msg,
        (_ret > 0
          ? '<button onclick="window.__haultraSync()" style="' + _BTN_STYLE + '">Retry Now</button>'
          : '')
      );
    }} else if (qlen > 0) {{
      var _lsOk = _lastSyncSuccess ? ' &bull; last sync ' + _lastSyncSuccess : '';
      _setBanner('ok',
        '&#8635;&nbsp;' + (_syncState === 'syncing'
          ? 'Syncing ' + qlen + ' action' + (qlen !== 1 ? 's' : '') + '&hellip;'
          : qlen + ' action' + (qlen !== 1 ? 's' : '') + ' pending' + _lsOk),
        (_syncState !== 'syncing'
          ? '<button onclick="window.__haultraSync()" style="' + _BTN_STYLE + '">Sync Now</button>'
          : '')
      );
      if (_syncState === 'idle') {{
        _syncState = 'syncing';
        doSync();
      }}
    }} else {{
      banner.style.display    = 'none';
      _conflictBox.style.display = 'none';
      return;
    }}
    banner.style.display = 'flex';
    _updateConflictBox();
  }}

  /* ── Conflict notification box ───────────────────────────────────── */
  function _updateConflictBox() {{
    var q = JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]');
    var conflicts = q.filter(function(i) {{ return i.conflict; }});
    if (!conflicts.length) {{ _conflictBox.style.display = 'none'; return; }}
    var html = (
      '<b>&#9888; ' + conflicts.length + ' action' +
      (conflicts.length !== 1 ? 's' : '') +
      ' need attention &mdash; stop was changed by someone else. Dismiss or reload to see current state.</b><br>'
    );
    conflicts.forEach(function(item) {{
      html += (
        '<span style="display:inline-flex;align-items:center;gap:6px;' +
        'margin:3px 8px 3px 0;padding:3px 8px;' +
        'background:rgba(255,60,60,.12);border:1px solid rgba(255,60,60,.25);border-radius:6px;">' +
        (item.label || item.url) +
        '<span style="opacity:.7;">&mdash; ' + (item.sync_error || 'Conflict') + '</span>' +
        '<button data-uid="' + item.uid + '" ' +
        'onclick="window.__haultsDismissConflict(this.dataset.uid)" ' +
        'style="background:none;border:1px solid currentColor;border-radius:4px;' +
        'padding:1px 6px;cursor:pointer;font-size:11px;color:inherit;">Dismiss &#10005;</button>' +
        '</span>'
      );
    }});
    _conflictBox.innerHTML = html;
    _conflictBox.style.display = 'block';
  }}

  /* ── Auto-retry scheduler ────────────────────────────────────────── */
  function _scheduleRetry() {{
    _cancelRetry();
    if (!navigator.onLine) return;
    var q = JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]');
    if (!q.filter(function(i) {{ return !i.conflict; }}).length) return;
    console.log('[HAULTRA] auto-retry scheduled in 15 s');
    _retryTimer = setTimeout(function() {{
      _retryTimer = null;
      if (navigator.onLine && _syncState !== 'syncing' && _syncState !== 'session') {{
        console.log('[HAULTRA] auto-retry firing');
        _syncState = 'syncing';
        updateBanner();
        doSync();
      }}
    }}, 15000);
  }}

  function _cancelRetry() {{
    if (_retryTimer) {{ clearTimeout(_retryTimer); _retryTimer = null; }}
  }}

  /* ── Online / offline / visibility events ────────────────────────── */
  window.addEventListener('online', function() {{
    _syncState = 'idle';
    _cancelRetry();
    updateBanner();
  }});
  window.addEventListener('offline', function() {{
    _cancelRetry();
    updateBanner();
  }});

  /* iOS/PWA: sync when app comes back to foreground */
  document.addEventListener('visibilitychange', function() {{
    if (!document.hidden && navigator.onLine && queueLen() > 0 && _syncState === 'idle') {{
      console.log('[HAULTRA] visibilitychange — triggering sync');
      _syncState = 'syncing';
      doSync();
    }}
  }});

  /* Sync on page load — picks up items from a previous session */
  document.addEventListener('DOMContentLoaded', function() {{
    if (navigator.onLine && queueLen() > 0 && _syncState === 'idle') {{
      console.log('[HAULTRA] page load — triggering sync for', queueLen(), 'queued item(s)');
      _syncState = 'syncing';
      doSync();
    }}
  }});

  updateBanner();

  /* ── Form interceptor (driver-action, clock) ─────────────────────── */
  document.addEventListener('DOMContentLoaded', function() {{
    document.querySelectorAll('form').forEach(function(form) {{
      if ((form.method || '').toLowerCase() !== 'post') return;
      form.addEventListener('submit', function(evt) {{
        if (navigator.onLine) return;          /* online: submit normally */

        var raw = form.getAttribute('action') || window.location.pathname;
        var url = raw;
        try {{ url = new URL(raw, window.location.href).pathname; }} catch(ex) {{}}

        var match = QUEUE_PAT.some(function(p) {{ return p.test(url); }});
        if (!match) return;

        evt.preventDefault();

        var data = {{}};
        new FormData(form).forEach(function(v, k) {{ data[k] = v; }});

        /* capture expected state for server-side conflict detection */
        var isDriverAction = /^\\/stop\\/\\d+\\/driver-action$/.test(url);
        if (isDriverAction) {{
          var card = form.closest('[data-stop-id]') || form.closest('.driver-stop-card');
          if (card && card.dataset.driverStatus) {{
            data.expected_driver_status = card.dataset.driverStatus;
          }}
        }}

        /* dedup: skip if same url+action already queued (double-tap guard) */
        var existing = JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]');
        var dup = existing.some(function(x) {{
          return x.url === url && x.body.action === data.action && !x.conflict;
        }});
        if (dup) {{
          console.log('[HAULTRA] dedup — skipping duplicate', url, data.action);
          return;
        }}

        existing.push({{
          uid:       _mkUid(),
          url:       url,
          body:      data,
          queued_at: new Date().toISOString(),
          label:     data.action || data.clock_action || url
        }});
        localStorage.setItem(QUEUE_KEY, JSON.stringify(existing));
        updateBanner();

        /* visual feedback — persist for workflow actions, brief for others */
        var btn = form.querySelector('button[type=submit], button:not([type])');
        if (btn) {{
          btn.innerHTML = '&#8635;&nbsp;Pending Sync';
          btn.disabled  = true;
          btn.style.opacity = '0.7';
          if (!isDriverAction && !/^\\/driver\\/clock$/.test(url)) {{
            var orig = btn.innerHTML;
            setTimeout(function() {{
              btn.innerHTML = orig;
              btn.disabled  = false;
              btn.style.opacity = '';
            }}, 2500);
          }}
        }}
      }});
    }});
  }});

  /* ── doSync ──────────────────────────────────────────────────────── */
  async function doSync() {{
    _cancelRetry();
    var queue      = JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]');
    var syncedUids = _getSyncedUids();

    /* items to replay: not already flagged conflict, not already synced this session */
    var toProcess = queue.filter(function(i) {{
      return !i.conflict && !syncedUids.has(i.uid);
    }});

    if (!toProcess.length) {{
      _syncState = (queueLen() > 0) ? 'error' : 'idle';
      updateBanner();
      return;
    }}

    _syncState    = 'syncing';
    _lastSyncTime = new Date().toISOString();
    updateBanner();
    console.log('[HAULTRA] doSync —', toProcess.length, 'item(s) to replay');

    /* fresh CSRF token */
    var freshToken;
    try {{
      var tr = await fetch('/api/csrf-token');
      if (tr.status === 401 || tr.status === 403) {{
        _syncState      = 'session';
        _lastSyncResult = 'session_expired';
        console.warn('[HAULTRA] session expired');
        updateBanner();
        return;
      }}
      if (!tr.ok) throw new Error('csrf-' + tr.status);
      freshToken = (await tr.json()).token;
    }} catch(ex) {{
      _syncState      = 'error';
      _lastSyncResult = 'csrf_failed: ' + ex.message;
      console.warn('[HAULTRA] CSRF fetch failed:', ex.message);
      _scheduleRetry();
      updateBanner();
      return;
    }}

    var syncedCount = 0;

    for (var i = 0; i < toProcess.length; i++) {{
      var item = toProcess[i];
      /* build form body with fresh token — do not mutate stored item */
      var body = Object.assign({{}}, item.body, {{ _csrf_token: freshToken }});
      var fd   = new URLSearchParams();
      Object.keys(body).forEach(function(k) {{ fd.append(k, body[k]); }});

      try {{
        var r = await fetch(item.url, {{
          method:   'POST',
          body:     fd,
          redirect: 'follow',
          headers:  {{ 'X-Sync-Replay': '1' }}
        }});

        if (r.status === 409) {{
          var cj = {{}};
          try {{ cj = await r.json(); }} catch(_) {{}}
          var detail = cj.current_status
            ? 'Stop changed to \u201c' + cj.current_status + '\u201d'
            : 'Conflict';
          _updateQueueItem(item.uid, {{ conflict: true, sync_error: detail }});
          console.warn('[HAULTRA] conflict:', item.label, '\u2014', detail);

        }} else if (!r.ok && r.type !== 'opaqueredirect') {{
          _updateQueueItem(item.uid, {{ sync_error: 'HTTP ' + r.status }});
          console.warn('[HAULTRA] error:', item.url, 'HTTP', r.status);

        }} else {{
          /* success — remove from queue immediately (transaction-safe) */
          _removeFromQueue(item.uid);
          _markSyncedUid(item.uid);
          syncedCount++;
          console.log('[HAULTRA] synced:', item.label || item.url);
        }}

      }} catch(ex) {{
        _updateQueueItem(item.uid, {{ sync_error: 'Network error' }});
        console.warn('[HAULTRA] network error on', item.url, ex.message);
      }}
    }}

    var remaining  = JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]');
    var failedNow  = remaining.filter(function(i) {{ return !i.conflict; }}).length;
    var conflictNow = remaining.filter(function(i) {{ return i.conflict; }}).length;
    _lastSyncResult = 'synced:' + syncedCount + ' failed:' + failedNow + ' conflicts:' + conflictNow;
    console.log('[HAULTRA] doSync done —', _lastSyncResult);

    if (syncedCount > 0 && failedNow === 0 && conflictNow === 0) {{
      /* everything clean */
      _lastSyncSuccess = new Date().toLocaleTimeString([], {{hour:'2-digit', minute:'2-digit'}});
      _syncState = 'success';
      updateBanner();
      setTimeout(function() {{ _syncState = 'idle'; updateBanner(); }}, 3000);
    }} else if (failedNow > 0) {{
      /* some non-conflict failures — auto-retry in 15 s */
      _syncState = 'error';
      updateBanner();
      _scheduleRetry();
    }} else {{
      /* only conflicts remain — not auto-retried, needs human review */
      _syncState = 'error';
      updateBanner();
    }}

    if (syncedCount > 0) {{
      setTimeout(function() {{ location.reload(); }}, 700);
    }}
  }}

  /* ── Public API ──────────────────────────────────────────────────── */
  window.__haultraSync = doSync;

  /* Push one item to the offline queue (called by AJAX toggle handler).
     Adds a uid if missing; deduplicates double-taps by url+action. */
  window.__haultraOfflineQueue = function(item) {{
    if (!item.uid) item.uid = _mkUid();
    var q = JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]');
    /* dedup guard: same url + same action already pending */
    var dup = q.some(function(x) {{
      return x.url === item.url &&
             (x.body.action || '') === (item.body.action || '') &&
             !x.conflict;
    }});
    if (dup) {{ updateBanner(); return; }}
    q.push(item);
    localStorage.setItem(QUEUE_KEY, JSON.stringify(q));
    updateBanner();
  }};

  /* Dismiss a conflicted item — removes from queue, hides its conflict row */
  window.__haultsDismissConflict = function(uid) {{
    _removeFromQueue(uid);
    _updateConflictBox();
    updateBanner();
  }};

  /* 5 ── Debug panel (Shift+Alt+D) ────────────────────────────────── */
  (function() {{
    var panel = document.createElement('div');
    panel.id  = 'haul-debug-panel';
    panel.style.cssText = (
      'display:none;position:fixed;bottom:60px;right:16px;z-index:99999;' +
      'width:340px;max-height:70vh;overflow-y:auto;' +
      'background:#060e1e;border:1px solid rgba(0,160,255,.3);border-radius:14px;' +
      'padding:16px 18px;font-size:12px;color:#b0c4de;font-family:monospace;' +
      'box-shadow:0 8px 32px rgba(0,0,0,.6);'
    );
    document.body.appendChild(panel);

    async function refreshDebug() {{
      var q = JSON.parse(localStorage.getItem(QUEUE_KEY) || '[]');
      var syncedUids = [];
      try {{ syncedUids = JSON.parse(sessionStorage.getItem(_SYNCED_KEY) || '[]'); }} catch(ex) {{}}
      var cachedUrls = [];
      try {{
        var c = await caches.open('haultra-v3');
        var keys = await c.keys();
        cachedUrls = keys.map(function(r) {{ return r.url; }});
      }} catch(ex) {{}}

      var conflicts = q.filter(function(i) {{ return i.conflict; }});
      var retryable = q.filter(function(i) {{ return !i.conflict; }});
      var html = (
        '<div style="font-size:14px;font-weight:700;color:#56f0b7;margin-bottom:10px;">' +
        '&#128203; HAULTRA Debug' +
        '<button onclick="document.getElementById(\'haul-debug-panel\').style.display=\'none\'" ' +
        'style="float:right;background:none;border:none;color:#b0c4de;cursor:pointer;font-size:16px;">&#10005;</button>' +
        '</div>' +
        '<b>Online:</b> ' + navigator.onLine + '<br>' +
        '<b>Sync state:</b> ' + _syncState + '<br>' +
        '<b>Retry timer:</b> ' + (_retryTimer ? 'scheduled' : 'none') + '<br>' +
        '<b>Last sync attempt:</b> ' + (_lastSyncTime || 'never') + '<br>' +
        '<b>Last sync success:</b> ' + (_lastSyncSuccess || 'never') + '<br>' +
        '<b>Last result:</b> ' + (_lastSyncResult || '\u2014') + '<br>' +
        '<b>Queue size:</b> ' + q.length +
        (retryable.length  ? ' (' + retryable.length  + ' retryable)' : '') +
        (conflicts.length  ? ' (' + conflicts.length  + ' conflicts)' : '') + '<br>' +
        '<b>Synced this session:</b> ' + syncedUids.length + '<br>' +
        '<b>Cached pages:</b> ' + cachedUrls.length + '<br><br>'
      );
      if (q.length) {{
        html += '<b>Queue items:</b><br>';
        q.forEach(function(item, i) {{
          html += (
            '<div style="margin:4px 0;padding:4px 6px;background:rgba(255,255,255,.05);border-radius:6px;">' +
            (i+1) + '. ' + (item.label || item.url) +
            (item.conflict ? ' <span style="color:#ff9a9a;">[CONFLICT: ' + (item.sync_error||'') + ']</span>' : '') +
            (item.sync_error && !item.conflict ? ' <span style="color:#fbbf24;">[ERR: ' + item.sync_error + ']</span>' : '') +
            '<br><span style="opacity:.6;">' + item.queued_at + '</span>' +
            '</div>'
          );
        }});
        html += (
          '<button onclick="if(confirm(\'Clear all queued actions?\')){{' +
          'localStorage.setItem(\'haultra_offline_queue\',\'[]\');' +
          'window.__haultraSync&&window.__haultraSync();}}" ' +
          'style="margin-top:8px;background:rgba(255,60,60,.15);border:1px solid rgba(255,60,60,.3);' +
          'border-radius:6px;padding:4px 10px;color:#ff9a9a;cursor:pointer;font-size:11px;">' +
          'Clear Queue</button>'
        );
      }}
      if (cachedUrls.length) {{
        html += '<br><b>Cached URLs:</b><br>';
        cachedUrls.slice(0,20).forEach(function(u) {{
          var path = u.replace(location.origin, '');
          html += '<div style="opacity:.7;word-break:break-all;">' + path + '</div>';
        }});
        if (cachedUrls.length > 20) html += '<div style="opacity:.5;">&hellip; +' + (cachedUrls.length-20) + ' more</div>';
      }}
      panel.innerHTML = html;
    }}

    document.addEventListener('keydown', function(ev) {{
      if (ev.shiftKey && ev.altKey && ev.key === 'D') {{
        if (panel.style.display === 'none') {{
          refreshDebug();
          panel.style.display = 'block';
        }} else {{
          panel.style.display = 'none';
        }}
      }}
    }});
  }})();
}})();
</script>

<script>{_ABBREV_EXPAND_JS}</script>

    </body>
    </html>
    """


# =========================================================
# AUTH PAGES
# =========================================================
@app.route("/init")
@boss_required
def init_route():
    init_db()
    flash("Database re-initialized.", "success")
    return redirect(url_for("dashboard"))


@app.route("/login", methods=["GET", "POST"])
def login():
    init_db()
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        password = request.form.get("password", "").strip()
        conn = get_db()
        user = conn.execute("SELECT * FROM users WHERE username = ?", (username,)).fetchone()
        conn.close()

        if user and check_password_hash(user["password_hash"], password):
            session.clear()
            session["user_id"]       = user["id"]
            session["username"]      = user["username"]
            session["role"]          = user["role"]
            session["company_id"]    = user["company_id"]
            session["is_superadmin"] = bool(user["is_superadmin"])
            flash("Logged in.", "success")

            if user["role"] == "driver":
                return redirect(url_for("driver_dashboard"))

            return redirect(url_for("dashboard"))

        flash("Invalid login.", "error")
        return redirect(url_for("login"))

    body = f"""
    <div style="max-width:520px;margin:70px auto;">
        <div class="hero">
            <h1>HAULTRA Login</h1>
            <p>Operations + AI dispatch in one system.</p>
        </div>
        <div class="card">
           
                <form method="POST">
                <label>Username</label>
                <input name="username" required>
                <label>Password</label>
                <input type="password" name="password" required>
                <div style="margin-top:10px;">
                    <button type="submit">Login</button>
                </div>

                <div style="margin-top:14px;" class="small muted">
                Need an account?
                <a href="/signup">Create one here</a>
                </div>

               </form>
        </div>
    </div>
    """
    return render_template_string(shell_page("Login", body))
@app.route("/logout", methods=["POST"])
def logout():
    session.clear()
    flash("Logged out.", "success")
    return redirect(url_for("login"))

@app.route("/driver")
@driver_required
def driver_dashboard():
    conn = get_db()
    routes = conn.execute("""
        SELECT
            r.*,
            (
                SELECT COUNT(*)
                FROM stops s
                WHERE s.route_id = r.id
            ) AS total_stops,
            (
                SELECT COUNT(*)
                FROM stops s
                WHERE s.route_id = r.id
                  AND s.status = 'completed'
            ) AS completed_stops
        FROM routes r
        WHERE r.assigned_to = ?
        ORDER BY r.route_date DESC, r.id DESC
    """, (session["user_id"],)).fetchall()
    conn.close()

    rows = ""
    for r in routes:
        rows += f"""
        <tr>
            <td>{e(r['route_date'])}</td>
            <td>{e(r['route_name'])}</td>
            <td><span class="badge {e(r['status'])}">{e(r['status'])}</span></td>
            <td>{r['completed_stops']} / {r['total_stops']}</td>
            <td><a class="btn secondary" href="{url_for('driver_route_detail', route_id=r['id'])}">Open</a></td>
        </tr>
        """

    # Build list of active route URLs to prefetch for offline use
    _prefetch_urls = json.dumps([
        url_for('driver_route_detail', route_id=r['id'])
        for r in routes
        if r['status'] in ('open', 'in_progress')
    ])

    body = f"""
    <div class="hero">
        <h1>Driver Dashboard</h1>
        <p>See your assigned routes, open them fast, and complete stops in the field.</p>
    </div>

    <div class="card">
        <h2>My Assigned Routes</h2>
        <div class="table-wrap">
            <table>
                <thead>
                    <tr>
                        <th>Date</th>
                        <th>Route</th>
                        <th>Status</th>
                        <th>Progress</th>
                        <th></th>
                    </tr>
                </thead>
                <tbody>
                    {rows if rows else '<tr><td colspan="5">No assigned routes.</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>

    <script>
    /* Prefetch active route pages into the service-worker cache so they
       are available if the driver loses signal before opening the route. */
    (function() {{
        var urls = {_prefetch_urls};
        if (!urls.length) return;
        window.addEventListener('load', function() {{
            var sw = navigator.serviceWorker && navigator.serviceWorker.controller;
            urls.forEach(function(url) {{
                /* Ask SW to cache it via message (no network noise in the tab) */
                if (sw) {{
                    sw.postMessage({{ type: 'CACHE_URL', url: url }});
                }} else {{
                    /* Fallback: direct fetch — SW fetch handler caches it */
                    fetch(url, {{ credentials: 'include' }}).catch(function() {{}});
                }}
            }});
            console.log('[HAULTRA] Prefetched', urls.length, 'route page(s) for offline use');
        }});
    }})();
    </script>
    """
    return render_template_string(shell_page("Driver Dashboard", body))

# =========================================================
# DASHBOARD / ANALYTICS
# =========================================================
@app.route("/")
def dashboard():
    if "user_id" not in session:
        return redirect(url_for("login"))

    conn = get_db()
    user = get_current_user()

    company_id = cid()
    if user["role"] == "boss":
        routes = conn.execute("""
            SELECT r.*, u.username AS assigned_username
            FROM routes r
            LEFT JOIN users u ON r.assigned_to = u.id
            WHERE r.company_id = ?
            ORDER BY r.route_date DESC, r.id DESC LIMIT 8
        """, (company_id,)).fetchall()
    else:
        routes = conn.execute("""
            SELECT r.*, u.username AS assigned_username
            FROM routes r
            LEFT JOIN users u ON r.assigned_to = u.id
            WHERE r.assigned_to = ? AND r.company_id = ?
            ORDER BY r.route_date DESC, r.id DESC LIMIT 8
        """, (user["id"], company_id)).fetchall()

    if user["role"] == "boss":
        route_total      = conn.execute("SELECT COUNT(*) n FROM routes WHERE company_id=?", (company_id,)).fetchone()["n"]
        open_routes      = conn.execute("SELECT COUNT(*) n FROM routes WHERE company_id=? AND status='open'", (company_id,)).fetchone()["n"]
        progress_routes  = conn.execute("SELECT COUNT(*) n FROM routes WHERE company_id=? AND status='in_progress'", (company_id,)).fetchone()["n"]
        completed_routes = conn.execute("SELECT COUNT(*) n FROM routes WHERE company_id=? AND status='completed'", (company_id,)).fetchone()["n"]
        stop_total       = conn.execute("SELECT COUNT(*) n FROM stops s JOIN routes r ON s.route_id=r.id WHERE r.company_id=?", (company_id,)).fetchone()["n"]
        total_loads      = conn.execute("SELECT COUNT(*) n FROM load_scores WHERE company_id=?", (company_id,)).fetchone()["n"]
    else:
        route_total      = conn.execute("SELECT COUNT(*) n FROM routes WHERE assigned_to=? AND company_id=?", (user["id"], company_id)).fetchone()["n"]
        open_routes      = conn.execute("SELECT COUNT(*) n FROM routes WHERE assigned_to=? AND company_id=? AND status='open'", (user["id"], company_id)).fetchone()["n"]
        progress_routes  = conn.execute("SELECT COUNT(*) n FROM routes WHERE assigned_to=? AND company_id=? AND status='in_progress'", (user["id"], company_id)).fetchone()["n"]
        completed_routes = conn.execute("SELECT COUNT(*) n FROM routes WHERE assigned_to=? AND company_id=? AND status='completed'", (user["id"], company_id)).fetchone()["n"]
        stop_total       = conn.execute("SELECT COUNT(*) n FROM stops s JOIN routes r ON s.route_id=r.id WHERE r.assigned_to=? AND r.company_id=?", (user["id"], company_id)).fetchone()["n"]
        total_loads      = conn.execute("SELECT COUNT(*) n FROM load_scores WHERE created_by=? AND company_id=?", (user["id"], company_id)).fetchone()["n"]

    top_load = conn.execute("SELECT * FROM load_scores WHERE company_id=? ORDER BY score DESC, estimated_profit DESC LIMIT 1", (company_id,)).fetchone()
    conn.close()

    route_rows = ""
    for r in routes:
       route_rows += f"""
<tr>
    <td>{e(r['route_date'])}</td>
    <td><a href="{url_for('view_route', route_id=r['id'])}">{e(r['route_name'])}</a></td>
    <td>{e(r['assigned_username'] or 'Unassigned')}</td>
    <td><span class="badge {e(r['status'])}">{e(r['status'])}</span></td>
    <td>
        <div class="row">
            <a class="btn secondary" href="{url_for('view_route', route_id=r['id'])}">Open</a>
            {f'''
            <form class="inline" method="POST"
                  action="{url_for('delete_route', route_id=r['id'])}"
                  onsubmit="return confirm('Delete this route?')">
                <button class="btn red" type="submit">Delete</button>
            </form>
            ''' if user['role'] == 'boss' else ''}
        </div>
    </td>
</tr>
"""

    top_load_html = "No loads scored yet"
    if top_load:
        top_load_html = f"{e(top_load['origin'])} → {e(top_load['destination'])} | Score {top_load['score']}"

    body = f"""
    <div class="hero">
        <div style="display:flex;align-items:flex-start;justify-content:space-between;flex-wrap:wrap;gap:12px;">
            <div>
                <div style="font-size:10px;font-weight:700;letter-spacing:2px;text-transform:uppercase;color:#1e3a52;margin-bottom:7px;">
                    HAULTRA AI &mdash; COMMAND CENTER
                </div>
                <h1 style="font-size:24px;letter-spacing:-.4px;">Dispatch Intelligence Dashboard</h1>
                <p style="margin-top:6px;">Run operations, track routes, manage drivers, complete stops, and score freight.</p>
            </div>
            {f'''<a class="btn gold" href="{url_for('routes_page')}" style="align-self:flex-start;white-space:nowrap;">
                View All Routes
            </a>''' if user['role'] == 'boss' else ''}
        </div>
    </div>

    <div class="grid" style="margin-bottom:20px;">
        <div class="stat">
            <div class="label">Total Routes</div>
            <div class="num">{route_total}</div>
        </div>
        <div class="stat">
            <div class="label">Open</div>
            <div class="num" style="color:#40b8ff;">{open_routes}</div>
        </div>
        <div class="stat">
            <div class="label">In Progress</div>
            <div class="num" style="color:#ffa830;">{progress_routes}</div>
        </div>
        <div class="stat">
            <div class="label">Completed</div>
            <div class="num" style="color:#00e87d;">{completed_routes}</div>
        </div>
        <div class="stat">
            <div class="label">Total Stops</div>
            <div class="num">{stop_total}</div>
        </div>
    </div>

    <div class="card">
        <div class="row between" style="margin-bottom:14px;">
            <h2 style="margin:0;font-size:11px;font-weight:700;letter-spacing:1.2px;text-transform:uppercase;color:#1e3a52;">
                Recent Routes
            </h2>
            {f'<a class="btn secondary" style="font-size:12px;padding:7px 14px;" href="{url_for("routes_page")}">All Routes →</a>' if user['role'] == 'boss' else ''}
        </div>
        <div class="table-wrap">
            <table>
                <thead>
                    <tr>
                        <th>Date</th>
                        <th>Route</th>
                        <th>Assigned</th>
                        <th>Status</th>
                        <th></th>
                    </tr>
                </thead>
                <tbody>
                    {route_rows if route_rows else '<tr><td colspan="5" style="color:#1e3a52;padding:20px 12px;">No routes yet.</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Dashboard", body))
    

@app.route("/analytics")
@login_required
def analytics_page():
    conn = get_db()
    company_id = cid()
    route_by_status = conn.execute(
        "SELECT status, COUNT(*) AS n FROM routes WHERE company_id=? GROUP BY status",
        (company_id,)
    ).fetchall()
    top_loads = conn.execute(
        "SELECT * FROM load_scores WHERE company_id=? ORDER BY score DESC, estimated_profit DESC LIMIT 10",
        (company_id,)
    ).fetchall()
    top_drivers = conn.execute("""
        SELECT u.username,
               COUNT(DISTINCT r.id) AS routes_handled,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS completed_stops
        FROM users u
        LEFT JOIN routes r ON r.assigned_to = u.id AND r.company_id = ?
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE u.role='driver' AND u.company_id = ?
        GROUP BY u.id
        ORDER BY completed_stops DESC, routes_handled DESC, u.username ASC
    """, (company_id, company_id)).fetchall()
    conn.close()

    route_status_html = "".join(
        f'<div class="stat"><div>{e(r["status"]).replace("_", " ").title()}</div><div class="num">{r["n"]}</div></div>'
        for r in route_by_status
    ) or '<div class="stat"><div>No route data yet</div></div>'

    top_load_rows = ""
    for l in top_loads:
        top_load_rows += f"""
        <tr>
            <td>{e(l['origin'])}</td>
            <td>{e(l['destination'])}</td>
            <td>${l['payout']:.2f}</td>
            <td>{l['miles']}</td>
            <td>${l['estimated_profit']:.2f}</td>
            <td>{l['score']}</td>
        </tr>
        """

    driver_rows = ""
    for d in top_drivers:
        driver_rows += f"""
        <tr>
            <td>{e(d['username'])}</td>
            <td>{d['routes_handled'] or 0}</td>
            <td>{d['completed_stops'] or 0}</td>
        </tr>
        """

    body = f"""
    <div class="hero">
        <h1>Analytics</h1>
        <p>Quick view of route flow, driver output, and strongest loads scored inside HAULTRA.</p>
    </div>

    <div class="grid">{route_status_html}</div>

    <div class="card">
        <h2>Top AI-Scored Loads</h2>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Origin</th><th>Destination</th><th>Payout</th><th>Miles</th><th>Profit</th><th>Score</th></tr></thead>
                <tbody>{top_load_rows if top_load_rows else '<tr><td colspan="6">No loads scored yet.</td></tr>'}</tbody>
            </table>
        </div>
    </div>

    <div class="card">
        <h2>Driver Output</h2>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Driver</th><th>Routes Handled</th><th>Completed Stops</th></tr></thead>
                <tbody>{driver_rows if driver_rows else '<tr><td colspan="3">No driver data yet.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Analytics", body))


# =========================================================
# USERS / DRIVERS
# =========================================================
@app.route("/users")
@boss_required
def manage_users():
    conn = get_db()
    users = conn.execute(
        "SELECT * FROM users WHERE company_id=? ORDER BY role, username",
        (cid(),)
    ).fetchall()
    conn.close()

    current_uid = session["user_id"]
    boss_count  = sum(1 for u in users if u["role"] == "boss")

    rows = ""
    for u in users:
        is_self      = u["id"] == current_uid
        is_last_boss = u["role"] == "boss" and boss_count <= 1

        _del_td_style = 'style="text-align:right;white-space:nowrap;width:80px;"'
        if is_self:
            delete_cell = f'<td {_del_td_style}><span class="muted small">You</span></td>'
        elif is_last_boss:
            delete_cell = f'<td {_del_td_style}><span class="muted small" title="Cannot delete the last boss">—</span></td>'
        else:
            _del_uname  = e(u["username"])
            _del_action = url_for("delete_user", user_id=u["id"])
            delete_cell = (
                f'<td {_del_td_style}>'
                f'<form method="POST" action="{_del_action}" style="margin:0;" '
                f'onsubmit="return confirm(\'Delete {_del_uname}? This cannot be undone.\');">'
                f'<button type="submit" '
                f'style="background:transparent;color:#f87171;border:1px solid rgba(248,113,113,0.4);'
                f'border-radius:6px;padding:3px 10px;font-size:11px;cursor:pointer;line-height:1.4;">'
                f'Delete</button>'
                f'</form>'
                f'</td>'
            )

        role_badge = (
            '<span class="badge completed">Boss</span>'
            if u["role"] == "boss"
            else '<span class="badge">Driver</span>'
        )

        rows += f"""
        <tr>
            <td>{e(u['username'])}</td>
            <td>{e(u['full_name'] or '')}</td>
            <td>{e(u['phone'] or '')}</td>
            <td>{role_badge}</td>
            <td>{e(u['created_at'])}</td>
            {delete_cell}
        </tr>
        """

    body = f"""
    <div class="hero">
        <h1>Users</h1>
        <p>Create drivers and bosses that can work inside the same HAULTRA system.</p>
    </div>

    <div class="card">
        <div class="row between">
            <h2 style="margin:0;">All Users</h2>
            <a class="btn" href="{url_for('register')}">Create User</a>
        </div>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Username</th><th>Full Name</th><th>Phone</th><th>Role</th><th>Created</th><th style="width:80px;"></th></tr></thead>
                <tbody>{rows}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Users", body))


@app.route("/users/<int:user_id>/delete", methods=["POST"])
@boss_required
def delete_user(user_id):
    conn = get_db()

    # Verify the target user belongs to this company
    target = conn.execute(
        "SELECT * FROM users WHERE id=? AND company_id=?", (user_id, cid())
    ).fetchone()
    if not target:
        conn.close()
        flash("User not found.", "error")
        return redirect(url_for("manage_users"))

    # Cannot delete yourself
    if user_id == session["user_id"]:
        conn.close()
        flash("You cannot delete your own account.", "error")
        return redirect(url_for("manage_users"))

    # Cannot delete the last boss
    if target["role"] == "boss":
        boss_count = conn.execute(
            "SELECT COUNT(*) n FROM users WHERE role='boss' AND company_id=?", (cid(),)
        ).fetchone()["n"]
        if boss_count <= 1:
            conn.close()
            flash("Cannot delete the last boss account.", "error")
            return redirect(url_for("manage_users"))

    # If deleting a driver: unassign their active routes (set assigned_to = NULL)
    if target["role"] == "driver":
        conn.execute(
            "UPDATE routes SET assigned_to=NULL WHERE assigned_to=? AND company_id=?",
            (user_id, cid())
        )

    conn.execute("DELETE FROM users WHERE id=? AND company_id=?", (user_id, cid()))
    conn.commit()
    conn.close()

    flash(f"User '{target['username']}' has been deleted.", "success")
    return redirect(url_for("manage_users"))


@app.route("/drivers")
@boss_required
def drivers_page():
    conn = get_db()
    drivers = conn.execute("""
        SELECT u.*, COUNT(DISTINCT r.id) AS routes_assigned,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS completed_stops
        FROM users u
        LEFT JOIN routes r ON r.assigned_to = u.id AND r.company_id = ?
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE u.role='driver' AND u.company_id = ?
        GROUP BY u.id
        ORDER BY u.username
    """, (cid(), cid())).fetchall()
    conn.close()

    cards = ""
    for d in drivers:
        cards += f"""
        <div class="stat">
            <div style="font-size:18px;font-weight:800;">{e(d['username'])}</div>
            <div class="small muted">{e(d['full_name'] or '')}</div>
            <div class="small muted">{e(d['phone'] or '')}</div>
            <div style="margin-top:10px;">Routes Assigned: <b>{d['routes_assigned'] or 0}</b></div>
            <div>Completed Stops: <b>{d['completed_stops'] or 0}</b></div>
        </div>
        """

    body = f"""
    <div class="hero">
        <h1>Drivers</h1>
        <p>See active drivers, route assignments, and stop completion totals.</p>
    </div>
    <div class="grid">{cards if cards else '<div class="stat">No drivers found.</div>'}</div>
    """
    return render_template_string(shell_page("Drivers", body))

@app.route("/signup")
def signup():
    """Legacy signup URL — redirect to company registration."""
    return redirect(url_for("company_register"))

@app.route("/order", methods=["GET", "POST"])
def public_order_form():
    init_db()

    if request.method == "POST":
        customer_name = request.form.get("customer_name", "").strip()
        phone = request.form.get("phone", "").strip()
        email = request.form.get("email", "").strip()
        address = request.form.get("address", "").strip()
        city = request.form.get("city", "").strip()
        state = request.form.get("state", "").strip()
        zip_code = request.form.get("zip_code", "").strip()
        service_type = request.form.get("service_type", "").strip()
        container_size = request.form.get("container_size", "").strip()
        requested_date = request.form.get("requested_date", "").strip()
        notes = request.form.get("notes", "").strip()

        if not customer_name or not address or not service_type:
            flash("Customer name, address, and service type are required.", "error")
            return redirect(url_for("public_order_form"))

        conn = get_db()
        # resolve company from ?company=slug or fall back to first company
        slug = request.args.get("company", "").strip()
        if slug:
            co_row = conn.execute("SELECT id FROM companies WHERE slug=?", (slug,)).fetchone()
        else:
            co_row = conn.execute("SELECT id FROM companies LIMIT 1").fetchone()
        form_company_id = co_row["id"] if co_row else None

        conn.execute("""
            INSERT INTO orders (
                customer_name, phone, email, address, city, state, zip_code,
                service_type, container_size, notes, requested_date, status, company_id, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'new', ?, ?)
        """, (
            customer_name, phone, email, address, city, state, zip_code,
            service_type, container_size, notes, requested_date, form_company_id, now_ts()
        ))
        conn.commit()
        conn.close()

        flash("Your dumpster request has been submitted.", "success")
        return redirect(url_for("public_order_form"))

    body = f"""
    <div style="max-width:760px;margin:0 auto;">
        <div class="hero">
            <h1>Request Dumpster Service</h1>
            <p>Book a drop-off, pickup, or swap from your phone in minutes.</p>
        </div>

        <div class="card">
            <form method="POST">
                <div class="grid">
                    <div>
                        <label>Customer Name</label>
                        <input name="customer_name" required>
                    </div>
                    <div>
                        <label>Phone</label>
                        <input name="phone">
                    </div>
                    <div>
                        <label>Email</label>
                        <input name="email" type="email">
                    </div>
                    <div>
                        <label>Requested Date</label>
                        <input name="requested_date" type="date" value="{today_str()}">
                    </div>
                </div>

                <label>Address</label>
                <input name="address" required>

                <div class="grid">
                    <div>
                        <label>City</label>
                        <input name="city">
                    </div>
                    <div>
                        <label>State</label>
                        <input name="state" maxlength="2">
                    </div>
                    <div>
                        <label>ZIP Code</label>
                        <input name="zip_code">
                    </div>
                </div>

                <div class="grid">
                    <div>
                        <label>Service Type</label>
                        <select name="service_type" required>
                            <option value="Drop">Drop</option>
                            <option value="Pickup">Pickup</option>
                            <option value="Swap">Swap</option>
                            <option value="Dump">Dump</option>
                            <option value="Service">Service</option>
                        </select>
                    </div>
                    <div>
                        <label>Container Size</label>
                        <select name="container_size">
                            <option value="">Select</option>
                            <option value="10">10 yd</option>
                            <option value="12">12 yd</option>
                            <option value="15">15 yd</option>
                            <option value="20">20 yd</option>
                            <option value="30">30 yd</option>
                            <option value="40">40 yd</option>
                        </select>
                    </div>
                </div>

                <label>Notes</label>
                <textarea name="notes" placeholder="Gate code, placement instructions, material type, callback notes, etc."></textarea>

                <div style="margin-top:14px;">
                    <button type="submit">Submit Order</button>
                </div>
            </form>
        </div>
    </div>
    """
    return render_template_string(shell_page("Request Dumpster Service", body))

@app.route("/register", methods=["GET", "POST"])
@boss_required
def register():
    if request.method == "POST":
        username  = request.form.get("username", "").strip()
        password  = request.form.get("password", "").strip()
        role      = request.form.get("role", "").strip()
        full_name = request.form.get("full_name", "").strip()
        phone     = request.form.get("phone", "").strip()

        if not username or not password or role not in ("boss", "driver"):
            flash("Fill everything correctly.", "error")
            return redirect(url_for("register"))

        company_id = cid()
        conn = get_db()

        # enforce driver seat limit from subscription plan
        if role == "driver":
            co = conn.execute("SELECT max_drivers FROM companies WHERE id=?", (company_id,)).fetchone()
            if co:
                current_drivers = conn.execute(
                    "SELECT COUNT(*) n FROM users WHERE role='driver' AND company_id=?",
                    (company_id,)
                ).fetchone()["n"]
                if current_drivers >= co["max_drivers"]:
                    conn.close()
                    flash(f"Driver limit reached ({co['max_drivers']}). Upgrade your plan to add more.", "error")
                    return redirect(url_for("register"))

        try:
            conn.execute(
                """INSERT INTO users (username, password_hash, role, full_name, phone,
                   company_id, created_at) VALUES (?, ?, ?, ?, ?, ?, ?)""",
                (username, generate_password_hash(password), role,
                 full_name, phone, company_id, now_ts())
            )
            conn.commit()
            flash("User created.", "success")
        except sqlite3.IntegrityError:
            flash("Username already exists.", "error")
        finally:
            conn.close()
        return redirect(url_for("manage_users"))

    body = """
    <div class="hero">
        <h1>Create User</h1>
        <p>Add drivers and boss accounts to HAULTRA.</p>
    </div>
    <div class="card">
        <form method="POST">
            <label>Username</label>
            <input name="username" required>
            <label>Password</label>
            <input type="password" name="password" required>
            <label>Full Name</label>
            <input name="full_name">
            <label>Phone</label>
            <input name="phone">
            <label>Role</label>
            <select name="role" required>
                <option value="driver">Driver</option>
                <option value="boss">Boss</option>
            </select>
            <div style="margin-top:10px;"><button type="submit">Create User</button></div>
        </form>
    </div>
    """
    return render_template_string(shell_page("Create User", body))


# =========================================================
# BOSS DASHBOARD
# =========================================================

@app.route("/orders")
@boss_required
def orders_page():
    conn = get_db()
    company_id = cid()
    drivers = conn.execute(
        "SELECT id, username FROM users WHERE role='driver' AND company_id=? ORDER BY username",
        (company_id,)
    ).fetchall()

    orders = conn.execute("""
        SELECT *
        FROM orders
        WHERE company_id = ?
        ORDER BY
            CASE status
                WHEN 'new' THEN 0
                WHEN 'converted' THEN 1
                WHEN 'closed' THEN 2
                ELSE 3
            END,
            id DESC
    """, (company_id,)).fetchall()
    conn.close()

    driver_options = '<option value="">Unassigned</option>'
    for d in drivers:
        driver_options += f'<option value="{d["id"]}">{e(d["username"])}</option>'

    rows = ""
    for o in orders:
        create_route_btn = ""
        close_btn = ""

        if o["status"] == "new":
            create_route_btn = f"""
            <form method="GET" action="{url_for('convert_order_to_route', order_id=o['id'])}">
                <select name="assigned_to" style="min-width:140px;">
                    {driver_options}
                </select>
                <button type="submit" class="btn green">Create Route</button>
            </form>
            """

        if o["status"] != "closed":
            close_btn = f"""
            <form method="POST"
                  action="{url_for('close_order', order_id=o['id'])}"
                  class="inline">
                <button class="btn orange" type="submit">Close</button>
            </form>
            """

        delete_btn = f"""
        <form method="POST"
              action="{url_for('delete_order', order_id=o['id'])}"
              class="inline"
              onsubmit="return confirm('Delete this order?')">
            <button class="btn red" type="submit">Delete</button>
        </form>
        """

        rows += f"""
        <tr>
            <td>{e(o['customer_name'])}</td>
            <td>{e(o['service_type'])}</td>
            <td>{e(o['container_size'] or '')}</td>
            <td>{e(o['address'])}</td>
            <td>{e(o['requested_date'] or '')}</td>
            <td><span class="badge {e(o['status'])}">{e(o['status'])}</span></td>
            <td>
                <div class="row">
                    {create_route_btn}
                    {close_btn}
                    {delete_btn}
                </div>
            </td>
        </tr>
        """

    body = f"""
    <div class="hero">
        <h1>Customer Orders</h1>
        <p>Review customer dumpster requests and convert them into live routes.</p>
    </div>

    <div class="card">
        <div class="row between">
            <h2 style="margin:0;">Incoming Orders</h2>
            <a class="btn secondary" href="{url_for('public_order_form')}">Open Public Form</a>
        </div>

        <div class="table-wrap">
            <table>
                <thead>
                    <tr>
                        <th>Customer</th>
                        <th>Service</th>
                        <th>Size</th>
                        <th>Address</th>
                        <th>Requested</th>
                        <th>Status</th>
                        <th></th>
                    </tr>
                </thead>
                <tbody>
                    {rows if rows else '<tr><td colspan="7">No orders yet.</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Orders", body))

def build_order_raw_text(order_row):
    parts = []
    if order_row["customer_name"]:
        parts.append(f"1. {order_row['customer_name']}")
    if order_row["address"]:
        parts.append(order_row["address"])
    csz = " ".join(filter(None, [
        order_row["city"] if order_row["city"] else "",
        order_row["state"] if order_row["state"] else "",
        order_row["zip_code"] if order_row["zip_code"] else "",
    ])).strip()
    if csz:
        parts.append(csz)
    if order_row["service_type"]:
        parts.append(order_row["service_type"])
    if order_row["container_size"]:
        parts.append(f"{order_row['container_size']} yd")
    if order_row["notes"]:
        parts.append(order_row["notes"])
    return "\n".join(parts)


@app.route("/order/<int:order_id>/convert")
@boss_required
def convert_order_to_route(order_id):
    conn = get_db()
    assigned_to_raw = request.args.get("assigned_to", "").strip()
    assigned_to = int(assigned_to_raw) if assigned_to_raw.isdigit() else None
    order_row = conn.execute(
        "SELECT * FROM orders WHERE id = ? AND company_id = ?",
        (order_id, cid())
    ).fetchone()

    if not order_row:
        conn.close()
        flash("Order not found.", "error")
        return redirect(url_for("orders_page"))

    if order_row["status"] != "new":
        conn.close()
        flash("Order already converted or closed.", "error")
        return redirect(url_for("orders_page"))

    route_date = order_row["requested_date"] or today_str()
    route_name = f"{order_row['service_type']} - {order_row['customer_name']}"
    raw_text = build_order_raw_text(order_row)

    cur = conn.cursor()
    cur.execute("""
        INSERT INTO routes (
            route_date, route_name, raw_text, assigned_to, created_by,
            status, notes, company_id, created_at
        ) VALUES (?, ?, ?, ?, ?, 'open', ?, ?, ?)
    """, (
        route_date,
        route_name,
        raw_text,
        assigned_to,
        session["user_id"],
        f"Created from customer order #{order_row['id']}",
        cid(),
        now_ts()
    ))
    route_id = cur.lastrowid

    parsed_stops, _parsed_dump = parse_boss_text(raw_text)
    for stop in parsed_stops:
        cur.execute("""
            INSERT INTO stops (
                route_id, stop_order, customer_name, address, city, state, zip_code,
                action, container_size, ticket_number, reference_number, dump_location, notes,
                status, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'open', ?)
        """, (
            route_id,
            stop["stop_order"],
            stop["customer_name"],
            stop["address"],
            stop["city"],
            stop["state"],
            stop["zip_code"],
            stop["action"],
            stop["container_size"],
            stop["ticket_number"],
            stop["reference_number"],
            stop.get("dump_location", ""),
            stop["notes"],
            now_ts()
        ))

    cur.execute("UPDATE orders SET status = 'converted' WHERE id = ?", (order_id,))
    conn.commit()
    conn.close()

    flash("Order converted into a route.", "success")
    return redirect(url_for("view_route", route_id=route_id))

@app.route("/boss")
@boss_required
def boss_dashboard():
    conn = get_db()

    company_id = cid()

    # --- summary counts ---
    total_routes    = conn.execute("SELECT COUNT(*) AS n FROM routes WHERE company_id=?", (company_id,)).fetchone()["n"]
    open_routes     = conn.execute("SELECT COUNT(*) AS n FROM routes WHERE company_id=? AND status='open'", (company_id,)).fetchone()["n"]
    progress_routes = conn.execute("SELECT COUNT(*) AS n FROM routes WHERE company_id=? AND status='in_progress'", (company_id,)).fetchone()["n"]
    completed_routes= conn.execute("SELECT COUNT(*) AS n FROM routes WHERE company_id=? AND status='completed'", (company_id,)).fetchone()["n"]
    total_stops     = conn.execute("SELECT COUNT(*) AS n FROM stops s JOIN routes r ON s.route_id=r.id WHERE r.company_id=?", (company_id,)).fetchone()["n"]
    completed_stops = conn.execute("SELECT COUNT(*) AS n FROM stops s JOIN routes r ON s.route_id=r.id WHERE r.company_id=? AND s.status='completed'", (company_id,)).fetchone()["n"]
    drivers_count   = conn.execute("SELECT COUNT(*) AS n FROM users WHERE role='driver' AND company_id=?", (company_id,)).fetchone()["n"]
    new_orders      = conn.execute("SELECT COUNT(*) AS n FROM orders WHERE status='new' AND company_id=?", (company_id,)).fetchone()["n"]

    # --- active routes (open + in_progress) with per-route stop progress ---
    active_routes = conn.execute("""
        SELECT r.id, r.route_name, r.route_date, r.status, r.assigned_to,
               COALESCE(u.username, 'Unassigned') AS assigned_username,
               COUNT(s.id) AS total_stops,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS done_stops
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE r.status IN ('open', 'in_progress') AND r.company_id = ?
        GROUP BY r.id
        ORDER BY CASE r.status WHEN 'in_progress' THEN 0 ELSE 1 END,
                 r.route_date DESC, r.id DESC
    """, (company_id,)).fetchall()

    # --- recently completed routes (capped at 25) ---
    recent_completed = conn.execute("""
        SELECT r.id, r.route_name, r.route_date, r.status, r.assigned_to,
               COALESCE(u.username, 'Unassigned') AS assigned_username,
               COUNT(s.id) AS total_stops,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS done_stops
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE r.status = 'completed' AND r.company_id = ?
        GROUP BY r.id
        ORDER BY r.route_date DESC, r.id DESC
        LIMIT 25
    """, (company_id,)).fetchall()

    # --- driver performance ---
    driver_stats = conn.execute("""
        SELECT u.id, u.username,
               COUNT(DISTINCT r.id) AS route_count,
               COUNT(s.id) AS stop_count,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS completed_stop_count,
               SUM(CASE WHEN r.status='in_progress' THEN 1 ELSE 0 END) AS active_routes
        FROM users u
        LEFT JOIN routes r ON r.assigned_to = u.id AND r.company_id = ?
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE u.role = 'driver' AND u.company_id = ?
        GROUP BY u.id
        ORDER BY u.username
    """, (company_id, company_id)).fetchall()

    # --- all drivers for reassign dropdowns ---
    all_drivers = conn.execute(
        "SELECT id, username FROM users WHERE role='driver' AND company_id=? ORDER BY username",
        (company_id,)
    ).fetchall()

    conn.close()

    # --- build driver options string (reused per route row) ---
    def driver_opts(current_id):
        opts = '<option value="">Unassigned</option>'
        for d in all_drivers:
            sel = " selected" if d["id"] == current_id else ""
            opts += f'<option value="{d["id"]}"{sel}>{e(d["username"])}</option>'
        return opts

    # --- route row builder ---
    def route_row(r, show_reassign=True):
        total = r["total_stops"] or 0
        done  = r["done_stops"] or 0
        pct   = int(done / total * 100) if total else 0
        status_label = e(r["status"].replace("_", " ").title())
        row_class = "status-in-progress" if r["status"] == "in_progress" else ""
        progress_cell = f"""
            <div style="display:flex;align-items:center;gap:8px;">
                <div class="mini-prog-track"><div class="mini-prog-fill" style="width:{pct}%"></div></div>
                <span style="font-size:12px;color:#9dc8f0;">{done}/{total}</span>
            </div>"""
        reassign_cell = ""
        if show_reassign:
            reassign_cell = f"""
            <form class="inline-reassign" method="POST"
                  action="{url_for('reassign_route', route_id=r['id'])}">
                <select name="driver_id" class="compact-select">
                    {driver_opts(r['assigned_to'])}
                </select>
                <button class="btn-reassign" type="submit">Save</button>
            </form>"""
        return f"""
        <tr class="{row_class}">
            <td>
                <a href="{url_for('view_route', route_id=r['id'])}">{e(r['route_name'])}</a>
                <br><a href="{url_for('route_daily_log', route_id=r['id'])}"
                       style="font-size:11px;color:#9dc8f0;">&#x1F4CB; Daily Log</a>
            </td>
            <td style="white-space:nowrap;">{e(r['route_date'] or '')}</td>
            <td><span class="badge {e(r['status'])}">{status_label}</span></td>
            <td>{e(r['assigned_username'])}</td>
            <td>{progress_cell}</td>
            <td>{reassign_cell}</td>
        </tr>"""

    active_rows   = "".join(route_row(r) for r in active_routes) or \
        '<tr><td colspan="6" style="text-align:center;color:#9dc8f0;">No active routes.</td></tr>'
    completed_rows= "".join(route_row(r, show_reassign=False) for r in recent_completed) or \
        '<tr><td colspan="6" style="text-align:center;color:#9dc8f0;">None yet.</td></tr>'

    route_thead = """<thead><tr>
        <th>Route</th><th>Date</th><th>Status</th>
        <th>Driver</th><th>Progress</th><th>Reassign</th>
    </tr></thead>"""
    completed_thead = """<thead><tr>
        <th>Route</th><th>Date</th><th>Status</th>
        <th>Driver</th><th>Progress</th><th></th>
    </tr></thead>"""

    driver_rows = ""
    for d in driver_stats:
        s_total = d["stop_count"] or 0
        s_done  = d["completed_stop_count"] or 0
        pct     = int(s_done / s_total * 100) if s_total else 0
        active_badge = (f'<span class="badge in_progress" style="font-size:11px;">'
                        f'{d["active_routes"] or 0} active</span>') if (d["active_routes"] or 0) > 0 else ""
        driver_rows += f"""
        <tr>
            <td>{e(d['username'])} {active_badge}</td>
            <td>{d['route_count'] or 0}</td>
            <td>
                <div style="display:flex;align-items:center;gap:8px;">
                    <div class="mini-prog-track"><div class="mini-prog-fill" style="width:{pct}%"></div></div>
                    <span style="font-size:12px;color:#9dc8f0;">{s_done}/{s_total}</span>
                </div>
            </td>
        </tr>"""

    body = f"""
    <div class="hero">
        <h1>Boss Panel</h1>
        <p>Live overview of all routes, driver progress, and assignments.</p>
    </div>

    <div class="grid">
        <div class="stat"><div>Total Routes</div><div class="num">{total_routes}</div></div>
        <div class="stat"><div>Open</div><div class="num">{open_routes}</div></div>
        <div class="stat" style="border-color:rgba(245,158,11,0.45);">
            <div>In Progress</div><div class="num" style="color:#fbbf24;">{progress_routes}</div>
        </div>
        <div class="stat" style="border-color:rgba(34,197,94,0.35);">
            <div>Completed</div><div class="num" style="color:#4ade80;">{completed_routes}</div>
        </div>
        <div class="stat"><div>Total Stops</div><div class="num">{total_stops}</div></div>
        <div class="stat" style="border-color:rgba(34,197,94,0.35);">
            <div>Stops Done</div><div class="num" style="color:#4ade80;">{completed_stops}</div>
        </div>
        <div class="stat"><div>Drivers</div><div class="num">{drivers_count}</div></div>
        <div class="stat"><div>New Orders</div><div class="num">{new_orders}</div></div>
    </div>

    <div class="card">
        <h2>&#128338; Active Routes</h2>
        <div class="table-wrap">
            <table>
                {route_thead}
                <tbody>{active_rows}</tbody>
            </table>
        </div>
    </div>

    <div class="card">
        <h2>&#10003; Recently Completed</h2>
        <div class="table-wrap">
            <table>
                {completed_thead}
                <tbody>{completed_rows}</tbody>
            </table>
        </div>
    </div>

    <div class="card">
        <h2>&#128100; Driver Performance</h2>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Driver</th><th>Routes</th><th>Stops Progress</th></tr></thead>
                <tbody>{driver_rows if driver_rows else '<tr><td colspan="3">No drivers.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Boss Panel", body))

# =========================================================
# REASSIGN ROUTE
# =========================================================
@app.route("/route/<int:route_id>/reassign", methods=["POST"])
@boss_required
def reassign_route(route_id):
    driver_id_raw = request.form.get("driver_id", "").strip()
    driver_id = int(driver_id_raw) if driver_id_raw.isdigit() else None

    conn = get_db()
    route = conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone()
    if not route:
        conn.close()
        abort(404)

    if driver_id is not None:
        driver = conn.execute(
            "SELECT id FROM users WHERE id=? AND role='driver' AND company_id=?",
            (driver_id, cid())
        ).fetchone()
        if not driver:
            conn.close()
            flash("Driver not found.", "error")
            return redirect(url_for("boss_dashboard"))

    conn.execute("UPDATE routes SET assigned_to=? WHERE id=? AND company_id=?",
                 (driver_id, route_id, cid()))
    conn.commit()
    conn.close()
    flash("Route reassigned.", "success")
    return redirect(url_for("boss_dashboard"))


# =========================================
# TEXT TO ROUTE  (parse → preview → confirm)
# =========================================

@app.route("/text-to-route", methods=["GET", "POST"])
@boss_required
def text_to_route():
    conn = get_db()
    company_id = cid()
    drivers = conn.execute(
        "SELECT id, username FROM users WHERE role='driver' AND company_id=? ORDER BY username",
        (company_id,)
    ).fetchall()
    dump_locs = conn.execute(
        "SELECT id, name, city FROM dump_locations WHERE active=1 ORDER BY name"
    ).fetchall()

    if request.method == "POST":
        parse_step = request.form.get("parse_step", "preview")

        # ── CONFIRM: save the route from the edited preview ──────────────────
        if parse_step == "confirm":
            route_date       = request.form.get("route_date",       "").strip() or today_str()
            route_name       = request.form.get("route_name",       "").strip()
            assigned_to_raw  = request.form.get("assigned_to",      "").strip()
            route_notes      = request.form.get("route_notes",      "").strip()
            dump_location_id = request.form.get("dump_location_id", "").strip()
            raw_text_hidden  = request.form.get("raw_text_hidden",  "").strip()
            stop_count_raw   = request.form.get("stop_count",       "0")

            assigned_to       = int(assigned_to_raw)  if assigned_to_raw.isdigit()  else None
            dump_location_val = int(dump_location_id) if dump_location_id.isdigit() else None
            stop_count        = int(stop_count_raw)   if stop_count_raw.isdigit()   else 0

            if not route_name:
                conn.close()
                flash("Route name is required.", "error")
                return redirect(url_for("text_to_route"))

            final_stops = []
            for i in range(stop_count):
                if request.form.get(f"stop_{i}_skip"):
                    continue
                cust = request.form.get(f"stop_{i}_customer_name", "").strip()
                addr = request.form.get(f"stop_{i}_address",       "").strip()
                if not cust and not addr:
                    continue
                final_stops.append({
                    "customer_name":  cust,
                    "address":        addr,
                    "city":           request.form.get(f"stop_{i}_city",           "").strip(),
                    "state":          request.form.get(f"stop_{i}_state",          "").strip(),
                    "zip_code":       request.form.get(f"stop_{i}_zip_code",       "").strip(),
                    "action":         request.form.get(f"stop_{i}_action",  "Service").strip(),
                    "container_size": request.form.get(f"stop_{i}_container_size", "").strip(),
                    "dump_location":  request.form.get(f"stop_{i}_dump_location",  "").strip(),
                    "ticket_number":  request.form.get(f"stop_{i}_ticket_number",  "").strip(),
                    "notes":          request.form.get(f"stop_{i}_notes",          "").strip(),
                })

            if not final_stops:
                conn.close()
                flash("No stops to save.", "error")
                return redirect(url_for("text_to_route"))

            cur = conn.cursor()
            cur.execute("""
                INSERT INTO routes (
                    route_date, route_name, raw_text, assigned_to, created_by,
                    status, notes, dump_location_id, company_id, created_at
                ) VALUES (?, ?, ?, ?, ?, 'open', ?, ?, ?, ?)
            """, (route_date, route_name, raw_text_hidden, assigned_to,
                  session["user_id"], route_notes, dump_location_val,
                  company_id, now_ts()))
            route_id = cur.lastrowid

            for order_num, stop in enumerate(final_stops, start=1):
                cur.execute("""
                    INSERT INTO stops (
                        route_id, stop_order, customer_name, address, city, state, zip_code,
                        action, container_size, ticket_number, reference_number,
                        dump_location, notes, status, created_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, '', ?, ?, 'open', ?)
                """, (route_id, order_num, stop["customer_name"], stop["address"],
                      stop["city"], stop["state"], stop["zip_code"], stop["action"],
                      stop["container_size"], stop.get("ticket_number", ""),
                      stop["dump_location"], stop["notes"], now_ts()))

            conn.commit()
            conn.close()
            flash(f"Route created with {len(final_stops)} stop(s).", "success")
            return redirect(url_for("view_route", route_id=route_id))

        # ── PREVIEW: parse text, show editable stop cards ────────────────────
        route_date       = request.form.get("route_date",       "").strip() or today_str()
        route_name       = request.form.get("route_name",       "").strip()
        raw_text         = request.form.get("raw_text",         "").strip()
        assigned_to_raw  = request.form.get("assigned_to",      "").strip()
        route_notes      = request.form.get("notes",            "").strip()
        dump_location_id = request.form.get("dump_location_id", "").strip()

        if not route_name or not raw_text:
            conn.close()
            flash("Route name and pasted text are required.", "error")
            return redirect(url_for("text_to_route"))

        parsed_stops, _dump = parse_boss_text(raw_text)

        if not parsed_stops:
            conn.close()
            flash("No stops could be parsed from the text. Check format and try again.", "error")
            return redirect(url_for("text_to_route"))

        # Driver name for summary bar
        assigned_name = next(
            (d["username"] for d in drivers if str(d["id"]) == assigned_to_raw), ""
        )

        _STOP_ACTION_OPTS = [
            "Pull", "Pickup and Return", "Delivery", "Relocate",
            "Swap", "Move", "Service", "Dump",
        ]

        # Confidence counts for summary bar
        _conf_counts = {"high": 0, "medium": 0, "low": 0}
        for s in parsed_stops:
            _conf_counts[s.get("confidence_label", "low")] = \
                _conf_counts.get(s.get("confidence_label", "low"), 0) + 1

        # Build per-stop editable cards
        stop_cards_html = ""
        for i, stop in enumerate(parsed_stops):
            orig_text = e(stop.get("original_line") or "")
            orig_html = (
                f'<div class="p-orig">Parsed from: &ldquo;{orig_text}&rdquo;</div>'
            ) if orig_text else ""

            conf_label = stop.get("confidence_label", "low")
            if conf_label == "high":
                conf_badge = '<span class="p-badge p-badge-hi">&#10003; HIGH</span>'
                card_border = "rgba(86,240,183,0.35)"
            elif conf_label == "medium":
                conf_badge = '<span class="p-badge p-badge-med">&#9888; MED</span>'
                card_border = "rgba(240,192,86,0.35)"
            else:
                conf_badge = '<span class="p-badge p-badge-low">? LOW &#8212; review</span>'
                card_border = "rgba(240,112,86,0.55)"

            action_val = stop.get("action") or "Service"
            act_opts = ""
            for opt in _STOP_ACTION_OPTS:
                sel = "selected" if opt.lower() == action_val.lower() else ""
                act_opts += f'<option value="{e(opt)}" {sel}>{e(opt)}</option>'

            # Relocate from/to row (only shown when present)
            rel_from = e(stop.get("relocate_from_address", "") or "")
            rel_to   = e(stop.get("relocate_to_address",   "") or "")
            relocate_row = ""
            if rel_from or rel_to:
                relocate_row = f"""
    <div class="p-col-full" style="background:rgba(120,100,240,0.10);border-radius:6px;padding:8px 10px;">
      <span class="p-lbl">Relocate: FROM</span>
      <span style="font-size:13px;color:#c0b8f8;">{rel_from or "(see address)"}</span>
      <span style="margin:0 8px;color:#7a9ab8;">&#8594;</span>
      <span class="p-lbl" style="display:inline;">TO&nbsp;</span>
      <span style="font-size:13px;color:#c0b8f8;">{rel_to or "(not detected)"}</span>
    </div>"""

            # Ticket number display
            ticket_val = e(stop.get("ticket_number") or "")
            ticket_row = (
                f'<div><label class="p-lbl">Ticket #</label>'
                f'<input name="stop_{i}_ticket_number" value="{ticket_val}" placeholder="TKT#"></div>'
            ) if ticket_val else ""

            stop_cards_html += f"""
<div class="p-stop-card" id="psc-{i}" style="border-color:{card_border};">
  <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;">
    <div style="font-weight:700;font-size:14px;">Stop {i + 1}&nbsp;{conf_badge}</div>
    <label style="display:flex;align-items:center;gap:5px;cursor:pointer;font-size:12px;color:#f07056;">
      <input type="checkbox" name="stop_{i}_skip" value="1"
             onchange="document.getElementById('psc-{i}').style.opacity=this.checked?'0.35':'1'">
      Skip
    </label>
  </div>
  {orig_html}
  {relocate_row}
  <div class="p-stop-grid">
    <div class="p-col-wide">
      <label class="p-lbl">Customer Name</label>
      <input name="stop_{i}_customer_name" value="{e(stop.get('customer_name',''))}" placeholder="Customer name">
    </div>
    <div class="p-col-wide">
      <label class="p-lbl">Address</label>
      <input name="stop_{i}_address" value="{e(stop.get('address',''))}" placeholder="Street address">
    </div>
    <div>
      <label class="p-lbl">City</label>
      <input name="stop_{i}_city" value="{e(stop.get('city',''))}">
    </div>
    <div>
      <label class="p-lbl">State</label>
      <input name="stop_{i}_state" value="{e(stop.get('state','VA'))}" maxlength="2" style="width:60px;">
    </div>
    <div>
      <label class="p-lbl">Service Type</label>
      <select name="stop_{i}_action" class="p-sel">{act_opts}</select>
    </div>
    <div>
      <label class="p-lbl">Can Size</label>
      <input name="stop_{i}_container_size" value="{e(stop.get('container_size',''))}" placeholder="30yd" style="width:80px;">
    </div>
    <div>
      <label class="p-lbl">Dump Location</label>
      <input name="stop_{i}_dump_location" value="{e(stop.get('dump_location',''))}" placeholder="Dominion">
    </div>
    {ticket_row}
    <div class="p-col-wide">
      <label class="p-lbl">Notes</label>
      <input name="stop_{i}_notes" value="{e(stop.get('notes',''))}" placeholder="Gate code, instructions...">
    </div>
  </div>
  <input type="hidden" name="stop_{i}_zip_code" value="{e(stop.get('zip_code',''))}">
</div>"""

        conn.close()

        _n_low = _conf_counts["low"]
        _low_warning = (
            f'<div style="background:rgba(240,112,86,0.12);border:1px solid rgba(240,112,86,0.4);'
            f'border-radius:8px;padding:10px 14px;margin-bottom:12px;font-size:13px;">'
            f'&#9888;&nbsp;<strong>{_n_low} stop{"s" if _n_low != 1 else ""} need review</strong>'
            f' &mdash; low-confidence fields are highlighted in orange. Edit before saving.</div>'
        ) if _n_low else ""

        body = f"""
<style>
.p-stop-card {{
  background: var(--card-bg, #1a2235);
  border: 1px solid rgba(255,255,255,0.07);
  border-radius: 10px;
  padding: 16px;
  margin-bottom: 10px;
  transition: opacity 0.2s;
}}
.p-stop-grid {{
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 8px 10px;
  margin-top: 10px;
}}
.p-col-wide {{ grid-column: span 2; }}
.p-col-full {{ grid-column: 1 / -1; margin-bottom: 6px; }}
@media (min-width: 680px) {{
  .p-stop-grid {{ grid-template-columns: 1fr 1fr 1fr; }}
  .p-col-wide {{ grid-column: span 2; }}
}}
.p-lbl {{ font-size: 11px; color: #7a9ab8; display: block; margin-bottom: 3px; }}
.p-sel {{
  width: 100%;
  background: var(--input-bg, #0f1724);
  color: inherit;
  border: 1px solid var(--border, rgba(255,255,255,0.1));
  border-radius: 6px;
  padding: 7px 10px;
  font-size: 14px;
}}
.p-badge {{
  font-size: 11px;
  font-weight: 700;
  padding: 2px 7px;
  border-radius: 4px;
  vertical-align: middle;
}}
.p-badge-hi  {{ background: rgba(86,240,183,0.15); color: #56f0b7; }}
.p-badge-med {{ background: rgba(240,192,86,0.15);  color: #f0c056; }}
.p-badge-low {{ background: rgba(240,112,86,0.18);  color: #f07056; }}
.p-orig {{
  font-size: 11px;
  color: #7a9ab8;
  font-style: italic;
  margin-bottom: 8px;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}}
</style>
<div class="hero">
  <h1>Preview Route</h1>
  <p>Review and edit each stop before saving. Orange border = low confidence &mdash; check those fields.</p>
</div>
<div class="card" style="margin-bottom:12px;padding:14px 18px;">
  <div style="display:flex;gap:20px;flex-wrap:wrap;align-items:flex-start;">
    <div><span style="font-size:11px;color:#7a9ab8;">Route</span><br><strong>{e(route_name)}</strong></div>
    <div><span style="font-size:11px;color:#7a9ab8;">Date</span><br><strong>{route_date}</strong></div>
    <div><span style="font-size:11px;color:#7a9ab8;">Driver</span><br><strong>{e(assigned_name) or "Unassigned"}</strong></div>
    <div><span style="font-size:11px;color:#7a9ab8;">Stops detected</span><br><strong>{len(parsed_stops)}</strong></div>
    <div><span style="font-size:11px;color:#56f0b7;">&#10003; High</span>&nbsp;
         <strong style="color:#56f0b7;">{_conf_counts["high"]}</strong>&ensp;
         <span style="font-size:11px;color:#f0c056;">&#9888; Med</span>&nbsp;
         <strong style="color:#f0c056;">{_conf_counts["medium"]}</strong>&ensp;
         <span style="font-size:11px;color:#f07056;">? Low</span>&nbsp;
         <strong style="color:#f07056;">{_conf_counts["low"]}</strong></div>
  </div>
</div>
{_low_warning}
<form method="POST">
  <input type="hidden" name="parse_step"      value="confirm">
  <input type="hidden" name="route_name"       value="{e(route_name)}">
  <input type="hidden" name="route_date"       value="{e(route_date)}">
  <input type="hidden" name="assigned_to"      value="{e(assigned_to_raw)}">
  <input type="hidden" name="route_notes"      value="{e(route_notes)}">
  <input type="hidden" name="dump_location_id" value="{e(dump_location_id)}">
  <input type="hidden" name="raw_text_hidden"  value="{e(raw_text)}">
  <input type="hidden" name="stop_count"       value="{len(parsed_stops)}">
  {stop_cards_html}
  <div style="display:flex;gap:10px;margin-top:16px;flex-wrap:wrap;">
    <button type="submit" class="btn green" style="flex:1;min-width:200px;">
      &#10003; Create Route ({len(parsed_stops)} stops)
    </button>
    <a href="{url_for('text_to_route')}" class="btn secondary">&#8592; Back</a>
  </div>
</form>"""
        return render_template_string(shell_page("Preview Route", body))

    # ── GET: show the paste form ──────────────────────────────────────────────
    driver_options = '<option value="">Unassigned</option>'
    for d in drivers:
        driver_options += f'<option value="{d["id"]}">{e(d["username"])}</option>'

    dump_options = '<option value="">— No dump location —</option>'
    for dl in dump_locs:
        city_label = f" ({e(dl['city'])})" if dl['city'] else ""
        dump_options += f'<option value="{dl["id"]}">{e(dl["name"])}{city_label}</option>'

    conn.close()

    body = f"""
<div class="hero">
  <h1>Text to Route</h1>
  <p>Paste route text in any format. HAULTRA detects stops automatically.</p>
</div>
<div class="card">
  <form method="POST">
    <label>Route Name</label>
    <input name="route_name" placeholder="Friday Roll Off Route" required>
    <label>Route Date</label>
    <input type="date" name="route_date" value="{today_str()}" required>
    <label>Assign Driver</label>
    <select name="assigned_to">{driver_options}</select>
    <label>Route-level Dump Location</label>
    <select name="dump_location_id">{dump_options}</select>
    <label>Route Text</label>
    <textarea name="raw_text" rows="10"
      placeholder="Paste boss text here..."
      required
      style="font-family:monospace;font-size:13px;min-height:160px;"></textarea>
    <label>Notes</label>
    <textarea name="notes" placeholder="Extra route instructions..."></textarea>
    <div style="margin-top:10px;">
      <button type="submit" name="parse_step" value="preview" class="btn green">
        Preview Stops &rarr;
      </button>
    </div>
  </form>
</div>
<div class="card">
  <div style="font-size:12px;font-weight:600;color:#7a9ab8;margin-bottom:10px;">SUPPORTED FORMATS</div>
  <div style="display:grid;grid-template-columns:1fr 1fr;gap:10px;">
    <div style="background:rgba(255,255,255,0.03);border-radius:8px;padding:12px;">
      <div style="font-size:10px;color:#7a9ab8;font-weight:700;margin-bottom:5px;">ROLL-OFF (commas)</div>
      <code style="font-size:12px;color:#56f0b7;display:block;">Pr 5660 lowery rd,vb, jaswal 30yd dump dom</code>
      <code style="font-size:12px;color:#56f0b7;display:block;">Pull 280 benton,suff, power bolt 20yd</code>
    </div>
    <div style="background:rgba(255,255,255,0.03);border-radius:8px;padding:12px;">
      <div style="font-size:10px;color:#7a9ab8;font-weight:700;margin-bottom:5px;">FREEFORM (no commas)</div>
      <code style="font-size:12px;color:#56f0b7;display:block;">Pull 4915 Broad St vb rhr 30yd dump dom</code>
      <code style="font-size:12px;color:#56f0b7;display:block;">R 7801 Shore Dr norf smith 20yd</code>
    </div>
    <div style="background:rgba(255,255,255,0.03);border-radius:8px;padding:12px;">
      <div style="font-size:10px;color:#7a9ab8;font-weight:700;margin-bottom:5px;">PIPE / STRUCTURED</div>
      <code style="font-size:12px;color:#56f0b7;display:block;">Smith | 123 Main St Norfolk | PR | 30yd</code>
      <code style="font-size:12px;color:#56f0b7;display:block;">Jones | 4100 Holland Rd VB | Delivery | 20yd</code>
    </div>
    <div style="background:rgba(255,255,255,0.03);border-radius:8px;padding:12px;">
      <div style="font-size:10px;color:#7a9ab8;font-weight:700;margin-bottom:5px;">WORK ORDER (typed)</div>
      <code style="font-size:12px;color:#56f0b7;display:block;">PR 1233 Westover Ave, Norfolk, VA, ringen 30yd</code>
      <code style="font-size:12px;color:#56f0b7;display:block;">D 2431 Southern Pines, Chesapeake, Roof Joe 20yd</code>
    </div>
  </div>
</div>"""
    return render_template_string(shell_page("Text to Route", body))

# =========================================================
# ROUTES / STOPS
# =========================================================
@app.route("/routes")
@login_required
def routes_page():
    user = get_current_user()
    conn = get_db()
    q = request.args.get("q", "").strip()
    status = request.args.get("status", "").strip()

    params = [cid()]
    sql = """
        SELECT r.*, u.username AS assigned_username, c.username AS created_username
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        LEFT JOIN users c ON r.created_by = c.id
        WHERE r.company_id = ?
    """

    if user["role"] != "boss":
        sql += " AND r.assigned_to = ?"
        params.append(user["id"])

    if q:
        sql += " AND (r.route_name LIKE ? OR r.notes LIKE ? OR r.raw_text LIKE ?)"
        like_q = f"%{q}%"
        params.extend([like_q, like_q, like_q])

    if status in ("open", "in_progress", "completed"):
        sql += " AND r.status = ?"
        params.append(status)

    sql += " ORDER BY r.route_date DESC, r.id DESC"

    routes = conn.execute(sql, tuple(params)).fetchall()
    conn.close()

    rows = ""
    for r in routes:
        rows += f"""
        <tr>
            <td>{e(r['route_date'])}</td>
            <td><a href="{url_for('view_route', route_id=r['id'])}">{e(r['route_name'])}</a></td>
            <td>{e(r['assigned_username'] or 'Unassigned')}</td>
            <td>{e(r['created_username'] or '')}</td>
            <td><span class="badge {e(r['status'])}">{e(r['status'])}</span></td>
            <td>
                <div class="row">
                  <td>
    <div class="row">
        <a class="btn secondary" href="{url_for('view_route', route_id=r['id'])}">Open</a>
        <a class="btn green" href="{url_for('export_route_csv', route_id=r['id'])}">CSV</a>

        {f'''
        <form class="inline" method="POST"
              action="{url_for('delete_route', route_id=r['id'])}"
              onsubmit="return confirm('Delete this entire route?')">
            <button class="btn red" type="submit">Delete</button>
        </form>
        ''' if user['role'] == 'boss' else ''}

    </div>
</td>
                </div>
            </td>
        </tr>
        """

    body = f"""
    <div class="hero">
        <h1>Routes</h1>
        <p>Search, filter, open, export, and manage route flow.</p>
    </div>
    {f'''
    <div class="row" style="margin-bottom:18px;gap:10px;">
        <a class="btn gold" href="{url_for('new_route')}">+ Create Route</a>
        <a class="btn secondary" href="{url_for('text_to_route')}">⌨ Paste Boss Text</a>
    </div>
    ''' if user['role'] == 'boss' else ''}
    <div class="card">
        <form method="GET" class="row">
            <div style="flex:1;min-width:220px;">
                <label>Search</label>
                <input name="q" value="{e(q)}" placeholder="Route name, notes, or pasted route text">
            </div>
            <div style="min-width:180px;">
                <label>Status</label>
                <select name="status">
                    <option value="">All</option>
                    <option value="open" {'selected' if status=='open' else ''}>Open</option>
                    <option value="in_progress" {'selected' if status=='in_progress' else ''}>In Progress</option>
                    <option value="completed" {'selected' if status=='completed' else ''}>Completed</option>
                </select>
            </div>
            <div style="align-self:flex-end;">
                <button type="submit">Filter</button>
            </div>
        </form>
    </div>
    <div class="card">
        <div class="row between">
            <h2 style="margin:0;">All Routes</h2>
        </div>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Date</th><th>Route</th><th>Assigned</th><th>Created By</th><th>Status</th><th>Actions</th></tr></thead>
                <tbody>{rows if rows else '<tr><td colspan="6">No routes found.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Routes", body))


@app.route("/route/new", methods=["GET", "POST"])
@boss_required
def new_route():
    conn = get_db()
    drivers = conn.execute(
        "SELECT id, username FROM users WHERE role='driver' AND company_id=? ORDER BY username",
        (cid(),)
    ).fetchall()
    dump_locs = conn.execute(
        "SELECT id, name, city FROM dump_locations WHERE active=1 ORDER BY name"
    ).fetchall()

    if request.method == "POST":
        route_name       = request.form.get("route_name", "").strip()
        route_date       = request.form.get("route_date", today_str()).strip()
        assigned_to      = request.form.get("assigned_to", "").strip()
        raw_text         = request.form.get("raw_text", "").strip()
        notes            = request.form.get("notes", "").strip()
        dump_location_id = request.form.get("dump_location_id", "").strip()

        if not route_name:
            flash("Route name required.", "error")
            conn.close()
            return redirect(url_for("new_route"))

        assigned_to_val    = int(assigned_to) if assigned_to.isdigit() else None
        dump_location_val  = int(dump_location_id) if dump_location_id.isdigit() else None
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO routes (route_date, route_name, raw_text, assigned_to, created_by,
                                status, notes, dump_location_id, company_id, created_at)
            VALUES (?, ?, ?, ?, ?, 'open', ?, ?, ?, ?)
        """, (route_date, route_name, raw_text, assigned_to_val, session["user_id"],
              notes, dump_location_val, cid(), now_ts()))
        route_id = cur.lastrowid

        parsed_stops, _parsed_dump = parse_boss_text(raw_text)
        for stop in parsed_stops:
            cur.execute("""
                INSERT INTO stops (
                    route_id, stop_order, customer_name, address, city, state, zip_code,
                    action, container_size, ticket_number, reference_number, dump_location, notes,
                    status, created_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'open', ?)
            """, (
                route_id,
                stop["stop_order"],
                stop["customer_name"],
                stop["address"],
                stop["city"],
                stop["state"],
                stop["zip_code"],
                stop["action"],
                stop["container_size"],
                stop["ticket_number"],
                stop["reference_number"],
                stop.get("dump_location", ""),
                stop["notes"],
                now_ts()
            ))

        conn.commit()
        conn.close()
        flash(f"Route created with {len(parsed_stops)} parsed stops.", "success")
        return redirect(url_for("view_route", route_id=route_id))

    conn.close()
    driver_options = '<option value="">Unassigned</option>'
    for d in drivers:
        driver_options += f'<option value="{d["id"]}">{e(d["username"])}</option>'

    dump_options = '<option value="">— No dump location —</option>'
    for dl in dump_locs:
        city_label = f" ({e(dl['city'])})" if dl['city'] else ""
        dump_options += f'<option value="{dl["id"]}">{e(dl["name"])}{city_label}</option>'

    body = f"""
    <div class="hero">
        <h1>Create Route</h1>
    </div>
    <div class="card">
        <form method="POST">
            <label>Route Name</label>
            <input name="route_name" placeholder="Friday Roll Off Route" required>
            <label>Route Date</label>
            <input type="date" name="route_date" value="{today_str()}" required>
            <label>Assign Driver</label>
            <select name="assigned_to">{driver_options}</select>
            <label>Dump Location</label>
            <select name="dump_location_id">{dump_options}</select>
            <label>Route Text</label>
            <textarea name="raw_text" placeholder="Paste route text to auto-parse stops..."></textarea>
            <label>Notes</label>
            <textarea name="notes" placeholder="Extra route instructions..."></textarea>
            <div style="margin-top:10px;"><button type="submit">Create Route + Parse Stops</button></div>
        </form>
    </div>
    """
    return render_template_string(shell_page("Create Route", body))

@app.route("/driver/route/<int:route_id>")
@driver_required
def driver_route_detail(route_id):
    conn = get_db()
    route = conn.execute("""
        SELECT r.*, u.username AS assigned_username
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        WHERE r.id = ? AND r.assigned_to = ?
    """, (route_id, session["user_id"])).fetchone()

    if not route:
        conn.close()
        flash("Route not found.", "error")
        return redirect(url_for("driver_dashboard"))

    stops = conn.execute("""
        SELECT *
        FROM stops
        WHERE route_id = ?
        ORDER BY stop_order ASC, id ASC
    """, (route_id,)).fetchall()

    # Ensure can_state_before is populated so PR mode always shows correctly
    if stops and any(s["can_state_before"] is None for s in stops):
        compute_can_flow(conn, route_id)
        conn.commit()
        stops = conn.execute("""
            SELECT *
            FROM stops
            WHERE route_id = ?
            ORDER BY stop_order ASC, id ASC
        """, (route_id,)).fetchall()

    stop_ids = [s["id"] for s in stops]
    photos_by_stop = load_stop_photos(conn, stop_ids)

    dump_loc = None
    if route["dump_location_id"]:
        dump_loc = conn.execute(
            "SELECT * FROM dump_locations WHERE id=?", (route["dump_location_id"],)
        ).fetchone()

    # Load all active dump locations keyed by lowercase name for per-stop nav lookup
    _dump_loc_rows = conn.execute(
        "SELECT name, address, city, state, zip_code FROM dump_locations WHERE active=1"
    ).fetchall()
    _dump_loc_by_name = {r["name"].lower(): dict(r) for r in _dump_loc_rows}

    conn.close()

    completed_count = sum(1 for s in stops if s["status"] == "completed")
    total_count = len(stops)

    from urllib.parse import quote_plus

    addresses = []
    for s in stops:
        full_address = " ".join(filter(None, [
            s["address"] or "",
            s["city"] or "",
            s["state"] or "",
            s["zip_code"] or "",
        ])).strip()
        if full_address:
            addresses.append(full_address)

    route_map_url = ""
    if len(addresses) == 1:
        route_map_url = "https://www.google.com/maps/search/?api=1&query=" + quote_plus(addresses[0])
    elif len(addresses) >= 2:
        origin = quote_plus(addresses[0])
        destination = quote_plus(addresses[-1])
        route_map_url = (
            "https://www.google.com/maps/dir/?api=1"
            f"&origin={origin}"
            f"&destination={destination}"
            "&travelmode=driving"
        )
        if len(addresses) > 2:
            waypoints = "|".join(quote_plus(a) for a in addresses[1:-1])
            route_map_url += f"&waypoints={waypoints}"

    # Apple Maps full route: supports origin→destination with optional +to: waypoints
    route_map_url_apple = ""
    if len(addresses) == 1:
        route_map_url_apple = "https://maps.apple.com/?q=" + quote_plus(addresses[0]) + "&dirflg=d"
    elif len(addresses) >= 2:
        # Apple Maps supports multi-stop via "daddr=A+to:B+to:C" (up to ~10 stops reliable)
        daddr = "+to:".join(quote_plus(a) for a in addresses[1:])
        route_map_url_apple = (
            "https://maps.apple.com/?saddr=" + quote_plus(addresses[0]) +
            "&daddr=" + daddr +
            "&dirflg=d"
        )

    # Google Maps waypoints cap at 8 intermediate stops (10 total incl. origin+dest)
    route_map_url_google = route_map_url
    if len(addresses) > 10:
        origin_g = quote_plus(addresses[0])
        dest_g   = quote_plus(addresses[-1])
        wpts     = "|".join(quote_plus(a) for a in addresses[1:9])
        route_map_url_google = (
            "https://www.google.com/maps/dir/?api=1"
            f"&origin={origin_g}&destination={dest_g}"
            f"&waypoints={wpts}&travelmode=driving"
        )

    nav_card_btns = ""
    if route_map_url_google:
        nav_card_btns += (
            f'<a class="btn-driver btn-driver-nav" target="_blank" href="{route_map_url_google}">'
            '&#128205; Google Maps</a>'
        )
    if route_map_url_apple:
        nav_card_btns += (
            f'<a class="btn-driver btn-driver-apple" target="_blank" href="{route_map_url_apple}">'
            '&#63743; Apple Maps</a>'
        )

    nav_card_html = ""
    if nav_card_btns:
        stop_word = "stop" if len(addresses) == 1 else "stops"
        nav_card_html = f"""
<div class="card" style="margin-bottom:14px;">
    <div style="font-weight:900;font-size:16px;margin-bottom:4px;">Start Full Route Navigation</div>
    <div class="small muted" style="margin-bottom:14px;">Opens all {len(addresses)} {stop_word} in order &bull; driving mode</div>
    <div class="dsc-action-row">{nav_card_btns}</div>
</div>"""

    # Dump location card
    dump_card_html = ""
    if dump_loc:
        from urllib.parse import quote_plus as _qp
        _dump_addr_parts = [
            dump_loc["address"] or "",
            dump_loc["city"] or "",
            dump_loc["state"] or "",
            dump_loc["zip_code"] or "",
        ]
        _dump_addr = " ".join(p for p in _dump_addr_parts if p).strip()
        _dump_google = "https://www.google.com/maps/dir/?api=1&destination=" + _qp(_dump_addr) if _dump_addr else ""
        _dump_apple  = "http://maps.apple.com/?daddr=" + _qp(_dump_addr) if _dump_addr else ""
        _dump_notes  = f'<div class="small muted" style="margin-top:4px;">{e(dump_loc["notes"])}</div>' if dump_loc["notes"] else ""
        _dump_nav = ""
        if _dump_google:
            _dump_nav += f'<a class="btn-driver btn-driver-nav" target="_blank" href="{_dump_google}">&#128205; Google Maps</a>'
        if _dump_apple:
            _dump_nav += f'<a class="btn-driver btn-driver-apple" target="_blank" href="{_dump_apple}">&#63743; Apple Maps</a>'
        dump_card_html = f"""
<div class="card" style="margin-bottom:14px;border-color:rgba(255,138,138,0.35);">
    <div style="font-weight:900;font-size:16px;margin-bottom:2px;">&#128465; Dump Location</div>
    <div style="font-size:18px;font-weight:800;color:#ff8a8a;margin-bottom:2px;">{e(dump_loc["name"])}</div>
    <div class="small muted">{e(_dump_addr)}</div>
    {_dump_notes}
    {f'<div class="dsc-action-row" style="margin-top:12px;">{_dump_nav}</div>' if _dump_nav else ""}
</div>"""

    # Build stop data list for JS distance calculation
    stop_address_data = []
    next_open_stop_id = None
    stop_cards = ""

    for s in stops:
        stop_key = s["id"]

        if next_open_stop_id is None and s["status"] != "completed":
            next_open_stop_id = stop_key

        is_next = (stop_key == next_open_stop_id)
        is_done = s["status"] == "completed"

        full_address = " ".join(filter(None, [
            s["address"] or "",
            s["city"] or "",
            s["state"] or "",
            s["zip_code"] or "",
        ])).strip()

        _enc_addr  = quote_plus(full_address)
        nav_google_web = "https://www.google.com/maps/dir/?api=1&destination=" + _enc_addr
        nav_google_app = "comgooglemaps://?daddr=" + _enc_addr + "&directionsmode=driving"
        nav_apple      = "https://maps.apple.com/?daddr=" + _enc_addr + "&dirflg=d"

        photo_html = build_photo_gallery_html(photos_by_stop.get(s["id"], []))

        action_color = {
            "Drop": "#3fd2ff", "Pickup": "#56f0b7", "Swap": "#ffd27c",
            "Pickup and Return": "#a78bfa",
            "Dump": "#ff8a8a", "Remove": "#ff8a8a", "Service": "#b0c4ff",
            "Final": "#c084fc", "Relocate": "#f9a8d4",
        }.get(s["action"] or "", "#b0c4ff")

        toggle_label = "Reopen Stop" if is_done else "Complete Stop"
        toggle_class = "btn-driver btn-driver-reopen" if is_done else "btn-driver btn-driver-complete"

        # --- driver workflow state ---
        _s = dict(s)
        _driver_status = _s.get("driver_status") or "pending"
        _csrf = get_csrf_token()

        # ---- classify this stop's workflow type ----
        _action_val   = (_s.get("action") or "").lower()
        # True PR / Swap action: needs box-in step
        _is_pr        = "pickup and return" in _action_val or (
                            "swap" in _action_val and "pull" not in _action_val)
        # Pure Pull: box-out → dump → complete (no box-in)
        _is_pull      = "pull" in _action_val and "return" not in _action_val
        # PR swap flag: driver is carrying empty can from prior Pull — skip dump entirely
        _is_swap_pr   = _is_pr and bool(_s.get("swap_with_prev_pull"))

        # Compact trail of completed workflow steps with times.
        # Swap PR logical order: Arrived → Box Out → Box In → To Dump
        # All other: Arrived → Box Out → To Dump → Box In
        _trail_order = (
            [("arrived_at","Arrived"),("box_out_at","Box Out"),("box_in_at","Box In"),("go_to_dump_at","To Dump")]
            if _is_swap_pr else
            [("arrived_at","Arrived"),("box_out_at","Box Out"),("go_to_dump_at","To Dump"),("box_in_at","Box In")]
        )
        _trail_parts = []
        for _tc, _tl in _trail_order:
            _tv = _s.get(_tc)
            if _tv:
                _trail_parts.append(
                    f'<span style="color:#4ade80;font-size:11px;background:rgba(74,222,128,0.1);'
                    f'padding:2px 7px;border-radius:6px;white-space:nowrap;">✓ {_tl} {_tv[-8:-3]}</span>'
                )
        _status_trail_html = (
            '<div style="display:flex;flex-wrap:wrap;gap:5px;margin-bottom:10px;">'
            + "".join(_trail_parts) + '</div>'
        ) if _trail_parts else ""

        # Next workflow action button
        _workflow_btn_html = ""
        if not is_done:
            if _is_swap_pr:
                # Swap PR full workflow: box out old → box in empty → leave with loaded can → dump → complete
                _wf_map = {
                    "pending":     ("arrived",       "🚛 Arrived at Stop",               "btn-driver btn-driver-complete"),
                    "arrived":     ("box_out",       "📦 Box Out — Remove Old Container", "btn-driver btn-driver-complete"),
                    "box_out":     ("need_box_in",   "📦 Box In — Place Empty Can",       "btn-driver btn-driver-complete"),
                    "need_box_in": ("box_in",        "✅ Confirm Box In",                 "btn-driver btn-driver-complete"),
                    "box_in":      ("going_to_dump", "🗑️ Go To Dump",                    "btn-driver btn-driver-dump"),
                }
            elif _is_pr:
                # Return Same Can: box-out → dump → return to same location → box-in empty
                _wf_map = {
                    "pending":     ("arrived",       "🚛 Arrived at Stop",                      "btn-driver btn-driver-complete"),
                    "arrived":     ("box_out",       "📦 Box Out — Remove Container",            "btn-driver btn-driver-complete"),
                    "box_out":     ("going_to_dump", "🗑️ Go To Dump",                           "btn-driver btn-driver-dump"),
                    "need_box_in": ("box_in",        "🔄 Return & Box In — Place Empty Can",    "btn-driver btn-driver-complete"),
                }
            elif _is_pull:
                # Pull: box-out → dump → complete (no box-in)
                _wf_map = {
                    "pending":     ("arrived",       "🚛 Arrived at Stop",           "btn-driver btn-driver-complete"),
                    "arrived":     ("box_out",        "📦 Box Out — Remove Container","btn-driver btn-driver-complete"),
                    "box_out":     ("going_to_dump",  "🗑️ Go To Dump",               "btn-driver btn-driver-dump"),
                }
            else:
                # Delivery / Drop / Service: arrived → complete
                _wf_map = {
                    "pending":     ("arrived",       "🚛 Arrived at Stop",           "btn-driver btn-driver-complete"),
                }

            if _driver_status in _wf_map:
                _nxt, _lbl, _cls = _wf_map[_driver_status]
                _workflow_btn_html = (
                    f'<form method="POST" action="{url_for("stop_driver_action", stop_id=s["id"])}"'
                    f' style="margin-bottom:8px;">'
                    f'<input type="hidden" name="_csrf_token" value="{_csrf}">'
                    f'<input type="hidden" name="action" value="{_nxt}">'
                    f'<button class="{_cls}" type="submit" style="width:100%;">{_lbl}</button>'
                    f'</form>'
                )
            elif _driver_status == "going_to_dump":
                _dump_loc_text = _s.get("dump_location") or ""
                _dump_label = f"🧾 Enter Dump Ticket{' — ' + _dump_loc_text if _dump_loc_text else ''}"
                _dump_ticket_link = (
                    f'<a class="btn-driver btn-driver-dump" '
                    f'href="{url_for("dump_ticket", stop_id=s["id"])}" '
                    f'style="display:block;text-align:center;text-decoration:none;'
                    f'padding:12px 16px;border-radius:12px;font-weight:700;margin-bottom:8px;">'
                    f'{_dump_label}</a>'
                )
                # Navigation buttons to drive to the dump site — resolved from DB
                _dl_rec = _dump_loc_by_name.get(_dump_loc_text.strip().lower()) if _dump_loc_text else None
                if _dl_rec:
                    _dl_addr_parts = [
                        _dl_rec.get("address") or "",
                        _dl_rec.get("city") or "",
                        _dl_rec.get("state") or "",
                        _dl_rec.get("zip_code") or "",
                    ]
                    _dl_addr = " ".join(p for p in _dl_addr_parts if p).strip()
                else:
                    _dl_addr = ""
                if _dl_addr:
                    _dl_enc = urllib.parse.quote_plus(_dl_addr)
                    _nav_html = (
                        f'<div style="display:flex;gap:8px;margin-bottom:8px;">'
                        f'<a class="btn-driver btn-driver-nav" target="_blank" '
                        f'href="https://www.google.com/maps/dir/?api=1&destination={_dl_enc}&travelmode=driving" '
                        f'style="flex:1;text-align:center;text-decoration:none;">&#128205; Google Maps</a>'
                        f'<a class="btn-driver btn-driver-apple" target="_blank" '
                        f'href="http://maps.apple.com/?daddr={_dl_enc}&dirflg=d" '
                        f'style="flex:1;text-align:center;text-decoration:none;">&#63743; Apple Maps</a>'
                        f'</div>'
                    )
                elif _dump_loc_text:
                    _nav_html = (
                        f'<div class="small muted" style="margin-bottom:8px;padding:8px;'
                        f'background:rgba(255,255,255,0.06);border-radius:8px;">'
                        f'&#9888;&#65039; Dump location &ldquo;{e(_dump_loc_text)}&rdquo; not found &mdash; '
                        f'update address in Dump Locations.</div>'
                    )
                else:
                    _nav_html = (
                        f'<div class="small muted" style="margin-bottom:8px;padding:8px;'
                        f'background:rgba(255,255,255,0.06);border-radius:8px;">'
                        f'Dump location not set for this stop.</div>'
                    )
                _workflow_btn_html = _nav_html + _dump_ticket_link

        # Badge on the stop card header showing PR mode
        if _is_swap_pr:
            _swap_badge = (
                '<span style="font-size:10px;background:rgba(255,200,80,0.22);color:#fde68a;'
                'padding:2px 8px;border-radius:6px;font-weight:700;letter-spacing:.4px;">'
                '&#x1F504; SWAP</span> '
            )
        elif _is_pr:
            _swap_badge = (
                '<span style="font-size:10px;background:rgba(150,200,255,0.18);color:#93c5fd;'
                'padding:2px 8px;border-radius:6px;font-weight:700;letter-spacing:.4px;">'
                '&#x21A9;&#xFE0F; RETURN</span> '
            )
        else:
            _swap_badge = ""

        card_class = "driver-stop-card"
        if is_next:
            card_class += " dsc-active"
        elif is_done:
            card_class += " dsc-done"

        card_id = "next-stop-card" if is_next else f"stop-{stop_key}"

        # detail block hidden for completed stops, visible for open
        detail_style = "display:none;" if is_done else ""

        if full_address:
            stop_address_data.append({"id": stop_key, "address": full_address})

        stop_cards += f"""
<div class="{card_class}" id="{card_id}" data-stop-id="{stop_key}" data-driver-status="{_driver_status}">

  <div class="dsc-header" onclick="toggleStopDetail({stop_key})">
    <div class="dsc-num">#{s['stop_order']}</div>
    <div class="dsc-summary">
      <div class="dsc-customer">{e(s['customer_name'] or 'Stop ' + str(s['stop_order']))}</div>
      <div class="dsc-addr">{e(full_address or 'No address')}</div>
      <div class="dsc-meta-row">
        {f'<span class="action-pill" style="background:rgba(255,200,80,0.22);color:#fde68a;font-weight:900;letter-spacing:.5px;">{e(dict(s).get("wo_type") or "")}</span>' if dict(s).get("wo_type") else ''}
        {_swap_badge}
        <span class="action-pill" style="background:{action_color};color:#06101f;">{e(s['action'] or 'Service')}</span>
        {f'<span class="action-pill" style="background:rgba(150,200,255,0.18);color:#cde;">{e(s["container_size"])} yd</span>' if s['container_size'] else ''}
        <span class="badge" id="badge-{stop_key}" style="font-size:11px;">{e(s['status'])}</span>
        <span class="dist-badge" id="dist-{stop_key}"></span>
      </div>
    </div>
    <div class="dsc-chevron" id="chev-{stop_key}">{'▲' if not is_done else '▼'}</div>
  </div>

  <div class="dsc-body" id="body-{stop_key}" style="{detail_style}">
    {"" if not s['ticket_number'] else f'<div class="dsc-field"><span class="dsc-label">Ticket</span>{e(s["ticket_number"])}</div>'}
    {"" if not _s.get('phone') else f'<div class="dsc-field"><span class="dsc-label">Phone</span><a href="tel:{e(_s["phone"])}" style="color:#56f0b7;">{e(_s["phone"])}</a></div>'}
    {"" if not _s.get('dump_location') else f'<div class="dsc-field"><span class="dsc-label">Dump Location</span>{e(_s["dump_location"])}</div>'}
    {"" if not s['notes'] else f'<div class="dsc-field"><span class="dsc-label">Notes</span><span style="white-space:pre-wrap;">{e(s["notes"] or "")}</span></div>'}
    <div class="dsc-field" id="done-at-row-{stop_key}" style="{'display:none;' if not s['completed_at'] else ''}">
      <span class="dsc-label">Done</span><span id="done-at-{stop_key}">{e(s['completed_at'] or '')}</span>
    </div>
    {photo_html}

    <div class="dsc-action-row" style="margin-bottom:10px;">
      <a class="btn-driver btn-driver-nav"
         href="{nav_google_web}"
         onclick="return openGoogleMapsStop(event, '{nav_google_app}', '{nav_google_web}')">
        &#128205; Google Maps
      </a>
      <a class="btn-driver btn-driver-apple" href="{nav_apple}">
        &#63743; Apple Maps
      </a>
    </div>

    {_status_trail_html}
    {_workflow_btn_html}
    <form class="dsc-toggle-form" method="POST"
          action="{url_for('toggle_stop_complete', stop_id=s['id'])}"
          data-stop-id="{stop_key}">
      <button id="toggle-btn-{stop_key}" class="{toggle_class}" type="submit" style="width:100%;">{toggle_label}</button>
    </form>

    <details class="upload-details">
      <summary>&#128247; Upload Photo / Proof</summary>
      <form method="POST" action="{url_for('upload_stop_photo', stop_id=s['id'])}" enctype="multipart/form-data" style="margin-top:10px;">
        <input type="file" name="photos" accept=".png,.jpg,.jpeg,.webp,.pdf" multiple required style="margin-bottom:8px;width:100%;">
        <button class="btn secondary" type="submit" style="width:100%;">Upload</button>
      </form>
    </details>
  </div>

</div>
"""

    route_action_buttons = ""
    if route["status"] == "open":
        route_action_buttons = f"""
        <form class="inline" method="POST" action="{url_for('mark_route_in_progress', route_id=route_id)}">
            <button class="btn orange" style="font-size:16px;padding:14px 22px;">Start Route</button>
        </form>"""
    elif route["status"] == "in_progress":
        route_action_buttons = f"""
        <form class="inline" method="POST" action="{url_for('mark_route_completed', route_id=route_id)}">
            <button class="btn green" style="font-size:16px;padding:14px 22px;">Finish Route</button>
        </form>"""

    pct = int(completed_count / total_count * 100) if total_count else 0
    next_stop_num = ""
    for s in stops:
        if s["status"] != "completed":
            next_stop_num = str(s["stop_order"])
            break

    sticky_label = f"Next Stop #{next_stop_num}" if next_stop_num else "All Stops Done!"
    sticky_disabled = "disabled" if not next_stop_num else ""

    # Serialize stop addresses for JS distance engine
    import json as _json
    stop_addr_json = _json.dumps(stop_address_data)

    extra_head = """
<style>
/* ════════════════════════════════════════════════════════
   DRIVER ROUTE PAGE — ROCKKSTAAR COMMAND THEME
   ════════════════════════════════════════════════════════ */

/* Stop cards */
.driver-stop-card {
    background: rgba(4,8,18,0.88);
    border: 1px solid rgba(0,150,255,0.13);
    border-radius: 14px;
    margin-bottom: 12px;
    overflow: hidden;
    transition: border-color .2s, box-shadow .2s;
}

.dsc-active {
    border-color: rgba(0,220,255,0.55) !important;
    box-shadow: 0 0 28px rgba(0,200,255,0.10), 0 0 0 1px rgba(0,200,255,0.08);
}

.dsc-done {
    opacity: 0.48;
    border-color: rgba(40,50,68,0.45) !important;
}

/* Header row (tap to expand) */
.dsc-header {
    display: flex;
    align-items: flex-start;
    gap: 12px;
    padding: 15px 16px;
    cursor: pointer;
    user-select: none;
    -webkit-tap-highlight-color: transparent;
}

/* Stop number */
.dsc-num {
    font-size: 18px;
    font-weight: 900;
    color: #00ccff;
    min-width: 32px;
    padding-top: 2px;
    letter-spacing: -1px;
    text-shadow: 0 0 12px rgba(0,200,255,0.40);
}
.dsc-done .dsc-num { color: #2e4050; text-shadow: none; }

/* Summary text */
.dsc-summary { flex: 1; min-width: 0; }

.dsc-customer {
    font-size: 16px;
    font-weight: 800;
    color: #ddeeff;
    line-height: 1.25;
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
}

.dsc-addr {
    font-size: 12px;
    color: #3d5a74;
    margin-top: 3px;
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
}

.dsc-meta-row {
    display: flex;
    flex-wrap: wrap;
    gap: 5px;
    margin-top: 7px;
    align-items: center;
}

/* Action / type pills */
.action-pill {
    display: inline-block;
    padding: 2px 9px;
    border-radius: 999px;
    font-size: 11px;
    font-weight: 800;
    letter-spacing: .3px;
}

.dist-badge {
    font-size: 11px;
    color: #2e5070;
    font-weight: 700;
}

.dsc-chevron {
    color: #1e3a50;
    font-size: 13px;
    padding-top: 4px;
    min-width: 16px;
    text-align: right;
}

/* Body (expandable) */
.dsc-body {
    padding: 0 16px 16px;
    border-top: 1px solid rgba(0,150,255,0.08);
}

.dsc-field {
    display: flex;
    gap: 10px;
    font-size: 13px;
    padding: 6px 0;
    border-bottom: 1px solid rgba(0,150,255,0.05);
    color: #8ab8d8;
}
.dsc-field:last-of-type { border-bottom: none; }

.dsc-label {
    font-size: 11px;
    font-weight: 700;
    letter-spacing: .4px;
    text-transform: uppercase;
    color: #1e3a52;
    min-width: 56px;
    flex-shrink: 0;
    padding-top: 1px;
}

/* Action button row */
.dsc-action-row {
    display: flex;
    gap: 8px;
    margin-top: 14px;
}

/* Driver buttons — large tap targets */
.btn-driver {
    flex: 1;
    display: block;
    padding: 15px 10px;
    border-radius: 11px;
    font-size: 15px;
    font-weight: 800;
    text-align: center;
    border: none;
    cursor: pointer;
    text-decoration: none;
    line-height: 1.1;
    -webkit-tap-highlight-color: transparent;
    touch-action: manipulation;
    transition: filter .15s, transform .1s;
}
.btn-driver:hover { filter: brightness(1.08); transform: translateY(-1px); }
.btn-driver:active { transform: scale(0.98); }

.btn-driver-nav {
    background: linear-gradient(135deg, #00d8ff 0%, #0090d8 100%);
    color: #020d18;
    box-shadow: 0 2px 14px rgba(0,180,255,0.18);
}
.btn-driver-complete {
    background: linear-gradient(135deg, #00e87d 0%, #00b058 100%);
    color: #011208;
    box-shadow: 0 2px 14px rgba(0,200,100,0.15);
}
.btn-driver-reopen {
    background: rgba(30,55,90,0.85);
    border: 1px solid rgba(0,150,255,0.22);
    color: #7aa8cc;
    box-shadow: none;
}
.btn-driver-dump {
    background: linear-gradient(135deg, #ffb830 0%, #ff7500 100%);
    color: #100400;
    box-shadow: 0 2px 14px rgba(255,140,0,0.16);
}
.btn-driver-apple {
    background: rgba(24,30,44,0.85);
    border: 1px solid rgba(150,160,180,0.18);
    color: #8090a8;
}

/* Upload details */
.upload-details { margin-top: 12px; }
.upload-details summary {
    color: #2e5070;
    font-size: 13px;
    cursor: pointer;
    padding: 6px 0;
}

/* Route progress bar */
.progress-bar-wrap {
    background: rgba(255,255,255,0.05);
    border-radius: 999px;
    height: 6px;
    margin: 12px 0 5px;
    overflow: hidden;
}
.progress-bar-fill {
    height: 100%;
    border-radius: 999px;
    background: linear-gradient(90deg, #0090e8, #00ccff);
    transition: width 0.4s ease;
}

/* Sticky next-stop bar */
#sticky-next-bar {
    position: fixed;
    bottom: 0; left: 0; right: 0;
    z-index: 999;
    padding: 10px 16px 14px;
    background: rgba(2,6,16,0.97);
    border-top: 1px solid rgba(0,200,255,0.15);
    backdrop-filter: blur(16px);
    -webkit-backdrop-filter: blur(16px);
}
#sticky-next-bar button {
    width: 100%;
    padding: 16px;
    font-size: 16px;
    font-weight: 900;
    border-radius: 11px;
    background: linear-gradient(135deg, #00d8ff 0%, #0090d8 100%);
    color: #020d18;
    border: none;
    cursor: pointer;
    touch-action: manipulation;
    box-shadow: 0 0 22px rgba(0,180,255,0.22);
    transition: filter .15s;
}
#sticky-next-bar button:hover { filter: brightness(1.1); }
#sticky-next-bar button:disabled {
    background: rgba(30,50,70,0.60);
    color: #2e4a62;
    box-shadow: none;
    cursor: default;
}

.stop-list-wrap { padding-bottom: 90px; }

@media (min-width: 900px) {
    #sticky-next-bar { left: 234px; }
}
</style>
"""

    body = f"""
<div class="hero" style="padding-bottom:14px;">
    <div class="row between" style="align-items:flex-start;flex-wrap:wrap;gap:10px;">
        <div>
            <h1 style="margin:0 0 4px;">{e(route['route_name'])}</h1>
            <div class="small muted">{e(route['route_date'])} &bull; {e(route['assigned_username'] or 'Unassigned')}</div>
        </div>
        <span class="badge {e(route['status'])}" style="font-size:14px;padding:8px 14px;">{e(route['status'].replace('_',' ').title())}</span>
    </div>
    <div class="progress-bar-wrap"><div id="progress-fill" class="progress-bar-fill" style="width:{pct}%;"></div></div>
    <div id="progress-text" class="small muted">{completed_count} of {total_count} stops complete</div>
    <div class="row" style="margin-top:14px;gap:10px;flex-wrap:wrap;">
        {route_action_buttons}
        <a class="btn secondary" href="{url_for('driver_dashboard')}">&#8592; Back</a>
    </div>
</div>

{nav_card_html}

{dump_card_html}

<div class="stop-list-wrap" id="stop-list">
    {stop_cards if stop_cards else '<div class="card">No stops on this route.</div>'}
</div>

<div id="sticky-next-bar">
    <button id="sticky-next-btn" onclick="scrollToNext()" {sticky_disabled}>{e(sticky_label)}</button>
</div>

<script>
(function() {{
    var csrfToken = (document.querySelector('meta[name="csrf-token"]') || {{}}).getAttribute
        ? document.querySelector('meta[name="csrf-token"]').getAttribute('content')
        : '';

    // ================================================================
    // DOM helpers
    // ================================================================
    function $id(id) {{ return document.getElementById(id); }}

    function openBody(stopId) {{
        var b = $id('body-' + stopId), c = $id('chev-' + stopId);
        if (b) b.style.display = 'block';
        if (c) c.textContent = '\u25b2';
    }}
    function closeBody(stopId) {{
        var b = $id('body-' + stopId), c = $id('chev-' + stopId);
        if (b) b.style.display = 'none';
        if (c) c.textContent = '\u25bc';
    }}

    // ================================================================
    // Open Google Maps: try app scheme first, fall back to web URL
    // ================================================================
    window.openGoogleMapsStop = function(e, appUrl, webUrl) {{
        e.preventDefault();
        var isIOS = /iPad|iPhone|iPod/.test(navigator.userAgent) ||
            (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
        var isAndroid = /Android/.test(navigator.userAgent);
        if (isIOS || isAndroid) {{
            var start = Date.now();
            var fallback = setTimeout(function() {{ window.location = webUrl; }}, 600);
            window.location = appUrl;
            window.addEventListener('blur', function onBlur() {{
                clearTimeout(fallback);
                window.removeEventListener('blur', onBlur);
            }});
        }} else {{
            window.open(webUrl, '_blank');
        }}
        return false;
    }};

    // ================================================================
    // Toggle stop detail (tap header)
    // ================================================================
    window.toggleStopDetail = function(stopId) {{
        var b = $id('body-' + stopId);
        if (!b) return;
        if (b.style.display === 'none') openBody(stopId); else closeBody(stopId);
    }};

    // ================================================================
    // Sticky "Next Stop" scroll
    // ================================================================
    window.scrollToNext = function() {{
        var next = $id('next-stop-card');
        if (next) next.scrollIntoView({{ behavior: 'smooth', block: 'center' }});
    }};

    // Auto-scroll to next open stop on page load
    window.addEventListener('load', function() {{
        var next = $id('next-stop-card');
        if (next) setTimeout(function() {{
            next.scrollIntoView({{ behavior: 'smooth', block: 'center' }});
        }}, 350);
    }});

    // ================================================================
    // Progress bar + text update
    // ================================================================
    function updateProgress(completed, total) {{
        var pct   = total > 0 ? Math.round(completed / total * 100) : 0;
        var fill  = $id('progress-fill');
        var text  = $id('progress-text');
        if (fill) fill.style.width = pct + '%';
        if (text) text.textContent = completed + ' of ' + total + ' stops complete';
    }}

    // ================================================================
    // Sticky button text update
    // ================================================================
    function updateStickyBtn() {{
        var btn = $id('sticky-next-btn');
        if (!btn) return;
        var nextCard = document.querySelector('.driver-stop-card:not(.dsc-done)');
        if (!nextCard) {{
            btn.disabled = true;
            btn.textContent = 'All Stops Done! \u2713';
        }} else {{
            var numEl = nextCard.querySelector('.dsc-num');
            var num   = numEl ? numEl.textContent.replace('#','') : '';
            btn.disabled = false;
            btn.textContent = 'Next Stop #' + num;
        }}
    }}

    // ================================================================
    // Mark one card as completed in the DOM
    // ================================================================
    function markDone(stopId, completedAt) {{
        var card = document.querySelector('[data-stop-id="' + stopId + '"]');
        if (!card) return;
        card.classList.remove('dsc-active');
        card.classList.add('dsc-done');
        if (card.id === 'next-stop-card') card.id = 'stop-' + stopId;

        var badge = $id('badge-' + stopId);
        if (badge) {{ badge.className = 'badge completed'; badge.textContent = 'completed'; }}

        var btn = $id('toggle-btn-' + stopId);
        if (btn) {{
            btn.textContent = 'Reopen Stop';
            btn.className   = 'btn-driver btn-driver-reopen';
            btn.style.width = '100%';
        }}

        var row = $id('done-at-row-' + stopId);
        var ts  = $id('done-at-' + stopId);
        if (ts)  ts.textContent  = completedAt;
        if (row) row.style.display = '';

        closeBody(stopId);
    }}

    // ================================================================
    // Mark one card as reopened in the DOM
    // ================================================================
    function markOpen(stopId) {{
        var card = document.querySelector('[data-stop-id="' + stopId + '"]');
        if (!card) return;
        card.classList.remove('dsc-done');

        var badge = $id('badge-' + stopId);
        if (badge) {{ badge.className = 'badge open'; badge.textContent = 'open'; }}

        var btn = $id('toggle-btn-' + stopId);
        if (btn) {{
            btn.textContent = 'Complete Stop';
            btn.className   = 'btn-driver btn-driver-complete';
            btn.style.width = '100%';
        }}

        var row = $id('done-at-row-' + stopId);
        if (row) row.style.display = 'none';

        openBody(stopId);
    }}

    // ================================================================
    // Highlight the next open stop as active
    // ================================================================
    function highlightNext() {{
        document.querySelectorAll('.driver-stop-card').forEach(function(c) {{
            c.classList.remove('dsc-active');
            if (c.id === 'next-stop-card') c.id = 'stop-' + c.dataset.stopId;
        }});
        var nextCard = document.querySelector('.driver-stop-card:not(.dsc-done)');
        if (!nextCard) return null;
        nextCard.classList.add('dsc-active');
        nextCard.id = 'next-stop-card';
        openBody(nextCard.dataset.stopId);
        return nextCard;
    }}

    // ================================================================
    // AJAX stop completion — intercept all .dsc-toggle-form submits
    // ================================================================
    document.getElementById('stop-list').addEventListener('submit', function(e) {{
        var form = e.target;
        if (!form.classList.contains('dsc-toggle-form')) return;
        e.preventDefault();

        var stopId      = form.dataset.stopId;
        var btn         = $id('toggle-btn-' + stopId);
        var isCompleting = btn && btn.classList.contains('btn-driver-complete');

        /* ── helper: queue this toggle + apply optimistic UI ─────── */
        function _queueOffline() {{
            /* extract pathname from absolute action URL */
            var togglePath;
            try {{ togglePath = new URL(form.action).pathname; }}
            catch(ex) {{ togglePath = '/stop/' + stopId + '/toggle'; }}

            if (typeof window.__haultraOfflineQueue === 'function') {{
                window.__haultraOfflineQueue({{
                    url:       togglePath,
                    body:      {{
                        _csrf_token:     '',
                        expected_status: isCompleting ? 'open' : 'completed'
                    }},
                    queued_at: new Date().toISOString(),
                    label:     (isCompleting ? 'Complete' : 'Reopen') + ' Stop #' + stopId
                }});
            }}

            /* optimistic DOM update */
            if (isCompleting) {{
                markDone(stopId, 'Pending Sync');
            }} else {{
                markOpen(stopId);
            }}
            /* count updated DOM state for progress bar */
            var allCards  = document.querySelectorAll('.driver-stop-card');
            var doneCards = document.querySelectorAll('.driver-stop-card.dsc-done');
            updateProgress(doneCards.length, allCards.length);
            highlightNext();
            updateStickyBtn();

            /* mark button as pending so driver knows it hasn't confirmed yet */
            var pb = $id('toggle-btn-' + stopId);
            if (pb) {{
                pb.innerHTML  = '&#8635; Pending Sync';
                pb.disabled   = true;
                pb.style.opacity = '0.65';
            }}
        }}

        /* ── Offline: queue immediately, no network attempt ─────── */
        if (!navigator.onLine) {{
            _queueOffline();
            return;
        }}

        /* ── Online: AJAX attempt ───────────────────────────────── */
        if (btn) {{ btn.disabled = true; btn.textContent = 'Saving\u2026'; }}

        var fd = new FormData();
        fd.append('_csrf_token', csrfToken);

        fetch(form.action, {{
            method:  'POST',
            headers: {{ 'X-Requested-With': 'XMLHttpRequest' }},
            body:    fd,
        }})
        .then(function(r) {{ return r.json(); }})
        .then(function(data) {{
            if (!data.success) throw new Error('not ok');

            if (data.new_status === 'completed') {{
                markDone(stopId, data.completed_at);
            }} else {{
                markOpen(stopId);
            }}

            updateProgress(data.progress.completed, data.progress.total);

            var nextCard = highlightNext();
            updateStickyBtn();

            if (data.new_status === 'completed' && nextCard) {{
                setTimeout(function() {{
                    nextCard.scrollIntoView({{ behavior: 'smooth', block: 'center' }});
                }}, 280);
            }}
        }})
        .catch(function() {{
            if (!navigator.onLine) {{
                /* connection dropped mid-request — queue + optimistic UI */
                _queueOffline();
            }} else {{
                /* server error — re-enable button, show brief error highlight */
                if (btn) {{
                    btn.disabled = false;
                    btn.textContent = isCompleting ? 'Complete Stop' : 'Reopen Stop';
                    btn.style.boxShadow = '0 0 0 2px #ff6b6b';
                    setTimeout(function() {{ btn.style.boxShadow = ''; }}, 3000);
                }}
            }}
        }});
    }});

    // ================================================================
    // Distance: Geolocation + Nominatim geocoding
    // ================================================================
    var stopAddresses = {stop_addr_json};

    function haversine(lat1, lon1, lat2, lon2) {{
        var R = 3958.8, dLat = (lat2-lat1)*Math.PI/180, dLon = (lon2-lon1)*Math.PI/180;
        var a = Math.sin(dLat/2)*Math.sin(dLat/2) +
                Math.cos(lat1*Math.PI/180)*Math.cos(lat2*Math.PI/180)*
                Math.sin(dLon/2)*Math.sin(dLon/2);
        return R * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
    }}

    function geocode(address, cb) {{
        fetch('https://nominatim.openstreetmap.org/search?format=json&limit=1&q=' +
              encodeURIComponent(address), {{ headers: {{ 'Accept-Language': 'en' }} }})
            .then(function(r) {{ return r.json(); }})
            .then(function(d) {{ if (d && d.length) cb(parseFloat(d[0].lat), parseFloat(d[0].lon)); }})
            .catch(function() {{}});
    }}

    if (stopAddresses.length && navigator.geolocation) {{
        navigator.geolocation.getCurrentPosition(function(pos) {{
            var uLat = pos.coords.latitude, uLon = pos.coords.longitude;
            var idx  = 0;
            (function tick() {{
                if (idx >= stopAddresses.length) return;
                var item = stopAddresses[idx++];
                geocode(item.address, function(lat, lon) {{
                    var el = $id('dist-' + item.id);
                    if (el) el.textContent = haversine(uLat, uLon, lat, lon).toFixed(1) + ' mi';
                }});
                setTimeout(tick, 1300);
            }})();
        }}, function() {{}}, {{ timeout: 8000 }});
    }}

    // ================================================================
    // Photo upload offline guard
    // Photo files cannot be serialised to localStorage, so we cannot
    // queue them. Instead, block the submit and give a clear message.
    // ================================================================
    document.querySelectorAll('.upload-details form').forEach(function(upForm) {{
        upForm.addEventListener('submit', function(evt) {{
            if (navigator.onLine) return;    /* online: let it submit */
            evt.preventDefault();
            evt.stopImmediatePropagation();

            var uploadBtn = upForm.querySelector('button[type=submit]');
            var origLabel = uploadBtn ? uploadBtn.textContent : 'Upload';

            /* Show an inline warning inside the form */
            if (!upForm.querySelector('.photo-offline-warn')) {{
                var warn = document.createElement('p');
                warn.className = 'photo-offline-warn';
                warn.style.cssText = (
                    'color:#fbbf24;font-size:13px;margin:8px 0 0;' +
                    'padding:8px 10px;background:rgba(255,180,0,.1);' +
                    'border:1px solid rgba(255,180,0,.25);border-radius:8px;'
                );
                warn.textContent = (
                    '\u26a0 You are offline. Photos cannot be saved to your device ' +
                    'and cannot be queued for upload. Keep this tab open — the Upload ' +
                    'button will re-enable when your connection returns.'
                );
                upForm.appendChild(warn);
            }}

            if (uploadBtn) {{
                uploadBtn.disabled = true;
                uploadBtn.textContent = '\u23f3 Waiting for connection\u2026';
                /* re-enable and restore label when connection returns */
                window.addEventListener('online', function _onlineOnce() {{
                    uploadBtn.disabled = false;
                    uploadBtn.textContent = origLabel;
                    var w = upForm.querySelector('.photo-offline-warn');
                    if (w) w.remove();
                    window.removeEventListener('online', _onlineOnce);
                }});
            }}
        }});
    }});
}})();
</script>
"""
    return render_template_string(shell_page("Driver Route", body, extra_head))


# =========================================================
# ADDRESS MEMORY — autocomplete JS + upsert helper
# =========================================================
_AUTOCOMPLETE_JS = """
(function() {
  'use strict';
  function buildSuggest(input) {
    var form = input.closest ? input.closest('form') : null;
    if (!form) return;
    var wrap = input.parentNode;
    if (window.getComputedStyle(wrap).position === 'static') wrap.style.position = 'relative';
    var box = document.createElement('div');
    box.style.cssText = [
      'position:absolute','left:0','right:0','top:100%','z-index:9999',
      'background:#0a1826','border:1px solid #1e3a52','border-top:none',
      'border-radius:0 0 10px 10px','max-height:260px','overflow-y:auto',
      'display:none','box-shadow:0 8px 32px rgba(0,0,0,.7)'
    ].join(';');
    wrap.appendChild(box);
    var timer = null;
    input.addEventListener('input', function() {
      clearTimeout(timer);
      var q = this.value.trim();
      if (q.length < 2) { box.style.display = 'none'; return; }
      timer = setTimeout(function() {
        fetch('/api/address-suggestions?q=' + encodeURIComponent(q))
          .then(function(r) { return r.json(); })
          .then(function(data) {
            box.innerHTML = '';
            if (!data.length) { box.style.display = 'none'; return; }
            data.forEach(function(d) {
              var item = document.createElement('div');
              item.style.cssText = [
                'padding:10px 14px','cursor:pointer',
                'border-bottom:1px solid rgba(30,58,82,.6)',
                'font-size:13px','line-height:1.4'
              ].join(';');
              var line2 = [d.address, d.city, d.state].filter(Boolean).join(', ');
              item.innerHTML =
                '<div style="color:#61f7df;font-weight:600;">' + _esc(d.customer_name) + '</div>' +
                (line2 ? '<div style="color:#6a8aa8;font-size:11px;margin-top:2px;">' + _esc(line2) + '</div>' : '');
              item.addEventListener('mouseenter', function() { this.style.background = 'rgba(97,247,223,.08)'; });
              item.addEventListener('mouseleave', function() { this.style.background = ''; });
              item.addEventListener('mousedown', function(ev) {
                ev.preventDefault();
                _fill(form, d);
                box.style.display = 'none';
              });
              box.appendChild(item);
            });
            box.style.display = 'block';
          })
          .catch(function() { box.style.display = 'none'; });
      }, 220);
    });
    input.addEventListener('blur', function() {
      setTimeout(function() { box.style.display = 'none'; }, 200);
    });
    input.addEventListener('focus', function() {
      if (box.children.length) box.style.display = 'block';
    });
  }
  function _esc(s) {
    return (s || '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  }
  function _fill(form, d) {
    /* Always fill address identity fields */
    var set = function(name, val) {
      if (!val) return;
      var el = form.querySelector('[name="' + name + '"]');
      if (el) el.value = val;
    };
    set('customer_name', d.customer_name);
    set('address',       d.address);
    set('city',          d.city);
    set('state',         d.state);
    set('zip_code',      d.zip);
    /* Smart defaults — only fill if the field is currently empty */
    var setIfEmpty = function(name, val) {
      if (!val) return;
      var el = form.querySelector('[name="' + name + '"]');
      if (el && !el.value.trim()) el.value = val;
    };
    setIfEmpty('action',         d.default_action);
    setIfEmpty('container_size', d.default_container_size);
    if (d.default_dump_location) {
      var dl = form.querySelector('[name="dump_location"]');
      if (dl && !dl.value.trim()) dl.value = d.default_dump_location;
    }
  }
  document.addEventListener('DOMContentLoaded', function() {
    document.querySelectorAll('[data-hac]').forEach(function(inp) {
      buildSuggest(inp);
    });
  });
})();
"""


_STOP_WARNINGS_JS = """
(function() {
  'use strict';
  var existingStops = window._HAULTRA_STOPS || [];

  var DUMP_NEEDED  = ['pickup and return', 'pull', 'swap'];
  var PICKUP_TYPES = ['pickup and return', 'pull', 'swap'];
  var KNOWN        = ['pickup and return', 'pull', 'delivery', 'dump run', 'swap'];
  var ABBREVS      = ['pr', 'p', 'd'];

  function has(str, keywords) {
    return keywords.some(function(k) { return str.indexOf(k) >= 0; });
  }
  function isKnown(a) {
    if (!a) return true;
    if (ABBREVS.indexOf(a) >= 0) return true;
    return has(a, KNOWN);
  }

  function check(form) {
    var g = function(n) {
      var el = form.querySelector('[name="' + n + '"]');
      return el ? (el.value || '').trim() : '';
    };
    var action   = g('action').toLowerCase();
    var address  = g('address');
    var city     = g('city');
    var state    = g('state');
    var dumpLoc  = g('dump_location');
    var customer = g('customer_name');
    var warns    = [];

    /* 1 — Missing dump location */
    if (action && has(action, DUMP_NEEDED) && !dumpLoc) {
      warns.push({ level: 'yellow',
        msg: 'Missing dump location \u2014 ' + action + ' stops require a dump site.' });
    }

    /* 2 — Incomplete address */
    if (address) {
      var missing = [];
      if (!city)  missing.push('city');
      if (!state) missing.push('state');
      if (missing.length) {
        warns.push({ level: 'yellow',
          msg: 'Incomplete address \u2014 missing ' + missing.join(' and ') + '.' });
      }
    }

    /* 3 — Duplicate stop */
    if (customer || address) {
      var cl = customer.toLowerCase();
      var al = address.toLowerCase();
      var dup = existingStops.some(function(s) {
        var sc = (s.customer_name || '').toLowerCase();
        var sa = (s.address || '').toLowerCase();
        return (cl && sc && sc === cl) || (al && sa && sa === al);
      });
      if (dup) {
        warns.push({ level: 'yellow',
          msg: 'Duplicate \u2014 a stop for this customer or address already exists on this route.' });
      }
    }

    /* 4 — Invalid service flow: consecutive pickups */
    if (action && existingStops.length > 0) {
      var lastA = (existingStops[existingStops.length - 1].action || '').toLowerCase();
      if (has(action, PICKUP_TYPES) && has(lastA, PICKUP_TYPES)) {
        warns.push({ level: 'red',
          msg: 'Service flow issue \u2014 consecutive pickup actions (' +
               lastA + ' \u2192 ' + action + '). Verify route logic.' });
      }
    }

    /* 5 — Unknown abbreviation */
    if (action && !isKnown(action)) {
      warns.push({ level: 'yellow',
        msg: 'Unknown action \u201c' + action + '\u201d \u2014 expected: PR, Pull, Delivery, Dump Run, or Swap.' });
    }

    return warns;
  }

  function render(box, warns) {
    if (!warns.length) { box.style.display = 'none'; box.innerHTML = ''; return; }
    box.innerHTML = warns.map(function(w) {
      var bg  = w.level === 'red' ? 'rgba(255,59,92,.10)'  : 'rgba(255,157,0,.09)';
      var bdr = w.level === 'red' ? 'rgba(255,59,92,.35)'  : 'rgba(255,157,0,.32)';
      var col = w.level === 'red' ? '#ff8099'              : '#fbbf24';
      return (
        '<div style="display:flex;gap:8px;align-items:flex-start;padding:9px 13px;' +
        'background:' + bg + ';border:1px solid ' + bdr + ';border-radius:8px;' +
        'font-size:12px;line-height:1.45;color:' + col + ';">' +
        '<span style="flex-shrink:0;">&#9888;</span>' +
        '<span>' + w.msg + '</span></div>'
      );
    }).join('');
    box.style.cssText = 'display:flex;flex-direction:column;gap:6px;margin-top:12px;';
  }

  document.addEventListener('DOMContentLoaded', function() {
    document.querySelectorAll('form').forEach(function(form) {
      if (!form.querySelector('[name="action"]')) return;

      var box = document.createElement('div');
      box.className = 'haultra-stop-warnings';
      box.style.display = 'none';

      /* insert just before the submit-button row */
      var submitRow = null;
      form.querySelectorAll('div').forEach(function(d) {
        if (!submitRow && d.querySelector('button[type="submit"]')) submitRow = d;
      });
      if (submitRow) form.insertBefore(box, submitRow);
      else form.appendChild(box);

      var WATCH = ['action','customer_name','address','city','state','dump_location','container_size'];
      WATCH.forEach(function(n) {
        var el = form.querySelector('[name="' + n + '"]');
        if (!el) return;
        el.addEventListener(el.tagName.toLowerCase() === 'select' ? 'change' : 'input',
          function() { render(box, check(form)); });
      });

      /* run immediately for pre-filled edit forms */
      render(box, check(form));
    });
  });
})();
"""


_ABBREV_EXPAND_JS = """
(function() {
  var MAP = {
    'dom':  'Dominion',
    'wat':  'Waterway',
    'vb':   'Virginia Beach',
    'ches': 'Chesapeake',
    'norf': 'Norfolk'
  };
  /* Exposed globally so other scripts can reuse the same map */
  window._haultraExpand = function(v) {
    var t = (v || '').trim();
    return MAP[t.toLowerCase()] || t;
  };
  document.addEventListener('DOMContentLoaded', function() {
    document.querySelectorAll('input[name], textarea[name]').forEach(function(el) {
      if (['password','hidden','file','submit','reset','button'].indexOf(el.type) >= 0) return;
      el.addEventListener('blur', function() {
        var expanded = window._haultraExpand(this.value);
        if (expanded !== (this.value || '').trim()) this.value = expanded;
      });
    });
  });
})();
"""


_PASTE_ROUTE_CSS = """<style>
/* ── Paste Route Panel ───────────────────────────────────────────── */
.pr-grid{display:grid;grid-template-columns:1fr 1fr;gap:20px;align-items:start}
@media(max-width:820px){.pr-grid{grid-template-columns:1fr}}
.pr-card{background:rgba(4,20,45,.55);border:1px solid rgba(0,160,255,.12);border-radius:14px;padding:20px 22px;margin-bottom:18px}
.pr-card h3{margin:0 0 4px;font-size:15px;color:#c8dff0;font-weight:800;letter-spacing:.3px}
.pr-card .pr-sub{font-size:12px;color:#4a6a88;margin:0 0 14px}
.pr-stop{border-radius:10px;padding:15px;margin-bottom:12px;position:relative;transition:opacity .2s,height .2s,padding .2s,margin .2s}
.pr-stop.h{background:rgba(0,232,125,.04);border:1px solid rgba(0,232,125,.18)}
.pr-stop.m{background:rgba(255,157,0,.05);border:1px solid rgba(255,157,0,.20)}
.pr-stop.l{background:rgba(255,59,92,.05);border:1px solid rgba(255,59,92,.20)}
.pr-badge{display:inline-flex;align-items:center;padding:3px 10px;border-radius:20px;font-size:11px;font-weight:700;letter-spacing:.3px;margin-right:4px}
.pr-b-pr{background:rgba(97,247,223,.12);color:#61f7df}
.pr-b-p{background:rgba(251,191,36,.12);color:#fbbf24}
.pr-b-d{background:rgba(96,165,250,.12);color:#60a5fa}
.pr-b-swap{background:rgba(167,139,250,.12);color:#a78bfa}
.pr-b-move{background:rgba(244,114,182,.12);color:#f472b6}
.pr-b-other{background:rgba(120,120,150,.12);color:#9aa5b8}
.pr-ch{background:rgba(0,232,125,.10);color:#00e87d}
.pr-cm{background:rgba(251,191,36,.10);color:#fbbf24}
.pr-cl{background:rgba(255,59,92,.10);color:#ff7090}
.pr-saved{background:rgba(97,247,223,.08);color:#61f7df;border:1px solid rgba(97,247,223,.2)}
.pr-lbl{display:block;font-size:10px;color:#4a6a88;font-weight:700;text-transform:uppercase;letter-spacing:.5px;margin-bottom:3px}
.pr-inp{width:100%;background:rgba(0,0,0,.35);border:1px solid rgba(0,160,255,.13);border-radius:7px;color:#c8dff0;padding:7px 10px;font-size:13px;box-sizing:border-box;font-family:inherit}
.pr-inp:focus{outline:none;border-color:rgba(0,200,255,.38)}
.pr-miss .pr-inp{border-color:rgba(251,191,36,.4)!important;background:rgba(251,191,36,.03)!important}
.pr-miss .pr-lbl{color:#fbbf24}
.pr-orig{font-size:11px;color:#3d5564;font-style:italic;font-family:monospace;background:rgba(0,0,0,.18);border-radius:5px;padding:5px 9px;margin-bottom:12px}
.pr-warn-strip{margin-top:10px;padding:6px 12px;border-radius:6px;font-size:12px;background:rgba(251,191,36,.07);border:1px solid rgba(251,191,36,.2);color:#fbbf24}
.pr-card-acts{display:flex;gap:8px;margin-top:12px;flex-wrap:wrap}
.pr-btn-sm{font-size:12px;padding:5px 12px;border-radius:6px;border:none;cursor:pointer;font-weight:600;font-family:inherit}
.pr-btn-remove{background:rgba(255,59,92,.10);color:#ff7090}
.pr-btn-remove:hover{background:rgba(255,59,92,.22)}
.pr-sugg{padding:9px 13px;border-radius:8px;margin-bottom:8px;font-size:13px;line-height:1.4;display:flex;align-items:flex-start;gap:8px}
.pr-sw{background:rgba(251,191,36,.07);border:1px solid rgba(251,191,36,.18);color:#fbbf24}
.pr-si{background:rgba(97,247,223,.05);border:1px solid rgba(97,247,223,.15);color:#61f7df}
.pr-se{background:rgba(255,59,92,.07);border:1px solid rgba(255,59,92,.18);color:#ff7090}
.pr-footer-bar{display:flex;gap:12px;align-items:center;flex-wrap:wrap;padding:14px 0 2px;border-top:1px solid rgba(0,160,255,.1);margin-top:10px}
.pr-footer-count{font-size:13px;color:#4a6a88;flex:1}
.pr-tip-item{font-size:12px;color:#6a8aa8;padding:7px 0;border-bottom:1px solid rgba(0,100,160,.1)}
.pr-tip-item:last-child{border-bottom:none}
.pr-tip-item strong{color:#8fd3ff}
.pr-tip-code{font-family:monospace;background:rgba(0,0,0,.3);border-radius:4px;padding:2px 6px;color:#8fd3ff;font-size:11px}
#pr-mobile-bar{display:none;position:fixed;bottom:0;left:0;right:0;z-index:1200;background:rgba(4,10,28,.97);border-top:1px solid rgba(0,160,255,.2);padding:12px 16px;gap:10px}
@media(max-width:820px){ #pr-mobile-bar.pr-show{display:flex} }
</style>"""


_PASTE_ROUTE_JS = """
(function() {
  'use strict';
  var csrf  = (document.querySelector('meta[name="csrf-token"]')||{}).getAttribute('content')||'';
  var RID   = window._HAULTRA_ROUTE_ID  || 0;
  var DUMPS = window._HAULTRA_DUMP_LOCS || [];

  var _stops = [], _removed = {};
  var $       = function(id) { return document.getElementById(id); };
  var ta       = $('pr-textarea');
  var parseBtn = $('pr-parse-btn');
  var clearBtn = $('pr-clear-btn');
  var closeBtn = $('pr-close-btn');
  var preview  = $('pr-preview');
  var suggCard = $('pr-sugg-card');
  var suggInner= $('pr-sugg-inner');
  var footer   = $('pr-footer-bar');
  var buildBtn = $('pr-build-btn');
  var cancelBtn= $('pr-cancel-btn');
  var panel    = $('paste-route-panel');
  var mobileBar= $('pr-mobile-bar');

  /* ── Toggle (called from hero button) ─────────────────────────────────── */
  window._haulsTogglePaste = function() {
    if (!panel) return;
    var open = panel.style.display !== 'none';
    panel.style.display = open ? 'none' : 'block';
    if (!open) { setTimeout(function(){ panel.scrollIntoView({behavior:'smooth',block:'start'}); }, 60); }
  };

  if (!parseBtn) return;

  /* ── Parse button ─────────────────────────────────────────────────────── */
  parseBtn.addEventListener('click', function() {
    var text = ta.value.trim();
    if (!text) { ta.focus(); return; }
    parseBtn.disabled = true; parseBtn.textContent = 'Parsing\u2026';
    preview.innerHTML = '<p style="color:#5a7a9a;padding:24px 0;font-size:13px;text-align:center;">Analyzing route lines\u2026</p>';
    if (footer) footer.style.display = 'none';
    if (mobileBar) mobileBar.classList.remove('pr-show');
    if (suggCard) suggCard.style.display = 'none';
    fetch('/api/parse-route-text', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({_csrf_token: csrf, text: text, route_id: RID})
    })
    .then(function(r) { return r.json(); })
    .then(function(d) {
      parseBtn.disabled = false; parseBtn.textContent = 'Parse Route';
      if (d.error) { preview.innerHTML = '<p style="color:#ff7090;padding:12px 0;">' + _esc(d.error) + '</p>'; return; }
      _stops = (d.stops || []).slice(); _removed = {};
      renderAll();
    })
    .catch(function() {
      parseBtn.disabled = false; parseBtn.textContent = 'Parse Route';
      preview.innerHTML = '<p style="color:#ff7090;padding:12px 0;">Request failed \u2014 check connection.</p>';
    });
  });

  /* ── Clear ────────────────────────────────────────────────────────────── */
  if (clearBtn) clearBtn.addEventListener('click', function() {
    ta.value = ''; preview.innerHTML = '';
    if (footer) footer.style.display = 'none';
    if (mobileBar) mobileBar.classList.remove('pr-show');
    if (suggCard) suggCard.style.display = 'none';
    _stops = []; _removed = {}; ta.focus();
  });

  /* ── Close / Cancel ───────────────────────────────────────────────────── */
  if (closeBtn)  closeBtn.addEventListener('click',  function() { if (panel) panel.style.display = 'none'; });
  if (cancelBtn) cancelBtn.addEventListener('click', function() { if (panel) panel.style.display = 'none'; });

  /* ── Render all ───────────────────────────────────────────────────────── */
  function renderAll() {
    var vis = _stops.filter(function(_, i) { return !_removed[i]; });
    if (!vis.length) {
      preview.innerHTML = '<p style="color:#5a7a9a;padding:16px 0;font-size:13px;">No stops detected. Try one stop per line.</p>';
      if (footer) footer.style.display = 'none';
      if (mobileBar) mobileBar.classList.remove('pr-show');
      if (suggCard) suggCard.style.display = 'none';
      return;
    }
    preview.innerHTML = _stops.map(function(s, i) { return _removed[i] ? '' : cardHTML(s, i); }).join('');
    renderSuggestions();
    if (footer) footer.style.display = 'flex';
    if (mobileBar) mobileBar.classList.add('pr-show');
    updateCount();
  }

  /* ── Remove card ──────────────────────────────────────────────────────── */
  window._haulsRemoveCard = function(i) {
    _removed[i] = true;
    var c = $('pr-card-' + i);
    if (c) { c.style.opacity = '0'; c.style.height = '0'; c.style.overflow = 'hidden'; c.style.padding = '0'; c.style.margin = '0'; }
    renderSuggestions(); updateCount();
    if (!_stops.some(function(_, idx) { return !_removed[idx]; })) {
      if (footer) footer.style.display = 'none';
      if (mobileBar) mobileBar.classList.remove('pr-show');
    }
  };

  /* ── Confidence helpers ───────────────────────────────────────────────── */
  function confCls(s)  { return s.confidence >= 75 ? 'h' : s.confidence >= 45 ? 'm' : 'l'; }
  function confBCls(s) { return s.confidence >= 75 ? 'pr-ch' : s.confidence >= 45 ? 'pr-cm' : 'pr-cl'; }
  function confLbl(s)  { return s.confidence >= 75 ? 'High' : s.confidence >= 45 ? 'Medium' : 'Low'; }

  /* ── Action badge ─────────────────────────────────────────────────────── */
  function actionBadge(action) {
    var a = (action || '').trim().toUpperCase();
    var cls = 'pr-b-other', lbl = a || '?';
    if (/PICKUP.*RETURN/.test(a) || a === 'PR' || /P.*&.*R/.test(a)) { cls = 'pr-b-pr'; lbl = 'PR'; }
    else if (/^PULL$|^P$/.test(a))   { cls = 'pr-b-p';    lbl = 'Pull'; }
    else if (/^DELIVERY$|^D$/.test(a)){ cls = 'pr-b-d';   lbl = 'Delivery'; }
    else if (/SWAP/.test(a))          { cls = 'pr-b-swap'; lbl = 'Swap'; }
    else if (/MOVE/.test(a))          { cls = 'pr-b-move'; lbl = 'Move'; }
    return '<span class="pr-badge ' + cls + '">' + _esc(lbl) + '</span>';
  }

  /* ── Missing field check ──────────────────────────────────────────────── */
  function missFlds(s) {
    var m = [];
    if (!s.dump_location) m.push('dump');
    if (!s.address)       m.push('address');
    if (!s.customer_name) m.push('customer');
    if (!s.action)        m.push('action');
    return m;
  }

  /* ── Dump select options ──────────────────────────────────────────────── */
  function dumpOpts(val) {
    return '<option value="">-- None --</option>' +
      DUMPS.map(function(n) {
        return '<option value="' + _esc(n) + '"' + (n === val ? ' selected' : '') + '>' + _esc(n) + '</option>';
      }).join('');
  }

  /* ── Field builder helpers ────────────────────────────────────────────── */
  function fld(lbl, id, val, col, miss) {
    var cs = col ? 'grid-column:' + col + ';' : '';
    return '<div style="' + cs + '"' + (miss ? ' class="pr-miss"' : '') + '>'
      + '<label class="pr-lbl" for="' + id + '">' + lbl + '</label>'
      + '<input id="' + id + '" class="pr-inp" value="' + _esc(val) + '">'
      + '</div>';
  }
  function dumpFld(id, val, miss) {
    return '<div' + (miss ? ' class="pr-miss"' : '') + '>'
      + '<label class="pr-lbl" for="' + id + '">Dump Location</label>'
      + '<select id="' + id + '" class="pr-inp">' + dumpOpts(val) + '</select>'
      + '</div>';
  }

  /* ── Card HTML ────────────────────────────────────────────────────────── */
  function cardHTML(s, i) {
    var miss = missFlds(s);
    var savedBadge = s.matched_saved ? '<span class="pr-badge pr-saved">&#11042; Saved</span>' : '';
    var warnStrip = '';
    if (miss.length) {
      var wMsgs = miss.map(function(f) {
        return {dump: 'Missing dump location', address: 'No address', customer: 'No customer name', action: 'Action unknown'}[f] || ('Missing: ' + f);
      });
      warnStrip = '<div class="pr-warn-strip">&#9888; ' + wMsgs.join(' &bull; ') + '</div>';
    }
    var mIdx = function(f) { return miss.indexOf(f) >= 0; };
    return (
      '<div class="pr-stop ' + confCls(s) + '" id="pr-card-' + i + '">'
      /* header */
      + '<div style="display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:10px;flex-wrap:wrap;">'
        + '<div style="display:flex;align-items:center;gap:6px;flex-wrap:wrap;">'
          + '<label style="display:flex;align-items:center;gap:7px;cursor:pointer;font-size:12px;color:#7aaac8;font-weight:700;">'
            + '<input type="checkbox" id="pr-chk-' + i + '" checked style="width:15px;height:15px;accent-color:#00ccff;"> Stop ' + (i + 1)
          + '</label>'
          + actionBadge(s.action)
        + '</div>'
        + '<div style="display:flex;align-items:center;gap:6px;">'
          + savedBadge
          + '<span class="pr-badge ' + confBCls(s) + '">' + confLbl(s) + ' (' + s.confidence + '%)</span>'
        + '</div>'
      + '</div>'
      /* original line */
      + '<div class="pr-orig">&ldquo;' + _esc(s.original_line) + '&rdquo;</div>'
      /* fields grid */
      + '<div style="display:grid;grid-template-columns:1fr 1fr;gap:8px;">'
        + fld('Customer', 'pr-cust-' + i,   s.customer_name,  '1/-1', mIdx('customer'))
        + fld('Address',  'pr-addr-' + i,   s.address,        '1/-1', mIdx('address'))
        + fld('City',     'pr-city-' + i,   s.city,           null,   false)
        + fld('State',    'pr-state-' + i,  s.state,          null,   false)
        + fld('Action',   'pr-action-' + i, s.action,         null,   mIdx('action'))
        + fld('Container','pr-cont-' + i,   s.container_size, null,   false)
        + dumpFld('pr-dump-' + i, s.dump_location, mIdx('dump'))
        + fld('ZIP',      'pr-zip-' + i,    s.zip_code,       null,   false)
      + '</div>'
      + warnStrip
      + '<div class="pr-card-acts">'
        + '<button class="pr-btn-sm pr-btn-remove" type="button" onclick="_haulsRemoveCard(' + i + ')">&#x2715; Remove</button>'
      + '</div>'
      + '</div>'
    );
  }

  /* ── Suggestions panel ────────────────────────────────────────────────── */
  function renderSuggestions() {
    if (!suggCard || !suggInner) return;
    var items = [];
    _stops.forEach(function(s, i) {
      if (_removed[i]) return;
      var n = i + 1;
      if (!s.dump_location) items.push({t: 'w', msg: 'Stop ' + n + ': Missing dump location'});
      if (!s.address)       items.push({t: 'e', msg: 'Stop ' + n + ': No address found \u2014 review before saving'});
      if (s.confidence < 45)items.push({t: 'e', msg: 'Stop ' + n + ': Low confidence \u2014 manual review recommended'});
      if (s.matched_saved)  items.push({t: 'i', msg: 'Stop ' + n + ': &#11042; Auto-filled from address history'});
      if (!s.action)        items.push({t: 'w', msg: 'Stop ' + n + ': Action not detected (enter P, D, PR, Swap, or Move)'});
    });
    if (!items.length) { suggCard.style.display = 'none'; return; }
    suggCard.style.display = 'block';
    suggInner.innerHTML = items.map(function(it) {
      var cls = it.t === 'e' ? 'pr-sugg pr-se' : it.t === 'i' ? 'pr-sugg pr-si' : 'pr-sugg pr-sw';
      var ic  = it.t === 'i' ? '&#10003;' : '&#9888;';
      return '<div class="' + cls + '"><span>' + ic + '</span><span>' + it.msg + '</span></div>';
    }).join('');
  }

  /* ── Stop count display ───────────────────────────────────────────────── */
  function updateCount() {
    var el = $('pr-stop-count'); if (!el) return;
    var n = _stops.filter(function(_, i) { return !_removed[i]; }).length;
    el.textContent = n + ' stop' + (n !== 1 ? 's' : '') + ' ready to add';
  }

  /* ── Build Route ──────────────────────────────────────────────────────── */
  if (buildBtn) buildBtn.addEventListener('click', function() {
    var toAdd = [], hasLow = false, hasMissReq = false;
    _stops.forEach(function(s, i) {
      if (_removed[i]) return;
      var chk = $('pr-chk-' + i);
      if (chk && !chk.checked) return;
      var stop = {
        customer_name: _v('pr-cust-' + i),   address:        _v('pr-addr-' + i),
        city:          _v('pr-city-' + i),    state:          _v('pr-state-' + i),
        zip_code:      _v('pr-zip-' + i),     action:         _v('pr-action-' + i),
        container_size:_v('pr-cont-' + i),    dump_location:  _v('pr-dump-' + i),
      };
      if (s.confidence < 45)                     hasLow = true;
      if (!stop.address || !stop.customer_name)  hasMissReq = true;
      toAdd.push(stop);
    });
    if (!toAdd.length) { alert('No stops selected.'); return; }
    if (hasLow || hasMissReq) {
      var msg = 'Some stops need review:\n';
      if (hasMissReq) msg += '\u2022 One or more stops missing address or customer name.\n';
      if (hasLow)     msg += '\u2022 One or more stops have low confidence.\n';
      msg += '\nContinue and add ' + toAdd.length + ' stop' + (toAdd.length !== 1 ? 's' : '') + ' anyway?';
      if (!confirm(msg)) return;
    }
    buildBtn.disabled = true; buildBtn.textContent = 'Adding\u2026';
    fetch('/route/' + RID + '/add-parsed-stops', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({_csrf_token: csrf, stops: toAdd})
    })
    .then(function(r) { return r.json(); })
    .then(function(d) {
      if (d.added) { location.reload(); }
      else { buildBtn.disabled = false; buildBtn.textContent = 'Build Route'; alert(d.error || 'Failed to add stops.'); }
    })
    .catch(function() { buildBtn.disabled = false; buildBtn.textContent = 'Build Route'; alert('Network error \u2014 try again.'); });
  });

  function _v(id) { var el = $(id); return el ? el.value.trim() : ''; }
  function _esc(s) {
    return (s || '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  }
})();
"""


def upsert_saved_address(conn, company_id, customer_name, address,
                          city, state, zip_code, action, container_size, dump_location):
    """Save or update a customer address in saved_addresses for autocomplete.
    Also tracks each (action, container_size, dump_location) combination in
    saved_address_details so the API can return the most-frequently-used defaults.
    """
    if not company_id:
        return
    cname = (customer_name or "").strip()
    addr  = (address or "").strip()
    if not cname:
        return
    ts   = now_ts()
    full = ", ".join(p for p in [addr, city or "", state or "", zip_code or ""] if p.strip())
    try:
        existing = conn.execute(
            "SELECT id FROM saved_addresses WHERE company_id=? AND customer_name=? AND address=?",
            (company_id, cname, addr)
        ).fetchone()
        if existing:
            sa_id = existing["id"]
            conn.execute("""
                UPDATE saved_addresses SET
                    city=?, state=?, zip=?, full_address=?,
                    times_used=times_used+1, last_used_at=?
                WHERE id=?
            """, (city or "", state or "", zip_code or "", full, ts, sa_id))
        else:
            conn.execute("""
                INSERT INTO saved_addresses
                    (company_id, customer_name, address, city, state, zip, full_address,
                     default_action, default_container_size, default_dump_location,
                     times_used, last_used_at, created_at)
                VALUES (?,?,?,?,?,?,?,?,?,?,1,?,?)
            """, (company_id, cname, addr, city or "", state or "", zip_code or "", full,
                  action or "", container_size or "", dump_location or "", ts, ts))
            sa_id = conn.execute(
                "SELECT id FROM saved_addresses WHERE company_id=? AND customer_name=? AND address=?",
                (company_id, cname, addr)
            ).fetchone()["id"]

        # Track this specific combination for frequency-based smart defaults
        act = (action or "").strip()
        cs  = (container_size or "").strip()
        dl  = (dump_location or "").strip()
        det = conn.execute(
            """SELECT id FROM saved_address_details
               WHERE saved_address_id=? AND action=? AND container_size=? AND dump_location=?""",
            (sa_id, act, cs, dl)
        ).fetchone()
        if det:
            conn.execute(
                "UPDATE saved_address_details SET times_used=times_used+1, last_used_at=? WHERE id=?",
                (ts, det["id"])
            )
        else:
            conn.execute(
                """INSERT INTO saved_address_details
                   (saved_address_id, action, container_size, dump_location, times_used, last_used_at)
                   VALUES (?,?,?,?,1,?)""",
                (sa_id, act, cs, dl, ts)
            )
    except Exception:
        pass


@app.route("/route/<int:route_id>")
@login_required
def view_route(route_id):
    conn = get_db()
    route = conn.execute("""
        SELECT r.*, u.username AS assigned_username, c.username AS created_username
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        LEFT JOIN users c ON r.created_by = c.id
        WHERE r.id = ? AND r.company_id = ?
    """, (route_id, cid())).fetchone()
    if not route:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    stops = conn.execute("SELECT * FROM stops WHERE route_id = ? ORDER BY stop_order ASC, id ASC", (route_id,)).fetchall()

    # Ensure can_state_before is populated so PR mode always shows correctly
    if stops and any(s["can_state_before"] is None for s in stops):
        compute_can_flow(conn, route_id)
        conn.commit()
        stops = conn.execute("SELECT * FROM stops WHERE route_id = ? ORDER BY stop_order ASC, id ASC", (route_id,)).fetchall()

    stop_ids = [s["id"] for s in stops]
    photos_by_stop = load_stop_photos(conn, stop_ids)
    dump_locs_for_form = conn.execute(
        "SELECT name FROM dump_locations WHERE active=1 ORDER BY name"
    ).fetchall()
    conn.close()

    completed_count = sum(1 for s in stops if s["status"] == "completed")
    total_count = len(stops)
    
    route_action_buttons = ""

    if route["status"] == "open":
        route_action_buttons += f"""
        <form class="inline" method="POST" action="{url_for('mark_route_in_progress', route_id=route_id)}">
            <button class="btn orange" type="submit">Start Route</button>
        </form>
        """

    if route["status"] == "in_progress":
        route_action_buttons += f"""
        <form class="inline" method="POST" action="{url_for('mark_route_completed', route_id=route_id)}">
            <button class="btn green" type="submit">Complete Route</button>
        </form>
        """

    if route["status"] == "completed":
        route_action_buttons += f"""
    <form class="inline" method="POST" action="{url_for('reopen_route', route_id=route_id)}">
        <button class="btn secondary" type="submit">Reopen Route</button>
    </form>
    """

    if session.get("role") == "boss":
        route_action_buttons += f"""
    <button class="btn" type="button" onclick="_haulsTogglePaste()" style="background:linear-gradient(135deg,#004e8c,#003060);border:1px solid rgba(0,160,255,.3);">&#x1F4CB; Paste Route</button>
    <a class="btn secondary" href="{url_for('route_daily_log', route_id=route_id)}">&#x1F4CB; Daily Log</a>
    <form class="inline" method="POST" action="{url_for('optimize_route', route_id=route_id)}"
          id="optimize-form"
          onsubmit="showOptimizeOverlay(event, {len(stops)})">
        <button class="btn orange" type="submit" id="optimize-btn">&#9883; Smart Optimize</button>
    </form>
    <form class="inline" method="POST"
      action="{url_for('delete_route', route_id=route_id)}"
      onsubmit="return confirm('Delete this entire route?')">
        <button class="btn red" type="submit">Delete Route</button>
    </form>
    """

    extra_head = '<script src="https://cdn.jsdelivr.net/npm/sortablejs@1.15.2/Sortable.min.js"></script>'
    reorder_script = ""
    if session.get("role") == "boss":
        reorder_script = f"""
        <script>
            document.addEventListener("DOMContentLoaded", function() {{
                const el = document.getElementById("stop-list");
                if (!el || typeof Sortable === "undefined") return;
                new Sortable(el, {{
                    animation: 150,
                    handle: ".stop-handle",
                    onEnd: function() {{
                        const ids = Array.from(el.querySelectorAll("[data-stop-id]")).map(x => x.dataset.stopId);
                        const csrfMeta = document.querySelector('meta[name="csrf-token"]');
                        fetch("{url_for('reorder_stops', route_id=route_id)}", {{
                            method: "POST",
                            headers: {{
                                "Content-Type": "application/json",
                                "X-CSRF-Token": csrfMeta ? csrfMeta.getAttribute('content') : ''
                            }},
                            body: JSON.stringify({{ stop_ids: ids }})
                        }}).then(r => r.json()).then(data => {{
                            if (data.success) window.location.reload();
                            else alert("Reorder failed");
                        }});
                    }}
                }});
            }});
        </script>
        """
    next_open_stop_id = None
    stop_cards = ""
    for s in stops:
        if next_open_stop_id is None and s["status"] != "completed":
         next_open_stop_id = s["stop_order"]
        photo_html = build_photo_gallery_html(photos_by_stop.get(s["id"], []))

        edit_button = f'<a class="btn secondary" href="{url_for("edit_stop", stop_id=s["id"])}">Edit</a>' if session.get("role") == "boss" else ''
        delete_button = f'<form class="inline" method="POST" action="{url_for("delete_stop", stop_id=s["id"])}" onsubmit="return confirm(\'Delete this stop?\')"><button class="btn red" type="submit">Delete</button></form>' if session.get("role") == "boss" else ''

        # Can-state pill — boss view only, shown when compute_can_flow has run
        _csb = dict(s).get("can_state_before") or ""
        if session.get("role") == "boss" and _csb:
            if _csb == "empty_can":
                _can_pill = (
                    ' <span title="Truck arrives with empty can" style="font-size:11px;'
                    'background:rgba(97,247,223,0.15);color:#61f7df;padding:2px 8px;'
                    'border-radius:6px;font-weight:700;vertical-align:middle;">'
                    '&#x1F7E2; Empty Can</span>'
                )
            else:  # no_can
                _can_pill = (
                    ' <span title="Truck arrives with no container" style="font-size:11px;'
                    'background:rgba(120,120,140,0.18);color:#9aa5b8;padding:2px 8px;'
                    'border-radius:6px;font-weight:700;vertical-align:middle;">'
                    '&#x26AA; No Can</span>'
                )
        else:
            _can_pill = ""

        # Swap badge + warning — PR stops only, boss view
        _action_sc  = (dict(s).get("action") or "").lower()
        _is_pr_sc   = (
            "pickup and return" in _action_sc
            or ("swap" in _action_sc and "pull" not in _action_sc)
        )
        if session.get("role") == "boss" and _is_pr_sc:
            if _csb == "empty_can":
                _swap_badge = (
                    ' <span title="PR Mode: Swap — driver carries empty can from prior Pull" '
                    'style="font-size:11px;background:rgba(97,247,223,0.15);color:#61f7df;'
                    'padding:2px 8px;border-radius:6px;font-weight:700;vertical-align:middle;">'
                    '&#x1F504; PR Mode: Swap</span>'
                )
                _swap_warning = ""
            elif _csb == "no_can":
                _swap_badge = (
                    ' <span title="PR Mode: Return Same Can — driver boxes out, dumps, returns empty can to site" '
                    'style="font-size:11px;background:rgba(150,200,255,0.18);color:#93c5fd;'
                    'padding:2px 8px;border-radius:6px;font-weight:700;vertical-align:middle;">'
                    '&#x21A9;&#xFE0F; PR Mode: Return Same Can</span>'
                )
                _swap_warning = ""
            else:
                # can_state_before is NULL — route not yet optimized
                _swap_badge = (
                    ' <span title="Run Smart Optimize to derive PR mode from stop sequence" '
                    'style="font-size:11px;background:rgba(120,120,140,0.12);color:#6a7a8a;'
                    'padding:2px 8px;border-radius:6px;font-weight:700;vertical-align:middle;">'
                    '&#x1F504; PR Mode: ?</span>'
                )
                _swap_warning = ""
        else:
            _swap_badge   = ""
            _swap_warning = ""

        stop_cards += f"""
        <div class="stop-card" data-stop-id="{s['id']}">
            <div class="row between">
                <div>
                    {'<span class="stop-handle">☰</span>' if session.get('role') == 'boss' else ''}
                    <strong>Stop #{s['stop_order']}</strong>
                    <span class="badge {e(s['status'])}">{e(s['status'])}</span>
                </div>
                <div class="row">
                    {edit_button}
                    {delete_button}
                    <a class="btn secondary" href="{url_for('dump_ticket', stop_id=s['id'])}" style="font-size:13px;">&#x1F9FE; Dump Ticket</a>
                    <form class="inline" method="POST" action="{url_for('toggle_stop_complete', stop_id=s['id'])}">
                        <button class="btn green" type="submit">{'Reopen Stop' if s['status']=='completed' else 'Complete Stop'}</button>
                    </form>
                </div>
            </div>
            <p><strong>Customer:</strong> {e(s['customer_name'] or '')}</p>
            <p><strong>Address:</strong> {e(s['address'] or '')} {e(s['city'] or '')} {e(s['state'] or '')} {e(s['zip_code'] or '')}</p>
            <p><strong>Action:</strong> {e(s['action'] or '')}{_can_pill}{_swap_badge}</p>
            {_swap_warning}
            <p><strong>Container:</strong> {e(s['container_size'] or '')}</p>
            <p><strong>Ticket:</strong> {e(s['ticket_number'] or '')}</p>
            <p><strong>Reference:</strong> {e(s['reference_number'] or '')}</p>
            <p><strong>Notes:</strong><br>{e(s['notes'] or '').replace(chr(10), '<br>')}</p>
            <p><strong>Signature:</strong> {e(s['driver_signature'] or '')}</p>
            <p><strong>Completed At:</strong> {e(s['completed_at'] or '')}</p>
            {photo_html}
            <form method="POST" action="{url_for('upload_stop_photo', stop_id=s['id'])}" enctype="multipart/form-data">
                <label>Upload Photo / Ticket / Proof</label>
                <input type="file" name="photos" accept=".png,.jpg,.jpeg,.webp,.pdf" multiple required>
                <button class="btn secondary" type="submit">Upload</button>
            </form>
        </div>
        """

    paste_panel_block = ""
    if session.get("role") == "boss":
        _dump_locs_json = json.dumps([dl["name"] for dl in dump_locs_for_form])
        paste_panel_block = f"""
        {_PASTE_ROUTE_CSS}
        <div id="paste-route-panel" style="display:none;margin-bottom:24px;">

            <!-- Panel header -->
            <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:18px;padding-bottom:16px;border-bottom:1px solid rgba(0,160,255,.1);">
                <div>
                    <h2 style="margin:0 0 4px;font-size:20px;color:#e5eefc;">&#x1F4CB; Paste Route</h2>
                    <p style="margin:0;font-size:13px;color:#4a6a88;">Paste messy route text &mdash; HAULTRA structures it into stops.</p>
                </div>
                <button id="pr-close-btn" type="button" style="background:rgba(255,255,255,.05);border:1px solid rgba(255,255,255,.1);border-radius:8px;color:#7a9ab8;padding:7px 14px;cursor:pointer;font-size:13px;font-family:inherit;">&#x2715; Close</button>
            </div>

            <!-- 2-column grid -->
            <div class="pr-grid">

                <!-- LEFT: Input + Tips -->
                <div>
                    <!-- A: Paste Input -->
                    <div class="pr-card">
                        <h3>Paste Route Text</h3>
                        <p class="pr-sub">Paste one stop per line. HAULTRA will structure the route.</p>
                        <div style="margin-bottom:14px;padding:10px 14px;background:rgba(0,0,0,.2);border-radius:8px;border-left:3px solid rgba(0,160,255,.3);">
                            <div style="font-size:10px;color:#3d5a74;font-weight:700;text-transform:uppercase;letter-spacing:.5px;margin-bottom:7px;">Examples</div>
                            <div class="pr-tip-code" style="display:block;margin-bottom:4px;">PR 515 central dr talent 30 dom</div>
                            <div class="pr-tip-code" style="display:block;margin-bottom:4px;">P 224 golden maple bartlett 20 wat</div>
                            <div class="pr-tip-code" style="display:block;">D 900 tidewater quick demo 20</div>
                        </div>
                        <textarea id="pr-textarea" rows="8" placeholder="Paste route here &mdash; one stop per line&hellip;" style="width:100%;background:rgba(0,0,0,.4);border:1px solid rgba(0,160,255,.15);border-radius:9px;color:#c8dff0;padding:12px 14px;font-size:13px;line-height:1.7;resize:vertical;box-sizing:border-box;font-family:monospace;"></textarea>
                        <div style="display:flex;gap:10px;margin-top:12px;flex-wrap:wrap;">
                            <button id="pr-parse-btn" class="btn" type="button" style="padding:9px 22px;">Parse Route</button>
                            <button id="pr-clear-btn" class="btn secondary" type="button" style="padding:9px 16px;">Clear</button>
                        </div>
                    </div>

                    <!-- B: Parsing Tips -->
                    <div class="pr-card">
                        <h3 style="margin-bottom:12px;">Parsing Tips</h3>
                        <div class="pr-tip-item">
                            <strong>Service Types</strong><br>
                            <span class="pr-tip-code">P</span> Pull &nbsp;
                            <span class="pr-tip-code">D</span> Delivery &nbsp;
                            <span class="pr-tip-code">PR</span> Pickup &amp; Return &nbsp;
                            <span class="pr-tip-code">Swap</span> &nbsp;
                            <span class="pr-tip-code">Move</span>
                        </div>
                        <div class="pr-tip-item">
                            <strong>City Abbreviations</strong><br>
                            <span class="pr-tip-code">vb</span> Virginia Beach &nbsp;
                            <span class="pr-tip-code">ches</span> Chesapeake &nbsp;
                            <span class="pr-tip-code">norf</span> Norfolk
                        </div>
                        <div class="pr-tip-item">
                            <strong>Dump Abbreviations</strong><br>
                            <span class="pr-tip-code">dom</span> Dominion &nbsp;
                            <span class="pr-tip-code">wat</span> Waterway &nbsp;
                            <span class="pr-tip-code">bay</span> Bay &nbsp;
                            <span class="pr-tip-code">spsa</span> SPSA Landfill
                        </div>
                        <div class="pr-tip-item">
                            <strong>Container Sizes</strong><br>
                            Include <span class="pr-tip-code">20yd</span> or <span class="pr-tip-code">30 yards</span> anywhere in the line
                        </div>
                        <div class="pr-tip-item">
                            <strong>Confidence Scores</strong><br>
                            <span class="pr-badge pr-ch" style="font-size:10px;">High</span> All fields found &nbsp;
                            <span class="pr-badge pr-cm" style="font-size:10px;">Medium</span> Some fields guessed &nbsp;
                            <span class="pr-badge pr-cl" style="font-size:10px;">Low</span> Needs review
                        </div>
                    </div>
                </div>

                <!-- RIGHT: Preview + Suggestions -->
                <div>
                    <!-- C: Parsed Stops Preview -->
                    <div class="pr-card">
                        <h3>Parsed Stops Preview</h3>
                        <p class="pr-sub" id="pr-preview-sub">Click <strong style="color:#7aaac8;">Parse Route</strong> to analyze your pasted text.</p>
                        <div id="pr-preview"></div>
                        <div class="pr-footer-bar" id="pr-footer-bar" style="display:none;">
                            <span class="pr-footer-count" id="pr-stop-count"></span>
                            <button id="pr-build-btn" class="btn green" type="button" style="padding:10px 24px;font-weight:800;font-size:14px;">Build Route</button>
                            <button id="pr-cancel-btn" class="btn secondary" type="button">Cancel</button>
                        </div>
                    </div>

                    <!-- D: Suggestions & Warnings -->
                    <div class="pr-card" id="pr-sugg-card" style="display:none;">
                        <h3 style="margin-bottom:12px;">&#x1F4A1; Suggestions &amp; Warnings</h3>
                        <div id="pr-sugg-inner"></div>
                    </div>
                </div>

            </div><!-- end pr-grid -->
        </div><!-- end paste-route-panel -->

        <!-- Mobile sticky bottom bar -->
        <div id="pr-mobile-bar">
            <button type="button" onclick="document.getElementById('pr-parse-btn').click()" class="btn" style="flex:1;">Parse Route</button>
            <button type="button" onclick="var b=document.getElementById('pr-build-btn');if(b)b.click();" class="btn green" style="flex:1;">Build Route</button>
        </div>

        <script>var _HAULTRA_ROUTE_ID = {route_id}; var _HAULTRA_DUMP_LOCS = {_dump_locs_json};</script>
        <script>{_PASTE_ROUTE_JS}</script>
        """

    add_stop_block = ""
    if session.get("role") == "boss":
        _existing_stops_json = json.dumps([
            {"customer_name": s["customer_name"] or "", "address": s["address"] or "", "action": s["action"] or ""}
            for s in stops
        ])
        add_stop_block = f"""
        <div class="card">
            <h2>Add Manual Stop</h2>
            <form method="POST" action="{url_for('add_stop', route_id=route_id)}">
                <div class="grid">
                    <div style="position:relative;"><label>Customer</label><input name="customer_name" data-hac="1" autocomplete="off"></div>
                    <div style="position:relative;"><label>Address</label><input name="address" data-hac="1" autocomplete="off"></div>
                    <div><label>City</label><input name="city"></div>
                    <div><label>State</label><input name="state"></div>
                    <div><label>ZIP</label><input name="zip_code"></div>
                    <div><label>Action</label><input name="action"></div>
                    <div><label>Container Size</label><input name="container_size"></div>
                    <div><label>Ticket Number</label><input name="ticket_number"></div>
                    <div><label>Reference Number</label><input name="reference_number"></div>
                    <div>
                        <label>Dump Location</label>
                        {'<select name="dump_location"><option value="">-- None --</option>' + "".join(f'<option value="{e(dl["name"])}">{e(dl["name"])}</option>' for dl in dump_locs_for_form) + '</select>' if dump_locs_for_form else '<input name="dump_location" placeholder="e.g. Dominion">'}
                    </div>
                </div>
                <label>Notes</label>
                <textarea name="notes"></textarea>
                <p style="margin:10px 0 4px;color:#6a8aa8;font-size:11px;">
                    Swap logic for PR stops is auto-derived from route order after Smart Optimize.
                </p>
                <div style="margin-top:6px;"><button type="submit">Add Stop</button></div>
            </form>
        </div>
        <script>{_AUTOCOMPLETE_JS}</script>
        <script>var _HAULTRA_STOPS = {_existing_stops_json};</script>
        <script>{_STOP_WARNINGS_JS}</script>
        """

    body = f"""
    <div class="hero">
        <h1>{e(route['route_name'])}</h1>
        <p>{e(route['route_date'])} | Assigned to: {e(route['assigned_username'] or 'Unassigned')}</p>
        <p>Status: <span class="badge {e(route['status'])}">{e(route['status'])}</span></p>
        <p>Progress: {completed_count}/{total_count} stops completed</p>
        <div class="row" style="margin-top:12px;">
            {route_action_buttons}
        </div>
    </div>

    <div id="stop-list">
        {stop_cards}
    </div>

    {paste_panel_block}
    {add_stop_block}
    {reorder_script}

    <!-- Optimize loading overlay -->
    <div id="optimize-overlay" style="
            display:none; position:fixed; inset:0; z-index:2000;
            background:rgba(4,10,22,0.88); backdrop-filter:blur(6px);
            flex-direction:column; align-items:center; justify-content:center;
            color:#e5eefc; font-family:inherit;">
        <div style="font-size:42px; margin-bottom:16px;">&#9883;</div>
        <div style="font-size:20px; font-weight:900; margin-bottom:8px;">Optimizing Route&hellip;</div>
        <div id="optimize-msg" style="font-size:14px; color:#8fd3ff; margin-bottom:24px;">
            Geocoding stops &mdash; this takes about 1 second per stop
        </div>
        <div style="width:240px; background:rgba(255,255,255,0.1); border-radius:999px; height:8px; overflow:hidden;">
            <div id="optimize-progress-bar"
                 style="height:100%; width:0%; border-radius:999px;
                        background:linear-gradient(90deg,#61f7df,#3fd2ff);
                        transition:width 1.1s linear;"></div>
        </div>
        <div id="optimize-step" style="font-size:12px; color:#6a8aa8; margin-top:10px;"></div>
    </div>

    <script>
    function showOptimizeOverlay(e, stopCount) {{
        var overlay = document.getElementById('optimize-overlay');
        if (overlay) {{
            overlay.style.display = 'flex';
            // Animate the fake progress bar in sync with geocoding (1.1s/stop)
            var bar  = document.getElementById('optimize-progress-bar');
            var step = document.getElementById('optimize-step');
            var done = 0;
            var interval = setInterval(function() {{
                done++;
                if (done <= stopCount) {{
                    var pct = Math.round(done / stopCount * 85); // cap at 85% until redirect
                    if (bar)  bar.style.width  = pct + '%';
                    if (step) step.textContent = 'Geocoding stop ' + done + ' of ' + stopCount + '\u2026';
                }} else {{
                    clearInterval(interval);
                    if (bar)  bar.style.width = '100%';
                    if (step) step.textContent = 'Saving optimized order\u2026';
                }}
            }}, 1100);
        }}
        // Let the form submit normally
    }}
    </script>
    """

    return render_template_string(shell_page("Route", body, extra_head))

@app.route("/route/<int:route_id>/start", methods=["POST"])
@login_required
def mark_route_in_progress(route_id):
    conn = get_db()
    route = conn.execute(
        "SELECT * FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone()

    if not route:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    conn.execute("""
        UPDATE routes SET status='in_progress', started_at=?
        WHERE id=? AND company_id=?
    """, (now_ts(), route_id, cid()))

    conn.commit()
    conn.close()

    flash("Route marked in progress.", "success")
    return redirect(url_for("view_route", route_id=route_id))


@app.route("/route/<int:route_id>/complete", methods=["POST"])
@login_required
def mark_route_completed(route_id):
    conn = get_db()
    route = conn.execute(
        "SELECT * FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone()

    if not route:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    conn.execute("""
        UPDATE routes SET status='completed', completed_at=?
        WHERE id=? AND company_id=?
    """, (now_ts(), route_id, cid()))

    conn.commit()
    conn.close()

    flash("Route marked completed.", "success")
    return redirect(url_for("view_route", route_id=route_id))


@app.route("/route/<int:route_id>/reopen", methods=["POST"])
@login_required
def reopen_route(route_id):
    conn = get_db()
    route = conn.execute(
        "SELECT * FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone()

    if not route:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    conn.execute("""
        UPDATE routes SET status='open', completed_at=NULL
        WHERE id=? AND company_id=?
    """, (route_id, cid()))

    conn.commit()
    conn.close()

    flash("Route reopened.", "success")
    return redirect(url_for("view_route", route_id=route_id))


# =========================================================
# ADD STOP
# =========================================================
@app.route("/route/<int:route_id>/add_stop", methods=["POST"])
@boss_required
def add_stop(route_id):
    conn = get_db()
    if not conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone():
        conn.close()
        abort(404)

    last = conn.execute(
        "SELECT MAX(stop_order) as m FROM stops WHERE route_id=?",
        (route_id,)
    ).fetchone()["m"] or 0

    conn.execute("""
        INSERT INTO stops (
            route_id, stop_order, customer_name, address, city, state, zip_code,
            action, container_size, ticket_number, reference_number, dump_location, notes,
            swap_with_prev_pull, status, created_at
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 'open', ?)
    """, (
        route_id,
        last + 1,
        expand_abbrev(request.form.get("customer_name")),
        expand_abbrev(request.form.get("address")),
        expand_abbrev(request.form.get("city")),
        expand_abbrev(request.form.get("state")),
        expand_abbrev(request.form.get("zip_code")),
        expand_abbrev(request.form.get("action")),
        expand_abbrev(request.form.get("container_size")),
        request.form.get("ticket_number"),
        request.form.get("reference_number"),
        expand_abbrev(request.form.get("dump_location", "")),
        request.form.get("notes"),
        now_ts()
    ))

    conn.commit()
    # Recompute can flow so the new stop gets swap_with_prev_pull derived from sequence
    compute_can_flow(conn, route_id)
    conn.commit()
    upsert_saved_address(conn, cid(),
        expand_abbrev(request.form.get("customer_name")), expand_abbrev(request.form.get("address")),
        expand_abbrev(request.form.get("city")), expand_abbrev(request.form.get("state")),
        expand_abbrev(request.form.get("zip_code")), expand_abbrev(request.form.get("action")),
        expand_abbrev(request.form.get("container_size")), expand_abbrev(request.form.get("dump_location", "")))
    conn.commit()
    conn.close()
    flash("Stop added.", "success")
    return redirect(url_for("view_route", route_id=route_id))


# =========================================================
# EDIT STOP
# =========================================================
@app.route("/stop/<int:stop_id>/edit", methods=["GET", "POST"])
@boss_required
def edit_stop(stop_id):
    conn = get_db()
    # verify stop belongs to this company
    ownership = conn.execute(
        """SELECT s.*, r.id AS route_id_chk FROM stops s
           JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()
    if not ownership:
        conn.close()
        abort(404)

    if request.method == "POST":
        conn.execute("""
            UPDATE stops SET
                customer_name=?, address=?, city=?, state=?, zip_code=?,
                action=?, container_size=?, ticket_number=?, reference_number=?,
                dump_location=?, notes=?
            WHERE id=?
        """, (
            expand_abbrev(request.form.get("customer_name")),
            expand_abbrev(request.form.get("address")),
            expand_abbrev(request.form.get("city")),
            expand_abbrev(request.form.get("state")),
            expand_abbrev(request.form.get("zip_code")),
            expand_abbrev(request.form.get("action")),
            expand_abbrev(request.form.get("container_size")),
            request.form.get("ticket_number"),
            request.form.get("reference_number"),
            expand_abbrev(request.form.get("dump_location", "")),
            request.form.get("notes"),
            stop_id
        ))
        conn.commit()
        route_id = ownership["route_id"]
        # Recompute can flow and derive swap_with_prev_pull from sequence
        compute_can_flow(conn, route_id)
        conn.commit()
        upsert_saved_address(conn, cid(),
            expand_abbrev(request.form.get("customer_name")), expand_abbrev(request.form.get("address")),
            expand_abbrev(request.form.get("city")), expand_abbrev(request.form.get("state")),
            expand_abbrev(request.form.get("zip_code")), expand_abbrev(request.form.get("action")),
            expand_abbrev(request.form.get("container_size")), expand_abbrev(request.form.get("dump_location", "")))
        conn.commit()
        conn.close()
        flash("Stop updated.", "success")
        return redirect(url_for("view_route", route_id=route_id))

    stop = ownership
    _stop = dict(stop)
    _edit_dump_locs = conn.execute(
        "SELECT name FROM dump_locations WHERE active=1 ORDER BY name"
    ).fetchall()
    _sibling_stops = conn.execute(
        "SELECT customer_name, address, action FROM stops WHERE route_id=? AND id!=? ORDER BY stop_order",
        (ownership["route_id"], stop_id)
    ).fetchall()
    conn.close()
    _sibling_json = json.dumps([
        {"customer_name": s["customer_name"] or "", "address": s["address"] or "", "action": s["action"] or ""}
        for s in _sibling_stops
    ])

    # Derive swap display for read-only info panel
    _csb_edit   = _stop.get("can_state_before") or ""
    _action_edit = (_stop.get("action") or "").lower()
    _is_pr_edit  = (
        "pickup and return" in _action_edit
        or ("swap" in _action_edit and "pull" not in _action_edit)
    )
    if _is_pr_edit:
        if _csb_edit == "empty_can":
            _swap_info_block = """
            <div style="margin-top:16px;padding:14px 16px;
                        background:rgba(97,247,223,0.08);
                        border:1px solid rgba(97,247,223,0.28);border-radius:10px;">
                <p style="margin:0 0 4px;color:#61f7df;font-size:13px;font-weight:700;">
                    &#x1F504; PR Mode: Swap
                </p>
                <p style="margin:0;color:#7ab8a8;font-size:12px;">
                    A Pull precedes this PR with no Delivery in between.
                    Driver carries an empty can to this stop and swaps it for the full one.
                    Workflow: Arrive &#x2192; Box Out &#x2192; Box In &#x2192; Go To Dump &#x2192; Complete.
                </p>
            </div>"""
        elif _csb_edit == "no_can":
            _swap_info_block = """
            <div style="margin-top:16px;padding:14px 16px;
                        background:rgba(150,200,255,0.07);
                        border:1px solid rgba(150,200,255,0.28);border-radius:10px;">
                <p style="margin:0 0 4px;color:#93c5fd;font-size:13px;font-weight:700;">
                    &#x21A9;&#xFE0F; PR Mode: Return Same Can
                </p>
                <p style="margin:0;color:#7a9ab8;font-size:12px;">
                    No empty can in sequence &#x2014; driver boxes out the full can, dumps it,
                    then returns the emptied can to the same site.
                    Workflow: Arrive &#x2192; Box Out &#x2192; Go To Dump &#x2192; Return &amp; Box In &#x2192; Complete.
                </p>
            </div>"""
        else:
            _swap_info_block = """
            <div style="margin-top:16px;padding:14px 16px;
                        background:rgba(120,140,160,0.08);
                        border:1px solid rgba(120,140,160,0.25);border-radius:10px;">
                <p style="margin:0 0 4px;color:#9aa5b8;font-size:13px;font-weight:700;">
                    &#x1F504; PR Mode: Unknown
                </p>
                <p style="margin:0;color:#6a7a8a;font-size:12px;">
                    Can flow has not been computed for this route yet.
                    Run Smart Optimize to derive PR mode from stop sequence.
                </p>
            </div>"""
    else:
        _swap_info_block = ""

    _cur_dump = _stop.get('dump_location') or ''
    _dump_field = (
        '<select name="dump_location">'
        + '<option value="">-- None --</option>'
        + "".join(
            f'<option value="{e(dl["name"])}"{"  selected" if dl["name"] == _cur_dump else ""}>{e(dl["name"])}</option>'
            for dl in _edit_dump_locs
        )
        + '</select>'
    ) if _edit_dump_locs else f'<input name="dump_location" placeholder="e.g. Dominion" value="{e(_cur_dump)}">'

    body = f"""
    <div class="card" style="max-width:680px;">
        <h2 style="margin-bottom:18px;">Edit Stop</h2>
        <form method="POST">
            <div class="grid" style="grid-template-columns:1fr 1fr;gap:12px 16px;">
                <div style="grid-column:1/-1;">
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Customer Name</label>
                    <input name="customer_name" value="{e(_stop['customer_name'])}" data-hac="1" autocomplete="off">
                </div>
                <div style="grid-column:1/-1;">
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Address</label>
                    <input name="address" value="{e(_stop['address'])}" data-hac="1" autocomplete="off">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">City</label>
                    <input name="city" value="{e(_stop['city'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">State</label>
                    <input name="state" value="{e(_stop['state'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">ZIP</label>
                    <input name="zip_code" value="{e(_stop['zip_code'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Action</label>
                    <input name="action" value="{e(_stop['action'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Container Size</label>
                    <input name="container_size" value="{e(_stop['container_size'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Ticket Number</label>
                    <input name="ticket_number" value="{e(_stop['ticket_number'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Reference Number</label>
                    <input name="reference_number" value="{e(_stop['reference_number'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Dump Location</label>
                    {_dump_field}
                </div>
                <div style="grid-column:1/-1;">
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Notes</label>
                    <textarea name="notes" rows="3">{e(_stop['notes'])}</textarea>
                </div>
            </div>

            {_swap_info_block}

            <div style="margin-top:18px;display:flex;gap:10px;">
                <button type="submit" class="btn">Save Changes</button>
                <a class="btn secondary" href="{url_for('view_route', route_id=_stop['route_id'])}">Cancel</a>
            </div>
        </form>
    </div>
    """
    body += "<script>" + _AUTOCOMPLETE_JS + "</script>"
    body += '<script>var _HAULTRA_STOPS = ' + _sibling_json + ';</script>'
    body += '<script>' + _STOP_WARNINGS_JS + '</script>'
    return render_template_string(shell_page("Edit Stop", body))

# =========================================================
# DELETE ROUTE
# =========================================================
@app.route("/route/<int:route_id>/delete", methods=["POST"])
@boss_required
def delete_route(route_id):
    conn = get_db()
    if not conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone():
        conn.close()
        abort(404)

    # delete child records first
    conn.execute("DELETE FROM route_photos WHERE stop_id IN (SELECT id FROM stops WHERE route_id=?)", (route_id,))
    conn.execute("DELETE FROM stops WHERE route_id=?", (route_id,))
    conn.execute("DELETE FROM routes WHERE id=? AND company_id=?", (route_id, cid()))

    conn.commit()
    conn.close()

    flash("Route deleted.", "success")
    return redirect(url_for("routes_page"))

# =========================================
# ORDER ACTIONS
# =========================================

@app.route("/order/<int:order_id>/close", methods=["POST"])
@boss_required
def close_order(order_id):
    conn = get_db()
    conn.execute(
        "UPDATE orders SET status='closed' WHERE id = ? AND company_id = ?",
        (order_id, cid())
    )
    conn.commit()
    conn.close()
    flash("Order closed.", "success")
    return redirect(url_for("orders_page"))


@app.route("/order/<int:order_id>/delete", methods=["POST"])
@boss_required
def delete_order(order_id):
    conn = get_db()

    order = conn.execute(
        "SELECT status FROM orders WHERE id = ? AND company_id = ?",
        (order_id, cid())
    ).fetchone()

    if not order:
        conn.close()
        abort(404)

    if order["status"] == "converted":
        conn.close()
        flash("Cannot delete a converted order.", "error")
        return redirect(url_for("orders_page"))

    conn.execute("DELETE FROM orders WHERE id = ? AND company_id = ?", (order_id, cid()))
    conn.commit()
    conn.close()

    flash("Order deleted.", "success")
    return redirect(url_for("orders_page"))


# =========================================================
# DELETE STOP
# =========================================================
@app.route("/stop/<int:stop_id>/delete", methods=["POST"])
@boss_required
def delete_stop(stop_id):
    conn = get_db()
    row = conn.execute(
        """SELECT s.route_id FROM stops s
           JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()
    if not row:
        conn.close()
        abort(404)
    route_id = row["route_id"]

    conn.execute("DELETE FROM route_photos WHERE stop_id=?", (stop_id,))
    conn.execute("DELETE FROM stops WHERE id=?", (stop_id,))
    conn.commit()
    # Recompute can flow with the stop removed
    compute_can_flow(conn, route_id)
    conn.commit()
    conn.close()

    flash("Stop deleted.", "success")
    return redirect(url_for("view_route", route_id=route_id))


# =========================================================
# COMPLETE / REOPEN STOP
# =========================================================
@app.route("/stop/<int:stop_id>/toggle", methods=["POST"])
@login_required
def toggle_stop_complete(stop_id):
    conn = get_db()
    stop = conn.execute(
        """SELECT s.*, r.assigned_to, r.company_id FROM stops s
           JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()

    if not stop:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and stop["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    # Conflict detection for offline sync replays
    is_replay = (request.headers.get("X-Sync-Replay") == "1" or
                 request.headers.get("X-Requested-With") == "XMLHttpRequest")
    expected_status = request.form.get("expected_status", "").strip()
    if is_replay and expected_status and stop["status"] != expected_status:
        conn.close()
        return jsonify({
            "conflict": True,
            "current_status": stop["status"],
            "stop_id": stop_id,
        }), 409

    new_status = "completed" if stop["status"] == "open" else "open"
    completed_at = now_ts() if new_status == "completed" else None
    new_driver_status = "completed" if new_status == "completed" else "pending"

    conn.execute("""
        UPDATE stops SET status=?, completed_at=?, driver_status=? WHERE id=?
    """, (new_status, completed_at, new_driver_status, stop_id))
    if new_status == "completed":
        update_container_flow(conn, stop_id)
    conn.commit()

    if request.headers.get("X-Requested-With") == "XMLHttpRequest":
        total     = conn.execute("SELECT COUNT(*) n FROM stops WHERE route_id=?", (stop["route_id"],)).fetchone()["n"]
        completed = conn.execute("SELECT COUNT(*) n FROM stops WHERE route_id=? AND status='completed'", (stop["route_id"],)).fetchone()["n"]
        conn.close()
        return jsonify({
            "success": True,
            "stop_id": stop_id,
            "new_status": new_status,
            "completed_at": completed_at or "",
            "progress": {"completed": completed, "total": total},
        })

    conn.close()
    return redirect(url_for("view_route", route_id=stop["route_id"]))


# =========================================================
# DRIVER WORKFLOW ACTION  (Arrived / Box In / Box Out / Go To Dump)
# =========================================================
@app.route("/stop/<int:stop_id>/driver-action", methods=["POST"])
@login_required
def stop_driver_action(stop_id):
    action = request.form.get("action", "").strip()
    valid_actions = {"arrived", "box_in", "box_out", "going_to_dump", "need_box_in", "skip_to_box_in"}
    if action not in valid_actions:
        flash("Invalid action.", "error")
        return redirect(url_for("dashboard"))

    conn = get_db()
    stop = conn.execute(
        """SELECT s.*, r.assigned_to, r.company_id, r.id AS rid
           FROM stops s JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()
    if not stop:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and stop["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    # Conflict detection for offline sync replays
    is_replay = request.headers.get("X-Sync-Replay") == "1"
    expected_driver_status = request.form.get("expected_driver_status", "").strip()
    if is_replay and expected_driver_status and stop["driver_status"] != expected_driver_status:
        conn.close()
        return jsonify({
            "conflict": True,
            "current_status": stop["driver_status"],
            "stop_id": stop_id,
        }), 409

    ts = now_ts()

    if action in ("need_box_in", "skip_to_box_in"):
        # Transition to box-in pending state — no timestamp column, just update status
        conn.execute(
            "UPDATE stops SET driver_status='need_box_in' WHERE id=?",
            (stop_id,)
        )
    else:
        col_map = {
            "arrived":       "arrived_at",
            "box_in":        "box_in_at",
            "box_out":       "box_out_at",
            "going_to_dump": "go_to_dump_at",
        }
        time_col = col_map[action]
        conn.execute(
            f"UPDATE stops SET driver_status=?, {time_col}=? WHERE id=?",
            (action, ts, stop_id)
        )

    conn.commit()
    route_id = stop["rid"]
    conn.close()

    if is_replay:
        return jsonify({"success": True, "stop_id": stop_id, "new_status": action})
    return redirect(url_for("driver_route_detail", route_id=route_id))


# =========================================================
# DUMP TICKET  (enter landfill scale ticket per stop)
# =========================================================
@app.route("/stop/<int:stop_id>/dump-ticket", methods=["GET", "POST"])
@login_required
def dump_ticket(stop_id):
    conn = get_db()
    stop = conn.execute(
        """SELECT s.*, r.assigned_to, r.company_id, r.id AS rid, r.dump_location_id
           FROM stops s JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()
    if not stop:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and stop["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    route_id = stop["rid"]

    if request.method == "POST":
        def _sf(k):
            v = request.form.get(k, "").strip()
            try:
                return float(v) if v else None
            except ValueError:
                return None

        dump_site      = request.form.get("dump_site", "").strip()
        arrival_time   = request.form.get("arrival_time", "").strip()
        departure_time = request.form.get("departure_time", "").strip()
        can_number     = request.form.get("can_number", "").strip()
        scale_in       = _sf("scale_in_weight")
        scale_out      = _sf("scale_out_weight")
        net_tons       = _sf("net_tons")
        ticket_number  = request.form.get("ticket_number", "").strip()
        notes          = request.form.get("notes", "").strip()

        existing = conn.execute(
            "SELECT id FROM dump_tickets WHERE stop_id=?", (stop_id,)
        ).fetchone()
        if existing:
            conn.execute(
                """UPDATE dump_tickets SET dump_site=?, arrival_time=?, departure_time=?,
                   can_number=?, scale_in_weight=?, scale_out_weight=?, net_tons=?,
                   ticket_number=?, notes=? WHERE stop_id=?""",
                (dump_site, arrival_time, departure_time, can_number,
                 scale_in, scale_out, net_tons, ticket_number, notes, stop_id)
            )
        else:
            conn.execute(
                """INSERT INTO dump_tickets
                   (stop_id, route_id, company_id, dump_site, arrival_time, departure_time,
                    can_number, scale_in_weight, scale_out_weight, net_tons, ticket_number,
                    notes, created_at, created_by)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                (stop_id, route_id, cid(), dump_site, arrival_time, departure_time,
                 can_number, scale_in, scale_out, net_tons, ticket_number,
                 notes, now_ts(), session["user_id"])
            )

        # Optional ticket photo
        photo = request.files.get("ticket_photo")
        if photo and photo.filename and allowed_file(photo.filename):
            uid = secrets.token_hex(8)
            fname = f"dt_{stop_id}_{uid}_{secure_filename(photo.filename)}"
            path = os.path.join(app.config["UPLOAD_FOLDER"], fname)
            photo.save(path)
            db_path = os.path.join("static", "uploads", fname)
            conn.execute(
                "UPDATE dump_tickets SET photo_path=? WHERE stop_id=?", (db_path, stop_id)
            )

        # After dump ticket saved: decide next state based on job type
        # - Normal PR (no swap)  → need_box_in (driver must still return empty can to customer)
        # - Swap PR              → auto-complete (box_in was already done before the dump run)
        # - Pull / everything else → auto-complete (no box-in needed)
        _ds = dict(stop).get("driver_status") or "pending"
        _stop_action = (dict(stop).get("action") or "").lower()
        _is_pr_action = (
            "pickup and return" in _stop_action
            or ("swap" in _stop_action and "pull" not in _stop_action)
        )
        _is_swap_pr_dump = _is_pr_action and bool(dict(stop).get("swap_with_prev_pull"))
        if _ds == "going_to_dump":
            if _is_pr_action and not _is_swap_pr_dump:
                # Normal PR: driver still needs to drop off an empty can at the customer
                conn.execute(
                    "UPDATE stops SET driver_status='need_box_in' WHERE id=?",
                    (stop_id,)
                )
            else:
                # Swap PR (box_in already done), Pull, Dump, or other — complete after dump
                conn.execute(
                    "UPDATE stops SET driver_status='completed', status='completed', completed_at=? WHERE id=?",
                    (now_ts(), stop_id)
                )
                update_container_flow(conn, stop_id)

        conn.commit()
        conn.close()
        flash("Dump ticket saved.", "success")
        if session.get("role") == "driver":
            return redirect(url_for("driver_route_detail", route_id=route_id))
        return redirect(url_for("view_route", route_id=route_id))

    # GET: show form
    ticket    = conn.execute("SELECT * FROM dump_tickets WHERE stop_id=?", (stop_id,)).fetchone()
    dump_locs = conn.execute(
        "SELECT * FROM dump_locations WHERE active=1 ORDER BY name"
    ).fetchall()

    # Pre-select route dump location name
    default_site = ""
    if stop["dump_location_id"]:
        _dl = conn.execute(
            "SELECT name FROM dump_locations WHERE id=?", (stop["dump_location_id"],)
        ).fetchone()
        if _dl:
            default_site = _dl["name"]

    conn.close()

    csrf_tok = get_csrf_token()

    def _fv(field):
        if ticket and ticket[field] is not None:
            return e(str(ticket[field]))
        return ""

    _cur_site = _fv("dump_site") or e(default_site)
    site_opts = "".join(
        f'<option value="{e(d["name"])}" {"selected" if e(d["name"]) == _cur_site else ""}>'
        f'{e(d["name"])}</option>'
        for d in dump_locs
    )

    body = f"""
    <div class="hero">
        <h1>&#x1F9FE; Dump Ticket</h1>
        <p>Stop #{e(str(stop["stop_order"]))} &mdash; {e(stop["customer_name"] or "")}
           &nbsp;|&nbsp; {e(stop["address"] or "")} {e(stop["city"] or "")}</p>
        <a class="btn secondary" href="javascript:history.back()" style="margin-top:10px;display:inline-block;">&#8592; Back</a>
    </div>
    <div class="card">
        <form method="POST" enctype="multipart/form-data">
            <input type="hidden" name="_csrf_token" value="{csrf_tok}">
            <div class="grid">
                <div>
                    <label>Dump Site</label>
                    <select name="dump_site">
                        <option value="">&#8212; Select &#8212;</option>
                        {site_opts}
                    </select>
                </div>
                <div>
                    <label>Can / Box Number</label>
                    <input name="can_number" value="{_fv("can_number")}" placeholder="e.g. 1042">
                </div>
                <div>
                    <label>Arrival Time</label>
                    <input name="arrival_time" type="time" value="{_fv("arrival_time")}">
                </div>
                <div>
                    <label>Departure Time</label>
                    <input name="departure_time" type="time" value="{_fv("departure_time")}">
                </div>
                <div>
                    <label>Scale-In Weight (tons)</label>
                    <input name="scale_in_weight" id="f-sin" type="number" step="0.001"
                           value="{_fv("scale_in_weight")}" placeholder="0.000">
                </div>
                <div>
                    <label>Scale-Out Weight (tons)</label>
                    <input name="scale_out_weight" id="f-sout" type="number" step="0.001"
                           value="{_fv("scale_out_weight")}" placeholder="0.000">
                </div>
                <div>
                    <label>Net Tons</label>
                    <input name="net_tons" id="f-net" type="number" step="0.001"
                           value="{_fv("net_tons")}" placeholder="Auto-calculated">
                </div>
                <div>
                    <label>Ticket Number</label>
                    <input name="ticket_number" value="{_fv("ticket_number")}" placeholder="Landfill ticket #">
                </div>
            </div>
            <label>Notes</label>
            <textarea name="notes" placeholder="Issues, observations, gate info...">{_fv("notes")}</textarea>
            <label>Ticket Photo / Scan</label>
            <input type="file" name="ticket_photo" accept=".png,.jpg,.jpeg,.webp,.pdf"
                   style="margin-bottom:16px;">
            <div style="display:flex;gap:10px;flex-wrap:wrap;margin-top:8px;">
                <button class="btn green" type="submit" style="flex:1;min-width:160px;">
                    &#128190; Save Dump Ticket
                </button>
                <a class="btn secondary" href="javascript:history.back()"
                   style="flex:1;min-width:120px;text-align:center;padding:12px 16px;">
                    &#8592; Back
                </a>
            </div>
        </form>
    </div>
    <script>
    (function() {{
        var sin  = document.getElementById('f-sin');
        var sout = document.getElementById('f-sout');
        var net  = document.getElementById('f-net');
        function calcNet() {{
            var i = parseFloat(sin.value), o = parseFloat(sout.value);
            if (!isNaN(i) && !isNaN(o) && i > 0)
                net.value = Math.max(0, i - o).toFixed(3);
        }}
        if (sin)  sin.addEventListener('input', calcNet);
        if (sout) sout.addEventListener('input', calcNet);
    }})();
    </script>
    """
    return render_template_string(shell_page("Dump Ticket", body))


# =========================================================
# DAILY ROUTE LOG  (boss printable route sheet)
# =========================================================
@app.route("/route/<int:route_id>/daily-log")
@boss_required
def route_daily_log(route_id):
    conn = get_db()
    route = conn.execute(
        """SELECT r.*, u.username AS driver_name, u.full_name AS driver_full
           FROM routes r LEFT JOIN users u ON r.assigned_to=u.id
           WHERE r.id=? AND r.company_id=?""",
        (route_id, cid())
    ).fetchone()
    if not route:
        conn.close()
        abort(404)

    stops = conn.execute(
        """SELECT s.*,
                  dt.dump_site, dt.arrival_time AS dump_arrival, dt.departure_time AS dump_departure,
                  dt.can_number, dt.scale_in_weight, dt.scale_out_weight, dt.net_tons,
                  dt.ticket_number AS dump_ticket_number, dt.notes AS dump_notes
           FROM stops s
           LEFT JOIN dump_tickets dt ON dt.stop_id = s.id
           WHERE s.route_id=?
           ORDER BY s.stop_order ASC""",
        (route_id,)
    ).fetchall()
    conn.close()

    def _t(ts):
        if not ts:
            return ""
        return ts[11:16] if len(ts) >= 16 else ts

    def _w(v):
        return f"{v:.3f}" if v is not None else ""

    total_net  = sum((s["net_tons"] or 0) for s in stops)
    done_count = sum(1 for s in stops if s["status"] == "completed")
    total_count = len(stops)

    rows = ""
    for s in stops:
        _sd = dict(s)
        rows += f"""
        <tr class="{'row-done' if s['status'] == 'completed' else ''}">
            <td class="col-num">#{e(str(s['stop_order']))}</td>
            <td>{e(s['customer_name'] or '')}</td>
            <td class="col-addr">{e(s['address'] or '')} {e(s['city'] or '')}</td>
            <td class="col-center">{e(s['action'] or '')}</td>
            <td class="col-center">{e(str(s['container_size']) + ' yd') if s['container_size'] else ''}</td>
            <td class="col-time">{_t(_sd.get('arrived_at'))}</td>
            <td class="col-time">{_t(_sd.get('box_in_at'))}</td>
            <td class="col-time">{_t(_sd.get('box_out_at'))}</td>
            <td class="col-time">{_t(_sd.get('go_to_dump_at'))}</td>
            <td class="col-center">{e(s['dump_site'] or '')}</td>
            <td class="col-time">{_t(s['dump_arrival'])}</td>
            <td class="col-time">{_t(s['dump_departure'])}</td>
            <td class="col-center">{e(s['can_number'] or '')}</td>
            <td class="col-num">{_w(s['scale_in_weight'])}</td>
            <td class="col-num">{_w(s['scale_out_weight'])}</td>
            <td class="col-num" style="font-weight:700;color:#61f7df;">{_w(s['net_tons'])}</td>
            <td class="col-center">{e(s['dump_ticket_number'] or '')}</td>
            <td class="col-center">
                <span class="badge {e(s['status'])}" style="font-size:10px;">{e(s['status'])}</span>
            </td>
        </tr>"""

    body = f"""
    <style>
    .log-tbl {{ width:100%;border-collapse:collapse;font-size:12px;min-width:900px; }}
    .log-tbl th {{
        background:rgba(97,247,223,0.10);color:#61f7df;font-size:10px;font-weight:700;
        padding:8px 5px;border-bottom:1px solid rgba(97,247,223,0.18);
        text-align:center;white-space:nowrap;letter-spacing:.4px;
    }}
    .log-tbl td {{ padding:7px 5px;border-bottom:1px solid rgba(80,100,140,0.15);font-size:12px; }}
    .log-tbl tr.row-done td {{ color:#4ade80;opacity:.85; }}
    .log-tbl tr:hover td {{ background:rgba(97,247,223,0.04); }}
    .col-num   {{ text-align:right;font-family:monospace; }}
    .col-time  {{ text-align:center;font-family:monospace;color:#9dc8f0; }}
    .col-center{{ text-align:center; }}
    .col-addr  {{ font-size:11px; }}
    .log-totals-row td {{ border-top:2px solid rgba(97,247,223,0.35);
                          font-weight:700;color:#fbbf24;font-size:13px; }}
    @media print {{
        .sidebar,.btn,.hero p {{display:none!important;}}
        body {{background:#fff!important;color:#000!important;}}
        .card {{background:#fff!important;border:none!important;}}
        .log-tbl th {{background:#eee!important;color:#000!important;}}
        .log-tbl td {{color:#000!important;}}
        .log-tbl tr.row-done td {{color:#007700!important;opacity:1;}}
        .col-time {{color:#333!important;}}
    }}
    </style>

    <div class="hero">
        <h1>&#x1F4CB; Daily Route Log</h1>
        <p>{e(route['route_name'])} &nbsp;&#124;&nbsp; {e(route['route_date'])}
           &nbsp;&#124;&nbsp; Driver: {e(route['driver_full'] or route['driver_name'] or 'Unassigned')}</p>
        <p>Progress: {done_count}/{total_count} stops &nbsp;&#124;&nbsp;
           Total Net Tons: <strong style="color:#fbbf24;">{total_net:.3f}</strong></p>
        <div style="display:flex;gap:10px;flex-wrap:wrap;margin-top:12px;">
            <a class="btn secondary" href="{url_for('view_route', route_id=route_id)}">&#8592; Route View</a>
            <button class="btn" onclick="window.print()">&#128424; Print</button>
            <a class="btn secondary" href="{url_for('export_route_csv', route_id=route_id)}">&#128229; CSV</a>
        </div>
    </div>

    <div class="card" style="padding:0;overflow-x:auto;">
        <table class="log-tbl">
            <thead>
                <tr>
                    <th>#</th>
                    <th style="text-align:left;">Customer</th>
                    <th style="text-align:left;">Address</th>
                    <th>Action</th>
                    <th>Size</th>
                    <th>Arrived</th>
                    <th>Box&nbsp;In</th>
                    <th>Box&nbsp;Out</th>
                    <th>To&nbsp;Dump</th>
                    <th>Dump Site</th>
                    <th>Dump&nbsp;In</th>
                    <th>Dump&nbsp;Out</th>
                    <th>Can&nbsp;#</th>
                    <th>Scale&nbsp;In</th>
                    <th>Scale&nbsp;Out</th>
                    <th>Net Tons</th>
                    <th>Ticket&nbsp;#</th>
                    <th>Status</th>
                </tr>
            </thead>
            <tbody>
                {rows}
                <tr class="log-totals-row">
                    <td colspan="15" style="text-align:right;padding-right:8px;">TOTAL NET TONS</td>
                    <td class="col-num">{total_net:.3f}</td>
                    <td colspan="2"></td>
                </tr>
            </tbody>
        </table>
    </div>
    """
    return render_template_string(shell_page("Daily Route Log", body))


# =========================================================
# REORDER STOPS
# =========================================================
@app.route("/route/<int:route_id>/reorder", methods=["POST"])
@boss_required
def reorder_stops(route_id):
    conn = get_db()
    if not conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone():
        conn.close()
        return jsonify({"success": False, "error": "not found"}), 404

    data = request.get_json(silent=True) or {}
    ids = [int(x) for x in data.get("stop_ids", []) if str(x).isdigit()]

    for i, sid in enumerate(ids, start=1):
        # scope update to stops that actually belong to this route
        conn.execute(
            "UPDATE stops SET stop_order=? WHERE id=? AND route_id=?",
            (i, sid, route_id)
        )
    conn.commit()
    # Recompute can flow so swap_with_prev_pull reflects the new order
    compute_can_flow(conn, route_id)
    conn.commit()
    conn.close()

    return jsonify({"success": True})


# =========================================================
# ROUTE OPTIMIZATION  (dump-aware)
# =========================================================
_EOD_KEYWORDS = ("end of day", "return to yard", "take to yard", "back to yard", "eod")


@app.route("/route/<int:route_id>/optimize", methods=["POST"])
@boss_required
def optimize_route(route_id):
    conn = get_db()

    stops = conn.execute(
        "SELECT * FROM stops WHERE route_id=? ORDER BY stop_order ASC, id ASC",
        (route_id,)
    ).fetchall()

    if len(stops) < 2:
        conn.close()
        flash("Need at least 2 stops to optimize.", "error")
        return redirect(url_for("view_route", route_id=route_id))

    # ------------------------------------------------------------------
    # 1. Yard / base origin
    # ------------------------------------------------------------------
    company = conn.execute(
        "SELECT yard_address, yard_city, yard_state, yard_zip FROM companies WHERE id=?",
        (cid(),)
    ).fetchone()
    _co = dict(company) if company else {}
    yard_str = " ".join(filter(None, [
        _co.get("yard_address") or "",
        _co.get("yard_city")    or "",
        _co.get("yard_state")   or "",
        _co.get("yard_zip")     or "",
    ])).strip()
    yard_origin = None
    if yard_str:
        yard_origin = _geocode_server(yard_str)
        time.sleep(1.1)

    # ------------------------------------------------------------------
    # 2. Load dump-location geocodes from DB (one query, cached by name)
    # ------------------------------------------------------------------
    dump_rows = conn.execute(
        "SELECT name, address, city, state, zip_code FROM dump_locations WHERE active=1"
    ).fetchall()
    # dict: normalised_name → full address string
    _dump_addr_map = {}
    for dr in dump_rows:
        addr_str = " ".join(filter(None, [
            dr["address"] or "", dr["city"] or "",
            dr["state"]   or "", dr["zip_code"] or "",
        ])).strip()
        if addr_str:
            _dump_addr_map[dr["name"].lower().strip()] = addr_str

    # geocode cache: normalised_name → (lat, lng) or None
    _dump_coords_cache = {}

    def _get_dump_coords(name_text):
        """Return (lat, lng) for a dump location name, geocoding on first use."""
        if not name_text:
            return None
        key = name_text.lower().strip()
        if key in _dump_coords_cache:
            return _dump_coords_cache[key]
        # Try full address from DB first; fall back to raw name search
        addr = _dump_addr_map.get(key) or name_text
        coords = _geocode_server(addr)
        time.sleep(1.1)
        _dump_coords_cache[key] = coords
        return coords

    # ------------------------------------------------------------------
    # 3. Bucket stops: pinned-first | main | no-address | pinned-last
    # ------------------------------------------------------------------
    first_pins = []   # notes: "do this first" etc.
    main_stops = []   # stops to be optimized
    no_address = []   # stop_ids with no geocodable address
    eod_stops  = []   # notes: "end of day" / "return to yard" etc.

    for s in stops:
        notes_lower = (s["notes"] or "").lower()
        if any(kw in notes_lower for kw in _FIRST_KEYWORDS):
            first_pins.append(s["id"])
        elif any(kw in notes_lower for kw in _EOD_KEYWORDS):
            eod_stops.append(s["id"])
        else:
            main_stops.append(s)

    # ------------------------------------------------------------------
    # 4. Geocode main stops; build stops_data for dump-aware algorithm
    # ------------------------------------------------------------------
    stops_data = []   # dicts for _dump_aware_order
    ungeocoded = []   # stop_ids that couldn't be geocoded

    for s in main_stops:
        addr = " ".join(filter(None, [
            s["address"] or "", s["city"] or "",
            s["state"] or "", s["zip_code"] or "",
        ])).strip()

        if not addr:
            ungeocoded.append(s["id"])
            continue

        coords = _geocode_server(addr)
        time.sleep(1.1)
        if not coords:
            ungeocoded.append(s["id"])
            continue

        action_lower = (s["action"] or "").lower().strip()
        is_dump = action_lower in _DUMP_ACTIONS
        dump_coords = None
        if is_dump:
            dl_name = (dict(s).get("dump_location") or "").strip()
            if dl_name:
                dump_coords = _get_dump_coords(dl_name)

        stops_data.append({
            "id":       s["id"],
            "lat":      coords[0],
            "lng":      coords[1],
            "is_dump":  is_dump,
            "dump_lat": dump_coords[0] if dump_coords else None,
            "dump_lng": dump_coords[1] if dump_coords else None,
        })

    if len(stops_data) < 2:
        conn.close()
        flash("Not enough addresses could be geocoded to optimize the route.", "error")
        return redirect(url_for("view_route", route_id=route_id))

    # ------------------------------------------------------------------
    # 5. Run dump-aware ordering with can-flow constraints
    # ------------------------------------------------------------------
    dump_stop_count = sum(1 for s in stops_data if s["is_dump"] and s["dump_lat"] is not None)

    # Build action_map so the optimizer can simulate can state during selection.
    # Only covers geocoded main_stops (the ones in stops_data).
    action_map = {s["id"]: (s["action"] or "") for s in main_stops if s["id"] in {d["id"] for d in stops_data}}

    ordered_ids, can_constrained = _dump_aware_order(
        stops_data, origin=yard_origin, action_map=action_map
    )

    final_order = (
        first_pins
        + ordered_ids
        + ungeocoded
        + no_address
        + eod_stops
    )

    for new_order, stop_id in enumerate(final_order, start=1):
        conn.execute("UPDATE stops SET stop_order=? WHERE id=?", (new_order, stop_id))
    conn.commit()

    # Stamp can_state_before on every stop now that order is final
    compute_can_flow(conn, route_id)
    conn.commit()
    conn.close()

    # ------------------------------------------------------------------
    # 6. Flash message
    # ------------------------------------------------------------------
    used_dump_logic  = dump_stop_count > 0
    used_yard        = yard_origin is not None
    skipped          = len(ungeocoded)
    eod_count        = len(eod_stops)
    first_count      = len(first_pins)

    # Build informative flash message reflecting all active optimization dimensions
    if used_dump_logic or used_yard:
        # Core dimensions always active for a smart route
        core_dims = "stop distance, can-flow, and dump-aware routing"
        detail_parts = []
        if used_yard:
            detail_parts.append(f"yard start ({_co.get('yard_city') or 'base'})")
        if used_dump_logic:
            detail_parts.append(
                f"{dump_stop_count} PR/Pull stop{'s' if dump_stop_count != 1 else ''} "
                f"scored by customer + dump leg"
            )
        if first_count:
            detail_parts.append(f"{first_count} stop{'s' if first_count != 1 else ''} pinned first")
        if eod_count:
            detail_parts.append(f"{eod_count} end-of-day stop{'s' if eod_count != 1 else ''} pinned last")
        if skipped:
            detail_parts.append(f"{skipped} without address appended")
        detail_str = f" ({'; '.join(detail_parts)})" if detail_parts else ""
        flash(
            f"Smart route optimized using {core_dims}{detail_str}.",
            "success"
        )
    else:
        skip_note = f" ({skipped} without address appended)" if skipped else ""
        flash(
            f"Basic route optimization applied by stop distance — {len(stops_data)} stops reordered{skip_note}.",
            "success"
        )

    if can_constrained:
        flash(
            "⚠️ Can-flow constraint: one or more stops could not be placed without "
            "violating truck state (e.g. PR with no empty can loaded). "
            "Those stops were kept in their original dispatcher order.",
            "warning"
        )
    return redirect(url_for("view_route", route_id=route_id))


# =========================================================
# PHOTO UPLOAD
# =========================================================
@app.route("/stop/<int:stop_id>/upload", methods=["POST"])
@login_required
def upload_stop_photo(stop_id):
    conn = get_db()
    stop_row = conn.execute(
        """SELECT r.id AS route_id, r.assigned_to FROM stops s
           JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()
    if not stop_row:
        conn.close()
        abort(404)
    route_id = stop_row["route_id"]

    # Drivers may only upload to their own routes
    if session.get("role") != "boss" and stop_row["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    files = request.files.getlist("photos")
    if not files or all(f.filename == "" for f in files):
        conn.close()
        flash("No file selected.", "error")
        return redirect(url_for("view_route", route_id=route_id))

    saved = 0
    for file in files:
        if file.filename == "" or not allowed_file(file.filename):
            continue
        uid = secrets.token_hex(8)
        filename = f"{stop_id}_{uid}_{secure_filename(file.filename)}"
        path = os.path.join(app.config["UPLOAD_FOLDER"], filename)
        file.save(path)
        # Always store a web-relative path so the URL builder at load_stop_photos works
        # regardless of whether UPLOAD_FOLDER is absolute or relative.
        db_path = os.path.join("static", "uploads", filename)
        conn.execute(
            "INSERT INTO route_photos (stop_id, file_path, uploaded_at, uploaded_by) VALUES (?,?,?,?)",
            (stop_id, db_path, now_ts(), session.get("user_id")),
        )
        saved += 1

    if saved:
        conn.commit()
        flash(f"{saved} photo(s) uploaded.", "success")
    else:
        flash("No valid files uploaded.", "error")
    conn.close()
    return redirect(url_for("view_route", route_id=route_id))


# =========================================================
# CSV EXPORT
# =========================================================
@app.route("/route/<int:route_id>/csv")
@login_required
def export_route_csv(route_id):
    conn = get_db()
    if not conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone():
        conn.close()
        abort(404)
    stops = conn.execute("SELECT * FROM stops WHERE route_id=?", (route_id,)).fetchall()
    conn.close()

    output = io.StringIO()
    writer = csv.writer(output)

    writer.writerow(["Stop", "Customer", "Address", "Action", "Status"])

    for s in stops:
        writer.writerow([
            s["stop_order"],
            s["customer_name"],
            s["address"],
            s["action"],
            s["status"]
        ])

    output.seek(0)

    return send_file(
        io.BytesIO(output.read().encode()),
        mimetype="text/csv",
        as_attachment=True,
        download_name="route.csv"
    )


# =========================================================
# AI DISPATCH SYSTEM
# =========================================================
@app.route("/ai", methods=["GET", "POST"])
@login_required
def ai_dispatch():
    results = []

    if request.method == "POST":
        lines = request.form.get("loads", "").splitlines()
        conn = get_db()

        for line in lines:
            parsed = parse_load_input_line(line)
            if parsed:
                conn.execute("""
                    INSERT INTO load_scores (
                        origin, destination, pickup_time, payout, miles,
                        estimated_profit, score, notes, created_by, company_id, created_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    parsed["origin"],
                    parsed["destination"],
                    parsed["pickup_time"],
                    parsed["payout"],
                    parsed["miles"],
                    parsed["estimated_profit"],
                    parsed["score"],
                    parsed["notes"],
                    session["user_id"],
                    cid(),
                    now_ts()
                ))
                results.append(parsed)

        conn.commit()
        conn.close()

    rows = ""
    for r in results:
        rows += f"<tr><td>{e(r['origin'])}</td><td>{e(r['destination'])}</td><td>{e(str(r['score']))}</td></tr>"

    body = f"""
    <div class="card">
        <h2>AI Load Scoring</h2>
        <form method="POST">
            <textarea name="loads" placeholder="VA > NC / 8am / 1200 / 300"></textarea>
            <button type="submit">Score Loads</button>
        </form>

        <table>
            <tr><th>Origin</th><th>Destination</th><th>Score</th></tr>
            {rows}
        </table>
    </div>
    """

    return render_template_string(shell_page("AI Dispatch", body))


# =========================================================
# COMPANY REGISTRATION (public — creates a new tenant)
# =========================================================
@app.route("/register-company", methods=["GET", "POST"])
def company_register():
    init_db()

    if request.method == "POST":
        company_name = request.form.get("company_name", "").strip()
        username     = request.form.get("username", "").strip()
        password     = request.form.get("password", "").strip()
        full_name    = request.form.get("full_name", "").strip()
        phone        = request.form.get("phone", "").strip()

        if not company_name or not username or not password:
            flash("Company name, username, and password are required.", "error")
            return redirect(url_for("company_register"))

        # make a URL-safe slug from company name
        slug_base = re.sub(r"[^a-z0-9]+", "-", company_name.lower()).strip("-")
        slug = slug_base
        conn = get_db()
        # ensure unique slug
        n = 1
        while conn.execute("SELECT id FROM companies WHERE slug=?", (slug,)).fetchone():
            slug = f"{slug_base}-{n}"
            n += 1

        try:
            trial_ends = (datetime.now() + timedelta(days=14)).strftime("%Y-%m-%d %H:%M:%S")
            conn.execute(
                """INSERT INTO companies (name, slug, subscription_plan, subscription_status,
                   max_drivers, trial_ends_at, created_at) VALUES (?,?,?,?,?,?,?)""",
                (company_name, slug, "trial", "active", 5, trial_ends, now_ts())
            )
            conn.commit()
            company_id = conn.execute("SELECT id FROM companies WHERE slug=?", (slug,)).fetchone()["id"]

            conn.execute(
                """INSERT INTO users (username, password_hash, role, full_name, phone,
                   company_id, created_at) VALUES (?,?,?,?,?,?,?)""",
                (username, generate_password_hash(password), "boss",
                 full_name, phone, company_id, now_ts())
            )
            conn.commit()
            owner_id = conn.execute("SELECT id FROM users WHERE username=? AND company_id=?",
                                    (username, company_id)).fetchone()["id"]
            conn.execute("UPDATE companies SET owner_id=? WHERE id=?", (owner_id, company_id))

            # record initial trial subscription
            conn.execute(
                """INSERT INTO subscriptions (company_id, plan, status, started_at, created_at)
                   VALUES (?,?,?,?,?)""",
                (company_id, "trial", "active", now_ts(), now_ts())
            )
            conn.commit()
            conn.close()
            flash("Account created! Please log in.", "success")
            return redirect(url_for("login"))

        except sqlite3.IntegrityError:
            conn.close()
            flash("That username is already taken.", "error")
            return redirect(url_for("company_register"))

    body = """
    <div style="max-width:560px;margin:60px auto;">
        <div class="hero">
            <h1>Start Free Trial</h1>
            <p>Create your HAULTRA company account — free for 14 days, no credit card required.</p>
        </div>
        <div class="card">
            <form method="POST">
                <label>Company Name</label>
                <input name="company_name" placeholder="ABC Hauling LLC" required>
                <label>Your Username (boss login)</label>
                <input name="username" required>
                <label>Password</label>
                <input type="password" name="password" required>
                <label>Full Name</label>
                <input name="full_name">
                <label>Phone</label>
                <input name="phone">
                <div style="margin-top:14px;">
                    <button type="submit" class="btn green" style="width:100%;font-size:16px;padding:14px;">
                        Create Company Account
                    </button>
                </div>
                <p class="muted small" style="margin-top:12px;text-align:center;">
                    Already have an account? <a href="/login">Log in</a>
                </p>
            </form>
        </div>
    </div>
    """
    return render_template_string(shell_page("Register", body))


# =========================================================
# COMPANY SETTINGS
# =========================================================
@app.route("/company/settings", methods=["GET", "POST"])
@boss_required
def company_settings():
    conn = get_db()
    company = conn.execute("SELECT * FROM companies WHERE id=?", (cid(),)).fetchone()

    if request.method == "POST":
        action = request.form.get("_action", "profile")

        if action == "yard":
            conn.execute(
                """UPDATE companies SET
                       yard_address=?, yard_city=?, yard_state=?, yard_zip=?
                   WHERE id=?""",
                (
                    request.form.get("yard_address", "").strip(),
                    request.form.get("yard_city",    "").strip(),
                    request.form.get("yard_state",   "").strip(),
                    request.form.get("yard_zip",     "").strip(),
                    cid(),
                )
            )
            conn.commit()
            flash("Yard / base location saved.", "success")
        elif action == "work_hours":
            conn.execute(
                """UPDATE companies SET
                       timezone=?, workweek_start_day=?, workweek_reset_day=?,
                       pay_period_type=?, pay_period_end_day=?, payday=?,
                       driver_day_start_rule=?, driver_day_end_rule=?
                   WHERE id=?""",
                (
                    request.form.get("timezone",              "America/New_York").strip(),
                    request.form.get("workweek_start_day",    "monday").strip(),
                    request.form.get("workweek_reset_day",    "friday").strip(),
                    request.form.get("pay_period_type",       "weekly").strip(),
                    request.form.get("pay_period_end_day",    "thursday").strip(),
                    request.form.get("payday",                "friday").strip(),
                    request.form.get("driver_day_start_rule", "first_action").strip(),
                    request.form.get("driver_day_end_rule",   "last_action").strip(),
                    cid(),
                )
            )
            conn.commit()
            flash("Work hours & pay cycle settings saved.", "success")
        else:
            new_name = request.form.get("company_name", "").strip()
            if new_name:
                conn.execute("UPDATE companies SET name=? WHERE id=?", (new_name, cid()))
                conn.commit()
                flash("Company name updated.", "success")

        conn.close()
        return redirect(url_for("company_settings"))

    conn.close()

    plan_labels = {
        "trial": ("Trial", "#fbbf24"),
        "starter": ("Starter", "#3fd2ff"),
        "pro": ("Pro", "#56f0b7"),
        "enterprise": ("Enterprise", "#c084fc"),
    }
    _co = dict(company) if company else {}
    plan      = _co.get("subscription_plan") or "trial"
    plan_name, plan_color = plan_labels.get(plan, ("Unknown", "#9dc8f0"))
    max_d     = _co.get("max_drivers") or 0
    co_name   = _co.get("name") or ""
    co_slug   = _co.get("slug") or ""
    trial_end = _co.get("trial_ends_at") or ""
    yard_addr  = _co.get("yard_address") or ""
    yard_city  = _co.get("yard_city")    or ""
    yard_state = _co.get("yard_state")   or ""
    yard_zip   = _co.get("yard_zip")     or ""
    wh_tz      = _co.get("timezone")              or "America/New_York"
    wh_wstart  = _co.get("workweek_start_day")    or "monday"
    wh_wreset  = _co.get("workweek_reset_day")    or "friday"
    wh_ptype   = _co.get("pay_period_type")       or "weekly"
    wh_pend    = _co.get("pay_period_end_day")    or "thursday"
    wh_payday  = _co.get("payday")                or "friday"
    wh_dstart  = _co.get("driver_day_start_rule") or "first_action"
    wh_dend    = _co.get("driver_day_end_rule")   or "last_action"

    _yard_set = bool(yard_addr or yard_city)
    _yard_status = (
        f'<span style="color:#00e87d;font-size:12px;">&#10003; Set — {e(yard_addr)}, {e(yard_city)}, {e(yard_state)} {e(yard_zip)}</span>'
        if _yard_set else
        '<span style="color:#ff9d00;font-size:12px;">&#9888; Not set — route optimization will use stop-to-stop ordering</span>'
    )

    body = f"""
    <div class="hero">
        <h1>Company Settings</h1>
        <p>Manage your company profile and account details.</p>
    </div>

    <div class="card">
        <h2>Profile</h2>
        <form method="POST">
            <input type="hidden" name="_action" value="profile">
            <label>Company Name</label>
            <input name="company_name" value="{e(co_name)}" required>
            <div style="margin-top:10px;">
                <button type="submit" class="btn">Save</button>
            </div>
        </form>
        <p class="muted small" style="margin-top:10px;">Slug: <code>{e(co_slug)}</code></p>
    </div>

    <div class="card">
        <h2>&#127968; Yard / Base Location</h2>
        <p style="color:#7aaac8;font-size:13px;margin-bottom:12px;">
            Used as the starting point when optimizing routes. Stops with notes containing
            <em>end of day</em>, <em>return to yard</em>, or <em>take to yard</em> are automatically
            pinned to the end of the optimized route.
        </p>
        <p style="margin-bottom:14px;">{_yard_status}</p>
        <form method="POST">
            <input type="hidden" name="_action" value="yard">
            <div class="grid" style="grid-template-columns:1fr 1fr;gap:12px 16px;">
                <div style="grid-column:1/-1;">
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Yard / Base Address</label>
                    <input name="yard_address" value="{e(yard_addr)}" placeholder="e.g. 100 Industrial Blvd">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">City</label>
                    <input name="yard_city" value="{e(yard_city)}" placeholder="e.g. Suffolk">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">State</label>
                    <input name="yard_state" value="{e(yard_state)}" placeholder="VA" style="max-width:100px;">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">ZIP</label>
                    <input name="yard_zip" value="{e(yard_zip)}" placeholder="23434" style="max-width:140px;">
                </div>
            </div>
            <div style="margin-top:14px;">
                <button type="submit" class="btn gold">Save Yard Location</button>
            </div>
        </form>
    </div>

    <div class="card" id="work-hours">
        <h2>&#9201; Work Hours &amp; Pay Cycle</h2>
        <p style="color:#7aaac8;font-size:13px;margin-bottom:16px;">
            Configure your company&rsquo;s pay schedule and how driver day hours are measured.
            These settings apply to all drivers in your company.
        </p>
        <form method="POST">
            <input type="hidden" name="_action" value="work_hours">
            <div class="grid" style="grid-template-columns:1fr 1fr;gap:12px 16px;">

                <div style="grid-column:1/-1;">
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Timezone</label>
                    <select name="timezone">
                        {"".join(f'<option value="{tz}" {"selected" if tz == wh_tz else ""}>{tz}</option>' for tz in [
                            "America/New_York","America/Chicago","America/Denver",
                            "America/Los_Angeles","America/Phoenix","America/Anchorage",
                            "America/Honolulu","UTC"
                        ])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Workweek Starts On</label>
                    <select name="workweek_start_day">
                        {"".join(f'<option value="{d}" {"selected" if d == wh_wstart else ""}>{d.title()}</option>' for d in ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Week Resets On</label>
                    <select name="workweek_reset_day">
                        {"".join(f'<option value="{d}" {"selected" if d == wh_wreset else ""}>{d.title()}</option>' for d in ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Pay Period Type</label>
                    <select name="pay_period_type">
                        {"".join(f'<option value="{pt}" {"selected" if pt == wh_ptype else ""}>{pt.title()}</option>' for pt in ["weekly","biweekly"])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Pay Period Ends On</label>
                    <select name="pay_period_end_day">
                        {"".join(f'<option value="{d}" {"selected" if d == wh_pend else ""}>{d.title()}</option>' for d in ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Payday</label>
                    <select name="payday">
                        {"".join(f'<option value="{d}" {"selected" if d == wh_payday else ""}>{d.title()}</option>' for d in ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Driver Day Start</label>
                    <select name="driver_day_start_rule">
                        <option value="first_action" {"selected" if wh_dstart == "first_action" else ""}>First route action (automatic)</option>
                        <option value="manual"       {"selected" if wh_dstart == "manual"       else ""}>Manual clock-in</option>
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#7aaac8;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Driver Day End</label>
                    <select name="driver_day_end_rule">
                        <option value="last_action" {"selected" if wh_dend == "last_action" else ""}>Last route action (automatic)</option>
                        <option value="manual"      {"selected" if wh_dend == "manual"      else ""}>Manual clock-out</option>
                    </select>
                </div>

            </div>
            <div style="margin-top:16px;">
                <button type="submit" class="btn gold">Save Work Hours Settings</button>
            </div>
        </form>
    </div>

    <div class="card">
        <h2>Subscription</h2>
        <div class="grid">
            <div class="stat" style="border-color:{plan_color}40;">
                <div>Current Plan</div>
                <div class="num" style="color:{plan_color};font-size:22px;">{plan_name}</div>
            </div>
            <div class="stat">
                <div>Max Drivers</div>
                <div class="num">{max_d}</div>
            </div>
            {"" if not trial_end else f'<div class="stat"><div>Trial Ends</div><div class="num" style="font-size:16px;">{e(trial_end)}</div></div>'}
        </div>
        <a class="btn orange" href="{url_for('company_subscription')}" style="margin-top:12px;display:inline-block;">
            Manage Subscription
        </a>
    </div>
    """
    return render_template_string(shell_page("Company Settings", body))


# =========================================================
# SUBSCRIPTION MANAGEMENT (placeholder)
# =========================================================
@app.route("/company/subscription")
@boss_required
def company_subscription():
    conn = get_db()
    company = conn.execute("SELECT * FROM companies WHERE id=?", (cid(),)).fetchone()
    history = conn.execute(
        "SELECT * FROM subscriptions WHERE company_id=? ORDER BY started_at DESC",
        (cid(),)
    ).fetchall()
    conn.close()

    plan   = company["subscription_plan"]   if company else "trial"
    status = company["subscription_status"] if company else "active"
    max_d  = company["max_drivers"]         if company else 5
    trial_ends_at = company["trial_ends_at"] if company else None

    # compute trial countdown
    trial_banner = ""
    if plan == "trial" and trial_ends_at:
        try:
            ends_dt   = datetime.strptime(trial_ends_at, "%Y-%m-%d %H:%M:%S")
            days_left = (ends_dt - datetime.now()).days
            if days_left > 0:
                trial_banner = (
                    f'<div style="background:rgba(251,191,36,0.15);border:1px solid rgba(251,191,36,0.4);'
                    f'border-radius:10px;padding:14px 18px;margin-bottom:18px;">'
                    f'&#9888; Your free trial ends in <strong>{days_left} day{"s" if days_left != 1 else ""}</strong>. '
                    f'Contact <a href="mailto:info@haultraai.com">info@haultraai.com</a> to upgrade.</div>'
                )
            elif status == "active":
                trial_banner = (
                    '<div style="background:rgba(248,113,113,0.15);border:1px solid rgba(248,113,113,0.4);'
                    'border-radius:10px;padding:14px 18px;margin-bottom:18px;">'
                    '&#128274; Your trial has expired. Upgrade to restore full access.</div>'
                )
        except ValueError:
            pass

    plans = [
        ("trial",      "Free",       "$0",    "14 days • up to 5 drivers",                  "#fbbf24"),
        ("starter",    "Starter",    "$49/mo","Up to 10 drivers",                            "#3fd2ff"),
        ("pro",        "Pro",        "$99/mo","Up to 30 drivers • priority support",         "#56f0b7"),
        ("enterprise", "Enterprise", "Custom","Unlimited drivers • dedicated support",       "#c084fc"),
    ]

    # plan display label map
    plan_labels = {
        "trial":      "Free Trial",
        "starter":    "Starter",
        "pro":        "Pro",
        "enterprise": "Enterprise",
    }
    plan_label = plan_labels.get(plan, plan.title())

    # expiration date display
    if plan == "trial" and trial_ends_at:
        exp_display = trial_ends_at[:10]   # YYYY-MM-DD
        try:
            ends_dt2 = datetime.strptime(trial_ends_at, "%Y-%m-%d %H:%M:%S")
            days_left2 = (ends_dt2 - datetime.now()).days
            if days_left2 > 0:
                exp_display = f"{trial_ends_at[:10]} ({days_left2}d left)"
            else:
                exp_display = f"{trial_ends_at[:10]} (expired)"
        except ValueError:
            pass
    else:
        exp_display = "—" if status == "active" else "Subscription ended"

    # upgrade CTA visibility: only show when not already on enterprise
    show_upgrade = plan in ("trial", "starter", "pro")
    upgrade_btn = (
        '<button onclick="haultraCheckout(\'starter\',this)" '
        'class="btn" style="background:linear-gradient(135deg,#3fd2ff,#56f0b7);'
        'color:#0a1628;font-weight:700;border:none;padding:10px 22px;'
        'border-radius:8px;cursor:pointer;">'
        '&#11014;&#65039; Upgrade Plan</button>'
    ) if show_upgrade else ""

    plan_cards = ""
    for key, label, price, desc, color in plans:
        active = key == plan
        border = f"border:2px solid {color};" if active else "border:1px solid rgba(255,255,255,0.08);"
        badge  = (f'<span class="badge" style="background:{color}30;color:{color};'
                  f'font-size:11px;margin-left:8px;">&#10003; Current</span>') if active else ""
        upgrade_card_btn = ""
        if not active and key in ("starter", "pro"):
            upgrade_card_btn = (
                f'<div style="margin-top:12px;">'
                f'<button onclick="haultraCheckout(\'{key}\',this)" '
                f'class="btn" style="background:{color}22;color:{color};border:1px solid {color}55;'
                f'font-size:13px;padding:7px 16px;border-radius:7px;cursor:pointer;width:100%;">'
                f'Upgrade to {label}</button></div>'
            )
        plan_cards += f"""
        <div class="stat" style="padding:18px;{border}border-radius:12px;">
            <div style="font-size:16px;font-weight:800;">{label}{badge}</div>
            <div class="num" style="color:{color};font-size:24px;margin:6px 0;">{price}</div>
            <div class="muted small">{desc}</div>
            {upgrade_card_btn}
        </div>"""

    # current usage
    conn2 = get_db()
    driver_count = conn2.execute(
        "SELECT COUNT(*) n FROM users WHERE role='driver' AND company_id=?", (cid(),)
    ).fetchone()["n"]
    conn2.close()

    pct = int(driver_count / max_d * 100) if max_d else 0
    bar_color = "#f87171" if pct >= 90 else "#3fd2ff"
    seat_bar = f"""
    <div style="margin-top:6px;">
        <div style="font-size:13px;color:#9dc8f0;margin-bottom:4px;">{driver_count} / {max_d} driver seats used</div>
        <div class="mini-prog-track" style="width:100%;height:10px;">
            <div class="mini-prog-fill" style="width:{pct}%;background:{bar_color};"></div>
        </div>
    </div>"""

    hist_rows = ""
    for h in history:
        plan_hl = plan_labels.get(h["plan"], h["plan"].title())
        hist_rows += f"""
        <tr>
            <td>{e(plan_hl)}</td>
            <td><span class="badge">{e(h['status'].title())}</span></td>
            <td>{e(h['started_at'])}</td>
            <td>{e(h['ends_at'] or '—')}</td>
            <td>{e(h['notes'] or '')}</td>
        </tr>"""

    status_color = "#4ade80" if status == "active" else "#f87171"
    plan_color_map = {
        "trial": "#fbbf24", "starter": "#3fd2ff",
        "pro": "#56f0b7", "enterprise": "#c084fc",
    }
    pc = plan_color_map.get(plan, "#9dc8f0")

    body = f"""
    <div class="hero">
        <h1>Billing &amp; Subscription</h1>
        <p>Your plan details, usage, and upgrade options.</p>
    </div>

    {trial_banner}

    <div class="card">
        <div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:12px;margin-bottom:18px;">
            <h2 style="margin:0;">Plan Overview</h2>
            {upgrade_btn}
        </div>
        <div class="grid">
            <div class="stat">
                <div class="muted small">Current Plan</div>
                <div class="num" style="color:{pc};font-size:22px;">{plan_label}</div>
            </div>
            <div class="stat">
                <div class="muted small">Status</div>
                <div class="num" style="color:{status_color};font-size:22px;">{status.title()}</div>
            </div>
            <div class="stat">
                <div class="muted small">{"Trial Expiration" if plan == "trial" else "Renewal / Expiration"}</div>
                <div class="num" style="font-size:16px;font-weight:600;">{exp_display}</div>
            </div>
            <div class="stat">
                <div class="muted small">Driver Seats</div>
                {seat_bar}
            </div>
        </div>
    </div>

    <div class="card">
        <h2>Available Plans</h2>
        <div class="grid">{plan_cards}</div>
        <p class="muted small" style="margin-top:14px;">
            Secure checkout powered by Stripe. Cancel anytime.
        </p>
    </div>

    <div class="card">
        <h2>Subscription History</h2>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Plan</th><th>Status</th><th>Started</th><th>Ends</th><th>Notes</th></tr></thead>
                <tbody>{hist_rows or '<tr><td colspan="5" class="muted">No history yet.</td></tr>'}</tbody>
            </table>
        </div>
    </div>

    <!-- Hidden form used by JS to POST to /create-checkout-session -->
    <form id="checkout-form" method="POST" action="{url_for('create_checkout_session')}" style="display:none;">
        <input type="hidden" name="_csrf_token" value="{get_csrf_token()}">
        <input type="hidden" name="plan" id="checkout-plan" value="">
    </form>

    <script>
    window.haultraCheckout = function(plan, btn) {{
        if (btn) {{ btn.disabled = true; btn.textContent = 'Redirecting to Stripe…'; }}
        document.getElementById('checkout-plan').value = plan;
        document.getElementById('checkout-form').submit();
    }};
    </script>
    """
    return render_template_string(shell_page("Subscription", body))


# =========================================================
# SUPERADMIN PANEL
# =========================================================
@app.route("/superadmin")
@superadmin_required
def superadmin_panel():
    conn = get_db()
    companies = conn.execute("""
        SELECT c.*,
               COALESCE(u.username, '—') AS owner_username,
               (SELECT COUNT(*) FROM users uu WHERE uu.company_id = c.id) AS user_count,
               (SELECT COUNT(*) FROM routes r WHERE r.company_id = c.id) AS route_count
        FROM companies c
        LEFT JOIN users u ON c.owner_id = u.id
        ORDER BY c.created_at DESC
    """).fetchall()
    conn.close()

    now_dt = datetime.now()

    rows = ""
    for c in companies:
        # compute trial days remaining
        trial_cell = "—"
        if c["subscription_plan"] == "trial" and c["trial_ends_at"]:
            try:
                ends = datetime.strptime(c["trial_ends_at"], "%Y-%m-%d %H:%M:%S")
                days_left = (ends - now_dt).days
                if days_left > 0:
                    trial_cell = f'<span style="color:#fbbf24;">{days_left}d left</span>'
                else:
                    trial_cell = '<span style="color:#f87171;">Expired</span>'
            except ValueError:
                trial_cell = e(c["trial_ends_at"])

        status_color = {"active": "completed", "suspended": "in_progress", "cancelled": "open"}
        status_cls   = status_color.get(c["subscription_status"], "")

        rows += f"""
        <tr>
            <td><strong>{e(c['name'])}</strong></td>
            <td><code style="font-size:11px;">{e(c['slug'])}</code></td>
            <td>{e(c['owner_username'])}</td>
            <td><span class="badge">{e(c['subscription_plan'].title())}</span></td>
            <td><span class="badge {status_cls}">{e(c['subscription_status'].title())}</span></td>
            <td>{trial_cell}</td>
            <td>{c['max_drivers']}</td>
            <td>{c['user_count']}</td>
            <td>{c['route_count']}</td>
            <td style="white-space:nowrap;">
                <a class="btn secondary" href="{url_for('superadmin_edit_company', company_id=c['id'])}"
                   style="font-size:12px;padding:4px 10px;">Edit</a>
            </td>
        </tr>"""

    body = f"""
    <div class="hero">
        <h1>&#128295; Superadmin</h1>
        <p>Full visibility across all companies on this HAULTRA instance.</p>
    </div>
    <div class="card">
        <h2>All Companies ({len(companies)})</h2>
        <div class="table-wrap">
            <table>
                <thead><tr>
                    <th>Company</th><th>Slug</th><th>Owner</th><th>Plan</th>
                    <th>Status</th><th>Trial</th><th>Max Drivers</th>
                    <th>Users</th><th>Routes</th><th></th>
                </tr></thead>
                <tbody>{rows or '<tr><td colspan="10" class="muted">No companies.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Superadmin", body))


# =========================================================
# STRIPE CHECKOUT
# =========================================================

def _stripe_apply_plan(company_id, plan, customer_id, sub_id, note):
    """
    Central helper — update companies + write a subscriptions history row.
    Called from multiple webhook handlers so the DB logic lives in one place.
    """
    max_d = STRIPE_PLAN_LIMITS.get(plan, 10)
    conn  = get_db()
    conn.execute(
        """UPDATE companies
           SET subscription_plan=?, subscription_status='active',
               max_drivers=?, stripe_customer_id=?, stripe_subscription_id=?
           WHERE id=?""",
        (plan, max_d, customer_id or "", sub_id or "", int(company_id))
    )
    conn.execute(
        """INSERT INTO subscriptions (company_id, plan, status, started_at, notes, created_at)
           VALUES (?,?,'active',?,?,?)""",
        (int(company_id), plan, now_ts(), note, now_ts())
    )
    conn.commit()
    conn.close()


def _stripe_suspend_by_sub(sub_id):
    """Suspend the company whose stripe_subscription_id matches sub_id."""
    conn = get_db()
    conn.execute(
        "UPDATE companies SET subscription_status='suspended' WHERE stripe_subscription_id=?",
        (sub_id,)
    )
    conn.commit()
    conn.close()


@app.route("/create-checkout-session", methods=["POST"])
@boss_required
def create_checkout_session():
    if not STRIPE_ENABLED or not stripe_configured:
        print("STRIPE NOT CONFIGURED — STRIPE_ENABLED={} stripe_configured={}".format(
            STRIPE_ENABLED, stripe_configured))
        flash("Stripe billing is not configured on this server.", "error")
        return redirect(url_for("billing"))

    plan = request.form.get("plan", "").lower()
    if plan not in STRIPE_PURCHASABLE_PLANS:
        flash("Invalid plan selected.", "error")
        return redirect(url_for("company_subscription"))

    price_id = STRIPE_PRICE_IDS.get(plan)
    if not price_id:
        flash("Price ID not configured for this plan.", "error")
        return redirect(url_for("company_subscription"))

    conn = get_db()
    company  = conn.execute("SELECT * FROM companies WHERE id=?", (cid(),)).fetchone()
    try:
        user_row = conn.execute("SELECT email FROM users WHERE id=?", (session["user_id"],)).fetchone()
        user_email = (user_row["email"] if user_row and user_row["email"] else "") or ""
    except Exception:
        user_email = ""
    conn.close()

    company_dict      = dict(company) if company else {}
    existing_customer = company_dict.get("stripe_customer_id") or None

    success_url = url_for("subscription_success", _external=True) + "?session_id={CHECKOUT_SESSION_ID}"
    cancel_url  = url_for("billing", _external=True)

    try:
        checkout_kwargs = dict(
            mode="subscription",
            line_items=[{"price": price_id, "quantity": 1}],
            success_url=success_url,
            cancel_url=cancel_url,
            # client_reference_id lets the webhook look up the company
            # without relying solely on metadata
            client_reference_id=str(cid()),
            metadata={"company_id": str(cid()), "plan": plan},
            allow_promotion_codes=True,
        )
        if existing_customer:
            # Re-use existing Stripe customer so payment history is preserved
            checkout_kwargs["customer"] = existing_customer
        elif user_email:
            checkout_kwargs["customer_email"] = user_email

        checkout = stripe.checkout.Session.create(**checkout_kwargs)
        return redirect(checkout.url, code=303)

    except stripe.error.StripeError as ex:
        flash(f"Stripe error: {getattr(ex, 'user_message', None) or str(ex)}", "error")
        return redirect(url_for("billing"))


@app.route("/stripe-webhook", methods=["POST"])
def stripe_webhook():
    """
    Receives Stripe events. Register this URL in your Stripe dashboard:
        https://yourdomain.com/stripe-webhook

    Enable these events:
        checkout.session.completed
        customer.subscription.created
        customer.subscription.updated
        customer.subscription.deleted

    Stripe-Signature header is verified against STRIPE_WEBHOOK_SECRET so
    spoofed POST requests are rejected before touching the database.
    """
    if not STRIPE_ENABLED or not stripe_configured or not STRIPE_WEBHOOK_SECRET:
        return "Webhook not configured", 400

    payload    = request.get_data()
    sig_header = request.headers.get("Stripe-Signature", "")

    try:
        event = stripe.Webhook.construct_event(payload, sig_header, STRIPE_WEBHOOK_SECRET)
    except ValueError:
        return "Bad payload", 400
    except stripe.error.SignatureVerificationError:
        return "Invalid signature", 400

    etype = event["type"]
    obj   = event["data"]["object"]

    # ------------------------------------------------------------------
    # checkout.session.completed
    # First payment succeeded; activate the plan immediately.
    # ------------------------------------------------------------------
    if etype == "checkout.session.completed":
        company_id  = obj.get("client_reference_id") or (obj.get("metadata") or {}).get("company_id")
        plan        = (obj.get("metadata") or {}).get("plan", "starter")
        customer_id = obj.get("customer")
        sub_id      = obj.get("subscription")

        if company_id and plan in STRIPE_PURCHASABLE_PLANS:
            _stripe_apply_plan(
                company_id, plan, customer_id, sub_id,
                f"Activated via Stripe checkout. sub={sub_id}"
            )

    # ------------------------------------------------------------------
    # customer.subscription.created
    # Stripe fires this when the subscription object is first created.
    # We already handled activation in checkout.session.completed, but
    # we store the sub ID here in case the checkout event arrives late.
    # ------------------------------------------------------------------
    elif etype == "customer.subscription.created":
        sub_id      = obj.get("id")
        customer_id = obj.get("customer")
        # Resolve plan from the price ID on the first item
        items    = (obj.get("items") or {}).get("data") or []
        price_id = items[0]["price"]["id"] if items else ""
        plan     = next((k for k, v in STRIPE_PRICE_IDS.items() if v == price_id), None)

        if plan and customer_id:
            # Look up company by stripe_customer_id (set during checkout)
            conn    = get_db()
            company = conn.execute(
                "SELECT id FROM companies WHERE stripe_customer_id=?", (customer_id,)
            ).fetchone()
            conn.close()
            if company:
                _stripe_apply_plan(
                    company["id"], plan, customer_id, sub_id,
                    f"Subscription created by Stripe. sub={sub_id}"
                )

    # ------------------------------------------------------------------
    # customer.subscription.updated
    # Handles plan changes (e.g. starter → pro upgrade via Stripe portal).
    # ------------------------------------------------------------------
    elif etype == "customer.subscription.updated":
        sub_id      = obj.get("id")
        customer_id = obj.get("customer")
        status      = obj.get("status", "")      # active, past_due, canceled, etc.
        items       = (obj.get("items") or {}).get("data") or []
        price_id    = items[0]["price"]["id"] if items else ""
        plan        = next((k for k, v in STRIPE_PRICE_IDS.items() if v == price_id), None)

        conn = get_db()
        if status in ("active", "trialing") and plan in STRIPE_PURCHASABLE_PLANS:
            max_d = STRIPE_PLAN_LIMITS.get(plan, 10)
            conn.execute(
                """UPDATE companies
                   SET subscription_plan=?, subscription_status='active', max_drivers=?
                   WHERE stripe_subscription_id=?""",
                (plan, max_d, sub_id)
            )
        elif status in ("past_due", "unpaid"):
            conn.execute(
                "UPDATE companies SET subscription_status='suspended' WHERE stripe_subscription_id=?",
                (sub_id,)
            )
        conn.commit()
        conn.close()

    # ------------------------------------------------------------------
    # customer.subscription.deleted
    # Subscription was cancelled or expired — suspend the company.
    # Trial logic stays in-app and is NOT affected by this event.
    # ------------------------------------------------------------------
    elif etype == "customer.subscription.deleted":
        sub_id = obj.get("id")
        if sub_id:
            _stripe_suspend_by_sub(sub_id)

    return "ok", 200


@app.route("/subscription/success")
@boss_required
def subscription_success():
    flash("Payment successful! Your plan is now active.", "success")
    return redirect(url_for("billing"))


@app.route("/debug-stripe")
@superadmin_required
def debug_stripe():
    """
    Safe Stripe config check — only accessible to superadmins.
    Shows whether each var is set and a masked preview; never returns the full key.
    Remove or gate this route before going live.
    """
    import os
    def _mask(val):
        if not val:
            return "MISSING"
        if len(val) <= 8:
            return "SET (too short to preview)"
        return val[:7] + "..." + val[-4:]

    sk  = os.getenv("STRIPE_SECRET_KEY")    or ""
    ps  = os.getenv("STRIPE_PRICE_STARTER") or ""
    pp  = os.getenv("STRIPE_PRICE_PRO")     or ""
    wh  = os.getenv("STRIPE_WEBHOOK_SECRET") or ""

    return jsonify({
        "stripe_configured": bool(sk and ps and pp),
        "STRIPE_SECRET_KEY":     _mask(sk),
        "STRIPE_PRICE_STARTER":  ps  or "MISSING",
        "STRIPE_PRICE_PRO":      pp  or "MISSING",
        "STRIPE_WEBHOOK_SECRET": "SET" if wh else "MISSING",
        "key_mode": ("live" if sk.startswith("sk_live_") else "test" if sk.startswith("sk_test_") else "unknown") if sk else "n/a",
    })


@app.route("/billing")
@boss_required
def billing():
    """Clean /billing URL — renders the same subscription management page."""
    return company_subscription()


# =========================================================
# SUBSCRIPTION BLOCKED PAGE
# =========================================================
@app.route("/subscription/blocked")
def subscription_blocked():
    conn = get_db()
    company_id = session.get("company_id")
    co = None
    if company_id:
        co = conn.execute(
            "SELECT name, subscription_plan, subscription_status, trial_ends_at FROM companies WHERE id=?",
            (company_id,)
        ).fetchone()
    conn.close()

    plan   = co["subscription_plan"] if co else "trial"
    status = co["subscription_status"] if co else "suspended"
    name   = co["name"] if co else ""

    if status == "suspended" and plan == "trial":
        reason = "Your 14-day free trial has ended."
        action = "Upgrade to a paid plan to restore access."
    elif status == "suspended":
        reason = "Your account has been suspended."
        action  = "Please contact support or upgrade your plan."
    else:
        reason = "Your account has been cancelled."
        action  = "Contact support to reactivate."

    sub_link = ""
    if session.get("role") == "boss":
        sub_link = f'<a class="btn green" href="{url_for("company_subscription")}" style="margin-top:16px;display:inline-block;font-size:16px;padding:14px 28px;">View Plans &amp; Upgrade</a>'

    body = f"""
    <div style="max-width:560px;margin:80px auto;text-align:center;">
        <div class="hero">
            <div style="font-size:52px;margin-bottom:12px;">&#128274;</div>
            <h1>Account Access Restricted</h1>
            <p style="font-size:16px;">{e(reason)}</p>
            <p class="muted">{e(action)}</p>
            {sub_link}
            <p style="margin-top:20px;">
                <form method="POST" action="{url_for('logout')}" style="display:inline;margin:0;padding:0;">
                    <button type="submit" class="muted small" style="background:none;border:none;cursor:pointer;padding:0;font:inherit;color:inherit;">Log out</button>
                </form>
                &nbsp;·&nbsp;
                <a href="mailto:info@haultraai.com" class="muted small">Contact Support</a>
            </p>
        </div>
    </div>
    """
    return render_template_string(shell_page("Access Restricted", body))


# =========================================================
# SUPERADMIN — EDIT COMPANY PLAN
# =========================================================
@app.route("/superadmin/company/<int:company_id>/edit", methods=["GET", "POST"])
@superadmin_required
def superadmin_edit_company(company_id):
    conn = get_db()
    co = conn.execute("SELECT * FROM companies WHERE id=?", (company_id,)).fetchone()
    if not co:
        conn.close()
        abort(404)

    PLAN_LIMITS = {
        "trial":      5,
        "starter":    10,
        "pro":        30,
        "enterprise": 9999,
    }

    if request.method == "POST":
        new_plan    = request.form.get("plan", "").strip()
        new_status  = request.form.get("status", "").strip()
        max_drivers = request.form.get("max_drivers", "").strip()
        notes       = request.form.get("notes", "").strip()
        trial_ends  = request.form.get("trial_ends_at", "").strip()

        if new_plan not in PLAN_LIMITS:
            flash("Invalid plan.", "error")
            conn.close()
            return redirect(url_for("superadmin_edit_company", company_id=company_id))
        if new_status not in ("active", "suspended", "cancelled"):
            flash("Invalid status.", "error")
            conn.close()
            return redirect(url_for("superadmin_edit_company", company_id=company_id))

        # default max_drivers from plan if not overridden
        try:
            max_d = int(max_drivers) if max_drivers else PLAN_LIMITS[new_plan]
        except ValueError:
            max_d = PLAN_LIMITS[new_plan]

        # set trial_ends_at only for trial plan
        t_ends = trial_ends if (new_plan == "trial" and trial_ends) else None

        conn.execute(
            """UPDATE companies SET subscription_plan=?, subscription_status=?,
               max_drivers=?, trial_ends_at=? WHERE id=?""",
            (new_plan, new_status, max_d, t_ends, company_id)
        )
        # record in subscription history
        conn.execute(
            """INSERT INTO subscriptions (company_id, plan, status, started_at, notes, created_at)
               VALUES (?,?,?,?,?,?)""",
            (company_id, new_plan, new_status, now_ts(),
             notes or f"Updated by superadmin", now_ts())
        )
        conn.commit()
        conn.close()
        flash(f"Company updated to {new_plan} / {new_status}.", "success")
        return redirect(url_for("superadmin_panel"))

    conn.close()

    plan_options = ""
    for p in ("trial", "starter", "pro", "enterprise"):
        sel = " selected" if p == co["subscription_plan"] else ""
        plan_options += f'<option value="{p}"{sel}>{p.title()}</option>'

    status_options = ""
    for s in ("active", "suspended", "cancelled"):
        sel = " selected" if s == co["subscription_status"] else ""
        status_options += f'<option value="{s}"{sel}>{s.title()}</option>'

    body = f"""
    <div class="hero">
        <h1>Edit Company: {e(co['name'])}</h1>
        <p>Change subscription plan, status, and seat limits.</p>
    </div>
    <div class="card" style="max-width:560px;">
        <form method="POST">
            <label>Plan</label>
            <select name="plan">{plan_options}</select>

            <label>Status</label>
            <select name="status">{status_options}</select>

            <label>Max Drivers <span class="muted small">(leave blank to use plan default)</span></label>
            <input name="max_drivers" type="number" min="1" value="{e(str(co['max_drivers']))}">

            <label>Trial Ends At <span class="muted small">(only applies to trial plan — YYYY-MM-DD HH:MM:SS)</span></label>
            <input name="trial_ends_at" value="{e(co['trial_ends_at'] or '')}">

            <label>Notes <span class="muted small">(recorded in subscription history)</span></label>
            <input name="notes" placeholder="e.g. Upgraded via Stripe payment">

            <div style="margin-top:14px;" class="row">
                <button type="submit" class="btn green">Save Changes</button>
                <a class="btn secondary" href="{url_for('superadmin_panel')}">Cancel</a>
            </div>
        </form>
    </div>
    """
    return render_template_string(shell_page("Edit Company", body))


# =========================================================
# PRIVACY POLICY
# =========================================================
@app.route("/privacy")
def privacy_policy():
    today = datetime.now().strftime("%B %d, %Y")
    body = f"""
    <div class="hero">
        <h1>Privacy Policy</h1>
        <p class="muted small">Effective date: <strong style="color:#e0f0ff;">{today}</strong>
        &nbsp;&middot;&nbsp; HAULTRA AI SYSTEMS &nbsp;&middot;&nbsp; Virginia, USA</p>
    </div>

    <div class="card" style="max-width:820px;line-height:1.8;">

        <div style="background:rgba(63,210,255,0.07);border:1px solid rgba(63,210,255,0.18);
                    border-radius:10px;padding:14px 18px;margin-bottom:24px;font-size:14px;">
            This policy describes how <strong>HAULTRA AI SYSTEMS</strong>, headquartered in
            <strong>Virginia, USA</strong>, collects, uses, and protects your information when
            you use our dispatch and route management platform. Please read it carefully before
            creating an account.
        </div>

        <h2>1. Who We Are</h2>
        <p>HAULTRA AI SYSTEMS ("HAULTRA", "we", "our", "us") is a software company incorporated
        in the Commonwealth of Virginia, United States. We provide dispatch and route management
        software built for the hauling and roll-off trucking industry. Our registered mailing
        address for privacy matters is:</p>
        <p style="margin-left:18px;color:#9dc8f0;">
            HAULTRA AI SYSTEMS<br>
            Virginia, USA<br>
            <a href="mailto:info@haultraai.com">info@haultraai.com</a>
        </p>

        <h2>2. Age Requirement</h2>
        <p>You must be at least <strong>18 years of age</strong> to create an account or use the
        HAULTRA platform. By registering, you represent and warrant that you are 18 or older. We
        do not knowingly collect personal information from anyone under 18. If we become aware that
        a user is under 18, we will promptly close the account and delete associated data.</p>

        <h2>3. Information We Collect</h2>
        <ul>
            <li><strong>Account data</strong> — company name, owner name, username, and password
            (stored as a bcrypt hash; we never store your plaintext password).</li>
            <li><strong>Operational data</strong> — routes, stops, customer addresses, order notes,
            and driver assignments you enter into the system.</li>
            <li><strong>Photos</strong> — images uploaded by drivers at job sites, stored on our
            servers and associated only with your company account.</li>
            <li><strong>Billing data</strong> — subscription plan selections and plan change history.
            We do not currently store credit card numbers directly; payment processing is handled
            by contracted processors under their own privacy policies.</li>
            <li><strong>Usage data</strong> — standard server logs including IP addresses, browser
            type, and pages visited, used solely for security and diagnostics.</li>
        </ul>

        <h2>4. How We Use Your Information</h2>
        <ul>
            <li>To provision and operate your HAULTRA company account.</li>
            <li>To authenticate users and enforce role-based access controls.</li>
            <li>To process and manage your subscription plan and billing status.</li>
            <li>To send transactional communications (account notices, trial expiry alerts,
            support replies).</li>
            <li>To improve the service — we analyze aggregated, anonymized usage patterns only
            and never sell individual data for advertising.</li>
        </ul>

        <h2>5. Billing and Subscription Data</h2>
        <p>When you select a paid subscription plan (Starter, Pro, or Enterprise), we record your
        plan type, activation date, and plan change history in our systems. This information is
        used to enforce access controls and maintain an audit trail for your account. Billing
        inquiries and disputes should be directed to
        <a href="mailto:info@haultraai.com">info@haultraai.com</a>.</p>
        <ul>
            <li>Trial accounts expire after 14 days. No payment data is collected during the
            free trial.</li>
            <li>Subscription records are retained for 7 years for accounting and legal compliance
            purposes, even after account cancellation.</li>
            <li>Payment card data is processed by our payment processor and is never stored on
            HAULTRA servers.</li>
        </ul>

        <h2>6. Account Responsibility</h2>
        <p>You are responsible for all activity that occurs under your company account, including
        actions taken by drivers and other users you add. Specifically:</p>
        <ul>
            <li>Keep your credentials confidential and do not share your password.</li>
            <li>Notify us immediately at <a href="mailto:info@haultraai.com">info@haultraai.com</a>
            if you suspect unauthorized access to your account.</li>
            <li>You are responsible for ensuring that users you add to your account (drivers,
            dispatchers) are authorized to access your company data.</li>
            <li>You must not add users who are under 18 years of age.</li>
            <li>HAULTRA is not liable for losses caused by unauthorized account access resulting
            from your failure to maintain credential security.</li>
        </ul>

        <h2>7. Data Isolation</h2>
        <p>Every company on HAULTRA operates in a fully isolated data environment. Your routes,
        drivers, orders, and uploaded photos are never visible to other companies on the platform.
        Technical access controls enforce this at the database layer on every request.</p>

        <h2>8. International Data Processing</h2>
        <p>HAULTRA is based in Virginia, USA, and your data is stored and processed on servers
        located in the United States. If you access the platform from outside the United States,
        your information will be transferred to and processed in the US, where data protection
        laws may differ from those in your country.</p>
        <p>For users in the European Economic Area (EEA), United Kingdom, or other jurisdictions
        with data transfer restrictions, we rely on Standard Contractual Clauses (SCCs) or
        equivalent mechanisms as the legal basis for transferring personal data to the US.
        By using the platform, you acknowledge and consent to this transfer. To inquire about
        our data transfer mechanisms, contact
        <a href="mailto:info@haultraai.com">info@haultraai.com</a>.</p>

        <h2>9. Third-Party Services</h2>
        <p>We use Nominatim (OpenStreetMap) for address geocoding. Stop addresses submitted for
        route optimization are sent to this service. No account credentials or driver names are
        included. We do not sell or rent your data to any third party for marketing purposes.</p>

        <h2>10. Data Retention</h2>
        <p>Your operational data (routes, stops, photos) is retained for as long as your account
        is active. Upon cancellation you may request a full export within 30 days, after which
        operational data is deleted from production systems. Backups are purged within 90 days.
        Billing and subscription records are retained for 7 years per section 5 above.</p>

        <h2>11. Security</h2>
        <p>All data is transmitted over HTTPS/TLS. Passwords are hashed with bcrypt. Sessions
        use cryptographically signed cookies with CSRF protection on all state-changing requests.
        We perform regular internal security reviews.</p>

        <h2>12. Your Rights</h2>
        <p>You may request access to, correction of, or deletion of your personal data at any
        time by contacting <a href="mailto:info@haultraai.com">info@haultraai.com</a>. We will
        respond within 30 days. Residents of California (CCPA) and the EEA/UK (GDPR) have
        additional rights including portability and the right to object to processing — contact
        us to exercise these rights.</p>

        <h2>13. Changes to This Policy</h2>
        <p>We will post updates to this page with a revised effective date. For material changes,
        we will notify account owners by email at least 14 days before the change takes effect.
        Continued use of the Service after the effective date constitutes acceptance.</p>

        <h2>14. Contact</h2>
        <p>
            Privacy questions: <a href="mailto:info@haultraai.com">info@haultraai.com</a><br>
            Billing questions: <a href="mailto:info@haultraai.com">info@haultraai.com</a><br>
            Security concerns: <a href="mailto:info@haultraai.com">info@haultraai.com</a>
        </p>

        <div style="margin-top:28px;padding-top:16px;border-top:1px solid rgba(100,160,220,0.15);
                    font-size:12px;color:#6a9bc0;">
            &copy; {datetime.now().year} HAULTRA AI SYSTEMS &mdash; Virginia, USA.
            All rights reserved.
        </div>
    </div>
    """
    return render_template_string(shell_page("Privacy Policy", body))


# =========================================================
# TERMS OF SERVICE
# =========================================================
@app.route("/terms")
def terms_of_service():
    today = datetime.now().strftime("%B %d, %Y")
    year  = datetime.now().year
    body = f"""
    <div class="hero">
        <h1>Terms of Service</h1>
        <p class="muted small">Effective date: <strong style="color:#e0f0ff;">{today}</strong>
        &nbsp;&middot;&nbsp; HAULTRA AI SYSTEMS &nbsp;&middot;&nbsp; Virginia, USA</p>
    </div>

    <div class="card" style="max-width:820px;line-height:1.8;">

        <div style="background:rgba(63,210,255,0.07);border:1px solid rgba(63,210,255,0.18);
                    border-radius:10px;padding:14px 18px;margin-bottom:24px;font-size:14px;">
            Welcome to <strong>HAULTRA Systems</strong> ("HAULTRA", "we", "our", "us"). By
            accessing or using our platform, you agree to these Terms of Service. If you do
            not agree, do not use the platform.
        </div>

        <h2>1. Use of Service</h2>
        <p>HAULTRA provides dispatch, routing, and operational management software for trucking
        and hauling businesses. You agree to use the platform only for lawful business purposes
        and in compliance with all applicable federal, state, and local laws.</p>

        <h2>2. Accounts</h2>
        <ul>
            <li>You are responsible for maintaining the security of your account credentials.</li>
            <li>You must provide accurate and complete information when registering.</li>
            <li>You are responsible for all activity that occurs under your account.</li>
            <li>Notify us immediately at
            <a href="mailto:info@haultraai.com">info@haultraai.com</a> if you suspect
            unauthorized access.</li>
        </ul>

        <h2>3. Company Accounts (Multi-Tenant)</h2>
        <p>Each company account operates independently. You are responsible for managing your
        users (drivers, dispatchers, etc.) and their level of access within your account.</p>
        <p>HAULTRA is not responsible for actions taken by users within your company account.
        You bear full responsibility for ensuring your users comply with these Terms.</p>

        <h2>4. Subscriptions &amp; Billing</h2>
        <ul>
            <li>Certain features require a paid subscription (Starter, Pro, or Enterprise).</li>
            <li>New accounts receive a <strong>14-day free trial</strong> with up to 5 driver
            seats — no credit card required.</li>
            <li>Subscription fees are billed on a recurring monthly basis unless canceled.</li>
            <li>Failure to maintain an active subscription may result in restricted or suspended
            access. Data is retained for 30 days after suspension before permanent deletion.</li>
            <li>All payments are <strong>non-refundable</strong> unless otherwise required by
            applicable law.</li>
            <li>Prices are subject to change with 30 days' advance notice to account owners.</li>
        </ul>

        <h2>5. Data &amp; Content</h2>
        <p>You retain full ownership of your data, including routes, customer information,
        driver records, and uploaded images. By using HAULTRA, you grant us a limited,
        non-exclusive license to store and process your data solely to provide the Service.</p>
        <p>You are responsible for ensuring you have the legal right to upload and use any
        data, addresses, or images submitted to the platform.</p>

        <h2>6. Acceptable Use</h2>
        <p>You agree <strong>not</strong> to:</p>
        <ul>
            <li>Use the platform for any illegal, fraudulent, or unauthorized purpose.</li>
            <li>Attempt to hack, probe, disrupt, or reverse-engineer the system or its
            underlying infrastructure.</li>
            <li>Access or attempt to access another company's data without authorization.</li>
            <li>Upload or transmit harmful, malicious, or offensive content.</li>
            <li>Resell or sublicense access to the Service without written consent from
            HAULTRA.</li>
        </ul>

        <h2>7. Service Availability</h2>
        <p>We aim to provide reliable, uninterrupted service but do not guarantee 100% uptime.
        HAULTRA may be temporarily unavailable due to scheduled maintenance, technical issues,
        or circumstances beyond our control. Scheduled maintenance windows will be announced
        in advance when possible.</p>

        <h2>8. Limitation of Liability</h2>
        <p>THE SERVICE IS PROVIDED "AS IS" WITHOUT WARRANTIES OF ANY KIND, EXPRESS OR IMPLIED.
        TO THE MAXIMUM EXTENT PERMITTED BY LAW, HAULTRA SHALL NOT BE LIABLE FOR:</p>
        <ul>
            <li>Business losses or lost profits</li>
            <li>Data loss or corruption</li>
            <li>Service interruptions or downtime</li>
            <li>Indirect, incidental, special, or consequential damages</li>
        </ul>
        <p>OUR AGGREGATE LIABILITY SHALL NOT EXCEED THE AMOUNTS PAID BY YOU IN THE PRIOR
        THREE (3) MONTHS.</p>

        <h2>9. Termination</h2>
        <p>We may suspend or terminate accounts that violate these Terms, with or without
        prior notice. You may cancel your account at any time by contacting us at
        <a href="mailto:info@haultraai.com">info@haultraai.com</a>. Upon cancellation,
        your data will be retained for 30 days before permanent deletion.</p>

        <h2>10. Changes to Terms</h2>
        <p>We may update these Terms at any time. We will post the revised Terms with an
        updated effective date. Continued use of the platform after the effective date
        constitutes your acceptance of the updated Terms.</p>

        <h2>11. Governing Law</h2>
        <p>These Terms are governed by the laws of the <strong>State of Virginia,
        United States</strong>, without regard to conflict-of-law principles. Any disputes
        shall be resolved in the courts of Virginia.</p>

        <h2>12. Contact</h2>
        <p>Questions about these Terms? Contact us at:<br>
        <a href="mailto:info@haultraai.com">info@haultraai.com</a><br>
        HAULTRA AI SYSTEMS &mdash; Virginia, USA</p>

        <div style="margin-top:28px;padding-top:16px;border-top:1px solid rgba(100,160,220,0.15);
                    font-size:12px;color:#6a9bc0;">
            &copy; {year} HAULTRA AI SYSTEMS &mdash; Virginia, USA. All rights reserved.
        </div>
    </div>
    """
    return render_template_string(shell_page("Terms of Service", body))


# =========================================================
# DUMP LOCATIONS
# =========================================================
@app.route("/dump-locations")
@boss_required
def dump_locations_page():
    conn = get_db()
    locs = conn.execute(
        "SELECT * FROM dump_locations ORDER BY active DESC, name ASC"
    ).fetchall()
    conn.close()

    rows = ""
    for dl in locs:
        addr = ", ".join(p for p in [dl["address"], dl["city"], dl["state"], dl["zip_code"]] if p)
        active_badge = (
            '<span class="badge completed">Active</span>'
            if dl["active"]
            else '<span class="badge" style="opacity:0.5;">Inactive</span>'
        )
        toggle_label = "Deactivate" if dl["active"] else "Activate"
        toggle_style = (
            'background:transparent;color:#fbbf24;border:1px solid rgba(251,191,36,0.4);'
            'border-radius:6px;padding:3px 10px;font-size:11px;cursor:pointer;'
        ) if dl["active"] else (
            'background:transparent;color:#4ade80;border:1px solid rgba(74,222,128,0.4);'
            'border-radius:6px;padding:3px 10px;font-size:11px;cursor:pointer;'
        )
        _dlid   = dl["id"]
        _dlname = e(dl["name"])
        rows += f"""
        <tr>
            <td><strong>{_dlname}</strong></td>
            <td class="muted small">{e(addr)}</td>
            <td class="muted small">{e(dl['notes'] or '')}</td>
            <td>{active_badge}</td>
            <td style="text-align:right;white-space:nowrap;">
                <a href="{url_for('edit_dump_location', loc_id=_dlid)}"
                   style="color:#3fd2ff;font-size:12px;margin-right:10px;">Edit</a>
                <form method="POST" action="{url_for('toggle_dump_location', loc_id=_dlid)}" style="display:inline;">
                    <button type="submit" style="{toggle_style}">{toggle_label}</button>
                </form>
                <form method="POST" action="{url_for('delete_dump_location', loc_id=_dlid)}" style="display:inline;margin-left:6px;"
                      onsubmit="return confirm('Delete {_dlname}?');">
                    <button type="submit"
                       style="background:transparent;color:#f87171;border:1px solid rgba(248,113,113,0.4);
                              border-radius:6px;padding:3px 10px;font-size:11px;cursor:pointer;">Delete</button>
                </form>
            </td>
        </tr>"""

    body = f"""
    <div class="hero">
        <h1>Dump Locations</h1>
        <p>Manage the disposal sites available for route assignment.</p>
    </div>
    <div class="card">
        <div class="row between" style="margin-bottom:16px;">
            <h2 style="margin:0;">All Locations</h2>
            <a class="btn" href="{url_for('add_dump_location')}">+ Add Location</a>
        </div>
        <div class="table-wrap">
            <table>
                <thead>
                    <tr><th>Name</th><th>Address</th><th>Notes</th><th>Status</th><th style="width:200px;"></th></tr>
                </thead>
                <tbody>
                    {rows or '<tr><td colspan="5" class="muted">No dump locations found.</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Dump Locations", body))


@app.route("/dump-locations/add", methods=["GET", "POST"])
@boss_required
def add_dump_location():
    if request.method == "POST":
        name     = request.form.get("name", "").strip()
        address  = request.form.get("address", "").strip()
        city     = request.form.get("city", "").strip()
        state    = request.form.get("state", "").strip()
        zip_code = request.form.get("zip_code", "").strip()
        notes    = request.form.get("notes", "").strip()

        if not name:
            flash("Location name is required.", "error")
            return redirect(url_for("add_dump_location"))

        conn = get_db()
        conn.execute(
            "INSERT INTO dump_locations (name, address, city, state, zip_code, notes, active, created_at) VALUES (?,?,?,?,?,?,1,?)",
            (name, address, city, state, zip_code, notes, now_ts())
        )
        conn.commit()
        conn.close()
        flash(f"Dump location '{name}' added.", "success")
        return redirect(url_for("dump_locations_page"))

    body = """
    <div class="hero"><h1>Add Dump Location</h1></div>
    <div class="card" style="max-width:560px;">
        <form method="POST">
            <label>Name *</label>
            <input name="name" required placeholder="e.g. Bay">
            <label>Address</label>
            <input name="address" placeholder="Street address">
            <div class="grid">
                <div><label>City</label><input name="city"></div>
                <div><label>State</label><input name="state" value="VA" maxlength="2"></div>
                <div><label>ZIP</label><input name="zip_code" maxlength="10"></div>
            </div>
            <label>Notes</label>
            <textarea name="notes" placeholder="Any special instructions..."></textarea>
            <div style="margin-top:12px;display:flex;gap:10px;">
                <button type="submit">Save Location</button>
                <a class="btn secondary" href="/dump-locations">Cancel</a>
            </div>
        </form>
    </div>
    """
    return render_template_string(shell_page("Add Dump Location", body))


@app.route("/dump-locations/<int:loc_id>/edit", methods=["GET", "POST"])
@boss_required
def edit_dump_location(loc_id):
    conn = get_db()
    dl = conn.execute("SELECT * FROM dump_locations WHERE id=?", (loc_id,)).fetchone()
    if not dl:
        conn.close()
        flash("Location not found.", "error")
        return redirect(url_for("dump_locations_page"))

    if request.method == "POST":
        name     = request.form.get("name", "").strip()
        address  = request.form.get("address", "").strip()
        city     = request.form.get("city", "").strip()
        state    = request.form.get("state", "").strip()
        zip_code = request.form.get("zip_code", "").strip()
        notes    = request.form.get("notes", "").strip()

        if not name:
            flash("Location name is required.", "error")
            conn.close()
            return redirect(url_for("edit_dump_location", loc_id=loc_id))

        conn.execute(
            "UPDATE dump_locations SET name=?, address=?, city=?, state=?, zip_code=?, notes=? WHERE id=?",
            (name, address, city, state, zip_code, notes, loc_id)
        )
        conn.commit()
        conn.close()
        flash("Location updated.", "success")
        return redirect(url_for("dump_locations_page"))

    conn.close()
    body = f"""
    <div class="hero"><h1>Edit Dump Location</h1></div>
    <div class="card" style="max-width:560px;">
        <form method="POST">
            <label>Name *</label>
            <input name="name" required value="{e(dl['name'])}">
            <label>Address</label>
            <input name="address" value="{e(dl['address'] or '')}">
            <div class="grid">
                <div><label>City</label><input name="city" value="{e(dl['city'] or '')}"></div>
                <div><label>State</label><input name="state" value="{e(dl['state'] or 'VA')}" maxlength="2"></div>
                <div><label>ZIP</label><input name="zip_code" value="{e(dl['zip_code'] or '')}" maxlength="10"></div>
            </div>
            <label>Notes</label>
            <textarea name="notes">{e(dl['notes'] or '')}</textarea>
            <div style="margin-top:12px;display:flex;gap:10px;">
                <button type="submit">Save Changes</button>
                <a class="btn secondary" href="{url_for('dump_locations_page')}">Cancel</a>
            </div>
        </form>
    </div>
    """
    return render_template_string(shell_page("Edit Dump Location", body))


@app.route("/dump-locations/<int:loc_id>/toggle", methods=["POST"])
@boss_required
def toggle_dump_location(loc_id):
    conn = get_db()
    dl = conn.execute("SELECT active, name FROM dump_locations WHERE id=?", (loc_id,)).fetchone()
    if not dl:
        conn.close()
        flash("Location not found.", "error")
        return redirect(url_for("dump_locations_page"))
    new_active = 0 if dl["active"] else 1
    conn.execute("UPDATE dump_locations SET active=? WHERE id=?", (new_active, loc_id))
    conn.commit()
    conn.close()
    status_word = "activated" if new_active else "deactivated"
    flash(f"'{dl['name']}' {status_word}.", "success")
    return redirect(url_for("dump_locations_page"))


@app.route("/dump-locations/<int:loc_id>/delete", methods=["POST"])
@boss_required
def delete_dump_location(loc_id):
    conn = get_db()
    dl = conn.execute("SELECT name FROM dump_locations WHERE id=?", (loc_id,)).fetchone()
    if not dl:
        conn.close()
        flash("Location not found.", "error")
        return redirect(url_for("dump_locations_page"))
    # Unlink from any routes that reference this location
    conn.execute("UPDATE routes SET dump_location_id=NULL WHERE dump_location_id=?", (loc_id,))
    conn.execute("DELETE FROM dump_locations WHERE id=?", (loc_id,))
    conn.commit()
    conn.close()
    flash(f"'{dl['name']}' deleted.", "success")
    return redirect(url_for("dump_locations_page"))


# =========================================================
# PHASE 5A — CONTAINER FLEET INVENTORY  (/boss/containers)
# =========================================================
@app.route("/boss/containers")
@boss_required
def containers_page():
    conn = get_db()
    containers = conn.execute(
        "SELECT * FROM containers WHERE company_id=? ORDER BY size ASC, label ASC",
        (cid(),)
    ).fetchall()
    # Count how many on-site records exist per container
    on_site_counts = {}
    rows = conn.execute(
        "SELECT container_id, COUNT(*) n FROM customer_containers WHERE company_id=? AND status='on_site' GROUP BY container_id",
        (cid(),)
    ).fetchall()
    for r in rows:
        if r["container_id"]:
            on_site_counts[r["container_id"]] = r["n"]
    conn.close()

    STATUS_COLOR = {
        "yard":     "#56f0b7",
        "deployed": "#fbbf24",
        "lost":     "#f87171",
        "retired":  "#6b7280",
    }

    rows_html = ""
    for c in containers:
        _cd   = dict(c)
        _cid  = _cd["id"]
        _sc   = STATUS_COLOR.get(_cd["status"], "#9dc8f0")
        _badge = (
            f'<span style="font-size:11px;padding:2px 8px;border-radius:5px;'
            f'background:rgba(0,0,0,0.3);color:{_sc};border:1px solid {_sc}33;">'
            f'{e(_cd["status"])}</span>'
        )
        _deployed_note = ""
        if _cd["status"] == "deployed":
            _deployed_note = f'<div class="small muted" style="margin-top:2px;">On site at {on_site_counts.get(_cid, "?")} location(s)</div>'
        rows_html += f"""
        <tr>
            <td><strong>{e(_cd["size"])}</strong></td>
            <td class="muted small">{e(_cd["label"] or "")}</td>
            <td>{_badge}{_deployed_note}</td>
            <td class="muted small">{e(_cd["notes"] or "")}</td>
            <td style="text-align:right;white-space:nowrap;">
                <a href="{url_for('edit_container', c_id=_cid)}"
                   style="color:#3fd2ff;font-size:12px;margin-right:10px;">Edit</a>
                <form method="POST" action="{url_for('delete_container', c_id=_cid)}"
                      style="display:inline;"
                      onsubmit="return confirm('Delete this container?');">
                    <input type="hidden" name="_csrf_token" value="{get_csrf_token()}">
                    <button type="submit"
                       style="background:transparent;color:#f87171;border:1px solid rgba(248,113,113,0.4);
                              border-radius:6px;padding:3px 10px;font-size:11px;cursor:pointer;">Delete</button>
                </form>
            </td>
        </tr>"""

    body = f"""
    <div class="hero">
        <h1>Container Fleet</h1>
        <p>Track your roll-off containers by size and status.</p>
    </div>
    <div class="card">
        <div class="row between" style="margin-bottom:16px;">
            <h2 style="margin:0;">All Containers</h2>
            <a class="btn" href="{url_for('add_container')}">+ Add Container</a>
        </div>
        <div class="table-wrap">
            <table>
                <thead>
                    <tr><th>Size</th><th>Label / Serial</th><th>Status</th><th>Notes</th><th style="width:160px;"></th></tr>
                </thead>
                <tbody>
                    {rows_html or '<tr><td colspan="5" class="muted">No containers on file.</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Container Fleet", body))


@app.route("/boss/containers/add", methods=["GET", "POST"])
@boss_required
def add_container():
    csrf_tok = get_csrf_token()
    if request.method == "POST":
        size   = request.form.get("size", "").strip()
        label  = request.form.get("label", "").strip()
        status = request.form.get("status", "yard").strip()
        notes  = request.form.get("notes", "").strip()
        if not size:
            flash("Container size is required.", "error")
            return redirect(url_for("add_container"))
        conn = get_db()
        conn.execute(
            "INSERT INTO containers (company_id, size, label, status, notes, created_at) VALUES (?,?,?,?,?,?)",
            (cid(), size, label or None, status, notes or None, now_ts())
        )
        conn.commit()
        conn.close()
        flash(f"{size} container added.", "success")
        return redirect(url_for("containers_page"))

    size_opts = "".join(
        f'<option value="{s}">{s}</option>'
        for s in ["10yd","15yd","20yd","30yd","40yd","Other"]
    )
    status_opts = "".join(
        f'<option value="{s}">{s.title()}</option>'
        for s in ["yard","deployed","lost","retired"]
    )
    body = f"""
    <div class="hero"><h1>Add Container</h1></div>
    <div class="card" style="max-width:480px;">
        <form method="POST">
            <input type="hidden" name="_csrf_token" value="{csrf_tok}">
            <label>Size *</label>
            <select name="size">{size_opts}</select>
            <label>Label / Serial # (optional)</label>
            <input name="label" placeholder="e.g. C-042">
            <label>Status</label>
            <select name="status">{status_opts}</select>
            <label>Notes</label>
            <textarea name="notes" placeholder="Any notes..."></textarea>
            <div style="margin-top:12px;display:flex;gap:10px;">
                <button type="submit">Save</button>
                <a class="btn secondary" href="{url_for('containers_page')}">Cancel</a>
            </div>
        </form>
    </div>"""
    return render_template_string(shell_page("Add Container", body))


@app.route("/boss/containers/<int:c_id>/edit", methods=["GET", "POST"])
@boss_required
def edit_container(c_id):
    conn = get_db()
    c = conn.execute("SELECT * FROM containers WHERE id=? AND company_id=?", (c_id, cid())).fetchone()
    if not c:
        conn.close()
        abort(404)
    csrf_tok = get_csrf_token()
    if request.method == "POST":
        size   = request.form.get("size", "").strip()
        label  = request.form.get("label", "").strip()
        status = request.form.get("status", "yard").strip()
        notes  = request.form.get("notes", "").strip()
        if not size:
            flash("Container size is required.", "error")
            conn.close()
            return redirect(url_for("edit_container", c_id=c_id))
        conn.execute(
            "UPDATE containers SET size=?, label=?, status=?, notes=? WHERE id=?",
            (size, label or None, status, notes or None, c_id)
        )
        conn.commit()
        conn.close()
        flash("Container updated.", "success")
        return redirect(url_for("containers_page"))

    _c = dict(c)
    conn.close()

    def _sel(name, opts, cur_val):
        return "".join(
            f'<option value="{o}" {"selected" if o == cur_val else ""}>{o}</option>'
            for o in opts
        )
    size_opts   = _sel("size",   ["10yd","15yd","20yd","30yd","40yd","Other"], _c["size"])
    status_opts = _sel("status", ["yard","deployed","lost","retired"], _c["status"])

    body = f"""
    <div class="hero"><h1>Edit Container</h1></div>
    <div class="card" style="max-width:480px;">
        <form method="POST">
            <input type="hidden" name="_csrf_token" value="{csrf_tok}">
            <label>Size *</label>
            <select name="size">{size_opts}</select>
            <label>Label / Serial #</label>
            <input name="label" value="{e(_c['label'] or '')}">
            <label>Status</label>
            <select name="status">{status_opts}</select>
            <label>Notes</label>
            <textarea name="notes">{e(_c['notes'] or '')}</textarea>
            <div style="margin-top:12px;display:flex;gap:10px;">
                <button type="submit">Save Changes</button>
                <a class="btn secondary" href="{url_for('containers_page')}">Cancel</a>
            </div>
        </form>
    </div>"""
    return render_template_string(shell_page("Edit Container", body))


@app.route("/boss/containers/<int:c_id>/delete", methods=["POST"])
@boss_required
def delete_container(c_id):
    conn = get_db()
    c = conn.execute("SELECT size FROM containers WHERE id=? AND company_id=?", (c_id, cid())).fetchone()
    if not c:
        conn.close()
        abort(404)
    conn.execute("DELETE FROM containers WHERE id=?", (c_id,))
    conn.commit()
    conn.close()
    flash(f"{c['size']} container deleted.", "success")
    return redirect(url_for("containers_page"))


# =========================================================
# PHASE 5B — DRIVER HOURS REPORT  (/boss/driver-hours)
# =========================================================
@app.route("/boss/driver-hours")
@boss_required
def driver_hours_page():
    conn = get_db()
    company = conn.execute("SELECT * FROM companies WHERE id=?", (cid(),)).fetchone()
    co_settings = {k: company[k] for k in company.keys()} if company else {}

    drivers = conn.execute(
        "SELECT id, username FROM users WHERE company_id=? AND role='driver' ORDER BY username",
        (cid(),)
    ).fetchall()
    drivers = [dict(d) for d in drivers]

    if not drivers:
        conn.close()
        body = """
        <div class="hero"><h1>Driver Hours</h1></div>
        <div class="card">
            <p class="muted">No drivers found. Add drivers under
            <a href="/boss/users">Users</a> to see hours here.</p>
        </div>
        """
        return render_template_string(shell_page("Driver Hours", body))

    _allowed_driver_ids = {d["id"] for d in drivers}
    selected_driver_id = request.args.get("driver_id", type=int)
    if not selected_driver_id or selected_driver_id not in _allowed_driver_ids:
        selected_driver_id = drivers[0]["id"]

    selected_driver_name = next(
        (d["username"] for d in drivers if d["id"] == selected_driver_id), ""
    )

    # get_pay_period_bounds uses company timezone to determine 'today'
    period_start, period_end = get_pay_period_bounds(co_settings)

    # Build ordered list of dates in the pay period
    start_d = date.fromisoformat(period_start)
    end_d   = date.fromisoformat(period_end)
    date_range = []
    cur_d = start_d
    while cur_d <= end_d:
        date_range.append(cur_d.isoformat())
        cur_d += timedelta(days=1)

    # Main report: per-day hours using configured rule
    day_rows = []
    total_hours = 0.0
    for ds in date_range:
        st, et, hrs = get_driver_day_hours(conn, selected_driver_id, ds, co_settings)
        day_rows.append((ds, st, et, hrs))
        if hrs is not None:
            total_hours += hrs

    # Determine whether any manual mode is active for this company
    _start_rule      = (co_settings.get("driver_day_start_rule") or "first_action").lower()
    _end_rule        = (co_settings.get("driver_day_end_rule")   or "last_action").lower()
    any_manual_mode  = (_start_rule == "manual" or _end_rule == "manual")

    # ── Collect manual entries first; build a date-presence set for override lookup
    activity_rows = []
    manual_dates  = set()
    try:
        for mr in conn.execute(
            """SELECT id, date, clock_in_at, clock_out_at
               FROM driver_clock_entries
               WHERE driver_id=? AND date BETWEEN ? AND ?
               ORDER BY date DESC""",
            (selected_driver_id, period_start, period_end)
        ).fetchall():
            d = mr["date"] or ""
            if d:
                manual_dates.add(d)
            activity_rows.append({
                "day":      d,
                "start":    mr["clock_in_at"]  or "",
                "end":      mr["clock_out_at"] or "",
                "source":   "manual",
                "entry_id": mr["id"],
            })
    except Exception:
        pass

    # ── Auto entries: omitted entirely when manual mode is on;
    #    otherwise only included for dates that have no manual entry
    if not any_manual_mode:
        try:
            for ar in conn.execute(
                """SELECT date(COALESCE(s.arrived_at, s.completed_at)) AS dy,
                          MIN(COALESCE(s.arrived_at, s.completed_at))  AS t_start,
                          MAX(s.completed_at)                          AS t_end
                   FROM stops s
                   JOIN routes r ON s.route_id = r.id
                   WHERE r.assigned_to = ?
                     AND date(COALESCE(s.arrived_at, s.completed_at)) BETWEEN ? AND ?
                     AND s.status = 'completed'
                   GROUP BY dy ORDER BY dy DESC""",
                (selected_driver_id, period_start, period_end)
            ).fetchall():
                if ar["dy"] and ar["t_start"] and ar["dy"] not in manual_dates:
                    activity_rows.append({
                        "day":    ar["dy"],
                        "start":  ar["t_start"],
                        "end":    ar["t_end"] or "",
                        "source": "auto",
                    })
        except Exception:
            pass

    activity_rows.sort(key=lambda r: r["day"], reverse=True)

    conn.close()

    # ── formatting helpers ───────────────────────────────────────────────────
    def _fmt_ts(ts):
        formatted = _fmt_12h(ts)
        if formatted:
            return e(formatted)
        return '<span class="muted">&#8212;</span>'

    def _fmt_h(h):
        if h is None:
            return '<span class="muted">&#8212;</span>'
        return "%.2f h" % h

    def _day_lbl(ds):
        try:
            return date.fromisoformat(ds).strftime("%a %b %d")
        except Exception:
            return ds or "—"

    # ── driver selector ──────────────────────────────────────────────────────
    driver_opts = "".join(
        '<option value="%s"%s>%s</option>' % (
            d["id"],
            ' selected' if d["id"] == selected_driver_id else '',
            e(d["username"] or "")
        )
        for d in drivers
    )

    # ── main report rows ─────────────────────────────────────────────────────
    rows_html = ""
    for ds, st, et, hrs in day_rows:
        rows_html += (
            "<tr>"
            "<td>%s</td><td>%s</td><td>%s</td>"
            '<td style="text-align:right;font-weight:600;">%s</td>'
            "</tr>" % (_day_lbl(ds), _fmt_ts(st), _fmt_ts(et), _fmt_h(hrs))
        )

    # ── clock activity rows (combined auto + manual) ─────────────────────────
    _auto_badge   = ('<span style="display:inline-block;padding:1px 8px;border-radius:4px;'
                     'background:rgba(0,180,255,0.10);color:#3fd2ff;font-size:11px;">Auto</span>')
    _manual_badge = ('<span style="display:inline-block;padding:1px 8px;border-radius:4px;'
                     'background:rgba(255,157,0,0.12);color:#fbbf24;font-size:11px;">Manual</span>')
    _csrf_tok = get_csrf_token()
    _del_btn_style = ('padding:4px 12px;font-size:12px;font-weight:600;border-radius:6px;'
                      'border:1px solid rgba(255,59,92,0.30);cursor:pointer;'
                      'background:rgba(255,59,92,0.10);color:#ff3b5c;')
    activity_html = ""
    for ar in activity_rows:
        badge = _manual_badge if ar["source"] == "manual" else _auto_badge
        if ar["source"] == "manual" and ar.get("entry_id"):
            _eid = str(ar["entry_id"])
            _did = str(selected_driver_id)
            delete_cell = (
                '<form method="POST" action="/boss/delete-clock-entry" style="margin:0;">'
                '<input type="hidden" name="_csrf_token" value="' + _csrf_tok + '">'
                '<input type="hidden" name="entry_id" value="' + _eid + '">'
                '<input type="hidden" name="driver_id" value="' + _did + '">'
                '<button type="submit" style="' + _del_btn_style + '" '
                'onclick="return confirm(\'Delete this clock entry? This cannot be undone.\');">'
                '&#215; Delete</button>'
                '</form>'
            )
        else:
            delete_cell = ""
        activity_html += (
            "<tr><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>" % (
                _day_lbl(ar["day"]), _fmt_ts(ar["start"]), _fmt_ts(ar["end"]),
                badge, delete_cell
            )
        )

    # ── meta strings ────────────────────────────────────────────────────────
    ptype       = (co_settings.get("pay_period_type") or "weekly").title()
    payday_raw  = co_settings.get("payday") or ""
    payday_note = (" &bull; Payday: %s" % e(payday_raw.title())) if payday_raw else ""
    settings_url = url_for("company_settings")
    start_lbl = ("Manual clock"    if (co_settings.get("driver_day_start_rule") or "") == "manual"
                 else "First completed stop")
    end_lbl   = ("Manual clock"    if (co_settings.get("driver_day_end_rule")   or "") == "manual"
                 else "Last completed stop")

    no_data_row     = ('<tr><td colspan="4" class="muted" style="text-align:center;padding:16px;">'
                       'No completed stops in this period.</td></tr>')
    no_activity_row = ('<tr><td colspan="5" class="muted" style="text-align:center;padding:16px;">'
                       'No clock activity in this period.</td></tr>')

    body = """
    <div class="hero">
        <h1>Driver Hours</h1>
        <p>%s pay period: %s &ndash; %s%s</p>
    </div>

    <div class="card" style="margin-bottom:16px;">
        <form method="GET" style="display:flex;gap:12px;align-items:flex-end;flex-wrap:wrap;">
            <div>
                <label style="font-size:12px;display:block;margin-bottom:4px;">Driver</label>
                <select name="driver_id" onchange="this.form.submit()">%s</select>
            </div>
        </form>
    </div>

    <div class="card" style="margin-bottom:16px;">
        <div class="table-wrap">
            <table>
                <thead>
                    <tr>
                        <th>Date</th>
                        <th>Day Start</th>
                        <th>Day End</th>
                        <th style="text-align:right;">Hours</th>
                    </tr>
                </thead>
                <tbody>%s</tbody>
                <tfoot>
                    <tr style="border-top:1px solid rgba(255,255,255,0.10);">
                        <td colspan="3" style="font-weight:700;">Pay Period Total</td>
                        <td style="text-align:right;font-weight:900;color:#56f0b7;">%.2f h</td>
                    </tr>
                </tfoot>
            </table>
        </div>
        <div class="small muted" style="margin-top:10px;">
            Start: %s &bull; End: %s &bull;
            <a href="%s#work-hours" style="color:#3fd2ff;">Configure in Company Settings</a>
        </div>
    </div>

    <div class="card">
        <div style="font-size:13px;font-weight:700;color:#3fd2ff;margin-bottom:14px;">
            Clock Activity &mdash; %s
        </div>
        <div class="table-wrap">
            <table>
                <thead>
                    <tr><th>Date</th><th>Start</th><th>End</th><th>Source</th><th></th></tr>
                </thead>
                <tbody>%s</tbody>
            </table>
        </div>
    </div>
    """ % (
        e(ptype), e(period_start), e(period_end), payday_note,
        driver_opts,
        rows_html if rows_html else no_data_row,
        total_hours,
        e(start_lbl), e(end_lbl), settings_url,
        e(selected_driver_name),
        activity_html if activity_html else no_activity_row,
    )
    return render_template_string(shell_page("Driver Hours", body))


# =========================================================
# PHASE 5B — DELETE CLOCK ENTRY  (/boss/delete-clock-entry)
# =========================================================
@app.route("/boss/delete-clock-entry", methods=["POST"])
@boss_required
def delete_clock_entry():
    entry_id  = request.form.get("entry_id",  "").strip()
    driver_id = request.form.get("driver_id", "").strip()

    if not entry_id or not entry_id.isdigit():
        flash("Invalid entry.", "error")
        return redirect(url_for("driver_hours_page"))

    conn = get_db()
    # Verify the entry belongs to this company before deleting
    row = conn.execute(
        "SELECT id FROM driver_clock_entries WHERE id=? AND company_id=?",
        (int(entry_id), cid())
    ).fetchone()

    if not row:
        conn.close()
        flash("Entry not found.", "error")
        return redirect(url_for("driver_hours_page"))

    conn.execute("DELETE FROM driver_clock_entries WHERE id=?", (int(entry_id),))
    conn.commit()
    conn.close()
    flash("Clock entry deleted.", "success")

    redir_url = url_for("driver_hours_page")
    if driver_id and driver_id.isdigit():
        redir_url += "?driver_id=" + driver_id
    return redirect(redir_url)


# =========================================================
# PHASE 5B — MANUAL CLOCK-IN / CLOCK-OUT  (/driver/clock)
# =========================================================
@app.route("/driver/clock", methods=["GET", "POST"])
@login_required
def driver_clock():
    conn = get_db()
    company = conn.execute("SELECT * FROM companies WHERE id=?", (cid(),)).fetchone()
    co_settings = {k: company[k] for k in company.keys()} if company else {}

    start_rule = (co_settings.get("driver_day_start_rule") or "first_action").lower()
    end_rule   = (co_settings.get("driver_day_end_rule")   or "last_action").lower()

    if start_rule != "manual" and end_rule != "manual":
        conn.close()
        flash("Manual clock-in is not enabled for your company.", "error")
        return redirect(url_for("driver_dashboard"))

    # Use company-local date so the entry lands in the correct pay period
    tz_name = (co_settings.get("timezone") or "America/New_York").strip()
    try:
        from zoneinfo import ZoneInfo
        today     = datetime.now(ZoneInfo(tz_name)).strftime("%Y-%m-%d")
        day_label = datetime.now(ZoneInfo(tz_name)).strftime("%A, %B %d, %Y")
    except Exception:
        today     = date.today().isoformat()
        day_label = date.today().strftime("%A, %B %d, %Y")

    driver_id = session["user_id"]
    entry = conn.execute(
        "SELECT * FROM driver_clock_entries WHERE driver_id=? AND date=?",
        (driver_id, today)
    ).fetchone()

    csrf_tok = get_csrf_token()

    # ── POST: all clock actions ──────────────────────────────────────────────
    if request.method == "POST":
        action = request.form.get("clock_action", "").strip()
        ts  = now_ts()
        _e  = {k: entry[k] for k in entry.keys()} if entry else {}

        def _note(base, msg):
            """Append a timestamped audit line to the notes field."""
            return (((base or "") + "\n[%s] %s" % (ts, msg)).strip())

        def _upsert_ci(new_ci, notes):
            if entry:
                conn.execute(
                    "UPDATE driver_clock_entries SET clock_in_at=?, notes=? "
                    "WHERE driver_id=? AND date=?",
                    (new_ci, notes, driver_id, today)
                )
            else:
                conn.execute(
                    "INSERT INTO driver_clock_entries "
                    "(company_id, driver_id, date, clock_in_at, notes, created_at) "
                    "VALUES (?,?,?,?,?,?)",
                    (cid(), driver_id, today, new_ci, notes, ts)
                )

        def _upsert_co(new_co, notes):
            if entry:
                conn.execute(
                    "UPDATE driver_clock_entries SET clock_out_at=?, notes=? "
                    "WHERE driver_id=? AND date=?",
                    (new_co, notes, driver_id, today)
                )
            else:
                conn.execute(
                    "INSERT INTO driver_clock_entries "
                    "(company_id, driver_id, date, clock_out_at, notes, created_at) "
                    "VALUES (?,?,?,?,?,?)",
                    (cid(), driver_id, today, new_co, notes, ts)
                )

        # ── clock_in ────────────────────────────────────────────────────────
        if action == "clock_in" and start_rule == "manual":
            _upsert_ci(ts, _note(_e.get("notes"), "clock_in"))
            conn.commit(); conn.close()
            flash("Clocked in.", "success")
            return redirect(url_for("driver_clock"))

        # ── clock_out ───────────────────────────────────────────────────────
        elif action == "clock_out" and end_rule == "manual":
            _upsert_co(ts, _note(_e.get("notes"), "clock_out"))
            conn.commit(); conn.close()
            flash("Clocked out.", "success")
            return redirect(url_for("driver_clock"))

        # ── edit_clock_in ───────────────────────────────────────────────────
        elif action == "edit_clock_in" and start_rule == "manual":
            raw = request.form.get("new_time", "").strip()
            if not raw or ":" not in raw:
                conn.close(); flash("Invalid time.", "error")
                return redirect(url_for("driver_clock"))
            new_ts = "%s %s:00" % (today, raw)
            old    = _e.get("clock_in_at") or "none"
            _upsert_ci(new_ts, _note(_e.get("notes"),
                       "edit_clock_in: %s -> %s" % (old, new_ts)))
            conn.commit(); conn.close()
            flash("Clock-in time updated.", "success")
            return redirect(url_for("driver_clock"))

        # ── edit_clock_out ──────────────────────────────────────────────────
        elif action == "edit_clock_out" and end_rule == "manual":
            raw = request.form.get("new_time", "").strip()
            if not raw or ":" not in raw:
                conn.close(); flash("Invalid time.", "error")
                return redirect(url_for("driver_clock"))
            new_ts = "%s %s:00" % (today, raw)
            old    = _e.get("clock_out_at") or "none"
            _upsert_co(new_ts, _note(_e.get("notes"),
                       "edit_clock_out: %s -> %s" % (old, new_ts)))
            conn.commit(); conn.close()
            flash("Clock-out time updated.", "success")
            return redirect(url_for("driver_clock"))

        # ── undo_clock_in ───────────────────────────────────────────────────
        elif action == "undo_clock_in" and start_rule == "manual":
            if entry and not _e.get("clock_out_at"):
                old       = _e.get("clock_in_at") or "none"
                new_notes = _note(_e.get("notes"), "undo_clock_in: cleared %s" % old)
                conn.execute(
                    "UPDATE driver_clock_entries SET clock_in_at=NULL, notes=? "
                    "WHERE driver_id=? AND date=?",
                    (new_notes, driver_id, today)
                )
                conn.commit()
                flash("Clock-in removed.", "success")
            else:
                flash("Cannot undo: clock-out already recorded.", "error")
            conn.close()
            return redirect(url_for("driver_clock"))

        # ── reopen_day ──────────────────────────────────────────────────────
        elif action == "reopen_day" and end_rule == "manual":
            if entry and _e.get("clock_out_at"):
                old       = _e.get("clock_out_at") or "none"
                new_notes = _note(_e.get("notes"),
                                  "reopen_day: cleared clock_out %s" % old)
                conn.execute(
                    "UPDATE driver_clock_entries SET clock_out_at=NULL, notes=? "
                    "WHERE driver_id=? AND date=?",
                    (new_notes, driver_id, today)
                )
                conn.commit()
                flash("Day reopened. Clock-out cleared.", "success")
            conn.close()
            return redirect(url_for("driver_clock"))

        conn.close()
        return redirect(url_for("driver_clock"))

    # ── GET: render page ─────────────────────────────────────────────────────
    conn.close()

    _entry = {k: entry[k] for k in entry.keys()} if entry else {}
    _ci    = _entry.get("clock_in_at")  or ""
    _co    = _entry.get("clock_out_at") or ""

    def _fmt(ts):
        return _fmt_12h(ts) if ts else ""

    has_ci = bool(_ci)
    has_co = bool(_co)

    can_edit_start = (start_rule == "manual")
    can_edit_end   = (end_rule   == "manual")

    # 24-hour HH:MM values for <input type="time"> pre-fill
    _ci_hhmm = str(_ci)[11:16] if _ci and len(str(_ci)) >= 16 else ""
    _co_hhmm = str(_co)[11:16] if _co and len(str(_co)) >= 16 else ""

    # Status badge
    if has_ci and not has_co:
        badge_bg = "rgba(0,232,125,0.14)"; badge_color = "#56f0b7"
        badge_text = "&#9899;&nbsp;Clocked In"
    elif has_co:
        badge_bg = "rgba(0,180,255,0.10)"; badge_color = "#3fd2ff"
        badge_text = "&#10003;&nbsp;Day Complete"
    else:
        badge_bg = "rgba(100,120,150,0.08)"; badge_color = "#7a9ab8"
        badge_text = "Not Clocked In"

    ci_display = _fmt(_ci) or "&mdash;"
    co_display = _fmt(_co) or "&mdash;"
    ci_color   = "#56f0b7" if has_ci else "#3d5a74"
    co_color   = "#fbbf24" if has_co else "#3d5a74"

    # ── style constants ──────────────────────────────────────────────────────
    S_GREEN  = ('width:100%;padding:18px;font-size:17px;font-weight:800;'
                'border-radius:12px;border:none;cursor:pointer;'
                'background:linear-gradient(135deg,#00c853,#00e57a);'
                'color:#001a0a;letter-spacing:.04em;'
                'box-shadow:0 4px 20px rgba(0,232,125,0.28);')
    S_RED    = ('width:100%;padding:18px;font-size:17px;font-weight:800;'
                'border-radius:12px;border:none;cursor:pointer;'
                'background:linear-gradient(135deg,#ff6d00,#ff3b5c);'
                'color:#fff;letter-spacing:.04em;'
                'box-shadow:0 4px 20px rgba(255,60,60,0.28);')
    S_UNDO   = ('width:100%;padding:13px;font-size:14px;font-weight:600;'
                'border-radius:10px;border:1px solid rgba(255,59,92,0.22);'
                'cursor:pointer;background:rgba(255,59,92,0.08);color:#ff3b5c;')
    S_REOPEN = ('width:100%;padding:13px;font-size:14px;font-weight:600;'
                'border-radius:10px;border:1px solid rgba(255,157,0,0.22);'
                'cursor:pointer;background:rgba(255,157,0,0.08);color:#ff9d00;')
    S_UPD    = ('padding:10px 16px;border-radius:8px;font-weight:600;font-size:13px;'
                'background:rgba(0,200,255,0.10);color:#3fd2ff;'
                'border:1px solid rgba(0,200,255,0.20);cursor:pointer;white-space:nowrap;')
    S_TIME   = ('flex:1;padding:10px 12px;background:rgba(255,255,255,0.05);'
                'border:1px solid rgba(0,160,255,0.20);border-radius:8px;'
                'color:#e8f2ff;font-size:15px;font-weight:600;')
    DIVIDER  = '<div style="height:1px;background:rgba(0,160,255,0.10);margin:12px 0;"></div>'
    LBL      = ('<div style="font-size:11px;color:var(--text-soft);'
                'text-transform:uppercase;letter-spacing:.05em;margin-bottom:6px;">')

    # ── form helpers ─────────────────────────────────────────────────────────
    def _hid(action_val):
        return (
            '<input type="hidden" name="_csrf_token" value="' + csrf_tok + '">'
            '<input type="hidden" name="clock_action" value="' + action_val + '">'
        )

    def _btn_form(action_val, btn_html, mb="12px"):
        return (
            '<form method="POST" style="margin-bottom:' + mb + ';">'
            + _hid(action_val) + btn_html + '</form>'
        )

    def _edit_form(action_val, lbl_text, hhmm_val):
        return (
            '<div style="margin-bottom:12px;">'
            + LBL + lbl_text + '</div>'
            '<form method="POST" style="display:flex;gap:8px;">'
            + _hid(action_val)
            + '<input type="time" name="new_time" value="' + hhmm_val + '" style="' + S_TIME + '">'
            + '<button type="submit" style="' + S_UPD + '">Update</button>'
            + '</form></div>'
        )

    # ── build action buttons by state ────────────────────────────────────────
    parts = []

    if not has_ci and not has_co:
        # ── State 1: Nothing recorded yet ───────────────────────────────────
        if can_edit_start:
            parts.append(_btn_form(
                "clock_in",
                '<button type="submit" style="' + S_GREEN + '">&#9654;&nbsp;Clock In</button>',
                mb="0"
            ))
        elif can_edit_end:
            # Auto start / manual end only — driver records end time
            parts.append(_btn_form(
                "clock_out",
                '<button type="submit" style="' + S_GREEN + '">&#9632;&nbsp;Clock Out</button>',
                mb="0"
            ))

    elif has_ci and not has_co:
        # ── State 2: Clocked In, waiting for clock-out ───────────────────────
        if can_edit_end:
            parts.append(_btn_form(
                "clock_out",
                '<button type="submit" style="' + S_RED + '">&#9632;&nbsp;Clock Out</button>'
            ))
        if can_edit_start:
            parts.append(DIVIDER)
            parts.append(_edit_form("edit_clock_in", "Edit Clock-In Time", _ci_hhmm))
            parts.append(_btn_form(
                "undo_clock_in",
                '<button type="submit" style="' + S_UNDO + '" '
                'onclick="return confirm(\'Remove clock-in for today?\');">'
                '&#215;&nbsp;Undo Clock In</button>',
                mb="0"
            ))

    elif has_ci and has_co:
        # ── State 3: Day Complete ────────────────────────────────────────────
        if can_edit_start:
            parts.append(_edit_form("edit_clock_in",  "Edit Clock-In Time",  _ci_hhmm))
        if can_edit_end:
            parts.append(_edit_form("edit_clock_out", "Edit Clock-Out Time", _co_hhmm))
        parts.append(DIVIDER)
        if can_edit_end:
            parts.append(_btn_form(
                "reopen_day",
                '<button type="submit" style="' + S_REOPEN + '" '
                'onclick="return confirm(\'Clear clock-out and reopen today?\');">'
                '&#8635;&nbsp;Reopen Day</button>',
                mb="0"
            ))

    else:
        # ── State 4: Auto-start, manual end recorded (clock_out only) ────────
        if can_edit_end:
            parts.append(_edit_form("edit_clock_out", "Edit Clock-Out Time", _co_hhmm))
            parts.append(DIVIDER)
            parts.append(_btn_form(
                "reopen_day",
                '<button type="submit" style="' + S_REOPEN + '" '
                'onclick="return confirm(\'Clear clock-out and reopen today?\');">'
                '&#8635;&nbsp;Reopen Day</button>',
                mb="0"
            ))

    actions_html = "".join(parts) if parts else (
        '<p class="muted small">No clock actions are available '
        'for your company&rsquo;s current configuration.</p>'
    )

    # ── assemble page ────────────────────────────────────────────────────────
    body = (
        '<div class="hero">'
        '<h1>&#9201; Clock In / Out</h1>'
        '<p>' + e(day_label) + '</p>'
        '</div>'

        '<div class="card" style="max-width:460px;margin:0 auto 16px;">'
        '<div style="font-size:11px;font-weight:700;letter-spacing:.08em;text-transform:uppercase;'
        'color:var(--text-soft);margin-bottom:14px;">Today&rsquo;s Status</div>'
        '<div style="display:inline-block;padding:8px 22px;border-radius:100px;margin-bottom:18px;'
        'background:' + badge_bg + ';color:' + badge_color + ';font-weight:700;font-size:15px;">'
        + badge_text + '</div>'
        '<div style="display:flex;border:1px solid rgba(0,160,255,0.12);'
        'border-radius:10px;overflow:hidden;">'
        '<div style="flex:1;padding:14px 18px;border-right:1px solid rgba(0,160,255,0.12);">'
        '<div style="font-size:11px;text-transform:uppercase;letter-spacing:.06em;'
        'color:var(--text-soft);margin-bottom:6px;">Clock In</div>'
        '<div style="font-size:24px;font-weight:800;color:' + ci_color + ';">'
        + ci_display + '</div></div>'
        '<div style="flex:1;padding:14px 18px;">'
        '<div style="font-size:11px;text-transform:uppercase;letter-spacing:.06em;'
        'color:var(--text-soft);margin-bottom:6px;">Clock Out</div>'
        '<div style="font-size:24px;font-weight:800;color:' + co_color + ';">'
        + co_display + '</div></div>'
        '</div></div>'

        '<div class="card" style="max-width:460px;margin:0 auto;">'
        + actions_html +
        '</div>'
    )
    return render_template_string(shell_page("Clock In / Out", body))


# =========================================================
# OFFLINE / PWA  — service worker, offline page, CSRF helper
# =========================================================

# Service-worker source (raw string — no f-string escaping needed)
_SW_JS = r"""
const CACHE   = 'haultra-v3';
const OFFLINE = '/offline';

// Pages pre-cached at install so drivers can use them without network
const PRECACHE = ['/driver', '/driver/clock', '/offline'];

self.addEventListener('install', e => {
  e.waitUntil(
    caches.open(CACHE).then(c =>
      Promise.all(
        PRECACHE.map(url =>
          fetch(url, {credentials: 'include'})
            .then(r => { if (r.ok) c.put(url, r); })
            .catch(() => {})
        )
      )
    ).then(() => self.skipWaiting())
  );
});

self.addEventListener('activate', e => {
  e.waitUntil(
    caches.keys()
      .then(keys => Promise.all(
        keys.filter(k => k !== CACHE).map(k => caches.delete(k))
      ))
      .then(() => self.clients.claim())
  );
});

// Cache a specific URL on demand (used by driver dashboard prefetch)
self.addEventListener('message', e => {
  if (e.data && e.data.type === 'CACHE_URL') {
    caches.open(CACHE).then(c =>
      fetch(e.data.url, {credentials: 'include'})
        .then(r => { if (r.ok) c.put(e.data.url, r); })
        .catch(() => {})
    );
  }
});

// Only cache driver-relevant paths — ignore boss/admin pages
const CACHE_PATHS  = ['/driver', '/stop/', '/offline', '/sw.js'];
const MAX_ENTRIES  = 50;   // maximum cached pages before eviction

function isCacheable(url) {
  try {
    const path = new URL(url).pathname;
    return CACHE_PATHS.some(p => path.startsWith(p));
  } catch { return false; }
}

function evictOld(cache) {
  cache.keys().then(keys => {
    const nonPrecache = keys.filter(r => !PRECACHE.includes(new URL(r.url).pathname));
    if (nonPrecache.length > MAX_ENTRIES) {
      nonPrecache.slice(0, nonPrecache.length - MAX_ENTRIES)
        .forEach(k => cache.delete(k));
    }
  });
}

// Network-first for all GET requests; cache as we go; serve cache when offline
self.addEventListener('fetch', e => {
  if (e.request.method !== 'GET') return;   // POSTs handled by page JS
  const nav = e.request.mode === 'navigate';
  e.respondWith(
    fetch(e.request).then(res => {
      if (res.ok && isCacheable(e.request.url)) {
        const clone = res.clone();
        caches.open(CACHE).then(c => { c.put(e.request, clone); evictOld(c); });
      }
      return res;
    }).catch(() =>
      caches.match(e.request).then(cached =>
        cached || (nav ? caches.match(OFFLINE) : new Response('', {status: 503}))
      )
    )
  );
});
"""


@app.route('/sw.js')
def service_worker():
    from flask import Response
    return Response(
        _SW_JS, mimetype='text/javascript',
        headers={'Service-Worker-Allowed': '/'}
    )


@app.route('/offline')
def offline_page():
    body = """
    <div class="hero" style="text-align:center;">
        <h1 style="color:#fbbf24;">&#9888; No Connection</h1>
        <p>You are currently offline.</p>
    </div>
    <div class="card" style="max-width:460px;margin:0 auto;text-align:center;">
        <p style="color:var(--text-soft);margin-bottom:20px;">
            Your driver dashboard and clock pages are still available.<br>
            Clock&nbsp;in/out and stop actions will be saved here and synced
            automatically when your connection returns.
        </p>
        <button onclick="location.reload()"
                style="padding:12px 28px;border-radius:10px;border:none;
                       background:linear-gradient(135deg,#00c853,#00e57a);
                       color:#001a0a;font-weight:700;cursor:pointer;font-size:15px;">
            &#8635;&nbsp;Try Again
        </button>
        <div id="qs" style="margin-top:16px;color:#fbbf24;font-size:13px;"></div>
    </div>
    <script>
    var q = JSON.parse(localStorage.getItem('haultra_offline_queue') || '[]');
    if (q.length) {
        document.getElementById('qs').textContent =
            q.length + ' action' + (q.length > 1 ? 's' : '') + ' queued \u2014 will sync on reconnect.';
    }
    </script>
    """
    return render_template_string(shell_page("Offline", body))


@app.route('/api/csrf-token')
@login_required
def api_csrf_token():
    """Return a fresh CSRF token so the offline sync replay can re-stamp queued POSTs."""
    from flask import jsonify
    return jsonify({'token': get_csrf_token()})


# =========================================================
# PASTE ROUTE — PARSE API
# =========================================================
@app.route("/api/parse-route-text", methods=["POST"])
@login_required
def parse_route_text_api():
    data = request.get_json(silent=True) or {}
    text = (data.get("text") or "").strip()
    if not text:
        return jsonify({"stops": []})
    conn = get_db()
    try:
        stops = parse_route_text(text, conn, cid())
    finally:
        conn.close()
    return jsonify({"stops": stops})


# =========================================================
# PASTE ROUTE — ADD CONFIRMED STOPS
# =========================================================
@app.route("/route/<int:route_id>/add-parsed-stops", methods=["POST"])
@boss_required
def add_parsed_stops(route_id):
    conn = get_db()
    if not conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone():
        conn.close()
        return jsonify({"error": "Route not found."}), 404

    data  = request.get_json(silent=True) or {}
    stops = data.get("stops") or []
    if not stops:
        conn.close()
        return jsonify({"error": "No stops provided."})

    last = conn.execute(
        "SELECT MAX(stop_order) as m FROM stops WHERE route_id=?", (route_id,)
    ).fetchone()["m"] or 0

    added = 0
    for stop in stops:
        if not isinstance(stop, dict):
            continue
        # Apply abbreviation expansion before inserting
        customer_name  = expand_abbrev(stop.get("customer_name")  or "")
        address        = expand_abbrev(stop.get("address")         or "")
        city           = expand_abbrev(stop.get("city")            or "")
        state          = expand_abbrev(stop.get("state")           or "")
        zip_code       = expand_abbrev(stop.get("zip_code")        or "")
        action         = expand_abbrev(stop.get("action")          or "")
        container_size = expand_abbrev(stop.get("container_size")  or "")
        dump_location  = expand_abbrev(stop.get("dump_location")   or "")
        last += 1
        conn.execute("""
            INSERT INTO stops (
                route_id, stop_order, customer_name, address, city, state, zip_code,
                action, container_size, dump_location,
                swap_with_prev_pull, status, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 'open', ?)
        """, (route_id, last, customer_name, address, city, state, zip_code,
              action, container_size, dump_location, now_ts()))
        added += 1
        upsert_saved_address(conn, cid(),
            customer_name, address, city, state, zip_code,
            action, container_size, dump_location)

    if added:
        conn.commit()
        compute_can_flow(conn, route_id)
        conn.commit()

    conn.close()
    return jsonify({"added": added})


# =========================================================
# ADDRESS AUTOCOMPLETE API
# =========================================================
@app.route("/api/address-suggestions")
@login_required
def address_suggestions():
    q = expand_abbrev((request.args.get("q") or "").strip())
    if len(q) < 2:
        return jsonify([])
    conn = get_db()
    like = "%" + q + "%"
    rows = conn.execute("""
        SELECT sa.customer_name, sa.address, sa.city, sa.state, sa.zip,
               COALESCE(sad.action, '')         AS default_action,
               COALESCE(sad.container_size, '') AS default_container_size,
               COALESCE(sad.dump_location, '')  AS default_dump_location
        FROM saved_addresses sa
        LEFT JOIN saved_address_details sad
               ON sad.saved_address_id = sa.id
              AND sad.id = (
                      SELECT id FROM saved_address_details
                      WHERE saved_address_id = sa.id
                        AND (action != '' OR container_size != '' OR dump_location != '')
                      ORDER BY times_used DESC, last_used_at DESC
                      LIMIT 1
                  )
        WHERE sa.company_id=? AND (sa.customer_name LIKE ? OR sa.address LIKE ?)
        ORDER BY sa.times_used DESC, sa.last_used_at DESC
        LIMIT 10
    """, (cid(), like, like)).fetchall()
    conn.close()
    return jsonify([dict(r) for r in rows])


# =========================================================
# DEBUG — temporary DB inspection route
# =========================================================
@app.route("/debug/db")
@boss_required
def debug_db():
    from flask import jsonify
    conn = get_db()
    total = conn.execute("SELECT COUNT(*) FROM routes").fetchone()[0]
    rows  = conn.execute(
        "SELECT id, route_date, route_name, status FROM routes ORDER BY route_date DESC, id DESC"
    ).fetchall()
    conn.close()
    return jsonify({
        "DATABASE_PATH": DATABASE,
        "total_routes":  total,
        "routes": [
            {"id": r["id"], "date": r["route_date"], "name": r["route_name"], "status": r["status"]}
            for r in rows
        ],
    })


# =========================================================
# STARTUP — initialize DB before gunicorn serves any request
# =========================================================
init_db()
print("Startup complete. DATABASE_PATH =", DATABASE, flush=True)

# =========================================================
# RUN APP
# =========================================================
if __name__ == "__main__":
    debug = os.environ.get("FLASK_DEBUG", "0") == "1"
    port  = int(os.environ.get("PORT", 5001))
    app.run(host="0.0.0.0", port=port, debug=debug)