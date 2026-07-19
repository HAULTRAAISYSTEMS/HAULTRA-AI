from flask import (
    Flask, request, redirect, url_for, session, flash,
    render_template_string, send_file, send_from_directory, abort, jsonify
)
import sqlite3
import os
import re
import io
import csv
import html
import math
import secrets
import hashlib
import warnings
import time
import threading
import json
import urllib.request
import urllib.parse
import requests
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
    raise RuntimeError(
        "SECRET_KEY env var not set. "
        "Generate one with: python -c \"import secrets; print(secrets.token_hex(32))\""
    )
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
# ERROR HANDLERS
# Without these, an unhandled exception anywhere in any route falls
# through to Flask's bare default response with nothing logged beyond
# whatever Render's raw process logs happen to capture, and no
# on-brand fallback shown to the user. debug=False already prevents any
# stack trace leaking to the client either way — these just make sure
# the failure is (a) actually logged server-side and (b) doesn't look
# broken to whoever hit it.
# =========================================================
_ERROR_PAGE_TEMPLATE = """
<!doctype html><html><head><title>{title}</title>
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
  * {{ box-sizing: border-box; }}
  html, body {{ background: #121212; margin: 0; min-height: 100%; }}
  body {{
    color: #F5F5F0; font-family: -apple-system, "Segoe UI", sans-serif;
    display: flex; align-items: center; justify-content: center;
    min-height: 100vh; text-align: center; padding: 24px;
  }}
  .box {{ max-width: 420px; }}
  h1 {{
    font-family: 'Bebas Neue', 'Anton', sans-serif;
    font-size: 64px; margin: 0 0 8px; letter-spacing: 1px;
    background: linear-gradient(130deg, #ffffff 0%, #F5F5F0 55%, #FF6B1A 100%);
    -webkit-background-clip: text; -webkit-text-fill-color: transparent; background-clip: text;
  }}
  p {{ color: #A6A69E; font-size: 14px; line-height: 1.6; margin-bottom: 22px; }}
  a {{
    display: inline-block; padding: 10px 22px; border-radius: 9px;
    background: linear-gradient(135deg, #FF8A42 0%, #FF6B1A 100%);
    color: #1A1000; text-decoration: none; font-weight: 700; font-size: 13px;
  }}
</style></head><body><div class="box">
  <h1>{code}</h1>
  <p>{message}</p>
  <a href="/">&larr; Back to HAULTRA</a>
</div></body></html>
"""


@app.errorhandler(404)
def _handle_not_found(err):
    if request.path.startswith("/api/") or request.is_json:
        return jsonify({"error": "Not found."}), 404
    return render_template_string(
        _ERROR_PAGE_TEMPLATE.format(
            title="Not Found", code="404",
            message="That page doesn&rsquo;t exist, or you don&rsquo;t have access to it.",
        )
    ), 404


@app.errorhandler(500)
def _handle_server_error(err):
    app.logger.error("Unhandled exception on %s %s", request.method, request.path, exc_info=True)
    if request.path.startswith("/api/") or request.is_json:
        return jsonify({"error": "Something went wrong on our end. Try again in a moment."}), 500
    return render_template_string(
        _ERROR_PAGE_TEMPLATE.format(
            title="Something Went Wrong", code="500",
            message="Something went wrong on our end. It&rsquo;s been logged &mdash; try again in a moment.",
        )
    ), 500


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
    return datetime.now(_EASTERN).strftime("%Y-%m-%d")


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
    # Relocate/Move-on-site — checked before bare "move" so specific wins
    (re.compile(r'\b(?:relocate|reloc|move\s+can)\b',                    re.I), "Relocate"),
    (re.compile(r'\breposition\b',                                        re.I), "Move"),
    (re.compile(r'\bpull\b',                                              re.I), "Pull"),
    (re.compile(r'\b(?:pick\s*up|pickup)\b',                              re.I), "Pull"),
    (re.compile(r'\bmove\b',                                              re.I), "Move"),
    (re.compile(r'\b(?:drop\s*off|drop)\b',                               re.I), "Delivery"),
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
    results      = []
    use_for_next = False  # carries swap-trigger past non-PR stops until consumed

    input_lines = [l.strip() for l in text.splitlines() if l.strip()]
    print(f"[PARSER] Input lines: {len(input_lines)}", flush=True)

    for raw in input_lines:
        raw_lo = raw.lower()

        # ── Annotation lines: attach to previous stop as notes, set swap trigger ──
        if _ANNOTATION_LINE_RE.match(raw) or _PENDING_EMPTY_RE.search(raw_lo):
            if results:
                prev_notes = results[-1].get("notes") or ""
                results[-1]["notes"] = (prev_notes + ("  " if prev_notes else "") + raw).strip()
                results[-1]["pending_empty_can_for_next_pr"] = True
            use_for_next = True
            print(f"[PARSER] Annotation line → attached to previous stop: {raw!r}", flush=True)
            continue

        try:
            parsed = _parse_one_line(raw, conn, company_id)
        except Exception as exc:
            print(f"[PARSER] ERROR parsing {raw!r}: {exc}", flush=True)
            continue

        if not parsed:
            print(f"[PARSER] SKIP (unparseable): {raw!r}", flush=True)
            continue

        action_lc = (parsed.get("action") or "").lower()
        notes     = parsed.get("notes") or ""
        notes_lc  = notes.lower()
        is_pr     = "pickup and return" in action_lc

        # Apply pending swap from a previous stop to this PR stop
        if use_for_next and is_pr:
            parsed["pr_mode"]                  = "swap"
            parsed["swap_with_prev_pull"]      = 1
            parsed["swap_with_previous_empty"] = True
            use_for_next = False

        # Detect swap trigger phrase in this stop's notes
        if _PENDING_EMPTY_RE.search(notes_lc):
            parsed["pending_empty_can_for_next_pr"] = True
            use_for_next = True

        # Detect "return to <dest>"
        rt = _RETURN_TO_RE.search(notes)
        if rt:
            parsed["return_destination"] = rt.group(1).strip().rstrip(".")

        results.append(parsed)
        print(
            f"[PARSER] Stop {len(results)}: action={parsed.get('action')!r}"
            f"  addr={parsed.get('address')!r}"
            f"  customer={parsed.get('customer_name')!r}"
            f"  conf={parsed.get('confidence')}",
            flush=True,
        )

    print(f"[PARSER] Total parsed stops: {len(results)}", flush=True)
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

    # ── Move on-site format ───────────────────────────────────────────────────
    mv = _parse_move_line(work, order_num=1)
    if mv:
        mv["original_line"] = raw
        return mv

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
            def _esc_like(s):
                return s.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")
            if customer_name:
                saved = conn.execute(
                    """SELECT * FROM saved_addresses
                       WHERE company_id=? AND LOWER(customer_name) LIKE ? ESCAPE '\\'
                       ORDER BY times_used DESC LIMIT 1""",
                    (company_id, "%" + _esc_like(customer_name.lower()) + "%")
                ).fetchone()
            if not saved and address:
                saved = conn.execute(
                    """SELECT * FROM saved_addresses
                       WHERE company_id=? AND LOWER(address) LIKE ? ESCAPE '\\'
                       ORDER BY times_used DESC LIMIT 1""",
                    (company_id, "%" + _esc_like(address.lower()) + "%")
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
        except Exception as e:
            app.logger.warning("Address lookup DB error for %r: %s", raw, e)

    conf = min(100, conf)
    conf_label = "high" if conf >= 75 else ("medium" if conf >= 45 else "low")

    return {
        "original_line":                raw,
        "customer_name":                customer_name,
        "address":                      address,
        "city":                         city,
        "state":                        state,
        "zip_code":                     zip_code,
        "action":                       action,
        "service_type":                 action,
        "container_size":               container_size,
        "dump_location":                dump_location,
        "notes":                        notes,
        "placement_note":               "",
        "ticket_number":                ticket_number,
        "reference_number":             "",
        "relocate_from_address":        "",
        "relocate_to_address":          "",
        "from_address":                 "",
        "from_city":                    "",
        "to_address":                   "",
        "to_city":                      "",
        "return_destination":           "",
        "pr_mode":                      "",
        "swap_with_previous_empty":     False,
        "pending_empty_can_for_next_pr": False,
        "warnings":                     [],
        "confidence":                   conf,
        "confidence_label":             conf_label,
        "matched_saved":                matched_saved,
        "conf_reasons":                 conf_reasons,
    }


def get_db():
    db_dir = os.path.dirname(DATABASE)
    if db_dir:
        os.makedirs(db_dir, exist_ok=True)
    # timeout=30: how long a connection waits on a lock before raising
    # "database is locked", instead of the sqlite3 default of 5s. WAL mode
    # lets readers proceed while a write is in progress instead of the
    # default rollback-journal's whole-file lock — both matter more now
    # that background threads (geocoding) open their own connections
    # alongside the 2 gunicorn workers x 2 threads handling requests.
    conn = sqlite3.connect(DATABASE, timeout=30)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA busy_timeout=30000")
    return conn


def get_csrf_token():
    if "_csrf_token" not in session:
        session["_csrf_token"] = secrets.token_hex(32)
    return session["_csrf_token"]


def send_email(to_email, subject, html_body):
    """
    Send a transactional email via Resend. This is the ONLY place that talks to
    the mail provider — swap providers by editing this function alone, every
    caller just passes to/subject/html and gets a bool back.

    Returns True on a confirmed send, False otherwise (including when
    RESEND_API_KEY isn't configured, e.g. local dev) — callers must not use
    the return value to change what they show the user, since doing so for
    the password-reset flow would leak whether an account/email exists.
    """
    api_key = os.environ.get("RESEND_API_KEY")
    from_addr = os.environ.get("RESEND_FROM_EMAIL", "HAULTRA AI <onboarding@resend.dev>")
    if not api_key:
        # Dev/misconfigured fallback: log what would have been sent (including
        # the body, so a reset link is still recoverable from the server log
        # while testing locally) instead of silently dropping it.
        app.logger.warning(
            "send_email: RESEND_API_KEY not configured — email not sent (to=%s, subject=%r)\n%s",
            to_email, subject, html_body
        )
        return False
    try:
        resp = requests.post(
            "https://api.resend.com/emails",
            headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
            json={"from": from_addr, "to": [to_email], "subject": subject, "html": html_body},
            timeout=10,
        )
        if resp.status_code >= 400:
            app.logger.warning("send_email: Resend API error %s: %s", resp.status_code, resp.text[:300])
            return False
        return True
    except Exception as exc:
        app.logger.warning("send_email: failed to send to %s: %s", to_email, exc)
        return False


# Endpoints that legitimately receive POST from external clients (no session/CSRF).
# customer_create_request is authenticated by the URL portal token, not a
# session cookie, so there is no session for CSRF to protect and it must be
# exempt (same rationale as the Stripe webhook).
_CSRF_EXEMPT_ENDPOINTS = {"stripe_webhook", "customer_create_request", "customer_rename_bin"}

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
    "company_subscription", "company_settings", "settings_page", "stripe_webhook",
    "privacy_policy", "terms_of_service",
}

_SUB_CACHE_TTL = 60  # seconds between DB re-checks per company

@app.before_request
def subscription_enforce():
    """
    Auto-suspend expired trials, then block suspended/cancelled accounts.
    Runs on every request after login, with a 60-second session cache to avoid
    hitting the DB on every single request.
    """
    if request.endpoint in _SUBSCRIPTION_EXEMPT or not session.get("company_id"):
        return

    company_id = session["company_id"]

    import time as _time
    now_ts_float = _time.time()
    cache_checked_at = session.get("_sub_checked_at", 0)

    if now_ts_float - cache_checked_at < _SUB_CACHE_TTL:
        cached_status = session.get("_sub_status")
        if cached_status in ("suspended", "cancelled"):
            if request.endpoint in ("company_subscription", "company_settings", "settings_page"):
                return
            return redirect(url_for("subscription_blocked"))
        return

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

    session["_sub_status"] = co["subscription_status"]
    session["_sub_checked_at"] = now_ts_float

    if co["subscription_status"] in ("suspended", "cancelled"):
        if request.endpoint in ("company_subscription", "company_settings", "settings_page"):
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


# Nominatim usage policy: max 1 request/second, identify the app + a real
# contact. This lock + timestamp throttles every call through
# _geocode_server below to that limit, process-wide, regardless of which
# caller (route optimization, the stop-completion hook, or the backfill
# script) is making it.
_NOMINATIM_USER_AGENT = "HAULTRA-AI dispatch, contact: timbobrown04@gmail.com"
_geocode_rate_lock = threading.Lock()
_geocode_last_call = [0.0]


def _geocode_server(address):
    """Geocode an address with Nominatim. Returns (lat, lng) or None.

    Self-throttles to <=1 request/second across the whole process, so
    callers don't each need their own time.sleep(). Never raises — any
    failure (network, timeout, no results) just returns None.
    """
    if not (address or "").strip():
        return None

    with _geocode_rate_lock:
        wait = 1.05 - (time.time() - _geocode_last_call[0])
        if wait > 0:
            time.sleep(wait)
        _geocode_last_call[0] = time.time()

        url = ("https://nominatim.openstreetmap.org/search?format=json&limit=1&q="
               + urllib.parse.quote_plus(address))
        req = urllib.request.Request(url, headers={
            "User-Agent": _NOMINATIM_USER_AGENT,
            "Accept-Language": "en",
        })
        try:
            with urllib.request.urlopen(req, timeout=8) as resp:
                data = json.loads(resp.read().decode())
                if data:
                    return float(data[0]["lat"]), float(data[0]["lon"])
        except Exception as exc:
            app.logger.warning("Nominatim geocode failed for %r: %s", address, exc)
    return None


def geocode_address_cached(conn, company_id, address, city, state="", zip_code=""):
    """Geocode a stop's address, reusing any coordinates already stored for
    the same address+city within this company instead of re-requesting
    Nominatim. Returns (lat, lng) or None — never raises, never blocks on a
    lock beyond what _geocode_server already serializes.
    """
    address = (address or "").strip()
    city = (city or "").strip()
    if not address:
        return None

    cached = conn.execute("""
        SELECT s.lat, s.lng FROM stops s JOIN routes r ON s.route_id = r.id
        WHERE r.company_id = ? AND lower(trim(s.address)) = lower(?)
          AND lower(trim(COALESCE(s.city, ''))) = lower(?)
          AND s.lat IS NOT NULL AND s.lng IS NOT NULL
        LIMIT 1
    """, (company_id, address, city)).fetchone()
    if cached:
        return cached["lat"], cached["lng"]

    full_address = ", ".join(p for p in [address, city, state, zip_code] if p)
    return _geocode_server(full_address)


def geocode_stop_in_background(stop_id):
    """Kick off geocoding for a stop's address on a daemon thread so the
    HTTP request that triggered it (a driver completing a stop) returns
    immediately. A failed or slow geocode never blocks or fails stop
    completion — it just leaves lat/lng null, same as if it were never
    attempted. Opens its own DB connection since it outlives the request.
    """
    def _worker():
        try:
            conn = get_db()
            stop = conn.execute(
                "SELECT address, city, state, zip_code, route_id, lat, lng FROM stops WHERE id=?",
                (stop_id,)
            ).fetchone()
            if not stop or stop["lat"] is not None or not (stop["address"] or "").strip():
                conn.close()
                return
            route = conn.execute(
                "SELECT company_id FROM routes WHERE id=?", (stop["route_id"],)
            ).fetchone()
            if not route:
                conn.close()
                return
            coords = geocode_address_cached(
                conn, route["company_id"], stop["address"], stop["city"],
                stop["state"], stop["zip_code"]
            )
            if coords:
                conn.execute("UPDATE stops SET lat=?, lng=? WHERE id=?",
                             (coords[0], coords[1], stop_id))
                conn.commit()
            conn.close()
        except Exception as exc:
            app.logger.warning("background geocode failed for stop %s: %s", stop_id, exc)

    threading.Thread(target=_worker, daemon=True).start()


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
        # After dump the driver keeps the emptied can on the truck.
        # That empty can is available for a swap on the very next PR stop.
        return "empty_can"

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
        "SELECT id, action, pr_mode FROM stops WHERE route_id=? ORDER BY stop_order ASC, id ASC",
        (route_id,)
    ).fetchall()

    can_state = "empty_can" if starts_with_can else "no_can"

    for s in stops:
        action_lower   = (s["action"]  or "").lower().strip()
        parser_pr_mode = (s["pr_mode"] or "").lower().strip()

        # Is this a PR-type stop (Pickup and Return or Swap-only)?
        is_pr = (
            "pickup and return" in action_lower
            or ("swap" in action_lower and "pull" not in action_lower)
        )

        if is_pr:
            # Boss language (pr_mode="swap") overrides sequence-derived can state.
            # This fires when the parser detected "use it to / before you return" etc.
            effective_state = "empty_can" if parser_pr_mode == "swap" else can_state
            derived_swap    = 1 if effective_state == "empty_can" else 0
            conn.execute(
                "UPDATE stops SET can_state_before=?, swap_with_prev_pull=? WHERE id=?",
                (effective_state, derived_swap, s["id"])
            )
            can_state = _next_can_state(action_lower, effective_state)
        else:
            conn.execute(
                "UPDATE stops SET can_state_before=? WHERE id=?",
                (can_state, s["id"])
            )
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
    except Exception as e:
        app.logger.error("Container flow tracking failed for stop %s: %s", stop_id, e)


def compute_containers_out(conn, company_id, asof_date=None):
    """
    Read-only view of containers on-site at customer addresses, as of a given
    date (defaults to "right now" — i.e. no cutoff).

    ENABLE_CONTAINER_TRACKING is off, so customer_containers is never written.
    Rather than fabricate numbers, this replays completed stops chronologically
    (same action semantics as update_container_flow / compute_can_flow: a
    Delivery or PR/swap stop leaves a container behind, a Pull closes it out)
    to derive what's actually out from real stop history.

    asof_date: optional "YYYY-MM-DD" string. When given, only stops completed
    on or before that date are replayed — lets callers reconstruct a historical
    snapshot (e.g. "how many were out 7 days ago") from the same real data,
    instead of tracking separate historical rows nobody writes.

    Returns a list of dicts: address, city, state, size, since (timestamp str),
    customer_name, route_id, stop_id, lat, lng, is_gps — one per address
    currently holding a container. lat/lng prefer the driver's GPS stamp
    from the moment that stop was completed (is_gps=True) over the
    geocoded address estimate (is_gps=False) when both exist, since GPS is
    where the truck actually stood. Both can be None if neither was ever
    captured/geocoded — callers should treat that as "no map location",
    not an error.
    """
    sql = """SELECT s.id, s.address, s.city, s.state, s.action, s.container_size,
                  s.completed_at, s.customer_name, s.route_id, s.lat, s.lng,
                  s.gps_lat, s.gps_lng, r.route_date
           FROM stops s
           JOIN routes r ON s.route_id = r.id
           WHERE r.company_id = ? AND s.status = 'completed'
             AND s.address IS NOT NULL AND TRIM(s.address) != ''"""
    params = [company_id]
    if asof_date:
        sql += " AND substr(COALESCE(s.completed_at, r.route_date), 1, 10) <= ?"
        params.append(asof_date)
    sql += " ORDER BY COALESCE(s.completed_at, r.route_date), s.id"
    rows = conn.execute(sql, tuple(params)).fetchall()

    on_site = {}
    for s in rows:
        addr_key = (s["address"] or "").strip().lower() + "|" + (s["city"] or "").strip().lower()
        action_lower = (s["action"] or "").lower()
        is_pr       = "pickup and return" in action_lower or ("swap" in action_lower and "pull" not in action_lower)
        is_delivery = "delivery" in action_lower or "drop" in action_lower
        is_pull     = "pull" in action_lower and "return" not in action_lower

        if is_delivery or is_pr:
            has_gps = s["gps_lat"] is not None and s["gps_lng"] is not None
            on_site[addr_key] = {
                "address": s["address"], "city": s["city"], "state": s["state"],
                "size": s["container_size"], "since": s["completed_at"] or s["route_date"],
                "customer_name": s["customer_name"], "route_id": s["route_id"],
                "stop_id": s["id"],
                "lat": s["gps_lat"] if has_gps else s["lat"],
                "lng": s["gps_lng"] if has_gps else s["lng"],
                "is_gps": has_gps,
            }
        elif is_pull:
            on_site.pop(addr_key, None)

    return list(on_site.values())


def is_pull_job(action):
    """True for any action that pulls a full container (plain Pull, or PR/swap)."""
    action_lower = (action or "").lower()
    is_pr   = "pickup and return" in action_lower or ("swap" in action_lower and "pull" not in action_lower)
    is_pull = "pull" in action_lower and "return" not in action_lower
    return is_pr or is_pull


def size_bucket(size_str):
    """Normalize a free-text container size to one of the standard buckets, else None."""
    s = (size_str or "")
    for bucket in ("10", "20", "30", "40"):
        if bucket in s:
            return f"{bucket}yd"
    return None


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
    """Render a gallery of uploaded photos with uploader name and timestamp.
    Links go through serve_stop_photo (login + company + ownership checked)
    rather than the raw /static/uploads/... path, which Flask's default
    static handler would otherwise serve to anyone with the URL, logged in
    or not, from any company."""
    if not photos:
        return ""
    items = []
    for p in photos:
        path = url_for("serve_stop_photo", photo_id=p["id"])
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


# Phase 6 — default pre-trip checklist for a roll-off truck. This is only the
# SEED for the checklist_items table (company_id IS NULL); the running app reads
# the table, never this list, so a company can customize it later without a code
# change. (label, hint) pairs, rendered top-to-bottom.
DEFAULT_CHECKLIST = [
    ("Service brakes", "Pedal feel, air pressure, no drag"),
    ("Parking brake", "Holds on a grade"),
    ("Tires, wheels & rims", "Tread, inflation, lugs, no cracks"),
    ("Lights, reflectors & signals", "Head/tail/brake/turn/markers"),
    ("Mirrors & glass", "Clean, intact, adjusted"),
    ("Horn", "Sounds"),
    ("Windshield wipers", "Blades, washer fluid"),
    ("Steering", "Free play within limits"),
    ("Coupling / hoist / hydraulics", "Hoist, cables, rollers, tarp system"),
    ("Leaks", "Oil, coolant, fuel, hydraulic"),
    ("Emergency equipment", "Fire extinguisher, triangles, kit"),
    ("Cab & seatbelt", "Belt latches, cab secure"),
    ("Overall vehicle condition", "Anything else affecting safe operation"),
]

# Phase 6 — inspection enums shared by the driver flow and management views.
INSPECTION_TYPES   = ("pre_trip", "post_trip")
INSPECTION_OVERALL = ("safe", "defects_safe", "out_of_service")
_INSPECTION_TYPE_LABEL = {"pre_trip": "Pre-trip", "post_trip": "Post-trip"}
_INSPECTION_OVERALL_LABEL = {
    "safe": "Safe to operate",
    "defects_safe": "Defects — safe to operate",
    "out_of_service": "OUT OF SERVICE (unsafe)",
}

# Phase 7A — data-driven maintenance category pick list (validated server-side).
# Repaired inspection defects are surfaced in the log under "Repair".
MAINTENANCE_CATEGORIES = [
    "Oil/Fluids", "Tires", "Brakes", "Hydraulics/Hoist",
    "Electrical", "PM Service", "Repair", "Other",
]
# How long after creation a manual maintenance entry stays editable (then locked).
MAINTENANCE_EDIT_WINDOW_SECONDS = 24 * 3600


def parse_cost_cents(raw):
    """Parse a user-entered dollar amount into INTEGER CENTS without ever
    touching a float (float cents are lossy). Accepts '', '12', '12.5',
    '$1,250.00'. Returns (cents:int|None, error:str|None). Empty → (None, None)
    since cost is optional. Negative or >~$1M rejected."""
    if raw is None:
        return None, None
    s = str(raw).strip().replace("$", "").replace(",", "")
    if s == "":
        return None, None
    neg = s.startswith("-")
    if neg:
        return None, "cost cannot be negative"
    if "." in s:
        whole, _, frac = s.partition(".")
    else:
        whole, frac = s, ""
    whole = whole or "0"
    if not whole.isdigit() or (frac and not frac.isdigit()):
        return None, "cost must be a number like 149.99"
    frac = (frac + "00")[:2]  # pad/truncate to exactly 2 decimals, integer-only
    cents = int(whole) * 100 + int(frac)
    if cents > 100_000_000:  # $1,000,000 sanity ceiling
        return None, "cost is too large"
    return cents, None


def format_cents(cents):
    """Integer cents → '$1,250.00'. None → '—'."""
    if cents is None:
        return "—"
    neg = cents < 0
    cents = abs(int(cents))
    dollars, rem = divmod(cents, 100)
    return f"{'-' if neg else ''}${dollars:,}.{rem:02d}"


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
    # Phase 5 — management sub-roles (additive flags layered on the existing
    # role column). A management user stays role='boss' (so every existing
    # @boss_required check keeps working) and carries one or more of these
    # flags. 'owner' implies both other management permissions. Drivers keep
    # role='driver' and no flags. Existing bosses are migrated to owner below.
    safe_add_column(conn, "users", "role_owner INTEGER NOT NULL DEFAULT 0")
    safe_add_column(conn, "users", "role_customer_manager INTEGER NOT NULL DEFAULT 0")
    safe_add_column(conn, "users", "role_dispatcher INTEGER NOT NULL DEFAULT 0")
    # Every pre-Phase-5 boss becomes an owner (full access) so nothing breaks.
    # Guard on "no role flags yet" so this stays a one-time promotion: it must
    # NOT re-run on every init_db and clobber a later cm-only / dispatcher-only
    # user (role='boss' with a single flag) back into an owner.
    conn.execute(
        """UPDATE users SET role_owner=1
            WHERE role='boss' AND role_owner=0
              AND role_customer_manager=0 AND role_dispatcher=0"""
    )
    conn.commit()
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
    safe_add_column(conn, "stops", "placement_note TEXT")
    safe_add_column(conn, "stops", "relocate_to_address TEXT")
    safe_add_column(conn, "stops", "relocate_to_city TEXT")
    safe_add_column(conn, "stops", "return_destination TEXT")
    safe_add_column(conn, "stops", "pr_mode TEXT")

    # --- Phase 5B: company work hours / pay cycle ---
    safe_add_column(conn, "companies", "timezone TEXT")
    safe_add_column(conn, "companies", "workweek_start_day TEXT")
    safe_add_column(conn, "companies", "workweek_reset_day TEXT")
    safe_add_column(conn, "companies", "pay_period_type TEXT")
    safe_add_column(conn, "companies", "pay_period_end_day TEXT")
    safe_add_column(conn, "companies", "payday TEXT")
    safe_add_column(conn, "companies", "driver_day_start_rule TEXT")
    safe_add_column(conn, "companies", "driver_day_end_rule TEXT")

    # --- Photo proof mode: off | encouraged (default) | required ---
    safe_add_column(conn, "companies", "photo_proof_mode TEXT NOT NULL DEFAULT 'encouraged'")

    # --- Driver nav app preference: NULL (unset, current behavior) | google |
    #     apple | waze | device_default ---
    safe_add_column(conn, "users", "nav_preference TEXT")

    # --- Geocoded coordinates for a stop's own address, used by the Bin
    #     Tracker map. NULL until geocoded (or if geocoding failed/was never
    #     attempted) — compute_containers_out() and the map degrade to
    #     list-only for those. See geocode_address_cached() for the cache
    #     that keeps a repeat address from ever being re-geocoded. ---
    safe_add_column(conn, "stops", "lat REAL")
    safe_add_column(conn, "stops", "lng REAL")

    # --- GPS stamp captured on the driver's device at the moment a stop was
    #     completed — separate from lat/lng (the geocoded address estimate)
    #     above. This is per-completion evidence and is never overwritten:
    #     it stays on this stop row even after the container is relocated by
    #     a later, different stop. compute_containers_out() prefers this over
    #     the geocoded address for the "current" container position when
    #     both exist, since GPS is where the truck actually stood. ---
    safe_add_column(conn, "stops", "gps_lat REAL")
    safe_add_column(conn, "stops", "gps_lng REAL")
    safe_add_column(conn, "stops", "gps_accuracy REAL")
    safe_add_column(conn, "stops", "gps_captured_at TEXT")
    # Customer Request System: link a stop back to the customer request it
    # fulfills (set later when the boss approves a request — future phase).
    # Nullable; no existing stop behavior depends on these.
    safe_add_column(conn, "stops", "request_id INTEGER")
    safe_add_column(conn, "stops", "customer_id INTEGER")
    # Customer Request System (Phase 3): boss's reason when denying a request.
    safe_add_column(conn, "requests", "deny_reason TEXT")
    # Phase 5 — two-stage workflow adds the 'accepted' status and a manager's
    # note-to-customer. The status CHECK from Phase 1 forbids 'accepted', and
    # SQLite can't ALTER a CHECK, so rebuild the table once (dropping the
    # status CHECK — transitions are validated in code) when 'accepted' isn't
    # yet allowed. Column-safe: copies by the intersection of old/new columns.
    safe_add_column(conn, "requests", "customer_note TEXT")
    _rq_sql_row = conn.execute(
        "SELECT sql FROM sqlite_master WHERE type='table' AND name='requests'"
    ).fetchone()
    if _rq_sql_row and "'accepted'" not in (_rq_sql_row["sql"] or ""):
        _old_cols = [r[1] for r in conn.execute("PRAGMA table_info(requests)").fetchall()]
        _new_cols = ["id", "customer_id", "site_id", "type", "bin_id", "size_requested",
                     "preferred_date", "notes", "status", "stop_id", "deny_reason",
                     "customer_note", "created_at", "updated_at"]
        _copy = [c for c in _new_cols if c in _old_cols]
        _copy_csv = ", ".join(_copy)
        conn.executescript(f"""
            PRAGMA foreign_keys=off;
            BEGIN;
            CREATE TABLE requests_p5_new (
                id             INTEGER PRIMARY KEY AUTOINCREMENT,
                customer_id    INTEGER NOT NULL,
                site_id        INTEGER NOT NULL,
                type           TEXT NOT NULL CHECK(type IN ('PR','P','D','NEW_BIN')),
                bin_id         INTEGER,
                size_requested TEXT,
                preferred_date TEXT NOT NULL,
                notes          TEXT,
                status         TEXT NOT NULL DEFAULT 'pending'
                    CHECK(status IN ('pending','accepted','approved','scheduled','in_progress','done','denied')),
                stop_id        INTEGER,
                deny_reason    TEXT,
                customer_note  TEXT,
                created_at     TEXT NOT NULL,
                updated_at     TEXT NOT NULL
            );
            INSERT INTO requests_p5_new ({_copy_csv}) SELECT {_copy_csv} FROM requests;
            DROP TABLE requests;
            ALTER TABLE requests_p5_new RENAME TO requests;
            COMMIT;
            PRAGMA foreign_keys=on;
        """)
        conn.commit()

    # Phase 7B — add 'S' (Swap) to the requests.type CHECK. SQLite can't ALTER a
    # CHECK, so rebuild once (guarded: only when 'S' isn't already allowed).
    # Column-safe copy by intersection, same pattern as the P5 rebuild above.
    _rq_type_row = conn.execute(
        "SELECT sql FROM sqlite_master WHERE type='table' AND name='requests'"
    ).fetchone()
    if _rq_type_row and "'S'" not in (_rq_type_row["sql"] or ""):
        _old_cols = [r[1] for r in conn.execute("PRAGMA table_info(requests)").fetchall()]
        _new_cols = ["id", "customer_id", "site_id", "type", "bin_id", "size_requested",
                     "preferred_date", "notes", "status", "stop_id", "deny_reason",
                     "customer_note", "created_at", "updated_at"]
        _copy = [c for c in _new_cols if c in _old_cols]
        _copy_csv = ", ".join(_copy)
        conn.executescript(f"""
            PRAGMA foreign_keys=off;
            BEGIN;
            CREATE TABLE requests_p7_new (
                id             INTEGER PRIMARY KEY AUTOINCREMENT,
                customer_id    INTEGER NOT NULL,
                site_id        INTEGER NOT NULL,
                type           TEXT NOT NULL CHECK(type IN ('PR','P','D','NEW_BIN','S')),
                bin_id         INTEGER,
                size_requested TEXT,
                preferred_date TEXT NOT NULL,
                notes          TEXT,
                status         TEXT NOT NULL DEFAULT 'pending'
                    CHECK(status IN ('pending','accepted','approved','scheduled','in_progress','done','denied')),
                stop_id        INTEGER,
                deny_reason    TEXT,
                customer_note  TEXT,
                created_at     TEXT NOT NULL,
                updated_at     TEXT NOT NULL
            );
            INSERT INTO requests_p7_new ({_copy_csv}) SELECT {_copy_csv} FROM requests;
            DROP TABLE requests;
            ALTER TABLE requests_p7_new RENAME TO requests;
            COMMIT;
            PRAGMA foreign_keys=on;
        """)
        conn.commit()

    # Phase 5 §4 — customers can be deactivated (soft delete). Active by
    # default; deactivating hides them from management lists and kills portal
    # token access without destroying history.
    safe_add_column(conn, "customers", "is_active INTEGER NOT NULL DEFAULT 1")
    # NOTE: Phase 7 additive columns for inspection_items / maintenance_entries /
    # trucks / bins live AFTER those tables are created (search "_phase7_migrate")
    # — placing them here would no-op on a fresh DB's first init_db because the
    # target tables don't exist yet.

    # --- Per-route boss <-> driver messages: minimal thread, one row per
    #     message. "Unread" is derived per-viewer as "not sent by me and
    #     read_at IS NULL" rather than tracked per-recipient, since a route
    #     thread only ever has two participants. ---
    cur.execute("""
    CREATE TABLE IF NOT EXISTS messages (
        id             INTEGER PRIMARY KEY AUTOINCREMENT,
        route_id       INTEGER NOT NULL,
        sender_user_id INTEGER NOT NULL,
        body           TEXT NOT NULL,
        created_at     TEXT NOT NULL,
        read_at        TEXT,
        FOREIGN KEY (route_id) REFERENCES routes(id),
        FOREIGN KEY (sender_user_id) REFERENCES users(id)
    )
    """)

    # --- Password reset tokens: single-use, 1-hour expiry, only the hash is stored ---
    cur.execute("""
    CREATE TABLE IF NOT EXISTS password_reset_tokens (
        id         INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id    INTEGER NOT NULL,
        token_hash TEXT NOT NULL,
        created_at TEXT NOT NULL,
        expires_at TEXT NOT NULL,
        used_at    TEXT,
        FOREIGN KEY (user_id) REFERENCES users(id)
    )
    """)

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

    # =========================================================
    # CUSTOMER REQUEST SYSTEM (Phase 1 — data layer)
    #
    # Customers submit REQUESTS (intent only). A request never becomes
    # driver work until the boss approves it (approval flow is a future
    # phase). Customers authenticate ONLY by a URL portal_token — no
    # sessions, no passwords. company_id ties each customer to a company
    # so the boss/admin side stays company-scoped like the rest of the app.
    # =========================================================
    cur.execute("""
    CREATE TABLE IF NOT EXISTS customers (
        id            INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id    INTEGER NOT NULL,
        business_name TEXT,
        contact_name  TEXT,
        phone         TEXT,
        portal_token  TEXT NOT NULL UNIQUE,
        is_active     INTEGER NOT NULL DEFAULT 1,
        created_at    TEXT NOT NULL,
        FOREIGN KEY (company_id) REFERENCES companies(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS sites (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        customer_id INTEGER NOT NULL,
        address     TEXT,
        lat         REAL,
        lng         REAL,
        notes       TEXT,
        created_at  TEXT NOT NULL,
        FOREIGN KEY (customer_id) REFERENCES customers(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS bins (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        customer_id INTEGER NOT NULL,
        site_id     INTEGER NOT NULL,
        size        TEXT,
        dropped_at  TEXT,
        FOREIGN KEY (customer_id) REFERENCES customers(id),
        FOREIGN KEY (site_id) REFERENCES sites(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS requests (
        id             INTEGER PRIMARY KEY AUTOINCREMENT,
        customer_id    INTEGER NOT NULL,
        site_id        INTEGER NOT NULL,
        type           TEXT NOT NULL CHECK(type IN ('PR','P','D','NEW_BIN')),
        bin_id         INTEGER,
        size_requested TEXT,
        preferred_date TEXT NOT NULL,
        notes          TEXT,
        status         TEXT NOT NULL DEFAULT 'pending'
            CHECK(status IN ('pending','accepted','approved','scheduled','in_progress','done','denied')),
        stop_id        INTEGER,
        deny_reason    TEXT,
        customer_note  TEXT,
        created_at     TEXT NOT NULL,
        updated_at     TEXT NOT NULL,
        FOREIGN KEY (customer_id) REFERENCES customers(id),
        FOREIGN KEY (site_id) REFERENCES sites(id),
        FOREIGN KEY (bin_id) REFERENCES bins(id),
        FOREIGN KEY (stop_id) REFERENCES stops(id)
    )
    """)

    # =========================================================
    # Phase 6 — DVIR (Driver Vehicle Inspection Reports) + defect tracking.
    # Inspections are IMMUTABLE after submit; defect resolution is a separate
    # management follow-up layered on the inspection_items rows. All tables are
    # company-scoped. No ELD / Hours-of-Service / GPS — inspections only.
    # =========================================================
    cur.execute("""
    CREATE TABLE IF NOT EXISTS trucks (
        id             INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id     INTEGER NOT NULL,
        name           TEXT NOT NULL,
        make_model     TEXT,
        plate          TEXT,
        is_active      INTEGER NOT NULL DEFAULT 1,
        out_of_service INTEGER NOT NULL DEFAULT 0,
        oos_note       TEXT,
        oos_at         TEXT,
        oos_by         INTEGER,
        oos_inspection_id INTEGER,
        oos_cleared_note  TEXT,
        oos_cleared_at    TEXT,
        oos_cleared_by    INTEGER,
        created_at     TEXT NOT NULL,
        FOREIGN KEY (company_id) REFERENCES companies(id)
    )
    """)

    # Checklist template, stored as DATA (not hardcoded) so it can become
    # per-company-customizable later. company_id IS NULL == the shared default
    # roll-off template seeded below.
    cur.execute("""
    CREATE TABLE IF NOT EXISTS checklist_items (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id  INTEGER,
        label       TEXT NOT NULL,
        hint        TEXT,
        sort_order  INTEGER NOT NULL DEFAULT 0,
        is_active   INTEGER NOT NULL DEFAULT 1,
        created_at  TEXT NOT NULL
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS inspections (
        id             INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id     INTEGER NOT NULL,
        truck_id       INTEGER NOT NULL,
        driver_id      INTEGER NOT NULL,
        type           TEXT NOT NULL CHECK(type IN ('pre_trip','post_trip')),
        overall        TEXT NOT NULL CHECK(overall IN ('safe','defects_safe','out_of_service')),
        signature_name TEXT NOT NULL,
        created_at     TEXT NOT NULL,
        FOREIGN KEY (company_id) REFERENCES companies(id),
        FOREIGN KEY (truck_id)   REFERENCES trucks(id),
        FOREIGN KEY (driver_id)  REFERENCES users(id)
    )
    """)

    # One row per checklist item answered. label is snapshotted so a report is
    # immutable even if the template changes later. The defect_* columns are the
    # ONLY mutable fields — they carry management's follow-up (repair/defer) and
    # are not part of the driver's immutable report.
    cur.execute("""
    CREATE TABLE IF NOT EXISTS inspection_items (
        id                INTEGER PRIMARY KEY AUTOINCREMENT,
        inspection_id     INTEGER NOT NULL,
        checklist_item_id INTEGER,
        label             TEXT NOT NULL,
        result            TEXT NOT NULL CHECK(result IN ('pass','defect','na')),
        note              TEXT,
        photo_path        TEXT,
        defect_status     TEXT CHECK(defect_status IN ('open','repaired','deferred')),
        resolution_note   TEXT,
        resolved_by       INTEGER,
        resolved_at       TEXT,
        FOREIGN KEY (inspection_id) REFERENCES inspections(id)
    )
    """)

    # Seed the default roll-off pre-trip template once (idempotent: only if no
    # global template rows exist yet).
    _has_tmpl = conn.execute(
        "SELECT 1 FROM checklist_items WHERE company_id IS NULL LIMIT 1"
    ).fetchone()
    if not _has_tmpl:
        _ts = now_ts()
        conn.executemany(
            """INSERT INTO checklist_items (company_id, label, hint, sort_order, is_active, created_at)
               VALUES (NULL, ?, ?, ?, 1, ?)""",
            [(lbl, hint, i, _ts) for i, (lbl, hint) in enumerate(DEFAULT_CHECKLIST)],
        )
        conn.commit()

    # Phase 7A — manual (non-inspection) maintenance entries. Money is stored as
    # INTEGER CENTS (cost_cents), never a float. Editable by owner/dispatcher for
    # EDIT_WINDOW after creation, then locked; never deleted — a `voided` flag +
    # required note preserves the record.
    cur.execute("""
    CREATE TABLE IF NOT EXISTS maintenance_entries (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id  INTEGER NOT NULL,
        truck_id    INTEGER NOT NULL,
        entry_date  TEXT NOT NULL,
        category    TEXT NOT NULL,
        description TEXT NOT NULL,
        cost_cents  INTEGER,
        vendor      TEXT,
        created_by  INTEGER NOT NULL,
        created_at  TEXT NOT NULL,
        updated_at  TEXT,
        voided      INTEGER NOT NULL DEFAULT 0,
        void_note   TEXT,
        voided_by   INTEGER,
        voided_at   TEXT,
        FOREIGN KEY (company_id) REFERENCES companies(id),
        FOREIGN KEY (truck_id)   REFERENCES trucks(id)
    )
    """)

    # Receipt photos for maintenance — attaches to EITHER a repaired defect
    # (inspection_items.id) or a manual entry (maintenance_entries.id). Exactly
    # one of the two link columns is set. Multiple rows per record = multiple
    # receipts. Cost data → management-only serving.
    cur.execute("""
    CREATE TABLE IF NOT EXISTS maintenance_photos (
        id             INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id     INTEGER NOT NULL,
        defect_item_id INTEGER,
        manual_entry_id INTEGER,
        file_path      TEXT NOT NULL,
        uploaded_at    TEXT NOT NULL,
        uploaded_by    INTEGER,
        FOREIGN KEY (company_id) REFERENCES companies(id)
    )
    """)

    # Phase 7A revision — company vendor/shop accounts. Repairs & manual entries
    # can reference one (or stay in-house/blank). Many companies run on vendor
    # accounts and never enter costs, so the log's primary value is the event
    # trail, not dollars.
    cur.execute("""
    CREATE TABLE IF NOT EXISTS vendors (
        id         INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id INTEGER NOT NULL,
        name       TEXT NOT NULL,
        phone      TEXT,
        notes      TEXT,
        is_active  INTEGER NOT NULL DEFAULT 1,
        created_at TEXT NOT NULL,
        FOREIGN KEY (company_id) REFERENCES companies(id)
    )
    """)

    # _phase7_migrate — additive columns on tables created ABOVE in this same
    # init_db pass (inspection_items / maintenance_entries / trucks / bins), so
    # they exist on a fresh DB's very first boot, not only after a restart.
    # Money is INTEGER CENTS, never a float.
    safe_add_column(conn, "inspection_items", "cost_cents INTEGER")
    safe_add_column(conn, "inspection_items", "vendor TEXT")
    safe_add_column(conn, "inspection_items", "vendor_id INTEGER")
    safe_add_column(conn, "inspection_items", "at_vendor INTEGER NOT NULL DEFAULT 0")
    safe_add_column(conn, "inspection_items", "sent_vendor_id INTEGER")
    safe_add_column(conn, "inspection_items", "sent_at TEXT")
    safe_add_column(conn, "maintenance_entries", "vendor_id INTEGER")
    safe_add_column(conn, "maintenance_entries", "at_vendor INTEGER NOT NULL DEFAULT 0")
    safe_add_column(conn, "maintenance_entries", "sent_vendor_id INTEGER")
    safe_add_column(conn, "maintenance_entries", "sent_at TEXT")
    safe_add_column(conn, "maintenance_entries", "completed_at TEXT")
    safe_add_column(conn, "trucks", "at_vendor INTEGER NOT NULL DEFAULT 0")
    safe_add_column(conn, "bins", "label TEXT")
    safe_add_column(conn, "bins", "drop_photo_path TEXT")
    safe_add_column(conn, "bins", "drop_stop_id INTEGER")

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


# =========================================================
# PHASE 5 — ROLES (owner / customer_manager / dispatcher / driver)
#
# Management sub-roles are additive flags on top of the legacy role column.
# 'owner' expands to hold every management permission. These helpers are the
# single source of truth for "what can this user do", used by both the
# server-side guards (roles_required) and the nav (shell_page).
# =========================================================
MGMT_ROLES = ("owner", "customer_manager", "dispatcher")


def user_role_set(user_row):
    """Return the set of role strings a user holds. Owner expands to include
    customer_manager + dispatcher so downstream checks are simple membership
    tests. A driver account contributes 'driver'."""
    if user_row is None:
        return set()
    roles = set()
    # sqlite3.Row supports mapping access; use dict() for safe .get semantics
    u = dict(user_row)
    if u.get("role") == "driver":
        roles.add("driver")
    if u.get("role_owner"):
        roles.update(("owner", "customer_manager", "dispatcher"))
    if u.get("role_customer_manager"):
        roles.add("customer_manager")
    if u.get("role_dispatcher"):
        roles.add("dispatcher")
    # Backward-compat / safety net: a plain "boss" carrying none of the Phase 5
    # flags is a full-access owner (the pre-Phase-5 meaning of "boss"). This
    # covers a freshly-registered company owner and any "boss" created on the
    # team page before init_db's one-time promotion runs, so nobody is ever
    # locked out of the management UI between deploy and the next restart.
    if u.get("role") == "boss" and not (
        u.get("role_owner") or u.get("role_customer_manager") or u.get("role_dispatcher")
    ):
        roles.update(("owner", "customer_manager", "dispatcher"))
    return roles


def session_roles():
    """The current session's role set (stored at login), as a set."""
    return set(session.get("roles") or [])


def has_role(*needed):
    """True if the session holds any of `needed` (superadmin always passes)."""
    if session.get("is_superadmin"):
        return True
    return bool(session_roles().intersection(needed))


def role_landing_endpoint():
    """Where to send a user after login / on an access redirect, by role:
    customer_manager (without dispatcher/owner) -> Requests; dispatcher/owner
    -> Route Board; driver -> driver dashboard; fallback -> Owner dashboard."""
    r = session_roles()
    if "dispatcher" in r or "owner" in r:
        return "routes_page"
    if "customer_manager" in r:
        return "requests_page"
    if "driver" in r:
        return "driver_dashboard"
    return "dashboard"


def roles_required(*needed, api=False):
    """Guard a route by management role. Owner satisfies everything (its set
    already contains cm+dispatcher). On failure: API routes get a 403 JSON,
    pages flash + redirect to the user's own landing view. UI hiding is never
    the security boundary — this is."""
    def deco(fn):
        @wraps(fn)
        def wrapper(*args, **kwargs):
            if "user_id" not in session:
                if api:
                    return jsonify({"error": "login required"}), 401
                flash("Login required.", "error")
                return redirect(url_for("login"))
            if not has_role(*needed):
                if api:
                    return jsonify({"error": "forbidden"}), 403
                flash("You don't have access to that.", "error")
                return redirect(url_for(role_landing_endpoint()))
            return fn(*args, **kwargs)
        return wrapper
    return deco


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


def driver_active_route_id(conn, user_id):
    """Best current route for a driver: today's assigned route if open,
    else the earliest other open/in_progress route. Returns None if none."""
    row = conn.execute(
        """SELECT id FROM routes
           WHERE assigned_to=? AND status IN ('open','in_progress')
           ORDER BY (route_date = ?) DESC, route_date ASC, id ASC
           LIMIT 1""",
        (user_id, today_str())
    ).fetchone()
    return row["id"] if row else None


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
    "SWAP":     "Swap",
    "MOVE":     "Move",
}

# City shorthand codes (Hampton Roads / Tidewater Virginia)
# Short codes first so they match before full-name variants in linear lookups
_CITY_CODES = {
    "orf":         ("Norfolk",        "VA"),
    "norf":        ("Norfolk",        "VA"),
    "vb":          ("Virginia Beach", "VA"),
    "nb":          ("Virginia Beach", "VA"),
    "suff":        ("Suffolk",        "VA"),
    "ches":        ("Chesapeake",     "VA"),
    "port":        ("Portsmouth",     "VA"),
    "ports":       ("Portsmouth",     "VA"),
    "prt":         ("Portsmouth",     "VA"),
    "smith":       ("Smithfield",     "VA"),
    "hamp":        ("Hampton",        "VA"),
    "nn":          ("Newport News",   "VA"),
    "york":        ("Yorktown",       "VA"),
    "isle":        ("Isle of Wight",  "VA"),
    # Full city names (used in free-form text like RELOCATE lines, and now
    # also recognized by the roll-off shorthand gate below — see
    # _ROLLOFF_CITY_RE, built from this dict so a boss can type either the
    # short code or the full name and still get the precise parser)
    "norfolk":       ("Norfolk",        "VA"),
    "chesapeake":    ("Chesapeake",     "VA"),
    "portsmouth":    ("Portsmouth",     "VA"),
    "suffolk":       ("Suffolk",        "VA"),
    "hampton":       ("Hampton",        "VA"),
    "williamsburg":  ("Williamsburg",   "VA"),
    "smithfield":    ("Smithfield",     "VA"),
    "yorktown":      ("Yorktown",       "VA"),
    "gloucester":    ("Gloucester",     "VA"),
    "camden":        ("Camden",         "NC"),
    "currituck":     ("Currituck",      "NC"),
    "newport":       ("Newport News",   "VA"),
    "newport news":  ("Newport News",   "VA"),
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
_ROLLOFF_LINE_RE = re.compile(r"^(PR|PULL|DEL|DELIVERY|SWAP|MOVE|RELOCATE|RELOC|D|P|R)\s+(?=\d)", re.IGNORECASE)

# Matches the city-shorthand pattern that confirms roll-off format. Built
# from _CITY_CODES itself (short codes AND full names) so a line using
# either "vb" or "Virginia Beach" is recognized the same way, and so this
# never drifts out of sync with _CITY_CODES again — longest keys first so
# "newport news" matches before the shorter "newport" substring.
_ROLLOFF_CITY_ALTERNATION = "|".join(
    re.escape(_k) for _k in sorted(_CITY_CODES.keys(), key=len, reverse=True)
)
_ROLLOFF_CITY_RE = re.compile(
    r",\s*(" + _ROLLOFF_CITY_ALTERNATION + r")\s*,",
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
    r"|use\s+it\s+to\b"
    r"|use\s+this\s+(?:empty|can)\b"
    r"|use\s+the\s+can\s+to\b"
    r"|use\s+for\s+next\b"
    r"|before\s+you\s+return\b"
    r"|return\s+to\b"
    r"|take\s+empty\b"
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
    address   = parts[0].strip().title()
    city_code = parts[1].strip().lower() if len(parts) > 1 else ""
    rest      = parts[2].strip()         if len(parts) > 2 else ""

    city, state = _CITY_CODES.get(city_code, (city_code.title(), "VA"))

    # Extract container size first (before dump extraction changes text positions)
    container_size = ""
    size_m = re.search(r"\b(\d{1,2})\s*yd\b", rest, re.IGNORECASE)
    if size_m:
        container_size = size_m.group(1) + "yd"
        rest = (rest[:size_m.start()] + " " + rest[size_m.end():]).strip()
        rest = re.sub(r"\s+", " ", rest)

    # Extract dump site
    dump_site, rest = _extract_rolloff_dump(rest)

    # Split remaining text into customer name and driver notes
    customer_name, instruction_notes = _split_rolloff_customer_notes(rest)
    customer_name = customer_name.title() if customer_name else customer_name

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
        "stop_order":                   order_num,
        "original_line":                " ".join(block_lines),
        "customer_name":                customer_name,
        "address":                      address,
        "city":                         city,
        "state":                        state,
        "zip_code":                     "",
        "action":                       action,
        "service_type":                 action,
        "container_size":               container_size,
        "ticket_number":                "",
        "reference_number":             "",
        "phone":                        "",
        "dump_location":                dump_site,
        "notes":                        instruction_notes,
        "placement_note":               "",
        "relocate_from_address":        "",
        "relocate_to_address":          "",
        "from_address":                 "",
        "from_city":                    "",
        "to_address":                   "",
        "to_city":                      "",
        "return_destination":           "",
        "pr_mode":                      "",
        "swap_with_previous_empty":     False,
        "pending_empty_can_for_next_pr": False,
        "warnings":                     [],
        "confidence":                   _conf,
        "confidence_label":             _conf_label,
        "matched_saved":                False,
        "conf_reasons":                 ["rolloff"],
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
    r"^(PR|PULL|DEL|DELIVERY|SWAP|MOVE|RELOCATE|RELOC|P|D|R)\s+(?=\d)",
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
        container_size = sz.group(1) + "yd"
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
        "stop_order":                   order_num,
        "original_line":                None,
        "customer_name":                _cust,
        "address":                      _addr,
        "city":                         city,
        "state":                        state,
        "zip_code":                     "",
        "action":                       action,
        "service_type":                 action,
        "container_size":               container_size,
        "ticket_number":                "",
        "reference_number":             "",
        "dump_location":                dump_location,
        "notes":                        notes.strip(),
        "placement_note":               "",
        "relocate_from_address":        "",
        "relocate_to_address":          "",
        "from_address":                 "",
        "from_city":                    "",
        "to_address":                   "",
        "to_city":                      "",
        "return_destination":           "",
        "pr_mode":                      "",
        "swap_with_previous_empty":     False,
        "pending_empty_can_for_next_pr": False,
        "warnings":                     [],
        "confidence":                   _conf,
        "confidence_label":             _conf_label,
        "matched_saved":                False,
        "conf_reasons":                 ["inline"],
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
# Matches: "relocate [can] <from> to <to>"
#          "move one [of the Xs] [from] <from> to <to>"
#          "move the can/container <from> to <to>"
_RELOCATE_TO_RE = re.compile(
    r"^(?:relocate|reloc"
    r"|move\s+one"
    r"|move\s+the\s+(?:can|container)"
    r"|move\s+can"
    r")\s+(.+?)\s+to\s+(.+)$",
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
    # Strip a redundant "can" token that sometimes appears between the keyword
    # and the address, e.g. "relocate can 100 main st" → "relocate 100 main st"
    work = re.sub(
        r"^(relocate|reloc|move\s+one|move\s+the\s+(?:can|container)|move\s+can)\s+can\s+",
        r"\1 ", work, flags=re.I
    )
    m = _RELOCATE_TO_RE.match(work)
    if not m:
        return None

    from_raw = m.group(1).strip()
    to_raw   = m.group(2).strip()

    def _extract_fields(text):
        """Pull size, dump site, city, and placement note from an address fragment."""
        # Container size: "30yd", "30 yd", or "one of the 20s" / "20s" with prefix
        sz = ""
        sz_m = re.search(
            r"\b(\d{1,2})\s*(?:yd|yds|yards?)\b"
            r"|\bone\s+of\s+the\s+(\d{1,2})s\b",
            text, re.I
        )
        if sz_m:
            sz = (sz_m.group(1) or sz_m.group(2)) + "yd"
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

        # Placement note: "place it on the street", "place it in gated lot", etc.
        placement_note = ""
        pm = re.search(
            r"\bplace\s+it\s+(?:on|in|at)\s+(?:the\s+)?(?:street|gated\s+lot|lot|driveway|yard|alley|curb|road|side\s+lot|back\s+lot)\b"
            r"|\bplace\s+(?:it\s+)?(?:on|in)\s+(?:the\s+)?(?:street|gated\s+lot|lot|driveway|yard|alley|curb)\b",
            text, re.I
        )
        if pm:
            placement_note = pm.group(0).strip()
            text = re.sub(r"\s+", " ", text[:pm.start()] + " " + text[pm.end():]).strip()

        city = state = ""
        for code, (city_name, state_code) in _CITY_CODES.items():
            mc = re.search(r"(?:(?<=\s)|^)" + re.escape(code) + r"(?=\s|$)", text, re.I)
            if mc:
                city  = city_name
                state = state_code
                text  = re.sub(r"\s+", " ", text[:mc.start()] + " " + text[mc.end():]).strip()
                break

        # Strip leading "from" or "at" preposition left after size/city extraction
        text = re.sub(r"^(?:from|at)\s+", "", text.strip(), flags=re.I)

        return text.strip(), sz, dump, city, state, placement_note

    from_addr, from_sz, from_dump, from_city, from_state, from_note = _extract_fields(from_raw)
    to_addr,   to_sz,   to_dump,   to_city,   _,           to_note   = _extract_fields(to_raw)

    # Prefer size / dump from whichever side had them; from-side wins ties
    container_size = from_sz   or to_sz
    dump_location  = from_dump or to_dump
    city           = from_city or to_city
    state          = from_state
    placement_note = to_note   or from_note

    # Build driver-facing note
    loc_from = f"{from_addr} ({from_city})" if from_city else from_addr
    loc_to   = f"{to_addr} ({to_city})"     if to_city   else to_addr
    notes = f"From: {loc_from} → To: {loc_to}"
    if placement_note:
        notes += f" | {placement_note}"

    return {
        "stop_order":                   order_num,
        "original_line":                raw,
        "customer_name":                "",
        "address":                      from_addr,
        "city":                         city,
        "state":                        state,
        "zip_code":                     "",
        "action":                       "Relocate",
        "service_type":                 "Relocate",
        "container_size":               container_size,
        "ticket_number":                "",
        "reference_number":             "",
        "dump_location":                dump_location,
        "notes":                        notes,
        "placement_note":               placement_note,
        "relocate_from_address":        from_addr,
        "relocate_to_address":          to_addr,
        "from_address":                 from_addr,
        "from_city":                    from_city,
        "to_address":                   to_addr,
        "to_city":                      to_city,
        "return_destination":           "",
        "pr_mode":                      "",
        "swap_with_previous_empty":     False,
        "pending_empty_can_for_next_pr": False,
        "warnings":                     [],
        "confidence":                   75,
        "confidence_label":             "high",
        "matched_saved":                False,
        "conf_reasons":                 ["relocate"],
    }


# ─── Move on-site parser ─────────────────────────────────────────────────────
# Handles: "Move the can into gated lot at 744 E 25th St Norfolk SICE 30yd"
#          "Reposition the container onto the street at 100 Main St vb customer 20yd"
_MOVE_LINE_RE = re.compile(
    r"^(?:move\s+(?:the\s+)?(?:can|it|container)\s+|reposition\s+(?:(?:the|it|can|container)\s+)?)",
    re.I,
)
_PLACEMENT_RE = re.compile(
    r"\b(?:into|onto|on|in)\s+(?:the\s+)?(?:gated\s+lot|lot|street|driveway|yard|side\s+lot|"
    r"back\s+lot|alley|curb|road|front|right\s+side|left\s+side)\b",
    re.I,
)


def _parse_move_line(raw, order_num=1):
    """Parse a MOVE-on-site line (can repositioned within the same property/area).

    Structure: MOVE [the can/it] [placement phrase] [at] [address] [customer] [size]

    Returns a stop dict with action='Move' and placement_note set, or None if
    the line does not look like a MOVE instruction.
    """
    work = raw.strip()
    m_start = _MOVE_LINE_RE.match(work)
    if not m_start:
        return None
    body = work[m_start.end():].strip()

    # Extract container size
    container_size = ""
    sz_m = re.search(r"\b(\d{1,2})\s*(?:yd|yds|yards?)\b|\bone\s+of\s+the\s+(\d{1,2})s\b", body, re.I)
    if sz_m:
        container_size = (sz_m.group(1) or sz_m.group(2)) + "yd"
        body = re.sub(r"\s+", " ", body[:sz_m.start()] + " " + body[sz_m.end():]).strip()

    # Extract placement note (e.g. "into the gated lot")
    placement_note = ""
    pm = _PLACEMENT_RE.search(body)
    if pm:
        placement_note = pm.group(0).strip()
        body = re.sub(r"\s+", " ", body[:pm.start()] + " " + body[pm.end():]).strip()

    # Strip leading "at" preposition before address
    body = re.sub(r"^at\s+", "", body, flags=re.I).strip()

    # City extraction
    city = state = ""
    for code, (city_name, state_code) in _CITY_CODES.items():
        mc = re.search(r"(?:(?<=\s)|^)" + re.escape(code) + r"(?=\s|$)", body, re.I)
        if mc:
            city  = city_name
            state = state_code
            body  = re.sub(r"\s+", " ", body[:mc.start()] + " " + body[mc.end():]).strip()
            break

    # Split "HOUSE_NUM STREET [CUSTOMER]" at last street suffix
    address = customer_name = ""
    house_m = re.match(r"\d+\s+", body)
    if house_m:
        sfx_m = None
        for sfx in _STREET_SFX_RE.finditer(body):
            sfx_m = sfx
        if sfx_m:
            address  = body[:sfx_m.end()].strip()
            rest     = body[sfx_m.end():].strip()
        else:
            words    = body.split()
            n        = min(4, len(words))
            address  = " ".join(words[:n])
            rest     = " ".join(words[n:])
        customer_name = rest.strip()
    else:
        customer_name = body

    notes = f"Move on-site: {placement_note}" if placement_note else "Move on-site"

    conf = 50
    if address:        conf += 15
    if city:           conf += 10
    if customer_name:  conf += 10
    if container_size: conf += 10
    conf = min(100, conf)

    return {
        "stop_order":                   order_num,
        "original_line":                raw,
        "customer_name":                customer_name,
        "address":                      address,
        "city":                         city,
        "state":                        state,
        "zip_code":                     "",
        "action":                       "Move",
        "service_type":                 "Move",
        "container_size":               container_size,
        "ticket_number":                "",
        "reference_number":             "",
        "dump_location":                "",
        "notes":                        notes,
        "placement_note":               placement_note,
        "relocate_from_address":        "",
        "relocate_to_address":          "",
        "from_address":                 "",
        "from_city":                    "",
        "to_address":                   "",
        "to_city":                      "",
        "return_destination":           "",
        "pr_mode":                      "",
        "swap_with_previous_empty":     False,
        "pending_empty_can_for_next_pr": False,
        "warnings":                     [],
        "confidence":                   conf,
        "confidence_label":             "high" if conf >= 75 else ("medium" if conf >= 45 else "low"),
        "matched_saved":                False,
        "conf_reasons":                 ["move-action"],
    }


# ─── Top-level parser dispatcher ──────────────────────────────────────────────

def _is_relocate_format(lines):
    """Return True when ALL non-empty lines are relocate-style (relocate X to Y)."""
    return (
        lines
        and all(_RELOCATE_TO_RE.match(l) for l in lines)
    )


# Patterns that signal "use this empty can for the NEXT PR stop"
_PENDING_EMPTY_RE = re.compile(
    r"\b(?:use\s+it\s+to\b"
    r"|use\s+it\s+for\s+next\b"
    r"|use\s+this\s+(?:empty|can)\b"
    r"|use\s+this\s+can\s+to\b"
    r"|use\s+the\s+can\s+to\b"
    r"|use\s+for\s+next\b"
    r"|before\s+you\s+return\b"
    r"|take\s+empty\b)\b",
    re.I,
)
# Matches whole annotation lines that should NOT become stops
# e.g. "Use pulled can from previous stop", "use it for the swap"
_ANNOTATION_LINE_RE = re.compile(
    r"^\s*(?:use\s+(?:pulled\s+)?can\b"
    r"|use\s+(?:it|this|the)\s+(?:pulled\s+)?can\b"
    r"|use\s+(?:it|this)\s+(?:to|for)\b"
    r"|use\s+for\s+next\b"
    r"|before\s+you\s+return\b"
    r"|take\s+(?:the\s+)?empty\b"
    r"|leave\s+(?:the\s+)?(?:can|empty)\b)",
    re.I,
)
# Pattern for "return to <destination>" in notes
_RETURN_TO_RE = re.compile(r"\breturn\s+to\s+(.+)", re.I)


def _apply_swap_inference(stops):
    """Post-process a stop list to detect cross-stop SWAP / pending-empty patterns.

    Carries a pending_swap flag past non-PR stops so the NEXT PR stop after a
    trigger phrase receives the SWAP mark, regardless of intervening stops.
    """
    pending_swap = False  # carries until consumed by a PR stop

    for stop in stops:
        notes     = stop.get("notes") or ""
        notes_lc  = notes.lower()
        action_lc = (stop.get("action") or "").lower()
        is_pr     = "pickup and return" in action_lc

        # Detect "return to <dest>"
        rt = _RETURN_TO_RE.search(notes)
        if rt:
            stop["return_destination"] = rt.group(1).strip().rstrip(".")

        # Check for trigger phrase before applying swap (order matters for chaining)
        this_triggers = bool(_PENDING_EMPTY_RE.search(notes_lc))

        # Apply pending swap to the next PR stop
        if is_pr and pending_swap:
            stop["swap_with_previous_empty"] = True
            stop["pr_mode"]                  = "swap"
            stop["swap_with_prev_pull"]      = 1
            pending_swap = False

        # Set pending if this stop has a trigger phrase
        if this_triggers:
            stop["pending_empty_can_for_next_pr"] = True
            pending_swap = True

    return stops


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
            mv = _parse_move_line(merged, idx)
            if mv:
                stops.append(mv)
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

    stops = _apply_swap_inference(stops)
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


# Boss-only: keep the nav "Requests" badge live without a full reload. Plain
# (non-f) string so its JS braces don't collide with the sidebar f-string.
_REQ_BADGE_POLLER_JS = """
<script>
(function(){
  function poll(badgeId, status){
    var badge = document.getElementById(badgeId);
    if (!badge) return;
    fetch('/api/requests?status=' + status, {headers:{'X-Requested-With':'XMLHttpRequest'}})
      .then(function(r){ return r.ok ? r.json() : null; })
      .then(function(list){
        if (!Array.isArray(list)) return;
        if (list.length > 0){ badge.textContent = list.length; badge.hidden = false; }
        else { badge.hidden = true; }
      })
      .catch(function(){ /* offline/transient — retry next cycle */ });
  }
  function pollCount(badgeId, url){
    var badge = document.getElementById(badgeId);
    if (!badge) return;
    fetch(url, {headers:{'X-Requested-With':'XMLHttpRequest'}})
      .then(function(r){ return r.ok ? r.json() : null; })
      .then(function(d){
        if (!d || typeof d.count !== 'number') return;
        if (d.count > 0){ badge.textContent = d.count; badge.hidden = false; }
        else { badge.hidden = true; }
      })
      .catch(function(){ /* offline/transient — retry next cycle */ });
  }
  function refresh(){
    poll('req-nav-badge','pending');
    poll('unassigned-nav-badge','accepted');
    pollCount('maint-nav-badge','/api/defects/open-count');
  }
  refresh();
  setInterval(refresh, 45000);
})();
</script>
"""


def shell_page(title, body, extra_head=""):
    user = get_current_user()
    path = request.path

    sidebar = ""
    if user:
        _co_name = session.get("company_name", "") if user["company_id"] else ""

        # ── Primary top-nav items (role-aware) ──────────────────────────
        if user["role"] == "boss":
            _rset   = user_role_set(user)
            is_disp = "dispatcher" in _rset
            is_cm   = "customer_manager" in _rset
            is_own  = "owner" in _rset

            def _nav_badge(bid, n):
                return (
                    '<span id="%s" style="display:inline-block;min-width:16px;padding:1px 6px;'
                    'margin-left:6px;border-radius:999px;background:var(--cyan);color:#121212;'
                    'font-size:10px;font-weight:800;line-height:16px;text-align:center;'
                    'vertical-align:middle;"%s>%s</span>'
                    % (bid, "" if n else " hidden", n or "")
                )

            _rc = get_db()
            _pending_reqs = _rc.execute(
                """SELECT COUNT(*) AS n FROM requests r
                     JOIN customers c ON r.customer_id = c.id
                    WHERE c.company_id = ? AND r.status = 'pending'""",
                (session.get("company_id"),),
            ).fetchone()["n"] if is_cm else 0
            _unassigned = _rc.execute(
                """SELECT COUNT(*) AS n FROM requests r
                     JOIN customers c ON r.customer_id = c.id
                    WHERE c.company_id = ? AND r.status = 'accepted'""",
                (session.get("company_id"),),
            ).fetchone()["n"] if is_disp else 0
            # Open-defect count — Maintenance is visible to any management role.
            _open_defects = _rc.execute(
                """SELECT COUNT(*) AS n FROM inspection_items ii
                     JOIN inspections i ON ii.inspection_id = i.id
                    WHERE i.company_id = ? AND ii.result='defect' AND ii.defect_status='open'""",
                (session.get("company_id"),),
            ).fetchone()["n"]
            _rc.close()

            _parts = []
            if is_disp:
                _parts.append(nav_link('/parser', '✦ Parser', path))
                _parts.append(nav_link(url_for("routes_page"), 'Route Board', path))
                _parts.append(nav_link(url_for("unassigned_work"),
                              '📋 Unassigned' + _nav_badge('unassigned-nav-badge', _unassigned), path))
            if is_cm:
                _parts.append(nav_link(url_for("requests_page"),
                              '✉ Requests' + _nav_badge('req-nav-badge', _pending_reqs), path))
                _parts.append(nav_link(url_for("customers_page"), '👤 Customers', path))
            if is_disp:
                _parts.append(nav_link(url_for("bin_tracker"), 'Bin Tracker', path))
            # Maintenance/defects — any management role can view.
            _parts.append(nav_link(url_for("maintenance_page"),
                          '🔧 Maintenance' + _nav_badge('maint-nav-badge', _open_defects), path))
            if is_own:
                _parts.append(nav_link(url_for("dashboard"), 'Owner', path))
            primary_items = "".join(_parts)
            # NOTE: unassigned_work + customers_page routes are defined in the
            # same module (sections 3 & 4); url_for resolves them at request
            # time, so ordering within the file doesn't matter.
        else:
            _cab_conn = get_db()
            _active_route_id = driver_active_route_id(_cab_conn, user["id"])
            _cab_conn.close()
            cab_href = (url_for('driver_route_detail', route_id=_active_route_id)
                        if _active_route_id else url_for('driver_dashboard'))
            # Driver nav is deliberately work-DOING only — no parser / dispatch
            # tooling (that creates or assigns work) is reachable from here.
            primary_items = (
                nav_link(url_for("dashboard"), 'My Day', path)
                + nav_link(cab_href, 'Cab View', path)
                + nav_link(url_for("inspection_new"), '🔧 Inspection', path)
            )

        # ── Overflow "More" items (role-aware) ───────────────────────────
        # Boss "More" is deliberately limited to these three — Driver Hours now
        # lives per-row on Team, and Boss Panel / Orders / Live Dispatch keep
        # working at their old URLs but no longer have a nav entry (see PR notes).
        if user["role"] == "boss":
            _mparts = []
            # Trucks/fleet — any management role can view (add/edit is gated
            # server-side to owner/dispatcher).
            _mparts.append(nav_link(url_for("trucks_page"), "🚛 Trucks", path))
            _mparts.append(nav_link(url_for("vendors_page"), "🔧 Vendors", path))
            if is_disp:
                _mparts.append(nav_link(url_for("team_page"), "👥 Team", path))
            if is_own:
                _mparts.append(nav_link(url_for("yard_setup_page"), "🏗 Yard Setup", path))
                _mparts.append(nav_link(url_for("settings_page"), "⚙ Settings", path))
            more_items = "".join(_mparts)
        else:
            more_items = (
                nav_link(url_for("driver_dashboard"), "◈ My Routes", path)
                + nav_link(url_for("my_inspections"), "🛠 My Inspections", path)
                + nav_link(url_for("driver_clock"), "⏱ Clock In/Out", path)
            )

        superadmin_link = nav_link(url_for("superadmin_panel"), "🔧 Superadmin", path) \
            if session.get("is_superadmin") else ""

        co_pill = (f'<span class="company-pill">{e(_co_name)}</span>') if _co_name else ""

        sidebar = f"""
        <nav class="topnav">
            <div class="topnav-inner">
                <a href="/" class="topnav-brand">
                    <span class="logo-h">H</span><span class="logo-rest">AULTRA</span>
                    <span class="topnav-brand-sub">AI</span>
                </a>
                <div class="topnav-links">
                    {primary_items}
                </div>
                <div class="topnav-right">
                    <details class="topnav-more">
                        <summary class="nav-item">More &#9662;</summary>
                        <div class="topnav-more-menu">
                            <div class="topnav-more-user">
                                {e(user['username'])} &middot; {e(user['role'])}
                            </div>
                            {more_items}
                            {superadmin_link}
                            <form method="POST" action="{url_for('logout')}" style="margin:0;padding:0;">
                                <button type="submit" class="nav-item nav-logout">⏻ Logout</button>
                            </form>
                        </div>
                    </details>
                    {co_pill}
                </div>
            </div>
        </nav>
        """
        # Live pending-requests badge poll (every 45s), boss only. Mirrors the
        # existing message-badge poll pattern; no-op if the badge isn't present.
        if user["role"] == "boss":
            sidebar += _REQ_BADGE_POLLER_JS

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
    <meta name="theme-color" content="#121212">
    <meta name="csrf-token" content="{csrf_token}">

    <link rel="manifest" href="/static/manifest.json">
    <link rel="apple-touch-icon" href="/static/icon-512.png">
    <link rel="icon" href="/static/icon-192.png" sizes="192x192">
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
    <link rel="stylesheet" href="/static/css/haultra-theme.css">

    {extra_head}
     <style>
/* ═══════════════════════════════════════════════════════════
   HAULTRA AI — ROCKKSTAAR COMMAND CENTER THEME
   ═══════════════════════════════════════════════════════════ */

/* ── Reset ─────────────────────────────────────────────────*/
*, *::before, *::after {{ box-sizing: border-box; margin: 0; padding: 0; }}

/* ── Design Tokens ─────────────────────────────────────────*/
:root {{
  --bg:          #121212;
  --bg-card:     rgba(23,23,23,0.92);
  --bg-sidebar:  #141414;
  --border:      rgba(255,107,26,0.12);
  --border-glow: rgba(255,107,26,0.30);
  /* NOTE: --cyan is now the PRIMARY (safety-orange) accent token, kept under its
     original name to avoid touching the hundreds of var(--cyan) references below.
     Electric teal (--teal) is reserved exclusively for AI-touched elements. */
  --cyan:        #FF6B1A;
  --cyan-dim:    rgba(255,107,26,0.14);
  --teal:        #00E5CC;
  --teal-dim:    rgba(0,229,204,0.12);
  --teal-border: rgba(0,229,204,0.45);
  --gold:        #FF6B1A;
  --gold-dim:    rgba(255,107,26,0.14);
  --slate:       #8CA0B3;
  --slate-dim:   rgba(140,160,179,0.16);
  --slate-border: rgba(140,160,179,0.45);
  --green:       #3DDC84;
  --red:         #FF5252;
  --text:        #F5F5F0;
  --text-muted:  #78786F;
  --text-soft:   #A6A69E;
  --radius:      12px;
  --radius-lg:   16px;
  --font-head:   'Bebas Neue', 'Anton', sans-serif;
  --font-body:   'Inter', -apple-system, 'Segoe UI', Arial, sans-serif;
  --font-mono:   'JetBrains Mono', 'SFMono-Regular', Consolas, 'Liberation Mono', Menlo, monospace;
}}

/* ── Base ───────────────────────────────────────────────────*/
html {{ background: var(--bg); scroll-behavior: smooth; }}

html, body {{
    width: 100%; min-height: 100%; overflow-x: hidden;
}}

body {{
    font-family: var(--font-body);
    font-size: 14px;
    line-height: 1.5;
    color: var(--text);
    background: var(--bg);
    /* subtle warm backdrop glow, flat charcoal otherwise (matches /parser) */
    background-image:
        radial-gradient(ellipse 100% 60% at 20% -5%,  rgba(255,107,26,0.045) 0%, transparent 65%),
        radial-gradient(ellipse  40% 30% at 50%  50%, rgba(0,0,0,0.6) 0%, transparent 100%);
    background-attachment: fixed;
}}

a {{ color: var(--cyan); text-decoration: none; transition: color .15s; }}
a:hover {{ color: #FF9D5C; }}

/* ── App Shell ──────────────────────────────────────────────*/
.app-shell {{ display: flex; flex-direction: column; min-height: 100vh; width: 100%; }}

/* ══════════════════════════════════════════════════════════
   TOP NAV
   ══════════════════════════════════════════════════════════*/
.topnav {{
    background: var(--bg-sidebar);
    border-bottom: 1px solid var(--border);
    position: sticky;
    top: 0;
    z-index: 200;
    box-shadow: 0 1px 0 rgba(255,107,26,0.05), 0 2px 20px rgba(0,0,0,0.4);
}}

.topnav-inner {{
    display: flex;
    align-items: center;
    gap: 18px;
    max-width: 1400px;
    margin: 0 auto;
    padding: 10px 20px;
}}

/* ── Brand ──────────────────────────────────────────────────*/
.topnav-brand {{
    display: flex;
    align-items: baseline;
    gap: 6px;
    line-height: 1;
    flex-shrink: 0;
}}

.logo-wordmark {{ display: flex; align-items: baseline; gap: 1px; line-height: 1; }}

.logo-icon {{
    font-size: 11px;
    font-weight: 900;
    letter-spacing: 1px;
    color: var(--gold);
    background: linear-gradient(135deg, #FF6B1A, #FFA35C);
    -webkit-background-clip: text;
    -webkit-text-fill-color: transparent;
    background-clip: text;
    margin-right: 6px;
    opacity: 0.85;
}}

.logo-h, .logo-rest {{
    font-family: var(--font-head);
    font-size: 19px;
    font-weight: 400;
    letter-spacing: 2px;
    background: linear-gradient(130deg, #ffffff 0%, #F5F5F0 55%, #FF6B1A 100%);
    -webkit-background-clip: text;
    -webkit-text-fill-color: transparent;
    background-clip: text;
    text-shadow: none;
}}
.logo-h {{ filter: drop-shadow(0 0 10px rgba(255,107,26,0.35)); }}

.logo-sub, .topnav-brand-sub {{
    font-size: 8.5px;
    font-weight: 700;
    letter-spacing: 2.5px;
    color: #55554C;
    text-transform: uppercase;
    align-self: center;
    margin-left: 2px;
}}

/* ── Primary links ────────────────────────────────────────── */
.topnav-links {{
    display: flex;
    align-items: center;
    gap: 2px;
    flex: 1;
    min-width: 0;
    overflow-x: auto;
    scrollbar-width: none;
}}
.topnav-links .nav-item {{ flex-shrink: 0; }}
.topnav-brand, .topnav-right {{ flex-shrink: 0; }}
.topnav-links::-webkit-scrollbar {{ display: none; }}

.nav-item {{
    display: inline-flex;
    align-items: center;
    white-space: nowrap;
    padding: 10px 14px;
    min-height: 48px;
    border-radius: 9px;
    background: transparent;
    border: 1px solid transparent;
    color: #8C8C82;
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
    background: rgba(255,107,26,0.06);
    border-color: rgba(255,107,26,0.12);
    color: #E0E0D8;
    text-decoration: none;
}}

.nav-item.active {{
    background: linear-gradient(180deg, rgba(255,107,26,0.13) 0%, rgba(255,107,26,0.04) 100%);
    border-color: rgba(255,107,26,0.25);
    color: var(--cyan);
    font-weight: 700;
}}

/* bottom accent bar on active (top-nav orientation) */
.nav-item.active::before {{
    content: '';
    position: absolute;
    left: 16%; right: 16%; bottom: 2px;
    height: 2px;
    border-radius: 2px;
    background: var(--cyan);
    box-shadow: 0 0 8px var(--cyan);
}}

.nav-logout {{
    color: #FF9A9A !important;
    margin-top: 4px;
}}
.nav-logout:hover {{
    background: rgba(255,50,50,0.10) !important;
    border-color: rgba(255,60,60,0.20) !important;
    color: #FF6B6B !important;
}}

/* ── Right side: More dropdown + company pill ────────────────*/
.topnav-right {{
    display: flex;
    align-items: center;
    gap: 10px;
    flex-shrink: 0;
}}

.topnav-more {{ position: relative; }}
.topnav-more > summary {{
    list-style: none;
    user-select: none;
}}
.topnav-more > summary::-webkit-details-marker {{ display: none; }}

.topnav-more-menu {{
    position: absolute;
    top: calc(100% + 8px);
    right: 0;
    min-width: 220px;
    background: var(--bg-card);
    border: 1px solid rgba(255,107,26,0.18);
    border-radius: var(--radius);
    padding: 10px;
    display: flex;
    flex-direction: column;
    gap: 2px;
    box-shadow: 0 12px 40px rgba(0,0,0,0.55);
    z-index: 250;
}}
.topnav-more-menu .nav-item {{ width: 100%; display: flex; }}

.topnav-more-user {{
    font-size: 11px;
    font-weight: 700;
    letter-spacing: .4px;
    color: #55554C;
    text-transform: uppercase;
    padding: 6px 10px 8px;
    border-bottom: 1px solid rgba(255,107,26,0.08);
    margin-bottom: 4px;
}}

.company-pill {{
    font-size: 11.5px;
    font-weight: 700;
    letter-spacing: .3px;
    color: var(--text-soft);
    background: rgba(255,255,255,0.03);
    border: 1px solid rgba(255,107,26,0.14);
    border-radius: 20px;
    padding: 7px 14px;
    white-space: nowrap;
}}

/* ══════════════════════════════════════════════════════════
   MAIN CONTENT
   ══════════════════════════════════════════════════════════*/
.content {{ flex: 1; width: 100%; max-width: 1400px; margin: 0 auto; padding: 28px 32px; min-width: 0; box-sizing: border-box; }}

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
    border: 1px solid rgba(255,107,26,0.14);
    border-radius: var(--radius-lg);
    padding: 28px 30px;
    margin-bottom: 22px;
    background: linear-gradient(145deg, rgba(23,23,23,0.97) 0%, rgba(18,18,18,0.99) 100%);
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
        rgba(255,107,26,0.7) 25%,
        rgba(255,107,26,0.9) 45%,
        rgba(255,107,26,0.9) 65%,
        rgba(255,107,26,0.5) 80%,
        transparent 100%);
}}

/* subtle corner glow */
.hero::after {{
    content: '';
    position: absolute;
    top: -40px; right: -40px;
    width: 200px; height: 200px;
    background: radial-gradient(circle, rgba(255,107,26,0.06) 0%, transparent 70%);
    pointer-events: none;
}}

.hero h1 {{
    font-family: var(--font-head);
    font-size: 30px;
    font-weight: 400;
    color: #F5F5F0;
    letter-spacing: .5px;
    margin-bottom: 5px;
    line-height: 1.15;
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
    border: 1px solid rgba(255,107,26,0.10);
    border-radius: var(--radius-lg);
    padding: 22px;
    margin-bottom: 16px;
    box-shadow: 0 2px 24px rgba(0,0,0,0.35);
}}

.card h2 {{
    font-size: 14px;
    font-weight: 700;
    letter-spacing: .2px;
    color: #A6A69E;
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
    background: rgba(20,20,20,0.70);
    border: 1px solid rgba(255,107,26,0.12);
    border-radius: var(--radius);
    padding: 18px 20px 16px;
    overflow: hidden;
    transition: border-color .2s, box-shadow .2s;
}}

.stat:hover {{
    border-color: rgba(255,107,26,0.22);
    box-shadow: 0 0 20px rgba(255,107,26,0.05);
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
    font-family: var(--font-head);
    font-size: 42px;
    font-weight: 400;
    color: #F5F5F0;
    line-height: 1;
    margin-top: 6px;
    letter-spacing: .5px;
}}

/* ══════════════════════════════════════════════════════════
   BUTTONS
   ══════════════════════════════════════════════════════════*/
.btn,
button:not(.nav-item):not(.btn-reassign):not([class*="btn-driver"]):not(.compact-select):not(.cab-copy-btn):not(.cab-gear-btn):not(.lane-message-btn) {{
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
    /* default = safety orange (primary/commit) */
    color: #1A1000;
    background: linear-gradient(135deg, #FF8A42 0%, #FF6B1A 100%);
    box-shadow: 0 0 18px rgba(255,107,26,0.22);
}}

.btn:hover,
button:not(.nav-item):not(.btn-reassign):not([class*="btn-driver"]):not(.compact-select):not(.cab-copy-btn):not(.cab-gear-btn):not(.lane-message-btn):hover {{
    filter: brightness(1.1);
    transform: translateY(-1px);
    text-decoration: none;
    color: #1A1000;
    box-shadow: 0 0 24px rgba(255,107,26,0.34);
}}

/* secondary — dark glass */
.btn.secondary {{
    background: rgba(26,26,26,0.90);
    border: 1px solid rgba(255,107,26,0.20);
    color: #C9C9C0;
    box-shadow: none;
}}
.btn.secondary:hover {{ color: #F0F0E8; filter: none; border-color: rgba(255,107,26,0.35); }}

/* gold — priority actions */
.btn.gold, .btn.orange {{
    background: linear-gradient(135deg, #FF8A42 0%, #FF6B1A 100%);
    color: #1A1000;
    box-shadow: 0 0 18px rgba(255,107,26,0.24);
}}
.btn.gold:hover, .btn.orange:hover {{
    filter: brightness(1.08);
    box-shadow: 0 0 28px rgba(255,107,26,0.38);
    color: #1A1000;
}}

/* green */
.btn.green {{
    background: linear-gradient(135deg, #3DDC84 0%, #22B368 100%);
    color: #06170D;
    box-shadow: 0 0 14px rgba(61,220,132,0.20);
}}
.btn.green:hover {{ filter: brightness(1.08); color: #06170D; }}

/* red / danger */
.btn.red {{
    background: linear-gradient(135deg, #FF5252 0%, #CC3333 100%);
    color: #1A0000;
    box-shadow: none;
}}
.btn.red:hover {{ filter: brightness(1.1); color: #1A0000; }}

/* ── Forms ──────────────────────────────────────────────────*/
form.inline {{ display: inline; }}

label {{
    display: block;
    font-weight: 600;
    font-size: 11px;
    letter-spacing: .5px;
    text-transform: uppercase;
    color: #8C8C82;
    margin-top: 14px;
    margin-bottom: 6px;
}}

input, textarea, select {{
    width: 100%;
    padding: 11px 14px;
    border-radius: 9px;
    border: 1px solid rgba(255,107,26,0.14);
    background: rgba(18,18,18,0.80);
    color: var(--text);
    font-size: 13px;
    font-family: inherit;
    transition: border-color .15s, box-shadow .15s;
}}

input:focus, textarea:focus, select:focus {{
    outline: none;
    border-color: rgba(255,107,26,0.40);
    box-shadow: 0 0 0 3px rgba(255,107,26,0.07);
}}

textarea {{ min-height: 130px; resize: vertical; }}

/* ── Tables ─────────────────────────────────────────────────*/
table {{ width: 100%; border-collapse: collapse; }}

th {{
    padding: 9px 12px;
    border-bottom: 1px solid rgba(255,107,26,0.10);
    text-align: left;
    font-size: 10px;
    font-weight: 700;
    letter-spacing: 1px;
    text-transform: uppercase;
    color: #55554C;
}}

td {{
    padding: 12px 12px;
    border-bottom: 1px solid rgba(255,255,255,0.033);
    vertical-align: middle;
    font-size: 13px;
    color: #D8D8D0;
}}

td a {{ color: #FF9D5C; font-weight: 600; }}
td a:hover {{ color: #FFB37A; }}

tr:hover td {{ background: rgba(255,107,26,0.025); }}
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
    background: rgba(140,160,179,0.16);
    border: 1px solid rgba(140,160,179,0.45);
    color: #ADC0D1;
}}

.badge.in_progress {{
    background: rgba(255,107,26,0.14);
    border: 1px solid rgba(255,107,26,0.45);
    color: #FF9D5C;
}}

.badge.completed {{
    background: rgba(61,220,132,0.12);
    border: 1px solid rgba(61,220,132,0.32);
    color: #3DDC84;
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
    border: 1px solid rgba(61,220,132,0.28);
    color: #5cffa7;
}}
.flash.error {{
    background: rgba(100,10,20,0.45);
    border: 1px solid rgba(255,60,80,0.22);
    color: #FF9A9A;
}}

/* ── Stop cards (boss route view) ───────────────────────────*/
.stop-card {{
    background: rgba(20,20,20,0.82);
    border: 1px solid rgba(255,107,26,0.12);
    border-radius: var(--radius);
    padding: 16px;
    margin-bottom: 10px;
}}

.next-stop-glow {{
    border-color: rgba(255,107,26,0.42);
    box-shadow: 0 0 22px rgba(255,107,26,0.09);
}}

.stop-handle {{
    cursor: grab;
    background: rgba(255,107,26,0.28);
    border: 1px solid rgba(255,107,26,0.16);
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
    border: 1px solid rgba(255,107,26,0.18); display: block;
}}
.photo-gallery {{ display: flex; flex-wrap: wrap; gap: 10px; margin-top: 10px; }}
.photo-item {{
    display: flex; flex-direction: column; align-items: center;
    background: rgba(255,255,255,0.025);
    border: 1px solid rgba(255,107,26,0.10);
    border-radius: 9px; padding: 8px; width: 160px;
}}
.photo-meta {{ font-size: 11px; color: #8C8C82; text-align: center; margin-top: 5px; line-height: 1.4; word-break: break-all; }}
.photo-pdf-link {{
    display: flex; align-items: center; justify-content: center;
    width: 140px; height: 80px;
    background: var(--cyan-dim); border: 1px solid rgba(255,107,26,0.18);
    border-radius: 8px; color: var(--cyan); text-decoration: none;
    font-size: 13px; font-weight: 600; gap: 6px;
}}
.photo-pdf-link:hover {{ background: rgba(255,107,26,0.18); }}

/* ── Progress mini bar ──────────────────────────────────────*/
.mini-prog-track {{
    width: 80px; height: 5px;
    background: rgba(255,255,255,0.06);
    border-radius: 3px; overflow: hidden; flex-shrink: 0;
}}
.mini-prog-fill {{
    height: 100%;
    background: linear-gradient(90deg, #FF8A42, #FF6B1A);
    border-radius: 3px; transition: width .4s;
}}

/* ── Inline reassign ────────────────────────────────────────*/
.inline-reassign {{ display: flex; align-items: center; gap: 6px; flex-wrap: nowrap; }}
.compact-select {{
    font-size: 12px; padding: 4px 8px; border-radius: 6px;
    background: rgba(18,18,18,0.82); border: 1px solid rgba(255,107,26,0.16);
    color: #B8B8AE; max-width: 130px;
}}
.btn-reassign {{
    font-size: 12px; padding: 4px 10px; border-radius: 6px;
    background: rgba(255,107,26,0.22); border: 1px solid rgba(255,107,26,0.20);
    color: #B8B8AE; cursor: pointer; white-space: nowrap;
    transition: background .13s;
}}
.btn-reassign:hover {{ background: rgba(255,107,26,0.38); }}
tr.status-in-progress td {{ background: rgba(255,107,26,0.03); }}

/* ── Footer ─────────────────────────────────────────────────*/
.footer-note {{
    text-align: center; color: #4A4A42; font-size: 11px;
    margin-top: 40px; padding: 16px 0 6px;
    border-top: 1px solid rgba(255,107,26,0.05); line-height: 2;
}}
.footer-note a {{ color: #4A4A42; margin: 0 6px; }}
.footer-note a:hover {{ color: var(--cyan); }}
.footer-trust {{ display: flex; justify-content: center; gap: 12px; flex-wrap: wrap; margin-bottom: 8px; }}
.footer-badge {{
    display: inline-flex; align-items: center; gap: 4px;
    font-size: 10px; color: #4A4A42;
    background: rgba(255,255,255,0.015);
    border: 1px solid rgba(255,107,26,0.06);
    border-radius: 20px; padding: 3px 10px;
}}

/* ══════════════════════════════════════════════════════════
   OWNER DASHBOARD — diesel-gauge stat cards, bar chart, inventory
   ══════════════════════════════════════════════════════════*/
.owner-header-row {{
    display: flex; align-items: flex-start; justify-content: space-between;
    flex-wrap: wrap; gap: 12px;
}}

.gauge-stat {{
    position: relative;
    background: rgba(20,20,20,0.70);
    border: 1px solid rgba(255,255,255,0.06);
    border-top: 3px solid var(--cyan);
    border-radius: var(--radius);
    padding: 18px 20px 16px;
}}
.gauge-stat .label {{
    font-size: 10px; font-weight: 700; letter-spacing: 1px;
    text-transform: uppercase; color: var(--text-muted);
}}
.gauge-stat .num {{
    font-family: var(--font-head); font-size: 40px; font-weight: 400;
    color: #F5F5F0; line-height: 1; margin-top: 8px; letter-spacing: .5px;
}}
.gauge-stat .num.red   {{ color: var(--red); }}
.gauge-stat .num.dim   {{ color: #55554C; }}
.gauge-stat .sub {{ font-size: 11px; color: var(--text-muted); margin-top: 6px; }}

.bar-chart-row {{
    display: flex; align-items: center; gap: 10px; margin-bottom: 12px;
}}
.bar-chart-row:last-child {{ margin-bottom: 0; }}
.bar-chart-label {{
    width: 100px; flex-shrink: 0; font-size: 12px; font-weight: 600;
    color: #D8D8D0; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
}}
.bar-chart-track {{
    flex: 1; height: 20px; background: rgba(255,255,255,0.04);
    border-radius: 5px; overflow: hidden; position: relative;
}}
.bar-chart-fill {{
    height: 100%; background: linear-gradient(90deg, #FF8A42, #FF6B1A);
    border-radius: 5px; min-width: 3px; transition: width .4s;
}}
.bar-chart-value {{
    width: 30px; flex-shrink: 0; text-align: right;
    font-size: 12.5px; font-weight: 700; color: #F5F5F0;
}}

.inv-row {{ margin-bottom: 14px; }}
.inv-row:last-child {{ margin-bottom: 0; }}
.inv-row-top {{
    display: flex; justify-content: space-between; align-items: baseline;
    margin-bottom: 5px; font-size: 12.5px;
}}
.inv-row-size {{ font-weight: 700; color: #F5F5F0; }}
.inv-row-count {{ color: var(--text-muted); font-size: 11.5px; }}
.inv-track {{
    height: 8px; background: rgba(255,255,255,0.05);
    border-radius: 4px; overflow: hidden;
}}
.inv-fill {{
    height: 100%; border-radius: 4px;
    background: linear-gradient(90deg, #FF8A42, #FF6B1A);
    transition: width .4s;
}}

/* ══════════════════════════════════════════════════════════
   BIN TRACKER
   ══════════════════════════════════════════════════════════*/
.bin-tracker-grid {{
    display: grid; grid-template-columns: 1.1fr 1fr; gap: 18px;
    align-items: start;
}}
@media (max-width: 900px) {{ .bin-tracker-grid {{ grid-template-columns: 1fr; }} }}

.bin-map-col {{ position: sticky; top: 76px; }}
@media (max-width: 900px) {{ .bin-map-col {{ position: static; }} }}

.bin-map-stub {{
    background: rgba(18,18,18,0.9);
    border: 1px dashed rgba(255,107,26,0.22);
    border-radius: var(--radius-lg);
    min-height: 360px;
    display: flex; flex-direction: column; align-items: center; justify-content: center;
    text-align: center; padding: 30px;
}}
.bin-map-stub-icon {{ font-size: 40px; opacity: .5; margin-bottom: 10px; }}
.bin-map-stub-title {{ font-family: var(--font-head); font-size: 22px; letter-spacing: .5px; color: #D8D8D0; }}
.bin-map-stub-sub {{ font-size: 12.5px; color: var(--text-muted); margin-top: 8px; max-width: 320px; line-height: 1.6; }}

.bin-map {{
    height: 460px;
    border-radius: var(--radius-lg);
    border: 1px solid rgba(255,107,26,0.18);
    overflow: hidden;
    background: #121212;
}}
@media (max-width: 900px) {{ .bin-map {{ height: 300px; }} }}
.bin-map-note {{
    margin-top: 10px; font-size: 12px; color: var(--text-muted);
    background: rgba(255,107,26,0.06); border: 1px solid rgba(255,107,26,0.15);
    border-radius: var(--radius-sm); padding: 10px 12px; line-height: 1.5;
}}
.bin-no-map {{ font-size: 11px; color: var(--text-muted); margin-top: 8px; }}

/* Dark-theme the Leaflet chrome so it matches the app instead of Leaflet's
   default white popups/controls */
.leaflet-popup-content-wrapper, .leaflet-popup-tip {{
    background: #1A1A1A; color: #F5F5F0;
    box-shadow: 0 4px 24px rgba(0,0,0,0.5);
}}
.leaflet-popup-content-wrapper {{ border: 1px solid rgba(255,107,26,0.22); border-radius: 10px; }}
.leaflet-popup-content {{ margin: 12px 14px; font-size: 13px; line-height: 1.5; }}
.leaflet-container a.leaflet-popup-close-button {{ color: #A6A69E; }}
.leaflet-bar a, .leaflet-bar a:hover {{
    background: #1A1A1A; color: #F5F5F0; border-bottom: 1px solid rgba(255,255,255,0.1);
}}
.leaflet-control-attribution {{ background: rgba(18,18,18,0.75) !important; color: #78786F !important; }}
.leaflet-control-attribution a {{ color: #A6A69E !important; }}

.bin-list-header {{
    display: flex; justify-content: space-between; align-items: flex-start;
    margin-bottom: 14px; flex-wrap: wrap; gap: 8px;
}}
.bin-list-title {{ font-family: var(--font-head); font-size: 22px; letter-spacing: 1px; color: #F5F5F0; }}
.bin-list-sub {{ font-size: 10.5px; font-weight: 700; letter-spacing: 1.5px; color: var(--text-muted); text-transform: uppercase; }}
.bin-list-stats {{ font-size: 13px; color: var(--text-muted); text-align: right; }}
.bin-count {{ font-family: var(--font-head); font-size: 22px; color: var(--cyan); margin-right: 4px; }}
.bin-overdue-count {{ display: block; color: var(--red); font-size: 11.5px; font-weight: 700; margin-top: 2px; }}

.bin-list {{ display: flex; flex-direction: column; gap: 10px; max-height: 74vh; overflow-y: auto; }}
.bin-card {{
    background: rgba(20,20,20,0.75);
    border: 1px solid rgba(255,255,255,0.07);
    border-radius: var(--radius);
    padding: 14px 16px;
}}
.bin-card.overdue {{ border-color: rgba(255,82,82,0.45); background: rgba(255,82,82,0.05); }}
.bin-card-top {{ display: flex; justify-content: space-between; align-items: center; margin-bottom: 6px; }}
.bin-days {{ font-weight: 700; font-size: 13px; letter-spacing: .2px; color: #D8D8D0; }}
.bin-days.overdue {{ color: var(--red); }}
.bin-size {{ font-size: 11px; font-weight: 700; color: var(--text-muted); background: rgba(255,255,255,0.05); padding: 2px 8px; border-radius: 20px; }}
.bin-addr {{ font-family: var(--font-mono); font-size: 13px; color: #F5F5F0; }}
.bin-customer {{ font-size: 12px; color: var(--text-muted); margin-top: 2px; }}
.bin-overdue-tag {{ font-size: 11px; font-weight: 700; color: var(--red); margin-top: 8px; letter-spacing: .3px; }}

/* ══════════════════════════════════════════════════════════
   CAB VIEW — single-stop mobile-first driver flow
   ══════════════════════════════════════════════════════════*/
.cab-wrap {{ max-width: 560px; margin: 0 auto; }}
.cab-header {{ display: flex; align-items: center; justify-content: space-between; margin-bottom: 14px; }}
.cab-title {{ font-family: var(--font-head); font-size: 26px; letter-spacing: 1px; color: #F5F5F0; }}
.cab-online-badge {{
    display: inline-flex; align-items: center; gap: 6px;
    font-size: 11px; font-weight: 700; letter-spacing: .5px; text-transform: uppercase;
    background: rgba(61,220,132,0.12); border: 1px solid rgba(61,220,132,0.35);
    color: var(--green); border-radius: 20px; padding: 5px 12px;
}}
.cab-gear-btn {{
    display: inline-flex; align-items: center; justify-content: center;
    min-width: 48px; min-height: 48px;
    background: rgba(255,255,255,0.06); border: 1px solid rgba(255,255,255,0.1);
    border-radius: 10px; color: #D8D8D0; font-size: 18px; cursor: pointer;
}}
.cab-gear-btn:hover {{ background: rgba(255,107,26,0.14); border-color: rgba(255,107,26,0.3); }}
.cab-online-dot {{ width: 7px; height: 7px; border-radius: 50%; background: var(--green); box-shadow: 0 0 6px var(--green); }}

.cab-progress-label {{ font-size: 12px; font-weight: 700; letter-spacing: 1px; color: var(--text-muted); text-transform: uppercase; margin-bottom: 6px; }}
.cab-progress-track {{ height: 8px; background: rgba(255,255,255,0.06); border-radius: 4px; overflow: hidden; margin-bottom: 22px; }}
.cab-progress-fill {{ height: 100%; background: linear-gradient(90deg, #FF8A42, #FF6B1A); border-radius: 4px; transition: width .4s; }}

.route-updated-banner {{
    display: flex; align-items: center; justify-content: space-between; gap: 10px;
    background: var(--cyan-dim); border: 1px solid rgba(255,107,26,0.4);
    border-radius: 10px; padding: 10px 14px; margin-bottom: 14px;
    font-size: 13px; font-weight: 600; color: #FF9D5C;
}}
.route-updated-banner[hidden] {{ display: none; }}
.route-updated-banner button {{
    background: none; border: none; color: #FF9D5C; cursor: pointer;
    font-size: 18px; line-height: 1; padding: 4px 6px; min-width: 32px; min-height: 32px;
}}

.cab-card {{
    background: rgba(20,20,20,0.85);
    border: 1px solid rgba(255,107,26,0.16);
    border-radius: var(--radius-lg);
    padding: 24px 22px;
    margin-bottom: 18px;
}}
.cab-action-row {{ display: flex; align-items: center; gap: 12px; margin-bottom: 18px; }}
.cab-action-badge {{
    min-width: 56px; min-height: 56px; display: flex; align-items: center; justify-content: center;
    font-family: var(--font-head); font-size: 22px; border-radius: 12px; flex-shrink: 0;
}}
.cab-action-badge.pickup {{ background: var(--cyan-dim); color: var(--cyan); border: 1px solid rgba(255,107,26,0.5); }}
.cab-action-badge.dropswap {{ background: rgba(140,160,179,0.16); color: #8CA0B3; border: 1px solid rgba(140,160,179,0.45); }}
.cab-action-name {{ font-size: 15px; font-weight: 700; color: #D8D8D0; letter-spacing: .3px; }}

.cab-address {{
    font-family: var(--font-mono); font-size: 26px; font-weight: 700;
    color: #F5F5F0; line-height: 1.3; word-break: break-word; margin-bottom: 10px;
}}
.cab-meta-line {{ font-size: 14px; color: var(--text-muted); margin-bottom: 4px; }}
.cab-meta-line strong {{ color: #D8D8D0; }}

.cab-nav-btn {{
    display: flex; align-items: center; justify-content: center; gap: 10px;
    width: 100%; min-height: 56px; margin-top: 18px;
    background: linear-gradient(135deg, #FF8A42 0%, #FF6B1A 100%);
    color: #1A1000; font-weight: 800; font-size: 16px; letter-spacing: .3px;
    border-radius: 12px; text-decoration: none;
    box-shadow: 0 4px 20px rgba(255,107,26,0.25);
}}
.cab-nav-btn:hover {{ color: #1A1000; filter: brightness(1.06); }}

.cab-copy-btn {{
    display: flex; align-items: center; justify-content: center; gap: 10px;
    width: 100%; min-height: 52px; margin-top: 10px;
    background: rgba(255,255,255,0.06); border: 1px solid rgba(255,255,255,0.14);
    color: #D8D8D0; font-weight: 700; font-size: 14px; letter-spacing: .2px;
    border-radius: 12px; cursor: pointer;
}}
.cab-copy-btn:hover {{ background: rgba(255,255,255,0.1); }}
.cab-copy-hint {{ font-size: 11.5px; color: var(--text-muted); text-align: center; margin-top: 8px; line-height: 1.5; }}

.cab-photo-status {{ font-size: 12.5px; color: var(--text-muted); text-align: center; margin-top: 14px; }}
.cab-photo-status.ready {{ color: var(--green); }}

.cab-complete-btn {{
    width: 100%; min-height: 56px; margin-top: 10px;
    background: linear-gradient(135deg, #3DDC84 0%, #22B368 100%);
    color: #06170D; font-weight: 800; font-size: 16px; border: none; border-radius: 12px;
    cursor: pointer;
}}
.cab-complete-btn:disabled {{ background: rgba(255,255,255,0.06); color: #55554C; cursor: not-allowed; box-shadow: none; }}

.cab-all-done {{
    text-align: center; padding: 60px 20px;
}}
.cab-all-done-icon {{ font-size: 48px; margin-bottom: 14px; }}
.cab-all-done h2 {{ font-family: var(--font-head); font-size: 30px; letter-spacing: .5px; color: #F5F5F0; }}

/* Photo-proof "Encouraged" nudge (Cab View: complete with zero photos) */
.no-photo-confirm-overlay {{
    position: fixed; inset: 0; background: rgba(0,0,0,0.7); z-index: 400;
}}
.no-photo-confirm-modal {{
    position: fixed; left: 50%; top: 50%; transform: translate(-50%,-50%);
    width: min(340px, 88vw);
    background: #171717; border: 1px solid rgba(255,107,26,0.28);
    border-radius: 16px; padding: 22px 22px 18px; z-index: 401;
    box-shadow: 0 20px 60px rgba(0,0,0,0.8); text-align: center;
}}
.no-photo-confirm-title {{ font-size: 17px; font-weight: 700; color: #F5F5F0; margin-bottom: 6px; }}
.no-photo-confirm-body {{ font-size: 13.5px; color: var(--text-muted); margin-bottom: 18px; }}
.no-photo-confirm-actions {{ display: flex; flex-direction: column; gap: 10px; }}
.no-photo-confirm-actions .btn {{ width: 100%; min-height: 48px; }}

/* Message thread — shared by Cab View (Message Boss) and Route Board (per-lane) */
.msg-modal {{
    position: fixed; left: 50%; top: 50%; transform: translate(-50%,-50%);
    width: min(420px, 92vw); max-height: 82vh; display: flex; flex-direction: column;
    background: #171717; border: 1px solid rgba(255,107,26,0.28);
    border-radius: 16px; padding: 18px 18px 16px; z-index: 401;
    box-shadow: 0 20px 60px rgba(0,0,0,0.8);
}}
.msg-modal[hidden] {{ display: none; }}
.msg-modal-header {{
    display: flex; align-items: center; justify-content: space-between;
    margin-bottom: 12px; flex-shrink: 0;
}}
.msg-modal-header #msg-modal-title {{ font-size: 15px; font-weight: 700; color: #F5F5F0; }}
.msg-modal-header button {{
    background: none; border: none; color: #78786F; cursor: pointer;
    font-size: 22px; line-height: 1; padding: 4px 8px; min-width: 40px; min-height: 40px;
}}
.msg-quick-taps {{ display: flex; flex-wrap: wrap; gap: 6px; margin-bottom: 12px; flex-shrink: 0; }}
.msg-quick-btn {{
    min-height: 40px; padding: 8px 12px; font-size: 12px; font-weight: 600;
    color: #FF9D5C; background: rgba(255,107,26,0.12);
    border: 1px solid rgba(255,107,26,0.3); border-radius: 20px; cursor: pointer;
}}
.msg-quick-btn:hover {{ background: rgba(255,107,26,0.2); }}
.msg-list {{
    flex: 1; overflow-y: auto; min-height: 120px; max-height: 40vh;
    display: flex; flex-direction: column; gap: 8px; margin-bottom: 12px;
    padding-right: 2px;
}}
.msg-empty {{ color: var(--text-muted); font-size: 13px; text-align: center; padding: 24px 0; }}
.msg-bubble {{ max-width: 82%; padding: 8px 12px; border-radius: 12px; font-size: 13.5px; line-height: 1.4; }}
.msg-bubble-meta {{ font-size: 10px; font-weight: 700; text-transform: uppercase; letter-spacing: .3px; opacity: .65; margin-bottom: 2px; }}
.msg-them {{ align-self: flex-start; background: rgba(255,255,255,0.07); color: #F0F0E8; border-bottom-left-radius: 3px; }}
.msg-me {{
    align-self: flex-end; background: linear-gradient(135deg, #FF8A42 0%, #FF6B1A 100%);
    color: #1A1000; border-bottom-right-radius: 3px;
}}
.msg-compose {{ display: flex; gap: 8px; flex-shrink: 0; }}
.msg-compose textarea {{
    flex: 1; resize: none; min-height: 48px; max-height: 100px;
    background: var(--bg-0); border: 1px solid rgba(255,255,255,0.12);
    border-radius: 10px; color: var(--text); font-family: inherit; font-size: 13px; padding: 10px 12px;
}}
.msg-compose .btn {{ min-height: 48px; align-self: flex-end; }}

/* Driver workflow buttons (Cab View: Arrived / Box In-Out / Go To Dump) */
.btn-driver {{
    display: block; width: 100%; min-height: 52px; padding: 14px 16px;
    border-radius: 12px; font-size: 15px; font-weight: 800; text-align: center;
    border: none; cursor: pointer; text-decoration: none; line-height: 1.2;
    box-sizing: border-box;
}}
.btn-driver-nav, .btn-driver-complete, .btn-driver-dump {{
    background: linear-gradient(135deg, #FF8A42 0%, #FF6B1A 100%);
    color: #1A1000;
}}
.btn-driver-apple {{
    background: rgba(26,26,26,0.85);
    border: 1px solid rgba(140,160,179,0.18);
    color: #8C8C82;
}}
.btn-driver-reopen {{
    background: rgba(38,38,35,0.85);
    border: 1px solid rgba(255,107,26,0.22);
    color: #B8B8AE;
}}
.upload-details {{ margin: 10px 0; }}
.upload-details summary {{
    color: #B8B8AE; font-size: 13px; font-weight: 600; cursor: pointer;
    padding: 8px 0; list-style: none;
}}
.upload-details summary::-webkit-details-marker {{ display: none; }}
.upload-details input[type="file"] {{
    background: rgba(20,20,20,0.7); border: 1px solid rgba(255,255,255,0.12);
    border-radius: 9px; padding: 10px; color: #D8D8D0; font-size: 12.5px;
}}

/* ══════════════════════════════════════════════════════════
   ROUTE BOARD — driver lanes
   ══════════════════════════════════════════════════════════*/
.route-tabs {{ display: flex; gap: 8px; margin-bottom: 18px; }}
.route-tab {{
    background: rgba(26,26,26,0.85); border: 1px solid rgba(255,107,26,0.16);
    color: #A6A69E; font-weight: 700; font-size: 12.5px; letter-spacing: .3px;
    padding: 9px 18px; border-radius: 9px; text-decoration: none;
}}
.route-tab.active {{
    background: linear-gradient(135deg, #FF8A42 0%, #FF6B1A 100%);
    color: #1A1000; border-color: transparent;
}}

.board-legend {{ display: flex; align-items: center; gap: 16px; flex-wrap: wrap; }}
.board-legend-item {{ display: flex; align-items: center; gap: 6px; font-size: 11px; color: var(--text-muted); font-weight: 600; }}
.board-legend-dot {{ width: 9px; height: 9px; border-radius: 3px; flex-shrink: 0; }}
.board-legend-dot.pickup {{ background: var(--cyan); }}
.board-legend-dot.dropswap {{ background: var(--slate); }}
.board-legend-dot.urgent {{ background: var(--red); }}

.board-empty {{
    text-align: center; padding: 60px 24px; color: var(--text-muted);
    background: rgba(20,20,20,0.6); border: 1px dashed rgba(255,107,26,0.2);
    border-radius: var(--radius-lg);
}}
.board-empty p {{ margin-bottom: 18px; font-size: 14px; }}

.lane {{
    display: flex; gap: 18px; align-items: stretch;
    background: rgba(20,20,20,0.68); border: 1px solid rgba(255,255,255,0.06);
    border-radius: var(--radius); padding: 16px; margin-bottom: 14px;
}}
.lane-driver {{ width: 170px; flex-shrink: 0; }}
.lane-name-row {{ display: flex; align-items: center; gap: 8px; }}
.lane-status-dot {{ width: 8px; height: 8px; border-radius: 50%; flex-shrink: 0; background: #55554C; }}
.lane-status-dot.active {{ background: var(--cyan); box-shadow: 0 0 6px var(--cyan); }}
.lane-status-dot.done {{ background: var(--green); box-shadow: 0 0 6px var(--green); }}
.lane-name {{
    font-family: var(--font-head); font-size: 19px; letter-spacing: .5px;
    text-transform: uppercase; color: #F5F5F0;
}}
.lane-sub {{ font-size: 11.5px; color: var(--text-muted); margin-top: 4px; line-height: 1.5; }}
.lane-actions {{ display: flex; flex-wrap: wrap; gap: 8px; margin-top: 10px; }}
.lane-add-stops {{
    display: inline-flex; align-items: center; min-height: 30px;
    padding: 5px 12px; font-size: 11px; font-weight: 700;
    color: var(--cyan); background: var(--cyan-dim);
    border: 1px solid rgba(255,107,26,0.35); border-radius: 20px;
    text-decoration: none; white-space: nowrap;
}}
.lane-add-stops:hover {{ background: rgba(255,107,26,0.24); color: #FFB37A; }}
.lane-message-btn {{
    display: inline-flex; align-items: center; gap: 5px; min-height: 30px;
    padding: 5px 12px; font-size: 11px; font-weight: 700;
    color: #C9C9C0; background: rgba(255,255,255,0.06);
    border: 1px solid rgba(255,255,255,0.14); border-radius: 20px;
    cursor: pointer; white-space: nowrap;
}}
.lane-message-btn:hover {{ background: rgba(255,255,255,0.1); }}
.lane-msg-badge {{
    display: inline-flex; align-items: center; justify-content: center;
    min-width: 16px; height: 16px; padding: 0 4px;
    background: var(--red); color: #1A0000; font-size: 10px; font-weight: 800;
    border-radius: 9px;
}}

.lane-track {{
    display: flex; gap: 10px; overflow-x: auto; flex: 1; min-width: 0;
    padding-bottom: 4px; scroll-snap-type: x proximity;
}}

.stop-mini {{
    flex-shrink: 0; scroll-snap-align: start;
    width: 190px; min-height: 48px;
    background: rgba(26,26,26,0.85); border: 1px solid rgba(255,255,255,0.08);
    border-left: 3px solid #55554C; border-radius: var(--radius-sm);
    padding: 10px 12px; text-decoration: none; display: block;
    transition: border-color .15s, transform .1s;
}}
.stop-mini:hover {{ transform: translateY(-1px); border-color: rgba(255,107,26,0.4); }}
.stop-mini.st-done    {{ border-left-color: var(--green); }}
.stop-mini.st-enroute {{ border-left-color: var(--cyan); }}
.stop-mini.st-pending {{ border-left-color: #55554C; }}

.stop-mini-top {{ display: flex; align-items: center; justify-content: space-between; gap: 6px; margin-bottom: 6px; }}
.stop-mini-badge {{
    font-size: 10px; font-weight: 800; letter-spacing: .4px;
    padding: 2px 6px; border-radius: 5px; flex-shrink: 0;
}}
.stop-mini-badge.pickup   {{ background: var(--cyan-dim); color: var(--cyan); border: 1px solid rgba(255,107,26,.4); }}
.stop-mini-badge.dropswap {{ background: rgba(140,160,179,0.16); color: #8CA0B3; border: 1px solid rgba(140,160,179,0.4); }}
.stop-mini-badge.neutral  {{ background: rgba(255,255,255,0.06); color: #A6A69E; border: 1px solid rgba(255,255,255,0.1); }}
.stop-mini-urgent {{ font-size: 9px; font-weight: 800; color: var(--red); letter-spacing: .3px; white-space: nowrap; }}
.stop-mini-addr {{ font-size: 12px; color: #D8D8D0; line-height: 1.35; margin-bottom: 6px; min-height: 32px; }}
.stop-mini-addr.done {{ text-decoration: line-through; color: #6B6B62; }}
.stop-mini-bottom {{ display: flex; align-items: center; justify-content: space-between; gap: 6px; }}
.stop-mini-size {{ font-size: 10.5px; color: var(--text-muted); font-weight: 600; }}
.stop-mini-pill {{
    font-size: 9.5px; font-weight: 800; letter-spacing: .3px; text-transform: uppercase;
    padding: 2px 7px; border-radius: 999px;
}}
.stop-mini-pill.done    {{ background: rgba(61,220,132,0.14); color: var(--green); }}
.stop-mini-pill.enroute {{ background: rgba(255,107,26,0.16); color: #FF9D5C; }}
.stop-mini-pill.pending {{ background: rgba(255,255,255,0.06); color: #A6A69E; }}
.stop-mini-time {{ font-size: 10px; color: var(--text-muted); margin-top: 4px; }}

/* ══════════════════════════════════════════════════════════
   RESPONSIVE
   ══════════════════════════════════════════════════════════*/
@media (max-width: 900px) {{
    .content {{ padding: 16px; }}
    .topnav-inner {{ padding: 8px 12px; gap: 10px; }}
    .nav-item {{ padding: 10px 11px; font-size: 12.5px; }}
    .company-pill {{ display: none; }}
    .grid {{ grid-template-columns: repeat(2, 1fr); }}
    .lane {{ flex-direction: column; }}
    .lane-driver {{ width: 100%; }}
}}

@media (max-width: 560px) {{
    .topnav-brand-sub {{ display: none; }}
    .logo-h, .logo-rest {{ font-size: 16px; }}
    .cab-address {{ font-size: 21px; }}
    .cab-card {{ padding: 18px 16px; }}
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

  /* Routes queued when offline */
  var QUEUE_PAT = [
    /^\\/stop\\/\\d+\\/driver-action$/,
    /^\\/stop\\/\\d+\\/toggle$/,
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
    ok:    'background:#001810;border-bottom:1px solid rgba(0,232,125,.30);color:#3DDC84;',
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
      'background:#060e1e;border:1px solid rgba(255,107,26,.3);border-radius:14px;' +
      'padding:16px 18px;font-size:12px;color:#B8B8AE;font-family:monospace;' +
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
        '<div style="font-size:14px;font-weight:700;color:#3DDC84;margin-bottom:10px;">' +
        '&#128203; HAULTRA Debug' +
        '<button onclick="document.getElementById(\'haul-debug-panel\').style.display=\'none\'" ' +
        'style="float:right;background:none;border:none;color:#B8B8AE;cursor:pointer;font-size:16px;">&#10005;</button>' +
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

        try:
            conn = get_db()
            # Case-insensitive, whitespace-trimmed match — the #1 silent login
            # killer is a username that differs only by case from how it was
            # typed at signup.
            user = conn.execute(
                "SELECT * FROM users WHERE username = ? COLLATE NOCASE", (username,)
            ).fetchone()
            conn.close()
        except Exception as exc:
            # A real server/DB error is NOT the same thing as wrong credentials —
            # don't let it masquerade as "invalid login" or the real cause never
            # gets diagnosed. Log it, show a distinct message, don't leak detail.
            app.logger.error("login: unexpected error looking up user %r: %s", username, exc)
            flash("Something went wrong on our end — please try again in a moment.", "error")
            return redirect(url_for("login"))

        if user and check_password_hash(user["password_hash"], password):
            session.clear()
            session["user_id"]       = user["id"]
            session["username"]      = user["username"]
            session["role"]          = user["role"]
            session["roles"]         = sorted(user_role_set(user))
            session["company_id"]    = user["company_id"]
            session["is_superadmin"] = bool(user["is_superadmin"])
            _co_conn = get_db()
            _co_row = _co_conn.execute(
                "SELECT name, subscription_plan FROM companies WHERE id=?",
                (user["company_id"],)
            ).fetchone()
            _co_conn.close()
            if _co_row:
                session["company_name"] = _co_row["name"]
                session["company_plan"] = _co_row["subscription_plan"]
            flash("Logged in.", "success")

            if user["role"] == "driver":
                return redirect(url_for("driver_dashboard"))

            # Land management users on the view their roles grant:
            # customer_manager -> Requests, dispatcher/owner -> Route Board.
            return redirect(url_for(role_landing_endpoint()))

        # Wrong username or wrong password both land here, with the same
        # message — never reveal which one was wrong.
        flash("Username or password incorrect.", "error")
        return redirect(url_for("login"))

    body = f"""
    <div style="min-height:calc(100vh - 60px);display:flex;align-items:center;justify-content:center;padding:24px;">
      <div style="width:100%;max-width:420px;">
        <div style="text-align:center;margin-bottom:28px;">
            <div style="font-family:var(--font-head);font-size:52px;letter-spacing:3px;line-height:1;
                        background:linear-gradient(130deg, #ffffff 0%, #F5F5F0 55%, #FF6B1A 100%);
                        -webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text;">
                HAULTRA
            </div>
            <div style="font-size:11px;font-weight:700;letter-spacing:4px;color:#78786F;
                        text-transform:uppercase;margin-top:6px;">
                AI Dispatch Systems
            </div>
        </div>
        <div class="card" style="background:#171717;border:1px solid rgba(255,255,255,0.08);">
                <form method="POST">
                <label>Username</label>
                <input name="username" required autocomplete="username">
                <label>Password</label>
                <div style="position:relative;">
                    <input type="password" id="login-password" name="password" required
                           autocomplete="current-password" style="padding-right:56px;">
                    <button type="button" id="toggle-login-password"
                            onclick="var p=document.getElementById('login-password');var showing=p.type==='text';p.type=showing?'password':'text';this.textContent=showing?'Show':'Hide';this.setAttribute('aria-label',showing?'Show password':'Hide password');"
                            aria-label="Show password"
                            style="position:absolute;right:0;top:0;bottom:0;min-width:48px;min-height:48px;
                                   background:none;border:none;color:#78786F;font-size:12px;font-weight:700;
                                   letter-spacing:.3px;text-transform:uppercase;cursor:pointer;padding:0 14px;">
                        Show
                    </button>
                </div>
                <div style="margin-top:16px;">
                    <button type="submit" style="width:100%;min-height:48px;font-size:15px;">Login</button>
                </div>

                <div style="margin-top:14px;text-align:center;">
                <a href="{url_for('forgot_password')}" class="small">Forgot password?</a>
                </div>

                <div style="margin-top:10px;text-align:center;" class="small muted">
                Need an account?
                <a href="/signup">Create one here</a>
                </div>

               </form>
        </div>
      </div>
    </div>
    """
    return render_template_string(shell_page("Login", body))
@app.route("/logout", methods=["POST"])
def logout():
    session.clear()
    flash("Logged out.", "success")
    return redirect(url_for("login"))


@app.route("/forgot-password", methods=["GET", "POST"])
def forgot_password():
    init_db()
    if request.method == "POST":
        email = request.form.get("email", "").strip().lower()
        want_username = request.form.get("_action") == "username"

        if email:
            conn = get_db()
            matches = conn.execute(
                "SELECT id, username, full_name FROM users WHERE email = ? COLLATE NOCASE",
                (email,)
            ).fetchall()

            if want_username:
                if matches:
                    names = ", ".join(sorted(m["username"] for m in matches))
                    html_body = (
                        f"<p>Hi,</p>"
                        f"<p>The HAULTRA username(s) linked to this email address:</p>"
                        f"<p style=\"font-size:18px;font-weight:700;\">{e(names)}</p>"
                        f"<p>If you didn't request this, you can safely ignore this email.</p>"
                    )
                    send_email(email, "Your HAULTRA username", html_body)
            else:
                for u in matches:
                    raw_token = secrets.token_urlsafe(32)
                    token_hash = hashlib.sha256(raw_token.encode()).hexdigest()
                    expires_at = (datetime.now() + timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
                    conn.execute(
                        """INSERT INTO password_reset_tokens (user_id, token_hash, created_at, expires_at)
                           VALUES (?, ?, ?, ?)""",
                        (u["id"], token_hash, now_ts(), expires_at)
                    )
                    conn.commit()
                    reset_link = url_for("reset_password", token=raw_token, _external=True)
                    html_body = (
                        f"<p>Hi {e(u['full_name'] or u['username'])},</p>"
                        f"<p>Someone requested a password reset for your HAULTRA account "
                        f"(username <strong>{e(u['username'])}</strong>). This link expires in "
                        f"1 hour and can only be used once:</p>"
                        f"<p><a href=\"{reset_link}\">{reset_link}</a></p>"
                        f"<p>If you didn't request this, you can safely ignore this email — "
                        f"your password will not change.</p>"
                    )
                    send_email(email, "Reset your HAULTRA password", html_body)
            conn.close()

        # Identical response whether or not the email matched an account, and
        # whether the send succeeded — the only thing that would ever differ
        # is server-side logging, never what the requester sees.
        flash("If that email is on file, we've sent you a message.", "success")
        return redirect(url_for("forgot_password"))

    body = f"""
    <div style="min-height:calc(100vh - 60px);display:flex;align-items:center;justify-content:center;padding:24px;">
      <div style="width:100%;max-width:420px;">
        <div style="text-align:center;margin-bottom:28px;">
            <div style="font-family:var(--font-head);font-size:40px;letter-spacing:3px;line-height:1;
                        background:linear-gradient(130deg, #ffffff 0%, #F5F5F0 55%, #FF6B1A 100%);
                        -webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text;">
                HAULTRA
            </div>
        </div>
        <div class="card" style="background:#171717;border:1px solid rgba(255,255,255,0.08);">
            <h2 style="margin-bottom:6px;">Account Recovery</h2>
            <p class="muted small" style="margin-bottom:18px;">
                Enter the email on your account. We'll send a password reset link, or your
                username if you just need a reminder.
            </p>
            <form method="POST">
                <label>Email</label>
                <input type="email" name="email" required autocomplete="email">
                <div style="margin-top:16px;display:flex;flex-direction:column;gap:10px;">
                    <button type="submit" name="_action" value="reset" style="width:100%;min-height:48px;font-size:15px;">
                        Send Reset Link
                    </button>
                    <button type="submit" name="_action" value="username" class="btn secondary" style="width:100%;min-height:48px;font-size:14px;">
                        Email Me My Username
                    </button>
                </div>
            </form>
            <div style="margin-top:16px;text-align:center;" class="small muted">
                <a href="{url_for('login')}">&larr; Back to login</a>
            </div>
        </div>
      </div>
    </div>
    """
    return render_template_string(shell_page("Account Recovery", body))


@app.route("/reset-password/<token>", methods=["GET", "POST"])
def reset_password(token):
    init_db()
    token_hash = hashlib.sha256(token.encode()).hexdigest()

    conn = get_db()
    row = conn.execute(
        """SELECT prt.id AS token_id, prt.user_id, prt.expires_at, prt.used_at, u.username
           FROM password_reset_tokens prt
           JOIN users u ON u.id = prt.user_id
           WHERE prt.token_hash = ?""",
        (token_hash,)
    ).fetchone()

    valid = False
    if row and not row["used_at"]:
        try:
            valid = datetime.now() <= datetime.strptime(row["expires_at"], "%Y-%m-%d %H:%M:%S")
        except Exception:
            valid = False

    if not valid:
        conn.close()
        flash("That reset link is invalid or has expired — request a new one below.", "error")
        return redirect(url_for("forgot_password"))

    if request.method == "POST":
        password = request.form.get("password", "").strip()
        confirm = request.form.get("confirm_password", "").strip()

        if len(password) < 8:
            conn.close()
            flash("Password must be at least 8 characters.", "error")
            return redirect(url_for("reset_password", token=token))
        if password != confirm:
            conn.close()
            flash("Passwords don't match.", "error")
            return redirect(url_for("reset_password", token=token))

        conn.execute(
            "UPDATE users SET password_hash=? WHERE id=?",
            (generate_password_hash(password), row["user_id"])
        )
        conn.execute(
            "UPDATE password_reset_tokens SET used_at=? WHERE id=?",
            (now_ts(), row["token_id"])
        )
        conn.commit()
        conn.close()
        flash("Password updated — please log in.", "success")
        return redirect(url_for("login"))

    conn.close()
    body = f"""
    <div style="min-height:calc(100vh - 60px);display:flex;align-items:center;justify-content:center;padding:24px;">
      <div style="width:100%;max-width:420px;">
        <div style="text-align:center;margin-bottom:28px;">
            <div style="font-family:var(--font-head);font-size:40px;letter-spacing:3px;line-height:1;
                        background:linear-gradient(130deg, #ffffff 0%, #F5F5F0 55%, #FF6B1A 100%);
                        -webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text;">
                HAULTRA
            </div>
        </div>
        <div class="card" style="background:#171717;border:1px solid rgba(255,255,255,0.08);">
            <h2 style="margin-bottom:6px;">Set a New Password</h2>
            <p class="muted small" style="margin-bottom:18px;">Resetting password for <strong>{e(row['username'])}</strong>.</p>
            <form method="POST">
                <label>New Password</label>
                <input type="password" name="password" required minlength="8" autocomplete="new-password">
                <label>Confirm Password</label>
                <input type="password" name="confirm_password" required minlength="8" autocomplete="new-password">
                <div style="margin-top:16px;">
                    <button type="submit" style="width:100%;min-height:48px;font-size:15px;">Set New Password</button>
                </div>
            </form>
        </div>
      </div>
    </div>
    """
    return render_template_string(shell_page("Reset Password", body))


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

    # Table only shows this pay period — same reasoning as the Owner
    # Dashboard's Recent Routes — but the offline prefetch below still
    # walks the FULL unfiltered `routes` list so an older open/in_progress
    # route is never silently dropped from offline caching.
    _co_row = conn.execute("SELECT * FROM companies WHERE id=?", (session["company_id"],)).fetchone()
    co_settings = {k: _co_row[k] for k in _co_row.keys()} if _co_row else {}
    pay_period_start, pay_period_end = get_pay_period_bounds(co_settings)
    conn.close()

    display_routes = [r for r in routes if pay_period_start <= r["route_date"] <= pay_period_end]

    rows = ""
    for r in display_routes:
        rows += f"""
        <tr>
            <td>{e(r['route_date'])}</td>
            <td>{e(r['route_name'])}</td>
            <td><span class="badge {e(r['status'])}">{e(r['status'])}</span></td>
            <td>{r['completed_stops']} / {r['total_stops']}</td>
            <td><a class="btn secondary" href="{url_for('driver_route_detail', route_id=r['id'])}">Open</a></td>
        </tr>
        """

    # Build list of active route URLs to prefetch for offline use — walks
    # the full route history, not just this pay period, so an active route
    # is always cached regardless of its date.
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
        <h2 style="margin-bottom:4px;">This Pay Week</h2>
        <p class="muted small" style="margin-bottom:14px;">{e(pay_period_start)} &ndash; {e(pay_period_end)}</p>
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
                    {rows if rows else '<tr><td colspan="5">No routes assigned this pay week.</td></tr>'}
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
    today = today_str()

    if user["role"] != "boss":
        # ── Driver: simple personal view (Cab View covers the working driver UX) ──
        routes = conn.execute("""
            SELECT r.*, u.username AS assigned_username
            FROM routes r
            LEFT JOIN users u ON r.assigned_to = u.id
            WHERE r.assigned_to = ? AND r.company_id = ?
            ORDER BY r.route_date DESC, r.id DESC LIMIT 8
        """, (user["id"], company_id)).fetchall()
        _rc = conn.execute("""
            SELECT COUNT(*) AS total, SUM(status='open') AS open,
                   SUM(status='in_progress') AS progress, SUM(status='completed') AS completed
            FROM routes WHERE assigned_to=? AND company_id=?
        """, (user["id"], company_id)).fetchone()
        route_total, open_routes, progress_routes, completed_routes = (
            _rc["total"], _rc["open"] or 0, _rc["progress"] or 0, _rc["completed"] or 0
        )
        stop_total = conn.execute(
            "SELECT COUNT(*) n FROM stops s JOIN routes r ON s.route_id=r.id WHERE r.assigned_to=? AND r.company_id=?",
            (user["id"], company_id)
        ).fetchone()["n"]
        conn.close()

        route_rows = ""
        for r in routes:
            route_rows += f"""
<tr>
    <td>{e(r['route_date'])}</td>
    <td><a href="{url_for('driver_route_detail', route_id=r['id'])}">{e(r['route_name'])}</a></td>
    <td><span class="badge {e(r['status'])}">{e(r['status'])}</span></td>
</tr>
"""
        body = f"""
    <div class="hero">
        <h1>My Day</h1>
        <p>{e(today)} &mdash; your assigned routes and stops.</p>
    </div>
    <div class="grid" style="margin-bottom:20px;">
        <div class="stat"><div class="label">Total Routes</div><div class="num">{route_total}</div></div>
        <div class="stat"><div class="label">Open</div><div class="num">{open_routes}</div></div>
        <div class="stat"><div class="label">In Progress</div><div class="num" style="color:#FF6B1A;">{progress_routes}</div></div>
        <div class="stat"><div class="label">Completed</div><div class="num" style="color:#3DDC84;">{completed_routes}</div></div>
        <div class="stat"><div class="label">Total Stops</div><div class="num">{stop_total}</div></div>
    </div>
    <div class="card">
        <h2 style="margin:0 0 14px;font-size:11px;font-weight:700;letter-spacing:1.2px;text-transform:uppercase;color:#55554C;">My Routes</h2>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Date</th><th>Route</th><th>Status</th></tr></thead>
                <tbody>{route_rows if route_rows else '<tr><td colspan="3" style="color:#55554C;padding:20px 12px;">No routes yet.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
        return render_template_string(shell_page("My Day", body))

    # ══════════════════════════════════════════════════════════
    # OWNER DASHBOARD (boss) — real data, "—" for anything we don't track
    # ══════════════════════════════════════════════════════════

    # Pulls today: completed pull/PR-type stops with completed_at falling on today
    _today_pull_stops = conn.execute("""
        SELECT s.action, r.assigned_to, u.username AS driver_username
        FROM stops s
        JOIN routes r ON s.route_id = r.id
        LEFT JOIN users u ON r.assigned_to = u.id
        WHERE r.company_id=? AND s.status='completed'
          AND substr(COALESCE(s.completed_at, r.route_date), 1, 10) = ?
    """, (company_id, today)).fetchall()
    pulls_today_rows = [s for s in _today_pull_stops if is_pull_job(s["action"])]
    pulls_today = len(pulls_today_rows)

    driver_pull_counts = {}
    for s in pulls_today_rows:
        name = s["driver_username"] or "Unassigned"
        driver_pull_counts[name] = driver_pull_counts.get(name, 0) + 1
    driver_pull_list = sorted(driver_pull_counts.items(), key=lambda kv: kv[1], reverse=True)

    # ── Pulls Today vs 7-day average (only shown when there's real history to compare) ──
    today_date    = datetime.strptime(today, "%Y-%m-%d").date()
    window_start  = (today_date - timedelta(days=7)).isoformat()
    window_end    = (today_date - timedelta(days=1)).isoformat()
    _window_stops = conn.execute("""
        SELECT s.action
        FROM stops s
        JOIN routes r ON s.route_id = r.id
        WHERE r.company_id=? AND s.status='completed'
          AND substr(COALESCE(s.completed_at, r.route_date), 1, 10) BETWEEN ? AND ?
    """, (company_id, window_start, window_end)).fetchall()
    _has_prior_history = conn.execute("""
        SELECT COUNT(*) n FROM routes WHERE company_id=? AND route_date < ?
    """, (company_id, today)).fetchone()["n"] > 0

    pulls_trend_sub = ""
    if _has_prior_history:
        window_pulls = sum(1 for s in _window_stops if is_pull_job(s["action"]))
        avg_per_day  = window_pulls / 7.0
        if avg_per_day > 0:
            pct_change = round((pulls_today - avg_per_day) / avg_per_day * 100)
            sign = "+" if pct_change >= 0 else ""
            pulls_trend_sub = f'<div class="sub">{sign}{pct_change}% vs 7-day avg ({avg_per_day:.1f}/day)</div>'
        elif pulls_today > 0:
            pulls_trend_sub = '<div class="sub">up from 0 in the past 7 days</div>'
        else:
            pulls_trend_sub = '<div class="sub">0 vs 7-day avg</div>'

    # Containers out (live, derived from stop history — see compute_containers_out)
    containers_out = compute_containers_out(conn, company_id)
    out_count = len(containers_out)
    for c in containers_out:
        c["days_out"] = _days_out(c["since"])
    overdue_count = sum(1 for c in containers_out if (c["days_out"] or 0) >= OVERDUE_RENTAL_DAYS)

    # ── Overdue 7-day trend — reconstructed from real stop history, not stored snapshots ──
    overdue_trend_sub = ""
    _has_history_7d_ago = conn.execute("""
        SELECT COUNT(*) n FROM stops s JOIN routes r ON s.route_id=r.id
        WHERE r.company_id=? AND s.status='completed'
          AND substr(COALESCE(s.completed_at, r.route_date), 1, 10) <= ?
    """, (company_id, window_start)).fetchone()["n"] > 0
    if _has_history_7d_ago:
        containers_out_7d_ago = compute_containers_out(conn, company_id, asof_date=window_start)
        overdue_7d_ago = sum(
            1 for c in containers_out_7d_ago
            if (_days_out(c["since"], asof_date=window_start) or 0) >= OVERDUE_RENTAL_DAYS
        )
        delta = overdue_count - overdue_7d_ago
        if delta == 0:
            overdue_trend_sub = '<div class="sub">flat vs 7 days ago</div>'
        else:
            sign = "+" if delta > 0 else ""
            overdue_trend_sub = f'<div class="sub">{sign}{delta} vs 7 days ago</div>'

    # Fleet totals by size (real, boss-registered inventory — 0 if not registered yet)
    fleet_rows = conn.execute(
        "SELECT size, COUNT(*) n FROM containers WHERE company_id=? AND status != 'retired' GROUP BY size",
        (company_id,)
    ).fetchall()
    fleet_by_bucket = {"10yd": 0, "20yd": 0, "30yd": 0, "40yd": 0}
    for fr in fleet_rows:
        b = size_bucket(fr["size"])
        if b:
            fleet_by_bucket[b] += fr["n"]
    total_fleet = sum(fleet_by_bucket.values())

    out_by_bucket = {"10yd": 0, "20yd": 0, "30yd": 0, "40yd": 0}
    for c in containers_out:
        b = size_bucket(c["size"])
        if b:
            out_by_bucket[b] += 1

    # "Recent Routes" = this pay period only, not just "the last 8 ever" —
    # otherwise old routes linger on the dashboard indefinitely once volume
    # is low. Same pay-period math already used for Driver Hours.
    _co_row = conn.execute("SELECT * FROM companies WHERE id=?", (company_id,)).fetchone()
    co_settings = {k: _co_row[k] for k in _co_row.keys()} if _co_row else {}
    pay_period_start, pay_period_end = get_pay_period_bounds(co_settings)

    routes = conn.execute("""
        SELECT r.*, u.username AS assigned_username
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        WHERE r.company_id = ? AND r.route_date BETWEEN ? AND ?
        ORDER BY r.route_date DESC, r.id DESC
    """, (company_id, pay_period_start, pay_period_end)).fetchall()
    conn.close()

    # ── Pulls by Driver bar chart ───────────────────────────────
    if driver_pull_list:
        max_pulls = max(n for _, n in driver_pull_list)
        bar_rows = ""
        for name, n in driver_pull_list:
            pct = round((n / max_pulls) * 100) if max_pulls else 0
            bar_rows += f"""
            <div class="bar-chart-row">
                <div class="bar-chart-label">{e(name)}</div>
                <div class="bar-chart-track"><div class="bar-chart-fill" style="width:{pct}%;"></div></div>
                <div class="bar-chart-value">{n}</div>
            </div>"""
    else:
        bar_rows = '<div class="empty-state" style="padding:20px 0;">No pulls completed yet today.</div>'

    # ── Container Inventory per-size bars ───────────────────────
    if total_fleet == 0 and out_count == 0:
        inv_html = '<div class="empty-state" style="padding:20px 0;">No containers registered yet &mdash; add your fleet in Containers to track inventory.</div>'
    else:
        inv_html = ""
        for bucket in ("10yd", "20yd", "30yd", "40yd"):
            y = fleet_by_bucket[bucket]
            x = out_by_bucket[bucket]
            if y == 0 and x == 0:
                continue
            if y == 0:
                count_label = f"{x} out &middot; fleet not registered"
                pct = 100
            else:
                count_label = f"{x} / {y} out"
                pct = min(100, round((x / y) * 100))
            inv_html += f"""
            <div class="inv-row">
                <div class="inv-row-top">
                    <span class="inv-row-size">{bucket}</span>
                    <span class="inv-row-count">{count_label}</span>
                </div>
                <div class="inv-track"><div class="inv-fill" style="width:{pct}%;"></div></div>
            </div>"""
        if not inv_html:
            inv_html = '<div class="empty-state" style="padding:20px 0;">No containers registered yet &mdash; add your fleet in Containers to track inventory.</div>'

    # ── Containers Out stat card body ───────────────────────────
    if total_fleet > 0:
        containers_out_num = f"{out_count}/{total_fleet}"
        in_yard = max(0, total_fleet - out_count)
        containers_out_sub = f"{in_yard} in yard"
    else:
        containers_out_num = str(out_count)
        containers_out_sub = "fleet not registered in Containers"

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
            <form class="inline" method="POST"
                  action="{url_for('delete_route', route_id=r['id'])}"
                  onsubmit="return confirm('Delete this route?')">
                <button class="btn red" type="submit">Delete</button>
            </form>
        </div>
    </td>
</tr>
"""

    body = f"""
    <div class="hero owner-header-row">
        <div>
            <div style="font-size:10px;font-weight:700;letter-spacing:2px;text-transform:uppercase;color:#55554C;margin-bottom:7px;">
                OWNER &middot; {e(today)}
            </div>
            <h1>Yard Overview</h1>
            <p style="margin-top:6px;">Real-time pulls, containers, and driver activity for today.</p>
        </div>
        <a class="btn gold" href="{url_for('export_day_csv')}" style="align-self:flex-start;white-space:nowrap;">
            &#8615; Export Day
        </a>
    </div>

    <div class="grid" style="margin-bottom:20px;">
        <div class="gauge-stat">
            <div class="label">Pulls Today</div>
            <div class="num">{pulls_today}</div>
            {pulls_trend_sub}
        </div>
        <div class="gauge-stat">
            <div class="label">Revenue</div>
            <div class="num dim">&mdash;</div>
            <div class="sub">not tracked yet</div>
        </div>
        <div class="gauge-stat">
            <div class="label">Containers Out</div>
            <div class="num">{containers_out_num}</div>
            <div class="sub">{containers_out_sub}</div>
        </div>
        <div class="gauge-stat">
            <div class="label">Overdue</div>
            <div class="num {'red' if overdue_count else ''}">{overdue_count}</div>
            <div class="sub">{OVERDUE_RENTAL_DAYS}+ days out</div>
            {overdue_trend_sub}
        </div>
    </div>

    <div class="row" style="align-items:stretch;gap:16px;flex-wrap:wrap;margin-bottom:16px;">
        <div class="card" style="flex:1;min-width:300px;margin-bottom:0;">
            <h2>Pulls by Driver</h2>
            {bar_rows}
        </div>
        <div class="card" style="flex:1;min-width:300px;margin-bottom:0;">
            <h2>Container Inventory</h2>
            {inv_html}
        </div>
    </div>

    <div class="card">
        <div class="row between" style="margin-bottom:4px;">
            <h2 style="margin:0;">This Pay Week</h2>
            <a class="btn secondary" style="font-size:12px;padding:7px 14px;" href="{url_for("routes_page")}">All Routes &rarr;</a>
        </div>
        <p class="muted small" style="margin-bottom:14px;">{e(pay_period_start)} &ndash; {e(pay_period_end)}</p>
        <div class="table-wrap">
            <table>
                <thead>
                    <tr><th>Date</th><th>Route</th><th>Assigned</th><th>Status</th><th></th></tr>
                </thead>
                <tbody>
                    {route_rows if route_rows else '<tr><td colspan="5" style="color:#55554C;padding:20px 12px;">No routes dispatched this pay week yet.</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Owner", body))

@app.route("/analytics")
@boss_required
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
# TEAM — merged Users + Drivers roster
# =========================================================
@app.route("/team")
@boss_required
def team_page():
    conn = get_db()
    users = conn.execute("""
        SELECT u.*, COUNT(DISTINCT r.id) AS routes_assigned,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS completed_stops
        FROM users u
        LEFT JOIN routes r ON r.assigned_to = u.id AND r.company_id = ?
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE u.company_id=?
        GROUP BY u.id
        ORDER BY u.role, u.username
    """, (cid(), cid())).fetchall()
    conn.close()

    current_uid = session["user_id"]
    boss_count  = sum(1 for u in users if u["role"] == "boss")

    rows = ""
    for u in users:
        is_self      = u["id"] == current_uid
        is_driver    = u["role"] == "driver"
        is_last_boss = u["role"] == "boss" and boss_count <= 1

        _del_td_style = 'style="text-align:right;white-space:nowrap;width:170px;"'
        if is_self:
            delete_cell = f'<span class="muted small">You</span>'
        elif is_last_boss:
            delete_cell = f'<span class="muted small" title="Cannot delete the last boss">&mdash;</span>'
        else:
            _del_uname  = e(u["username"])
            _del_action = url_for("delete_user", user_id=u["id"])
            delete_cell = (
                f'<form method="POST" action="{_del_action}" style="margin:0;display:inline;" '
                f'onsubmit="return confirm(\'Delete {_del_uname}? This cannot be undone.\');">'
                f'<button type="submit" '
                f'style="background:transparent;color:#f87171;border:1px solid rgba(248,113,113,0.4);'
                f'border-radius:6px;padding:3px 10px;font-size:11px;cursor:pointer;line-height:1.4;">'
                f'Delete</button>'
                f'</form>'
            )

        hours_cell = (
            f'<a href="{url_for("driver_hours_page")}?driver_id={u["id"]}" '
            f'style="color:#FF9D5C;font-size:12px;margin-right:10px;">Hours</a>'
            if is_driver else ""
        )

        role_badge = (
            '<span class="badge completed">Boss</span>'
            if u["role"] == "boss"
            else '<span class="badge">Driver</span>'
        )

        stats_cell = (
            f'{u["routes_assigned"] or 0} routes &middot; {u["completed_stops"] or 0} stops'
            if is_driver else '<span class="muted small">&mdash;</span>'
        )

        if is_driver:
            _cur_pref = u["nav_preference"] or ""
            _nav_opts = "".join(
                f'<option value="{val}" {"selected" if _cur_pref == val else ""}>{label}</option>'
                for val, label in [
                    ("", "Default"), ("google", "Google Maps"), ("apple", "Apple Maps"),
                    ("waze", "Waze"), ("device_default", "Device Default"),
                ]
            )
            nav_cell = (
                f'<form method="POST" action="{url_for("set_nav_preference", user_id=u["id"])}" style="margin:0;">'
                f'<input type="hidden" name="next" value="{url_for("team_page")}">'
                f'<select name="nav_preference" class="compact-select" onchange="this.form.submit()">{_nav_opts}</select>'
                f'</form>'
            )
        else:
            nav_cell = '<span class="muted small">&mdash;</span>'

        rows += f"""
        <tr>
            <td>{e(u['username'])}</td>
            <td>{e(u['full_name'] or '')}</td>
            <td>{e(u['phone'] or '')}</td>
            <td>{role_badge}</td>
            <td class="muted small">{stats_cell}</td>
            <td>{nav_cell}</td>
            <td>{e(u['created_at'])}</td>
            <td {_del_td_style}>{hours_cell}{delete_cell}</td>
        </tr>
        """

    body = f"""
    <div class="hero">
        <h1>Team</h1>
        <p>Everyone who can work inside this HAULTRA system &mdash; bosses and drivers, one roster.</p>
    </div>

    <div class="card">
        <div class="row between">
            <h2 style="margin:0;">All Team Members</h2>
            <a class="btn" href="{url_for('register')}">Create User</a>
        </div>
        <div class="table-wrap">
            <table>
                <thead>
                    <tr>
                        <th>Username</th><th>Full Name</th><th>Phone</th><th>Role</th>
                        <th>Driver Activity</th><th>Nav App</th><th>Created</th><th style="width:170px;"></th>
                    </tr>
                </thead>
                <tbody>{rows or '<tr><td colspan="8" class="muted">No team members found.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Team", body))


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
        return redirect(url_for("team_page"))

    # Cannot delete yourself
    if user_id == session["user_id"]:
        conn.close()
        flash("You cannot delete your own account.", "error")
        return redirect(url_for("team_page"))

    # Cannot delete the last boss
    if target["role"] == "boss":
        boss_count = conn.execute(
            "SELECT COUNT(*) n FROM users WHERE role='boss' AND company_id=?", (cid(),)
        ).fetchone()["n"]
        if boss_count <= 1:
            conn.close()
            flash("Cannot delete the last boss account.", "error")
            return redirect(url_for("team_page"))

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
    return redirect(url_for("team_page"))


_NAV_PREFERENCES = {"google", "apple", "waze", "device_default"}


@app.route("/users/<int:user_id>/nav-preference", methods=["POST"])
@login_required
def set_nav_preference(user_id):
    """Shared by both editing surfaces — a driver setting their own preference
    from the Cab View gear panel, and a boss setting any driver's preference
    from Team."""
    if session.get("role") != "boss" and user_id != session["user_id"]:
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    pref = (request.form.get("nav_preference") or "").strip()
    if pref not in _NAV_PREFERENCES:
        pref = None  # blank/unrecognized clears it back to "current behavior"

    conn = get_db()
    target = conn.execute(
        "SELECT id FROM users WHERE id=? AND company_id=?", (user_id, cid())
    ).fetchone()
    if not target:
        conn.close()
        abort(404)
    conn.execute("UPDATE users SET nav_preference=? WHERE id=?", (pref, user_id))
    conn.commit()
    conn.close()

    flash("Navigation preference saved.", "success")
    next_url = request.form.get("next") or url_for("team_page")
    return redirect(next_url)


# ── Legacy URLs — redirect to their new home on Team ────────────────────────
@app.route("/users")
@boss_required
def manage_users():
    return redirect(url_for("team_page"))


@app.route("/drivers")
@boss_required
def drivers_page():
    return redirect(url_for("team_page"))

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
        email     = request.form.get("email", "").strip()

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

        # Case-insensitive duplicate check — the DB's UNIQUE constraint on
        # username is case-sensitive, so "Bob" and "bob" wouldn't collide
        # there, but login now matches case-insensitively and two accounts
        # that only differ by case would make that lookup ambiguous.
        existing = conn.execute(
            "SELECT id FROM users WHERE username = ? COLLATE NOCASE", (username,)
        ).fetchone()
        if existing:
            conn.close()
            flash("Username already exists.", "error")
            return redirect(url_for("register"))

        try:
            conn.execute(
                """INSERT INTO users (username, password_hash, role, full_name, phone, email,
                   company_id, created_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
                (username, generate_password_hash(password), role,
                 full_name, phone, email or None, company_id, now_ts())
            )
            conn.commit()
            flash("User created.", "success")
        except sqlite3.IntegrityError:
            flash("Username already exists.", "error")
        finally:
            conn.close()
        return redirect(url_for("team_page"))

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
            <label>Email</label>
            <input type="email" name="email" placeholder="for password reset / recovery">
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
    _rc = conn.execute("""
        SELECT COUNT(*) AS total,
               SUM(status='open') AS open,
               SUM(status='in_progress') AS progress,
               SUM(status='completed') AS completed
        FROM routes WHERE company_id=?
    """, (company_id,)).fetchone()
    total_routes     = _rc["total"]
    open_routes      = _rc["open"] or 0
    progress_routes  = _rc["progress"] or 0
    completed_routes = _rc["completed"] or 0

    _sc = conn.execute("""
        SELECT COUNT(*) AS total, SUM(s.status='completed') AS completed
        FROM stops s JOIN routes r ON s.route_id=r.id WHERE r.company_id=?
    """, (company_id,)).fetchone()
    total_stops     = _sc["total"]
    completed_stops = _sc["completed"] or 0

    drivers_count = conn.execute("SELECT COUNT(*) AS n FROM users WHERE role='driver' AND company_id=?", (company_id,)).fetchone()["n"]
    new_orders    = conn.execute("SELECT COUNT(*) AS n FROM orders WHERE status='new' AND company_id=?", (company_id,)).fetchone()["n"]

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
                <span style="font-size:12px;color:#D8D8D0;">{done}/{total}</span>
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
                       style="font-size:11px;color:#D8D8D0;">&#x1F4CB; Daily Log</a>
            </td>
            <td style="white-space:nowrap;">{e(r['route_date'] or '')}</td>
            <td><span class="badge {e(r['status'])}">{status_label}</span></td>
            <td>{e(r['assigned_username'])}</td>
            <td>{progress_cell}</td>
            <td>{reassign_cell}</td>
        </tr>"""

    active_rows   = "".join(route_row(r) for r in active_routes) or \
        '<tr><td colspan="6" style="text-align:center;color:#D8D8D0;">No active routes.</td></tr>'
    completed_rows= "".join(route_row(r, show_reassign=False) for r in recent_completed) or \
        '<tr><td colspan="6" style="text-align:center;color:#D8D8D0;">None yet.</td></tr>'

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
                    <span style="font-size:12px;color:#D8D8D0;">{s_done}/{s_total}</span>
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
        <div class="stat" style="border-color:rgba(255,107,26,0.45);">
            <div>In Progress</div><div class="num" style="color:#FF6B1A;">{progress_routes}</div>
        </div>
        <div class="stat" style="border-color:rgba(61,220,132,0.35);">
            <div>Completed</div><div class="num" style="color:#3DDC84;">{completed_routes}</div>
        </div>
        <div class="stat"><div>Total Stops</div><div class="num">{total_stops}</div></div>
        <div class="stat" style="border-color:rgba(61,220,132,0.35);">
            <div>Stops Done</div><div class="num" style="color:#3DDC84;">{completed_stops}</div>
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
                card_border = "rgba(61,220,132,0.35)"
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
      <span style="margin:0 8px;color:#A6A69E;">&#8594;</span>
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
  background: var(--card-bg, #171717);
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
.p-lbl {{ font-size: 11px; color: #A6A69E; display: block; margin-bottom: 3px; }}
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
.p-badge-hi  {{ background: rgba(61,220,132,0.15); color: #3DDC84; }}
.p-badge-med {{ background: rgba(240,192,86,0.15);  color: #f0c056; }}
.p-badge-low {{ background: rgba(240,112,86,0.18);  color: #f07056; }}
.p-orig {{
  font-size: 11px;
  color: #A6A69E;
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
    <div><span style="font-size:11px;color:#A6A69E;">Route</span><br><strong>{e(route_name)}</strong></div>
    <div><span style="font-size:11px;color:#A6A69E;">Date</span><br><strong>{route_date}</strong></div>
    <div><span style="font-size:11px;color:#A6A69E;">Driver</span><br><strong>{e(assigned_name) or "Unassigned"}</strong></div>
    <div><span style="font-size:11px;color:#A6A69E;">Stops detected</span><br><strong>{len(parsed_stops)}</strong></div>
    <div><span style="font-size:11px;color:#3DDC84;">&#10003; High</span>&nbsp;
         <strong style="color:#3DDC84;">{_conf_counts["high"]}</strong>&ensp;
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
  <div style="font-size:12px;font-weight:600;color:#A6A69E;margin-bottom:10px;">SUPPORTED FORMATS</div>
  <div style="display:grid;grid-template-columns:1fr 1fr;gap:10px;">
    <div style="background:rgba(255,255,255,0.03);border-radius:8px;padding:12px;">
      <div style="font-size:10px;color:#A6A69E;font-weight:700;margin-bottom:5px;">ROLL-OFF (commas)</div>
      <code style="font-size:12px;color:#3DDC84;display:block;">Pr 5660 lowery rd,vb, jaswal 30yd dump dom</code>
      <code style="font-size:12px;color:#3DDC84;display:block;">Pull 280 benton,suff, power bolt 20yd</code>
    </div>
    <div style="background:rgba(255,255,255,0.03);border-radius:8px;padding:12px;">
      <div style="font-size:10px;color:#A6A69E;font-weight:700;margin-bottom:5px;">FREEFORM (no commas)</div>
      <code style="font-size:12px;color:#3DDC84;display:block;">Pull 4915 Broad St vb rhr 30yd dump dom</code>
      <code style="font-size:12px;color:#3DDC84;display:block;">R 7801 Shore Dr norf smith 20yd</code>
    </div>
    <div style="background:rgba(255,255,255,0.03);border-radius:8px;padding:12px;">
      <div style="font-size:10px;color:#A6A69E;font-weight:700;margin-bottom:5px;">PIPE / STRUCTURED</div>
      <code style="font-size:12px;color:#3DDC84;display:block;">Smith | 123 Main St Norfolk | PR | 30yd</code>
      <code style="font-size:12px;color:#3DDC84;display:block;">Jones | 4100 Holland Rd VB | Delivery | 20yd</code>
    </div>
    <div style="background:rgba(255,255,255,0.03);border-radius:8px;padding:12px;">
      <div style="font-size:10px;color:#A6A69E;font-weight:700;margin-bottom:5px;">WORK ORDER (typed)</div>
      <code style="font-size:12px;color:#3DDC84;display:block;">PR 1233 Westover Ave, Norfolk, VA, ringen 30yd</code>
      <code style="font-size:12px;color:#3DDC84;display:block;">D 2431 Southern Pines, Chesapeake, Roof Joe 20yd</code>
    </div>
  </div>
</div>"""
    return render_template_string(shell_page("Text to Route", body))

# =========================================================
# ROUTES / STOPS
# =========================================================
def _board_action_badge(action):
    """Map a stop's raw action text to the mockup's P/PR/D/S/R card badge.

    This is a display-only classification for the Route Board's badge color —
    it intentionally does not reuse the can-flow "is_pr" logic (which treats
    plain Swap as a PR variant), since the mockup calls for Swap to render as
    its own slate 'S' badge distinct from the orange PR badge.
    """
    a = (action or "").strip().lower()
    if "pickup and return" in a:
        return "PR", "pickup"
    if "pull" in a and "return" not in a:
        return "P", "pickup"
    if "swap" in a:
        return "S", "dropswap"
    if "delivery" in a or "drop" in a:
        return "D", "dropswap"
    if "relocate" in a or "move" in a:
        return "R", "neutral"
    label = (action or "?").strip()[:1].upper() or "?"
    return label, "neutral"


_MESSAGE_QUICK_TAPS = [
    "Blocked / can't access",
    "Running late",
    "Site wants to talk to you",
    "Done early",
]


def _message_thread_modal_html(show_quick_taps=False):
    """Shared thread modal, injected once per page (Cab View or Route Board).
    JS opens it for a specific route_id via openMessageThread(routeId, title)."""
    quick_taps_html = ""
    if show_quick_taps:
        buttons = "".join(
            f'<button type="button" class="msg-quick-btn" data-msg="{e(t)}">{e(t)}</button>'
            for t in _MESSAGE_QUICK_TAPS
        )
        quick_taps_html = f'<div class="msg-quick-taps">{buttons}</div>'

    return f"""
    <div id="msg-overlay" class="no-photo-confirm-overlay" hidden onclick="closeMessageThread()"></div>
    <div id="msg-modal" class="msg-modal" hidden>
        <div class="msg-modal-header">
            <div id="msg-modal-title">Messages</div>
            <button type="button" onclick="closeMessageThread()" aria-label="Close">&times;</button>
        </div>
        {quick_taps_html}
        <div id="msg-list" class="msg-list"></div>
        <div class="msg-compose">
            <textarea id="msg-input" placeholder="Type a message..." rows="2"></textarea>
            <button type="button" id="msg-send-btn" class="btn orange" onclick="sendMessageFreeText()">Send</button>
        </div>
    </div>
    """


def _gps_settings_js():
    """Gear-modal 'Enable Location' status + retry control — shared by both
    Cab View screens since the gear button/modal appear on both."""
    return """
(function() {
    var btn = document.getElementById('gps-enable-btn');
    var status = document.getElementById('gps-status-line');
    if (!btn || !status) return;

    function refreshStatus() {
        if (!navigator.geolocation) {
            status.textContent = "Location isn't supported on this device.";
            btn.style.display = 'none';
            return;
        }
        if (navigator.permissions && navigator.permissions.query) {
            navigator.permissions.query({ name: 'geolocation' }).then(function(result) {
                if (result.state === 'granted') {
                    status.textContent = 'Location is enabled.';
                } else if (result.state === 'denied') {
                    status.textContent = 'Location is turned off for HAULTRA. Enable it in your browser or device settings, then reopen this page.';
                } else {
                    status.textContent = "Location hasn't been set up yet — tap Enable Location.";
                }
            }).catch(function() { /* Permissions API present but query unsupported for this name — leave default copy */ });
        }
    }
    refreshStatus();

    btn.addEventListener('click', function() {
        btn.disabled = true;
        btn.textContent = 'Requesting…';
        navigator.geolocation.getCurrentPosition(function() {
            status.textContent = 'Location is enabled.';
            btn.disabled = false;
            btn.textContent = 'Enable Location';
        }, function() {
            status.textContent = 'Location is turned off for HAULTRA. Enable it in your browser or device settings, then reopen this page.';
            btn.disabled = false;
            btn.textContent = 'Enable Location';
        }, { timeout: 8000 });
    });
})();
"""


def _gps_capture_js():
    """GPS stamp capture on Complete Stop.

    Checks for a Capacitor Geolocation plugin at runtime (this app has no
    Capacitor wrapper today — nothing currently sets window.Capacitor — so
    this always falls through to the standard browser Geolocation API in
    production; the check is here so a future native wrapper picks it up
    automatically with no code change).

    window.captureGpsStamp(callback) always calls back within ~5.3s with
    either {lat, lng, accuracy} or null. It never throws and never blocks
    the caller beyond that timeout — permission denial, an unsupported
    browser, or a dead-zone timeout all just resolve to null.
    """
    return """
(function() {
    var PROMPT_KEY = 'haultra_gps_preprompt_shown';

    function getCapacitorGeolocation() {
        try {
            var cap = window.Capacitor;
            if (cap && typeof cap.isNativePlatform === 'function' && cap.isNativePlatform() &&
                cap.Plugins && cap.Plugins.Geolocation) {
                return cap.Plugins.Geolocation;
            }
        } catch (e) {}
        return null;
    }

    function requestBrowserPosition(onDone) {
        navigator.geolocation.getCurrentPosition(function(pos) {
            onDone({
                lat: pos.coords.latitude,
                lng: pos.coords.longitude,
                accuracy: pos.coords.accuracy,
            });
        }, function() {
            onDone(null);
        }, { timeout: 5000, maximumAge: 0 });
    }

    function showPrePrompt(onChoice) {
        var overlay = document.getElementById('gps-preprompt-overlay');
        var modal = document.getElementById('gps-preprompt-modal');
        var allowBtn = document.getElementById('gps-preprompt-allow');
        var skipBtn = document.getElementById('gps-preprompt-skip');
        if (!overlay || !modal || !allowBtn || !skipBtn) { onChoice(true); return; }

        function close() { overlay.hidden = true; modal.hidden = true; }
        overlay.hidden = false;
        modal.hidden = false;
        allowBtn.onclick = function() { close(); onChoice(true); };
        skipBtn.onclick = function() { close(); onChoice(false); };
    }

    window.captureGpsStamp = function(callback) {
        var finished = false;
        function finish(result) {
            if (finished) return;
            finished = true;
            callback(result);
        }
        var timer = setTimeout(function() { finish(null); }, 5300);

        var nativeGeo = getCapacitorGeolocation();
        if (nativeGeo) {
            nativeGeo.getCurrentPosition({ timeout: 5000 }).then(function(pos) {
                clearTimeout(timer);
                finish({
                    lat: pos.coords.latitude,
                    lng: pos.coords.longitude,
                    accuracy: pos.coords.accuracy,
                });
            }).catch(function() {
                clearTimeout(timer);
                finish(null);
            });
            return;
        }

        if (!navigator.geolocation) {
            clearTimeout(timer);
            finish(null);
            return;
        }

        if (!localStorage.getItem(PROMPT_KEY)) {
            localStorage.setItem(PROMPT_KEY, '1');
            showPrePrompt(function(proceed) {
                if (!proceed) { clearTimeout(timer); finish(null); return; }
                requestBrowserPosition(function(result) { clearTimeout(timer); finish(result); });
            });
        } else {
            requestBrowserPosition(function(result) { clearTimeout(timer); finish(result); });
        }
    };
})();
"""


def _message_thread_js():
    """Shared open/send/render logic for the thread modal — identical on Cab
    View and Route Board, just wired to different trigger buttons."""
    return """
(function() {
    var CSRF = (document.querySelector('meta[name="csrf-token"]') || {}).content || '';
    var currentThreadRouteId = null;
    var currentThreadTitle = '';

    function el(id) { return document.getElementById(id); }

    function escapeHtml(s) {
        var d = document.createElement('div');
        d.textContent = s == null ? '' : String(s);
        return d.innerHTML;
    }

    function renderThread(messages) {
        var list = el('msg-list');
        if (!list) return;
        if (!messages.length) {
            list.innerHTML = '<div class="msg-empty">No messages yet.</div>';
            return;
        }
        list.innerHTML = messages.map(function(m) {
            var cls = 'msg-bubble ' + (m.is_me ? 'msg-me' : 'msg-them');
            return '<div class="' + cls + '">' +
                '<div class="msg-bubble-meta">' + escapeHtml(m.sender_username) + '</div>' +
                '<div class="msg-bubble-body">' + escapeHtml(m.body) + '</div>' +
                '</div>';
        }).join('');
        list.scrollTop = list.scrollHeight;
    }

    window.openMessageThread = function(routeId, title) {
        currentThreadRouteId = routeId;
        currentThreadTitle = title || 'Messages';
        if (el('msg-modal-title')) el('msg-modal-title').textContent = 'Messages \\u2014 ' + currentThreadTitle;
        if (el('msg-overlay')) el('msg-overlay').hidden = false;
        if (el('msg-modal')) el('msg-modal').hidden = false;
        fetch('/route/' + routeId + '/messages', { credentials: 'same-origin' })
            .then(function(r) { return r.json(); })
            .then(function(data) { renderThread(data.messages || []); })
            .catch(function() {
                if (el('msg-list')) el('msg-list').innerHTML = '<div class="msg-empty">Could not load messages.</div>';
            });
    };

    window.closeMessageThread = function() {
        if (el('msg-overlay')) el('msg-overlay').hidden = true;
        if (el('msg-modal')) el('msg-modal').hidden = true;
    };

    function postMessage(body) {
        if (!currentThreadRouteId || !body) return;
        fetch('/route/' + currentThreadRouteId + '/messages', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json', 'X-CSRF-Token': CSRF },
            credentials: 'same-origin',
            body: JSON.stringify({ body: body }),
        })
            .then(function(r) { return r.json(); })
            .then(function(data) {
                if (data && data.success) {
                    window.openMessageThread(currentThreadRouteId, currentThreadTitle);
                }
            });
    }

    window.sendQuickMessage = function(text) { postMessage(text); };

    window.sendMessageFreeText = function() {
        var input = el('msg-input');
        if (!input) return;
        var text = (input.value || '').trim();
        if (!text) return;
        input.value = '';
        postMessage(text);
    };

    document.querySelectorAll('.msg-quick-btn').forEach(function(b) {
        b.addEventListener('click', function() { sendQuickMessage(b.dataset.msg); });
    });
})();
"""


def _build_route_board_html(user):
    """Render the #lane-container contents for the Route Board — one lane per
    driver with stops today, built from real route/stop rows only. Shared by
    the initial page render and the 30s polling partial so both stay in sync.
    """
    conn = get_db()
    company_id = cid()
    today = today_str()

    params = [company_id, today]
    sql = """
        SELECT r.id AS route_id, r.route_name, r.assigned_to,
               u.username AS driver_username,
               s.id AS stop_id, s.stop_order, s.customer_name, s.address, s.city,
               s.action, s.container_size, s.status AS stop_status, s.driver_status,
               s.completed_at,
               EXISTS(SELECT 1 FROM route_photos rp WHERE rp.stop_id = s.id) AS has_photo
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE r.company_id = ? AND r.route_date = ?
    """
    if user["role"] != "boss":
        sql += " AND r.assigned_to = ?"
        params.append(user["id"])
    sql += " ORDER BY r.id, s.stop_order, s.id"

    board_rows = conn.execute(sql, tuple(params)).fetchall()

    # Real, derived "urgent" signal: a pending Pull/PR stop whose container has
    # already been sitting overdue at that address (from compute_containers_out,
    # the same replay used for the Owner Dashboard / Bin Tracker overdue counts).
    containers_out = compute_containers_out(conn, company_id)
    overdue_addr_keys = {
        (c["address"] or "").strip().lower() + "|" + (c["city"] or "").strip().lower()
        for c in containers_out
        if (_days_out(c["since"]) or 0) >= OVERDUE_RENTAL_DAYS
    }

    unread_by_route = {
        r["route_id"]: r["n"]
        for r in conn.execute("""
            SELECT m.route_id, COUNT(*) n
            FROM messages m JOIN routes r ON r.id = m.route_id
            WHERE r.company_id=? AND r.route_date=? AND m.sender_user_id != ? AND m.read_at IS NULL
            GROUP BY m.route_id
        """, (company_id, today, user["id"])).fetchall()
    }
    conn.close()

    lanes = {}
    for row in board_rows:
        driver_key = row["driver_username"] or "__unassigned__"
        lane = lanes.setdefault(driver_key, {
            "driver_username": row["driver_username"],
            "route_names": [],
            "route_ids_seen": set(),
            "stops": [],
        })
        if row["route_id"] not in lane["route_ids_seen"]:
            lane["route_ids_seen"].add(row["route_id"])
            lane["route_names"].append(row["route_name"])
        if row["stop_id"] is not None:
            lane["stops"].append(row)

    if not lanes:
        return (
            '<div class="board-empty"><p>No dispatches yet today.</p>'
            f'<a class="btn gold" href="/parser" style="min-height:48px;display:inline-flex;align-items:center;">+ New Dispatch</a></div>'
        )

    sorted_keys = sorted(lanes.keys(), key=lambda k: (1, "") if k == "__unassigned__" else (0, k.lower()))

    lanes_html = ""
    for key in sorted_keys:
        lane = lanes[key]
        stops = lane["stops"]
        display_name = lane["driver_username"] or "Unassigned"
        total = len(stops)
        done = sum(1 for s in stops if s["stop_status"] == "completed")

        if total > 0 and done == total:
            dot_cls = "done"
        elif done > 0 or any((s["driver_status"] or "pending") != "pending" for s in stops):
            dot_cls = "active"
        else:
            dot_cls = ""

        route_label = lane["route_names"][0] if len(lane["route_names"]) == 1 else f"{len(lane['route_names'])} routes"
        progress_label = f"{done}/{total} done" if total else "No stops"

        add_stops_html = ""
        message_html = ""
        if user["role"] == "boss" and len(lane["route_ids_seen"]) == 1:
            _lane_route_id = next(iter(lane["route_ids_seen"]))
            add_stops_html = (
                f'<a class="lane-add-stops" href="{url_for("parser_view", route_id=_lane_route_id)}">'
                f'+ Add Stops</a>'
            )
            _lane_unread = unread_by_route.get(_lane_route_id, 0)
            _lane_msg_badge = f'<span class="lane-msg-badge">{_lane_unread}</span>' if _lane_unread else ""
            message_html = (
                f'<button type="button" class="lane-message-btn" '
                f'onclick="openMessageThread({_lane_route_id}, {e(json.dumps(display_name))})">'
                f'&#128172; Message{_lane_msg_badge}</button>'
            )

        cards_html = ""
        for s in stops:
            letter, group = _board_action_badge(s["action"])
            stop_status = s["stop_status"]
            driver_status = s["driver_status"] or "pending"

            if stop_status == "completed":
                pill_label, pill_cls, card_cls = "Done", "done", "st-done"
            elif driver_status != "pending":
                pill_label, pill_cls, card_cls = "En Route", "enroute", "st-enroute"
            else:
                pill_label, pill_cls, card_cls = "Pending", "pending", "st-pending"

            addr_text = ", ".join(p for p in [s["address"] or "", s["city"] or ""] if p) or (s["customer_name"] or "Stop")
            addr_cls = "stop-mini-addr done" if stop_status == "completed" else "stop-mini-addr"
            size_label = size_bucket(s["container_size"]) or (s["container_size"] or "")

            time_html = ""
            if stop_status == "completed" and s["completed_at"]:
                t = _fmt_12h(s["completed_at"])
                if t:
                    time_html = f'<div class="stop-mini-time">{e(t)}</div>'

            addr_key = (s["address"] or "").strip().lower() + "|" + (s["city"] or "").strip().lower()
            is_urgent = group == "pickup" and stop_status != "completed" and addr_key in overdue_addr_keys
            urgent_html = '<span class="stop-mini-urgent">&#9888; OVERDUE</span>' if is_urgent else ""
            photo_html = '<span class="stop-mini-photo" title="Has photo">&#128247;</span>' if s["has_photo"] else ""

            link = (url_for("edit_stop", stop_id=s["stop_id"]) if user["role"] == "boss"
                    else url_for("view_route", route_id=s["route_id"]))

            cards_html += f"""
            <a class="stop-mini {card_cls}" href="{link}">
                <div class="stop-mini-top">
                    <span class="stop-mini-badge {group}">{e(letter)}</span>
                    {urgent_html}
                    {photo_html}
                </div>
                <div class="{addr_cls}">{e(addr_text)}</div>
                <div class="stop-mini-bottom">
                    <span class="stop-mini-size">{e(size_label) if size_label else '&mdash;'}</span>
                    <span class="stop-mini-pill {pill_cls}">{e(pill_label)}</span>
                </div>
                {time_html}
            </a>"""

        if not cards_html:
            cards_html = '<div class="muted small" style="padding:10px;">No stops.</div>'

        lanes_html += f"""
        <div class="lane">
            <div class="lane-driver">
                <div class="lane-name-row">
                    <span class="lane-status-dot {dot_cls}"></span>
                    <span class="lane-name">{e(display_name)}</span>
                </div>
                <div class="lane-sub">{e(route_label)}<br>{e(progress_label)}</div>
                <div class="lane-actions">
                    {add_stops_html}
                    {message_html}
                </div>
            </div>
            <div class="lane-track">{cards_html}</div>
        </div>"""

    return lanes_html


@app.route("/routes/board-partial")
@login_required
def route_board_partial():
    return _build_route_board_html(get_current_user())


@app.route("/routes")
@roles_required("dispatcher")
def routes_page():
    user = get_current_user()
    q = request.args.get("q", "").strip()
    status = request.args.get("status", "").strip()
    active_tab = "history" if request.args.get("tab") == "history" else "board"

    today = today_str()
    weekday = datetime.strptime(today, "%Y-%m-%d").strftime("%A").upper()

    history_params = {"tab": "history"}
    if q:
        history_params["q"] = q
    if status:
        history_params["status"] = status
    history_tab_href = url_for("routes_page") + "?" + urllib.parse.urlencode(history_params)

    tabs_html = f"""
    <div class="route-tabs">
        <a class="route-tab {'active' if active_tab == 'board' else ''}" href="{url_for('routes_page')}"
           style="min-height:48px;display:inline-flex;align-items:center;">Board</a>
        <a class="route-tab {'active' if active_tab == 'history' else ''}" href="{history_tab_href}"
           style="min-height:48px;display:inline-flex;align-items:center;">History</a>
    </div>
    """

    header_html = f"""
    <div class="hero owner-header-row">
        <div>
            <div style="font-size:10px;font-weight:700;letter-spacing:2px;text-transform:uppercase;color:#55554C;margin-bottom:7px;">
                {e(weekday)} &middot; {e(today)}
            </div>
            <h1>Route Board</h1>
        </div>
        <div class="row" style="align-items:center;gap:18px;">
            <div class="board-legend">
                <span class="board-legend-item"><span class="board-legend-dot pickup"></span>Pickup</span>
                <span class="board-legend-item"><span class="board-legend-dot dropswap"></span>Drop/Swap</span>
                <span class="board-legend-item"><span class="board-legend-dot urgent"></span>Urgent</span>
            </div>
            <a class="btn gold" href="/parser" style="min-height:48px;display:inline-flex;align-items:center;white-space:nowrap;">+ New Dispatch</a>
        </div>
    </div>
    """

    if active_tab == "board":
        board_inner = _build_route_board_html(user)
        poll_script = f"""
        <script>
        (function() {{
            var container = document.getElementById('lane-container');
            if (!container) return;
            setInterval(function() {{
                fetch('{url_for("route_board_partial")}', {{credentials: 'same-origin'}})
                    .then(function(r) {{ return r.ok ? r.text() : null; }})
                    .then(function(html) {{ if (html !== null) container.innerHTML = html; }})
                    .catch(function() {{}});
            }}, 30000);
        }})();
        </script>
        """
        main_panel = f'<div id="lane-container">{board_inner}</div>{poll_script}'
    else:
        conn = get_db()
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
            sql += " AND (r.route_name LIKE ? ESCAPE '\\' OR r.notes LIKE ? ESCAPE '\\' OR r.raw_text LIKE ? ESCAPE '\\')"
            like_q = "%" + q.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_") + "%"
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
            </tr>
            """

        main_panel = f"""
        {f'''
        <div class="row" style="margin-bottom:18px;gap:10px;">
            <a class="btn gold" href="{url_for('new_route')}">+ Create Route</a>
            <a class="btn secondary" href="{url_for('text_to_route')}">⌨ Paste Boss Text</a>
        </div>
        ''' if user['role'] == 'boss' else ''}
        <div class="card">
            <form method="GET" class="row">
                <input type="hidden" name="tab" value="history">
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

    body = f"""
    {header_html}
    {tabs_html}
    {main_panel}
    {_message_thread_modal_html(show_quick_taps=False)}
    <script>{_message_thread_js()}</script>
    """
    return render_template_string(shell_page("Route Board", body))


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
        SELECT r.*, u.username AS assigned_username, u.nav_preference
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        WHERE r.id = ? AND r.assigned_to = ? AND r.company_id = ?
    """, (route_id, session["user_id"], session["company_id"])).fetchone()

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

    # Load all active dump locations keyed by lowercase name for per-stop nav lookup
    _dump_loc_rows = conn.execute(
        "SELECT name, address, city, state, zip_code FROM dump_locations WHERE active=1"
    ).fetchall()
    _dump_loc_by_name = {r["name"].lower(): dict(r) for r in _dump_loc_rows}

    photo_proof_mode = (conn.execute(
        "SELECT photo_proof_mode FROM companies WHERE id=?", (session["company_id"],)
    ).fetchone() or {"photo_proof_mode": "encouraged"})["photo_proof_mode"] or "encouraged"

    unread_messages = conn.execute(
        "SELECT COUNT(*) n FROM messages WHERE route_id=? AND sender_user_id != ? AND read_at IS NULL",
        (route_id, session["user_id"])
    ).fetchone()["n"]

    conn.close()

    completed_count = sum(1 for s in stops if s["status"] == "completed")
    total_count = len(stops)
    pct = int(completed_count / total_count * 100) if total_count else 0

    current_stop = None
    current_stop_num = None
    for i, s in enumerate(stops, start=1):
        if s["status"] != "completed":
            current_stop = s
            current_stop_num = i
            break

    # The stop immediately before current_stop, if any — by definition it's
    # completed (current_stop is the first non-completed stop in order), so
    # a driver who made a mistake can reopen it instead of being stuck.
    prev_stop = stops[current_stop_num - 2] if current_stop_num and current_stop_num > 1 else None
    _csrf = get_csrf_token()

    route_action_buttons = ""
    if route["status"] == "open":
        route_action_buttons = f"""
        <form class="inline" method="POST" action="{url_for('mark_route_in_progress', route_id=route_id)}">
            <button class="btn orange" style="min-height:44px;">Start Route</button>
        </form>"""
    elif route["status"] == "in_progress" and not current_stop:
        route_action_buttons = f"""
        <form class="inline" method="POST" action="{url_for('mark_route_completed', route_id=route_id)}">
            <button class="btn green" style="min-height:44px;">Finish Route</button>
        </form>"""

    # ══════════════════════════════════════════════════════════
    # ALL STOPS DONE — celebration screen
    # ══════════════════════════════════════════════════════════
    _nav_pref = route["nav_preference"] or ""
    _nav_pref_options = "".join(
        f'<label style="display:flex;align-items:center;gap:10px;min-height:48px;cursor:pointer;">'
        f'<input type="radio" name="nav_preference" value="{val}" {"checked" if _nav_pref == val else ""} '
        f'style="width:18px;height:18px;">{label}</label>'
        for val, label in [
            ("", "Default (current behavior)"), ("google", "Google Maps"), ("apple", "Apple Maps"),
            ("waze", "Waze"), ("device_default", "Device Default"),
        ]
    )
    gear_button_html = (
        '<button type="button" class="cab-gear-btn" '
        "onclick=\"document.getElementById('nav-pref-overlay').hidden=false;"
        "document.getElementById('nav-pref-modal').hidden=false;\" "
        'aria-label="Navigation settings">&#9881;</button>'
    )
    nav_pref_modal_html = f"""
    <div id="nav-pref-overlay" class="no-photo-confirm-overlay" hidden
         onclick="document.getElementById('nav-pref-overlay').hidden=true;document.getElementById('nav-pref-modal').hidden=true;"></div>
    <div id="nav-pref-modal" class="no-photo-confirm-modal" hidden style="text-align:left;">
        <div class="no-photo-confirm-title" style="margin-bottom:14px;">&#9881; Navigation App</div>
        <form method="POST" action="{url_for('set_nav_preference', user_id=session['user_id'])}">
            <input type="hidden" name="next" value="{e(request.path)}">
            <div style="display:flex;flex-direction:column;gap:4px;margin-bottom:16px;">
                {_nav_pref_options}
            </div>
            <button type="submit" class="btn orange" style="width:100%;min-height:48px;">Save</button>
        </form>

        <div class="no-photo-confirm-title" style="font-size:15px;margin:22px 0 8px;">&#128205; Location</div>
        <div id="gps-status-line" class="no-photo-confirm-body" style="margin-bottom:12px;">
            Used to record where containers are placed when you complete a stop.
        </div>
        <button type="button" id="gps-enable-btn" class="btn secondary" style="width:100%;min-height:48px;">
            Enable Location
        </button>
    </div>
    """

    if not current_stop:
        body = f"""
<div class="cab-wrap">
    <div class="cab-header">
        <div class="cab-title">MY ROUTE</div>
        <div style="display:flex;align-items:center;gap:10px;">
            {gear_button_html}
            <span class="cab-online-badge" id="online-badge"><span class="cab-online-dot"></span>ONLINE</span>
        </div>
    </div>
    {nav_pref_modal_html}
    <div class="cab-progress-label">{e(route['route_name'])} &middot; {e(route['route_date'])}</div>
    <div class="cab-progress-track"><div class="cab-progress-fill" style="width:100%;"></div></div>

    <div class="cab-all-done">
        <div class="cab-all-done-icon">&#9989;</div>
        <h2>All Stops Done</h2>
        <p style="color:var(--text-muted);margin-top:8px;">{total_count} of {total_count} stops completed.</p>
        <div style="margin-top:22px;display:flex;gap:10px;justify-content:center;flex-wrap:wrap;">
            {route_action_buttons}
            {f'''
            <form method="POST" action="{url_for('toggle_stop_complete', stop_id=stops[-1]['id'])}"
                  onsubmit="return confirm('Reopen the last stop? Its progress will reset and it will become your current stop again.');">
                <input type="hidden" name="_csrf_token" value="{_csrf}">
                <button type="submit" class="btn secondary" style="min-height:48px;">&#8592; Fix Last Stop</button>
            </form>
            ''' if total_count > 0 else ''}
            <a class="btn secondary" href="{url_for('driver_dashboard')}">&#8592; Back to My Routes</a>
        </div>
    </div>
</div>
<script>
(function() {{
    var badge = document.getElementById('online-badge');
    function upd() {{
        if (!badge) return;
        badge.innerHTML = navigator.onLine
            ? '<span class="cab-online-dot"></span>ONLINE'
            : '<span class="cab-online-dot" style="background:#FF5252;box-shadow:0 0 6px #FF5252;"></span>OFFLINE';
        badge.style.color = navigator.onLine ? '' : '#FF5252';
    }}
    window.addEventListener('online', upd);
    window.addEventListener('offline', upd);
    upd();
}})();
</script>
<script>{_gps_settings_js()}</script>
"""
        return render_template_string(shell_page("Cab View", body))

    # ══════════════════════════════════════════════════════════
    # CURRENT STOP — single-stop Cab View
    # ══════════════════════════════════════════════════════════
    s = current_stop
    stop_id = s["id"]
    _s = dict(s)

    full_address = " ".join(filter(None, [
        s["address"] or "", s["city"] or "", s["state"] or "", s["zip_code"] or "",
    ])).strip()
    _enc_addr = urllib.parse.quote_plus(full_address)
    nav_google_web = "https://www.google.com/maps/dir/?api=1&destination=" + _enc_addr
    nav_google_app = "comgooglemaps://?daddr=" + _enc_addr + "&directionsmode=driving"
    # HTML-escaped so the JSON-quoted JS string literal (which itself uses
    # double quotes, and may contain an apostrophe from the address) can't
    # collide with the double-quoted HTML attribute it's embedded in below.
    _nav_pref_js = e(json.dumps(_nav_pref))
    _full_addr_js = e(json.dumps(full_address))

    action_lower = (s["action"] or "").lower()
    is_pr    = "pickup and return" in action_lower or ("swap" in action_lower and "pull" not in action_lower)
    is_pull  = "pull" in action_lower and "return" not in action_lower
    is_swap_pr = is_pr and bool(_s.get("swap_with_prev_pull"))
    badge_group = "pickup" if (is_pull or "pickup" in action_lower or is_pr) else "dropswap"
    # Delivery/Drop/Service/Relocate read as dropswap; explicit pull-family reads as pickup
    if "delivery" in action_lower or "drop" in action_lower or "relocate" in action_lower or "service" in action_lower:
        badge_group = "dropswap"

    driver_status = _s.get("driver_status") or "pending"

    # ── Reuse the exact existing workflow state machine (arrived / box out /
    #    go to dump / dump ticket / box in) — same _wf_map + same POST target
    #    as before, just rendered inside the new single-stop card. ──────────
    workflow_btn_html = ""
    if is_swap_pr:
        wf_map = {
            "pending":     ("arrived",       "&#128666; Arrived at Stop",               "btn-driver btn-driver-complete"),
            "arrived":     ("box_out",       "&#128230; Box Out &mdash; Remove Old Container", "btn-driver btn-driver-complete"),
            "box_out":     ("need_box_in",   "&#128230; Box In &mdash; Place Empty Can",       "btn-driver btn-driver-complete"),
            "need_box_in": ("box_in",        "&#9989; Confirm Box In",                 "btn-driver btn-driver-complete"),
            "box_in":      ("going_to_dump", "&#128465;&#65039; Go To Dump",                    "btn-driver btn-driver-dump"),
        }
    elif is_pr:
        wf_map = {
            "pending":     ("arrived",       "&#128666; Arrived at Stop",                      "btn-driver btn-driver-complete"),
            "arrived":     ("box_out",       "&#128230; Box Out &mdash; Remove Container",            "btn-driver btn-driver-complete"),
            "box_out":     ("going_to_dump", "&#128465;&#65039; Go To Dump",                           "btn-driver btn-driver-dump"),
            "need_box_in": ("box_in",        "&#128260; Return &amp; Box In &mdash; Place Empty Can",  "btn-driver btn-driver-complete"),
        }
    elif is_pull:
        wf_map = {
            "pending":     ("arrived",       "&#128666; Arrived at Stop",           "btn-driver btn-driver-complete"),
            "arrived":     ("box_out",       "&#128230; Box Out &mdash; Remove Container", "btn-driver btn-driver-complete"),
            "box_out":     ("going_to_dump", "&#128465;&#65039; Go To Dump",               "btn-driver btn-driver-dump"),
        }
    else:
        wf_map = {"pending": ("arrived", "&#128666; Arrived at Stop", "btn-driver btn-driver-complete")}

    if driver_status in wf_map:
        nxt, lbl, cls = wf_map[driver_status]
        workflow_btn_html = (
            f'<form method="POST" action="{url_for("stop_driver_action", stop_id=stop_id)}" style="margin-bottom:10px;">'
            f'<input type="hidden" name="_csrf_token" value="{_csrf}">'
            f'<input type="hidden" name="action" value="{nxt}">'
            f'<button class="{cls}" type="submit" style="width:100%;min-height:52px;">{lbl}</button>'
            f'</form>'
        )
    elif driver_status == "going_to_dump":
        dump_loc_text = _s.get("dump_location") or ""
        dump_label = f"&#129534; Enter Dump Ticket{' &mdash; ' + e(dump_loc_text) if dump_loc_text else ''}"
        dump_ticket_link = (
            f'<a class="btn-driver btn-driver-dump" href="{url_for("dump_ticket", stop_id=stop_id)}" '
            f'style="display:block;text-align:center;text-decoration:none;padding:14px 16px;'
            f'border-radius:12px;font-weight:700;margin-bottom:10px;min-height:52px;">{dump_label}</a>'
        )
        dl_rec = _dump_loc_by_name.get(dump_loc_text.strip().lower()) if dump_loc_text else None
        dl_addr = ""
        if dl_rec:
            dl_addr = " ".join(p for p in [dl_rec.get("address") or "", dl_rec.get("city") or "",
                                            dl_rec.get("state") or "", dl_rec.get("zip_code") or ""] if p).strip()
        if dl_addr:
            dl_enc = urllib.parse.quote_plus(dl_addr)
            nav_html = (
                f'<div style="display:flex;gap:8px;margin-bottom:10px;">'
                f'<a class="btn-driver btn-driver-nav" target="_blank" style="flex:1;text-align:center;text-decoration:none;"'
                f' href="https://www.google.com/maps/dir/?api=1&destination={dl_enc}&travelmode=driving">&#128205; Google Maps</a>'
                f'<a class="btn-driver btn-driver-apple" target="_blank" style="flex:1;text-align:center;text-decoration:none;"'
                f' href="http://maps.apple.com/?daddr={dl_enc}&dirflg=d">&#63743; Apple Maps</a>'
                f'</div>'
            )
        elif dump_loc_text:
            nav_html = (f'<div class="small muted" style="margin-bottom:10px;padding:8px;'
                        f'background:rgba(255,255,255,0.06);border-radius:8px;">'
                        f'&#9888;&#65039; Dump location &ldquo;{e(dump_loc_text)}&rdquo; not found &mdash; update in Dump Locations.</div>')
        else:
            nav_html = (f'<div class="small muted" style="margin-bottom:10px;padding:8px;'
                        f'background:rgba(255,255,255,0.06);border-radius:8px;">Dump location not set for this stop.</div>')
        workflow_btn_html = nav_html + dump_ticket_link

    # ── Photo proof: Off / Encouraged (nudge) / Required (hard gate) ───────
    stop_photos = photos_by_stop.get(stop_id, [])
    has_photo = len(stop_photos) > 0
    photo_gallery = build_photo_gallery_html(stop_photos)

    upload_widget = f"""
    <form method="POST" action="{url_for('upload_stop_photo', stop_id=stop_id)}"
          enctype="multipart/form-data" id="cab-photo-form" style="margin-bottom:10px;">
        <input type="file" name="photos" accept=".png,.jpg,.jpeg,.webp,.pdf" multiple
               capture="environment" id="cab-photo-input" style="display:none;">
        <button type="button" class="btn secondary" id="cab-add-photo-btn" style="width:100%;min-height:48px;"
                onclick="triggerAddPhoto();">
            &#128247; {"Add Another Photo" if has_photo else "Add Photo"}
        </button>
    </form>
    {photo_gallery}
    """

    required_locked = (photo_proof_mode == "required" and not has_photo)
    complete_section = f"""
    <form method="POST" action="{url_for('toggle_stop_complete', stop_id=stop_id)}" id="cab-complete-form"
          data-has-photo="{'1' if has_photo else '0'}" data-photo-mode="{e(photo_proof_mode)}">
        <input type="hidden" name="_csrf_token" value="{_csrf}">
        <button class="cab-complete-btn" type="submit" {"disabled" if required_locked else ""}>&#9989; Complete Stop</button>
    </form>
    {'<div class="cab-photo-status">Take at least one photo to unlock Complete Stop</div>' if required_locked else ''}

    <div id="no-photo-confirm-overlay" class="no-photo-confirm-overlay" hidden></div>
    <div id="no-photo-confirm-modal" class="no-photo-confirm-modal" hidden>
        <div class="no-photo-confirm-title">&#128247; No photo added</div>
        <p class="no-photo-confirm-body">Complete anyway?</p>
        <div class="no-photo-confirm-actions">
            <button type="button" class="btn orange" id="no-photo-complete-anyway">Complete Without Photo</button>
            <button type="button" class="btn secondary" id="no-photo-add-first">Add Photo First</button>
        </div>
    </div>
    """

    meta_bits = []
    if s["container_size"]:
        meta_bits.append(e(s["container_size"]))
    if s["notes"]:
        meta_bits.append(e(s["notes"]))
    meta_line = " &middot; ".join(meta_bits) if meta_bits else ""
    ticket_line = f'<div class="cab-meta-line"><strong>Ticket:</strong> {e(s["ticket_number"])}</div>' if s["ticket_number"] else ""
    phone_line = f'<div class="cab-meta-line"><strong>Phone:</strong> <a href="tel:{e(_s["phone"])}" style="color:#3DDC84;">{e(_s["phone"])}</a></div>' if _s.get("phone") else ""

    body = f"""
<div class="cab-wrap">
    <div class="cab-header">
        <div class="cab-title">MY ROUTE</div>
        <div style="display:flex;align-items:center;gap:10px;">
            {gear_button_html}
            <span class="cab-online-badge" id="online-badge"><span class="cab-online-dot"></span>ONLINE</span>
        </div>
    </div>
    {nav_pref_modal_html}

    <div id="route-updated-banner" class="route-updated-banner" hidden>
        <span id="route-updated-text"></span>
        <button type="button" onclick="document.getElementById('route-updated-banner').hidden=true;" aria-label="Dismiss">&times;</button>
    </div>

    <div class="cab-progress-label" id="cab-progress-label">STOP {current_stop_num} OF {total_count}</div>
    <div class="cab-progress-track"><div class="cab-progress-fill" id="cab-progress-fill" style="width:{pct}%;"></div></div>

    {f'''
    <form method="POST" action="{url_for('toggle_stop_complete', stop_id=prev_stop['id'])}" style="margin-bottom:14px;"
          onsubmit="return confirm('Reopen the previous stop? Its progress will reset and it will become your current stop again.');">
        <input type="hidden" name="_csrf_token" value="{_csrf}">
        <button type="submit" class="btn secondary" style="min-height:48px;">&#8592; Previous Stop</button>
    </form>
    ''' if prev_stop else ''}

    <div class="cab-card">
        <div class="cab-action-row">
            <div class="cab-action-badge {badge_group}">{e(s['action'] or 'STOP')}</div>
            <div class="cab-action-name">{e(s['customer_name'] or ('Stop ' + str(current_stop_num)))}</div>
        </div>

        <div class="cab-address">{e(full_address or 'No address on file')}</div>
        {f'<div class="cab-meta-line">{meta_line}</div>' if meta_line else ''}
        {ticket_line}
        {phone_line}

        <a class="cab-nav-btn" href="{nav_google_web}"
           onclick="return openNavStop(event, {_nav_pref_js}, {_full_addr_js})">
            &#128205; Tap to Navigate
        </a>
        <button type="button" class="cab-copy-btn" onclick="copyStopAddress(this, {_full_addr_js})">
            &#128203; Copy Address
        </button>
        <div id="cab-copy-hint" class="cab-copy-hint" hidden>
            Using a Garmin or in-dash GPS? Copy the address and enter it on your unit.
        </div>
        <button type="button" class="cab-copy-btn" id="msg-boss-btn" onclick="openMessageThread({route_id}, 'Boss')">
            &#128172; Message Boss<span id="msg-boss-badge" class="lane-msg-badge" {"hidden" if not unread_messages else ""}>{unread_messages or ""}</span>
        </button>

        <div style="margin-top:20px;">
            {workflow_btn_html}
            {upload_widget}
            {complete_section}
        </div>
    </div>

    <div style="display:flex;gap:10px;flex-wrap:wrap;">
        {route_action_buttons}
        <a class="btn secondary" href="{url_for('driver_dashboard')}">&#8592; My Routes</a>
    </div>
</div>

{_message_thread_modal_html(show_quick_taps=True)}

<div id="gps-preprompt-overlay" class="no-photo-confirm-overlay" hidden></div>
<div id="gps-preprompt-modal" class="no-photo-confirm-modal" hidden>
    <div class="no-photo-confirm-title">&#128205; Location</div>
    <p class="no-photo-confirm-body">HAULTRA uses your location at stop completion
    to record where containers are placed.</p>
    <div class="no-photo-confirm-actions">
        <button type="button" class="btn orange" id="gps-preprompt-allow">Allow Location</button>
        <button type="button" class="btn secondary" id="gps-preprompt-skip">Not Now</button>
    </div>
</div>

<script>{_gps_settings_js()}</script>
<script>{_gps_capture_js()}</script>
<script>
(function() {{
    var badge = document.getElementById('online-badge');
    function upd() {{
        if (!badge) return;
        badge.innerHTML = navigator.onLine
            ? '<span class="cab-online-dot"></span>ONLINE'
            : '<span class="cab-online-dot" style="background:#FF5252;box-shadow:0 0 6px #FF5252;"></span>OFFLINE';
        badge.style.color = navigator.onLine ? '' : '#FF5252';
    }}
    window.addEventListener('online', upd);
    window.addEventListener('offline', upd);
    upd();

    // Show the Garmin/GPS-unit hint under Copy Address once, ever, per device.
    try {{
        if (!localStorage.getItem('haultra_copy_hint_seen')) {{
            var copyHint = document.getElementById('cab-copy-hint');
            if (copyHint) {{ copyHint.hidden = false; }}
            localStorage.setItem('haultra_copy_hint_seen', '1');
        }}
    }} catch (e) {{ /* localStorage unavailable (e.g. private browsing) — skip the hint */ }}

    // Poll for mid-route changes (a boss adding stops via Route Board) every
    // ~30s. Never swaps the currently-displayed stop out from under the driver
    // — only the progress counter/bar and a dismissible banner update live.
    (function() {{
        var baselineTotal = {total_count};
        var lastKnownTotal = baselineTotal;
        var lastKnownUnread = {unread_messages};
        function poll() {{
            fetch('{url_for("driver_route_status", route_id=route_id)}', {{credentials: 'same-origin'}})
                .then(function(r) {{ return r.ok ? r.json() : null; }})
                .then(function(data) {{
                    if (!data) return;
                    var banner = document.getElementById('route-updated-banner');
                    var text = document.getElementById('route-updated-text');

                    if (typeof data.total === 'number' && data.total > lastKnownTotal) {{
                        var delta = data.total - lastKnownTotal;
                        lastKnownTotal = data.total;
                        var label = document.getElementById('cab-progress-label');
                        if (label && data.current_stop_num) {{
                            label.textContent = 'STOP ' + data.current_stop_num + ' OF ' + data.total;
                        }}
                        var fill = document.getElementById('cab-progress-fill');
                        if (fill && data.total > 0) {{
                            fill.style.width = Math.round((data.completed / data.total) * 100) + '%';
                        }}
                        if (banner && text) {{
                            text.textContent = 'Route updated — ' + delta + ' stop' + (delta === 1 ? '' : 's') + ' added.';
                            banner.hidden = false;
                        }}
                    }}

                    if (typeof data.unread_messages === 'number') {{
                        var msgBadge = document.getElementById('msg-boss-badge');
                        if (msgBadge) {{
                            if (data.unread_messages > 0) {{
                                msgBadge.textContent = data.unread_messages;
                                msgBadge.hidden = false;
                            }} else {{
                                msgBadge.hidden = true;
                            }}
                        }}
                        var threadOpen = document.getElementById('msg-modal') && !document.getElementById('msg-modal').hidden;
                        if (data.unread_messages > lastKnownUnread && !threadOpen && banner && text) {{
                            text.textContent = 'New message from boss';
                            banner.hidden = false;
                        }}
                        lastKnownUnread = data.unread_messages;
                    }}
                }})
                .catch(function() {{ /* offline or transient — try again next cycle */ }});
        }}
        setInterval(poll, 30000);
    }})();

    // Photo input opens the camera/file picker directly and uploads on
    // selection — no separate Upload press, multi-photo still supported
    // via the `multiple` attribute on the hidden input. This is the web
    // path; inside the Capacitor app, triggerAddPhoto() below uses the
    // native Camera plugin instead and this input is never clicked.
    var photoInput = document.getElementById('cab-photo-input');
    var photoForm = document.getElementById('cab-photo-form');
    if (photoInput && photoForm) {{
        photoInput.addEventListener('change', function() {{
            if (photoInput.files && photoInput.files.length) {{
                photoForm.submit();
            }}
        }});
    }}

    // Add Photo — native Camera plugin when running inside the Capacitor
    // app (this site has no Capacitor wrapper today, so on the web this
    // always falls through to the plain file input, unchanged from before).
    function getCapacitorCamera() {{
        try {{
            var cap = window.Capacitor;
            if (cap && typeof cap.isNativePlatform === 'function' && cap.isNativePlatform() &&
                cap.Plugins && cap.Plugins.Camera) {{
                return cap.Plugins.Camera;
            }}
        }} catch (e) {{}}
        return null;
    }}

    window.triggerAddPhoto = function() {{
        var camera = getCapacitorCamera();
        if (!camera || !photoForm) {{
            if (photoInput) photoInput.click();
            return;
        }}
        var btn = document.getElementById('cab-add-photo-btn');
        var originalLabel = btn ? btn.textContent : '';
        camera.getPhoto({{
            quality: 85,
            allowEditing: false,
            resultType: 'uri',
            source: 'PROMPT',
        }}).then(function(photo) {{
            if (btn) {{ btn.disabled = true; btn.textContent = 'Uploading…'; }}
            return fetch(photo.webPath).then(function(r) {{ return r.blob(); }}).then(function(blob) {{
                var fd = new FormData();
                var csrf = (document.querySelector('meta[name="csrf-token"]') || {{}}).content || '';
                fd.append('_csrf_token', csrf);
                fd.append('photos', blob, 'photo.' + (photo.format || 'jpeg'));
                return fetch(photoForm.action, {{ method: 'POST', body: fd }});
            }});
        }}).then(function() {{
            window.location.reload();
        }}).catch(function() {{
            // Driver cancelled the native camera sheet, or capture failed —
            // stay silent and restore the button, same as cancelling the
            // web file picker does nothing either.
            if (btn) {{ btn.disabled = false; btn.textContent = originalLabel; }}
        }});
    }};

    // Submit Complete Stop via AJAX (X-Requested-With) so the shared
    // /stop/<id>/toggle endpoint takes its JSON branch instead of its
    // default redirect to the boss route page — then just reload this
    // page so Cab View naturally advances to the next stop.
    var completeForm = document.getElementById('cab-complete-form');
    if (completeForm) {{
        var hasPhoto  = completeForm.dataset.hasPhoto === '1';
        var photoMode = completeForm.dataset.photoMode;
        var overlay   = document.getElementById('no-photo-confirm-overlay');
        var modal     = document.getElementById('no-photo-confirm-modal');

        function doSubmit(gps) {{
            var btn = completeForm.querySelector('button');
            var fd = new FormData(completeForm);
            if (gps) {{
                fd.append('gps_lat', gps.lat);
                fd.append('gps_lng', gps.lng);
                if (gps.accuracy != null) fd.append('gps_accuracy', gps.accuracy);
            }}
            fetch(completeForm.action, {{
                method: 'POST',
                headers: {{ 'X-Requested-With': 'XMLHttpRequest' }},
                body: fd,
            }})
            .then(function(r) {{ return r.json(); }})
            .then(function(data) {{
                if (data && data.success) {{
                    window.location.reload();
                }} else {{
                    throw new Error('not ok');
                }}
            }})
            .catch(function() {{
                if (btn) {{
                    btn.disabled = false;
                    btn.textContent = '✅ Complete Stop';
                }}
                alert('Could not complete stop — check your connection and try again.');
            }});
        }}

        // GPS capture never blocks completion — permission denial, an
        // unsupported browser, or a dead-zone timeout all resolve to null
        // within ~5.3s (see _gps_capture_js) and the stop completes anyway.
        function submitComplete() {{
            var btn = completeForm.querySelector('button');
            if (btn) {{ btn.disabled = true; btn.textContent = 'Saving…'; }}
            if (typeof window.captureGpsStamp === 'function') {{
                window.captureGpsStamp(function(gps) {{ doSubmit(gps); }});
            }} else {{
                doSubmit(null);
            }}
        }}

        function closeNoPhotoConfirm() {{
            if (overlay) overlay.hidden = true;
            if (modal) modal.hidden = true;
        }}

        var completeAnywayBtn = document.getElementById('no-photo-complete-anyway');
        var addFirstBtn = document.getElementById('no-photo-add-first');
        if (completeAnywayBtn) {{
            completeAnywayBtn.addEventListener('click', function() {{
                closeNoPhotoConfirm();
                submitComplete();
            }});
        }}
        if (addFirstBtn) {{
            addFirstBtn.addEventListener('click', function() {{
                closeNoPhotoConfirm();
                if (photoInput) photoInput.click();
            }});
        }}

        completeForm.addEventListener('submit', function(ev) {{
            ev.preventDefault();
            // Encouraged mode + zero photos: nudge once, one tap through either way.
            // Off mode never prompts; Required mode's button is disabled server-side
            // until a photo exists, so this branch only ever applies to Encouraged.
            if (!hasPhoto && photoMode === 'encouraged') {{
                if (overlay) overlay.hidden = false;
                if (modal) modal.hidden = false;
                return;
            }}
            submitComplete();
        }});
    }}

    // Tap to Navigate — respects the driver's nav app preference (set via the
    // gear panel / Team). pref === '' means no preference was ever set, which
    // keeps the original Google-app-then-web-fallback behavior unchanged.
    window.openNavStop = function(ev, pref, address) {{
        ev.preventDefault();
        var enc = encodeURIComponent(address);
        var isIOS = /iPad|iPhone|iPod/.test(navigator.userAgent) ||
            (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
        var isAndroid = /Android/.test(navigator.userAgent);

        if (pref === 'google') {{
            window.location = 'https://maps.google.com/?daddr=' + enc;
            return false;
        }}
        if (pref === 'apple') {{
            window.location = 'https://maps.apple.com/?daddr=' + enc;
            return false;
        }}
        if (pref === 'waze') {{
            window.location = 'https://waze.com/ul?q=' + enc + '&navigate=yes';
            return false;
        }}
        if (pref === 'device_default') {{
            if (isAndroid) {{
                window.location = 'geo:0,0?q=' + enc;
            }} else if (isIOS) {{
                window.location = 'https://maps.apple.com/?daddr=' + enc;
            }} else {{
                window.location = 'https://maps.google.com/?daddr=' + enc;
            }}
            return false;
        }}

        // No preference set — original behavior: try the Google Maps app via
        // its URL scheme, fall back to the web version if it didn't open.
        var appUrl = 'comgooglemaps://?daddr=' + enc + '&directionsmode=driving';
        var webUrl = 'https://www.google.com/maps/dir/?api=1&destination=' + enc;
        if (isIOS || isAndroid) {{
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

    // Copy Address — for drivers using a dedicated GPS unit (Garmin etc.)
    // that can't receive links.
    window.copyStopAddress = function(btn, address) {{
        var original = btn.textContent;
        function flash() {{
            btn.textContent = 'Copied ✓';
            setTimeout(function() {{ btn.textContent = original; }}, 2000);
        }}
        if (navigator.clipboard && navigator.clipboard.writeText) {{
            navigator.clipboard.writeText(address).then(flash, function() {{
                alert('Could not copy — long-press the address above to copy it manually.');
            }});
        }} else {{
            // Fallback for older/non-secure-context browsers without the Clipboard API.
            var ta = document.createElement('textarea');
            ta.value = address;
            ta.style.position = 'fixed';
            ta.style.opacity = '0';
            document.body.appendChild(ta);
            ta.focus();
            ta.select();
            try {{
                document.execCommand('copy');
                flash();
            }} catch (err) {{
                alert('Could not copy — long-press the address above to copy it manually.');
            }}
            document.body.removeChild(ta);
        }}
    }};
}})();
{_message_thread_js()}
</script>
"""
    return render_template_string(shell_page("Cab View", body))


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
      'background:#0a1826','border:1px solid #55554C','border-top:none',
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
                '<div style="color:#FF9D5C;font-weight:600;">' + _esc(d.customer_name) + '</div>' +
                (line2 ? '<div style="color:#8C8C82;font-size:11px;margin-top:2px;">' + _esc(line2) + '</div>' : '');
              item.addEventListener('mouseenter', function() { this.style.background = 'rgba(255,107,26,.08)'; });
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
.pr-card{background:rgba(23,23,23,.75);border:1px solid rgba(255,107,26,.14);border-radius:14px;padding:20px 22px;margin-bottom:18px}
.pr-card h3{margin:0 0 4px;font-size:15px;color:#F5F5F0;font-weight:800;letter-spacing:.3px}
.pr-card .pr-sub{font-size:12px;color:#8C8C82;margin:0 0 14px}
.pr-stop{border-radius:10px;padding:15px;margin-bottom:12px;position:relative;transition:opacity .2s,height .2s,padding .2s,margin .2s}
.pr-stop.h{background:rgba(0,232,125,.04);border:1px solid rgba(0,232,125,.18)}
.pr-stop.m{background:rgba(255,157,0,.05);border:1px solid rgba(255,157,0,.20)}
.pr-stop.l{background:rgba(255,59,92,.05);border:1px solid rgba(255,59,92,.20)}
.pr-badge{display:inline-flex;align-items:center;padding:3px 10px;border-radius:20px;font-size:11px;font-weight:700;letter-spacing:.3px;margin-right:4px}
.pr-b-pr{background:rgba(255,107,26,.14);color:#FF9D5C}
.pr-b-p{background:rgba(251,191,36,.12);color:#fbbf24}
.pr-b-d{background:rgba(140,160,179,.16);color:#8CA0B3}
.pr-b-swap{background:rgba(140,160,179,.16);color:#8CA0B3}
.pr-b-move{background:rgba(140,160,179,.16);color:#8CA0B3}
.pr-b-relocate{background:rgba(140,160,179,.16);color:#8CA0B3}
.pr-b-other{background:rgba(120,120,150,.12);color:#9aa5b8}
.pr-ch{background:rgba(61,220,132,.14);color:#3DDC84}
.pr-cm{background:rgba(251,191,36,.10);color:#fbbf24}
.pr-cl{background:rgba(255,59,92,.10);color:#ff7090}
.pr-saved{background:rgba(140,160,179,.12);color:#8CA0B3;border:1px solid rgba(140,160,179,.28)}
.pr-lbl{display:block;font-size:10px;color:#8C8C82;font-weight:700;text-transform:uppercase;letter-spacing:.5px;margin-bottom:3px}
.pr-inp{width:100%;background:rgba(0,0,0,.35);border:1px solid rgba(255,107,26,.14);border-radius:7px;color:#F5F5F0;padding:7px 10px;font-size:13px;box-sizing:border-box;font-family:inherit}
.pr-inp:focus{outline:none;border-color:rgba(255,107,26,.40)}
.pr-miss .pr-inp{border-color:rgba(251,191,36,.4)!important;background:rgba(251,191,36,.03)!important}
.pr-miss .pr-lbl{color:#fbbf24}
.pr-orig{font-size:11px;color:#78786F;font-style:italic;font-family:monospace;background:rgba(0,0,0,.18);border-radius:5px;padding:5px 9px;margin-bottom:12px}
.pr-warn-strip{margin-top:10px;padding:6px 12px;border-radius:6px;font-size:12px;background:rgba(251,191,36,.07);border:1px solid rgba(251,191,36,.2);color:#fbbf24}
.pr-card-acts{display:flex;gap:8px;margin-top:12px;flex-wrap:wrap}
.pr-btn-sm{font-size:12px;padding:5px 12px;border-radius:6px;border:none;cursor:pointer;font-weight:600;font-family:inherit}
.pr-btn-remove{background:rgba(255,59,92,.10);color:#ff7090}
.pr-btn-remove:hover{background:rgba(255,59,92,.22)}
.pr-sugg{padding:9px 13px;border-radius:8px;margin-bottom:8px;font-size:13px;line-height:1.4;display:flex;align-items:flex-start;gap:8px}
.pr-sw{background:rgba(251,191,36,.07);border:1px solid rgba(251,191,36,.18);color:#fbbf24}
.pr-si{background:rgba(140,160,179,.08);border:1px solid rgba(140,160,179,.22);color:#8CA0B3}
.pr-se{background:rgba(255,59,92,.07);border:1px solid rgba(255,59,92,.18);color:#ff7090}
.pr-footer-bar{display:flex;gap:12px;align-items:center;flex-wrap:wrap;padding:14px 0 2px;border-top:1px solid rgba(255,107,26,.12);margin-top:10px}
.pr-footer-count{font-size:13px;color:#8C8C82;flex:1}
.pr-tip-item{font-size:12px;color:#A6A69E;padding:7px 0;border-bottom:1px solid rgba(255,107,26,.10)}
.pr-tip-item:last-child{border-bottom:none}
.pr-tip-item strong{color:#FF9D5C}
.pr-tip-code{font-family:monospace;background:rgba(0,0,0,.3);border-radius:4px;padding:2px 6px;color:#FF9D5C;font-size:11px}
#pr-mobile-bar{display:none;position:fixed;bottom:0;left:0;right:0;z-index:1200;background:rgba(20,20,20,.97);border-top:1px solid rgba(255,107,26,.24);padding:12px 16px;gap:10px}
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
    preview.innerHTML = '<p style="color:#78786F;padding:24px 0;font-size:13px;text-align:center;">Analyzing route lines\u2026</p>';
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
      preview.innerHTML = '<p style="color:#78786F;padding:16px 0;font-size:13px;">No stops detected. Try one stop per line.</p>';
      if (footer) footer.style.display = 'none';
      if (mobileBar) mobileBar.classList.remove('pr-show');
      if (suggCard) suggCard.style.display = 'none';
      return;
    }
    var _cards = [];
    _stops.forEach(function(s, i) {
      if (_removed[i]) { _cards.push(''); return; }
      try { _cards.push(cardHTML(s, i)); }
      catch(e) {
        console.error('pr card render error stop ' + i, e);
        _cards.push('<div class="pr-stop l" id="pr-card-' + i + '" style="padding:12px;">'
          + '<p style="color:#ff7090;margin:0;">Stop ' + (i+1) + ' render error: ' + String(e) + '</p>'
          + '</div>');
      }
    });
    preview.innerHTML = _cards.join('');
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
  function actionBadge(action, prMode) {
    var a = (action || '').trim().toUpperCase();
    var cls = 'pr-b-other', lbl = a || '?';
    if (/PICKUP.*RETURN|^PICKUP AND RETURN$/.test(a) || a === 'PR' || /P.*&.*R/.test(a)) {
      cls = 'pr-b-pr';
      lbl = (prMode === 'swap') ? 'PR • Swap' : 'Pickup & Return';
    }
    else if (/^PULL$|^P$/.test(a))    { cls = 'pr-b-p';        lbl = 'Pull'; }
    else if (/^DELIVERY$|^D$/.test(a)){ cls = 'pr-b-d';        lbl = 'Delivery'; }
    else if (/^SWAP$/.test(a))        { cls = 'pr-b-swap';     lbl = 'Swap'; }
    else if (/^MOVE$/.test(a))        { cls = 'pr-b-move';     lbl = 'Move'; }
    else if (/^RELOCATE$/.test(a))    { cls = 'pr-b-relocate'; lbl = 'Relocate'; }
    return '<span class="pr-badge ' + cls + '">' + _esc(lbl) + '</span>';
  }

  /* ── Missing field check ──────────────────────────────────────────────── */
  function missFlds(s) {
    var m = [];
    var a = (s.action || '').toUpperCase();
    var noDump = /^(MOVE|RELOCATE)$/.test(a);
    if (!noDump && !s.dump_location) m.push('dump');
    if (!s.address && !s.from_address) m.push('address');
    if (!s.customer_name && a !== 'RELOCATE' && a !== 'MOVE') m.push('customer');
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
    var a = (s.action || '').toUpperCase();
    var isRelocate = a === 'RELOCATE';
    var isMove     = a === 'MOVE';
    var savedBadge = s.matched_saved ? '<span class="pr-badge pr-saved">&#11042; Saved</span>' : '';

    // Warnings
    var warnMsgs = miss.map(function(f) {
      return {dump:'Missing dump location', address:'No address', customer:'No customer name', action:'Action unknown'}[f] || ('Missing: ' + f);
    });
    if (s.warnings && s.warnings.length) warnMsgs = warnMsgs.concat(s.warnings);
    var warnStrip = warnMsgs.length ? '<div class="pr-warn-strip">&#9888; ' + warnMsgs.join(' &bull; ') + '</div>' : '';

    var mIdx = function(f) { return miss.indexOf(f) >= 0; };

    // Extra info strip (RELOCATE from/to, return destination, placement note)
    var extraInfo = '';
    if (isRelocate && (s.from_address || s.to_address)) {
      extraInfo += '<div style="font-size:11px;color:#B8B8AE;margin-bottom:6px;">'
        + '&#8680; From: <b>' + _esc(s.from_address || s.address) + (s.from_city ? ' (' + _esc(s.from_city) + ')' : '') + '</b>'
        + ' &nbsp;&#8594;&nbsp; To: <b>' + _esc(s.to_address) + (s.to_city ? ' (' + _esc(s.to_city) + ')' : '') + '</b>'
        + '</div>';
    }
    if (s.placement_note) {
      extraInfo += '<div style="font-size:11px;color:#fbbf24;margin-bottom:6px;">&#128204; Placement: ' + _esc(s.placement_note) + '</div>';
    }
    if (s.return_destination) {
      extraInfo += '<div style="font-size:11px;color:#3DDC84;margin-bottom:6px;">&#8617; Return to: <b>' + _esc(s.return_destination) + '</b></div>';
    }
    if (s.swap_with_previous_empty) {
      extraInfo += '<div style="font-size:11px;color:#ff9d00;margin-bottom:6px;">&#9654; SWAP — uses empty can from previous stop</div>';
    }
    if (s.pending_empty_can_for_next_pr) {
      extraInfo += '<div style="font-size:11px;color:#ff9d00;margin-bottom:6px;">&#9654; Empty can held for next PR stop</div>';
    }

    // For RELOCATE: show from/to address fields; for others: show normal address
    var addrFields = isRelocate
      ? fld('From Address', 'pr-addr-' + i,  s.from_address || s.address, '1/-1', mIdx('address'))
        + fld('To Address',   'pr-toaddr-' + i, s.to_address,              '1/-1', false)
      : fld('Address', 'pr-addr-' + i, s.address, '1/-1', mIdx('address'));

    var dumpField = (isMove || isRelocate)
      ? fld('Placement Note', 'pr-place-' + i, s.placement_note, '1/-1', false)
      : dumpFld('pr-dump-' + i, s.dump_location, mIdx('dump'));

    return (
      '<div class="pr-stop ' + confCls(s) + '" id="pr-card-' + i + '">'
      + '<div style="display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:10px;flex-wrap:wrap;">'
        + '<div style="display:flex;align-items:center;gap:6px;flex-wrap:wrap;">'
          + '<label style="display:flex;align-items:center;gap:7px;cursor:pointer;font-size:12px;color:#B8B8AE;font-weight:700;">'
            + '<input type="checkbox" id="pr-chk-' + i + '" checked style="width:15px;height:15px;accent-color:#FF9D5C;"> Stop ' + (i + 1)
          + '</label>'
          + actionBadge(s.action, s.pr_mode)
        + '</div>'
        + '<div style="display:flex;align-items:center;gap:6px;">'
          + savedBadge
          + '<span class="pr-badge ' + confBCls(s) + '">' + confLbl(s) + ' (' + s.confidence + '%)</span>'
        + '</div>'
      + '</div>'
      + '<div class="pr-orig">&ldquo;' + _esc(s.original_line || '') + '&rdquo;</div>'
      + extraInfo
      + '<div style="display:grid;grid-template-columns:1fr 1fr;gap:8px;">'
        + fld('Customer', 'pr-cust-' + i,   s.customer_name,  '1/-1', mIdx('customer'))
        + addrFields
        + fld('City',     'pr-city-' + i,   s.city,           null,   false)
        + fld('State',    'pr-state-' + i,  s.state,          null,   false)
        + fld('Action',   'pr-action-' + i, s.action,         null,   mIdx('action'))
        + fld('Container','pr-cont-' + i,   s.container_size, null,   false)
        + dumpField
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
      var isRel = (s.action || '').toUpperCase() === 'RELOCATE';
      var stop = {
        customer_name:       _v('pr-cust-'   + i),
        address:             _v('pr-addr-'   + i),
        city:                _v('pr-city-'   + i),
        state:               _v('pr-state-'  + i),
        zip_code:            _v('pr-zip-'    + i),
        action:              _v('pr-action-' + i),
        container_size:      _v('pr-cont-'   + i),
        dump_location:       _v('pr-dump-'   + i),
        placement_note:      _v('pr-place-'  + i),
        relocate_to_address: _v('pr-toaddr-' + i),
        // preserve parser-detected flags through to the backend
        pr_mode:             s.pr_mode             || '',
        swap_with_prev_pull: s.swap_with_prev_pull || 0,
        swap_with_previous_empty: s.swap_with_previous_empty || false,
        return_destination:  s.return_destination  || '',
        relocate_to_city:    s.to_city             || '',
      };
      if (s.confidence < 45)                           hasLow = true;
      var addrOk = stop.address || (isRel && _v('pr-toaddr-' + i));
      if (!addrOk || (!stop.customer_name && !isRel))  hasMissReq = true;
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
            _sarow = conn.execute(
                "SELECT id FROM saved_addresses WHERE company_id=? AND customer_name=? AND address=?",
                (company_id, cname, addr)
            ).fetchone()
            if not _sarow:
                return
            sa_id = _sarow["id"]

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
    except Exception as e:
        app.logger.warning("upsert_saved_address failed for %r: %s", addr, e)


@app.route("/driver/route/<int:route_id>/status")
@login_required
def driver_route_status(route_id):
    """Lightweight JSON polled by Cab View (~30s) so a boss adding stops mid-route
    shows up as an updated stop count + banner without disrupting the driver's
    current stop."""
    conn = get_db()
    route = conn.execute(
        "SELECT id, assigned_to FROM routes WHERE id=? AND company_id=?",
        (route_id, cid())
    ).fetchone()
    if not route:
        conn.close()
        return jsonify({"error": "Route not found."}), 404
    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        return jsonify({"error": "Access denied."}), 403

    stops = conn.execute(
        "SELECT status FROM stops WHERE route_id=? ORDER BY stop_order ASC, id ASC",
        (route_id,)
    ).fetchall()

    unread_messages = conn.execute(
        "SELECT COUNT(*) n FROM messages WHERE route_id=? AND sender_user_id != ? AND read_at IS NULL",
        (route_id, session["user_id"])
    ).fetchone()["n"]

    conn.close()

    total = len(stops)
    completed = sum(1 for s in stops if s["status"] == "completed")
    current_stop_num = None
    for i, s in enumerate(stops, start=1):
        if s["status"] != "completed":
            current_stop_num = i
            break

    return jsonify({
        "total": total, "completed": completed, "current_stop_num": current_stop_num,
        "unread_messages": unread_messages,
    })


@app.route("/route/<int:route_id>/messages", methods=["GET", "POST"])
@login_required
def route_messages(route_id):
    """Minimal per-route boss<->driver thread. GET returns the full thread and
    marks the other party's messages as read; POST appends a new message.
    'Unread' is derived per-viewer (not sent by me, read_at IS NULL) rather
    than tracked per-recipient — a route thread only ever has two sides."""
    conn = get_db()
    route = conn.execute(
        "SELECT id, assigned_to FROM routes WHERE id=? AND company_id=?",
        (route_id, cid())
    ).fetchone()
    if not route:
        conn.close()
        return jsonify({"error": "Route not found."}), 404
    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        return jsonify({"error": "Access denied."}), 403

    if request.method == "POST":
        data = request.get_json(silent=True) or {}
        body = (data.get("body") or "").strip()[:500]
        if not body:
            conn.close()
            return jsonify({"error": "Message can't be empty."}), 400

        cur = conn.cursor()
        cur.execute(
            "INSERT INTO messages (route_id, sender_user_id, body, created_at) VALUES (?, ?, ?, ?)",
            (route_id, session["user_id"], body, now_ts())
        )
        conn.commit()
        msg_id = cur.lastrowid
        conn.close()
        return jsonify({"success": True, "id": msg_id})

    # GET — mark the other party's messages read, then return the full thread.
    conn.execute(
        "UPDATE messages SET read_at=? WHERE route_id=? AND sender_user_id != ? AND read_at IS NULL",
        (now_ts(), route_id, session["user_id"])
    )
    conn.commit()

    rows = conn.execute("""
        SELECT m.id, m.sender_user_id, u.username AS sender_username, u.role AS sender_role,
               m.body, m.created_at
        FROM messages m JOIN users u ON u.id = m.sender_user_id
        WHERE m.route_id=?
        ORDER BY m.id ASC
    """, (route_id,)).fetchall()
    conn.close()

    return jsonify({"messages": [
        {
            "id": r["id"], "sender_username": r["sender_username"], "sender_role": r["sender_role"],
            "body": r["body"], "created_at": r["created_at"],
            "is_me": r["sender_user_id"] == session["user_id"],
        }
        for r in rows
    ]})


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

    # can_state_before is populated by write operations (add/edit/reorder/optimize).
    # Legacy routes with null values are repaired on the next explicit write, not here.

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
        # Paste Route is dispatch tooling (parses text → builds stops), so it's
        # dispatcher/owner only — not a customer-manager-only boss — consistent
        # with the /api/parse-route-text gate. Daily Log / Optimize / Delete stay
        # available to any management boss.
        _paste_route_btn = (
            '<button class="btn" type="button" onclick="_haulsTogglePaste()" '
            'style="background:linear-gradient(135deg,#FF8A42,#FF6B1A);border:1px solid rgba(255,107,26,.3);">'
            '&#x1F4CB; Paste Route</button>'
            if has_role("dispatcher") else ''
        )
        route_action_buttons += f"""
    {_paste_route_btn}
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
                    'background:rgba(255,107,26,0.15);color:#FF9D5C;padding:2px 8px;'
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
            _pr_mode_col = (dict(s).get("pr_mode") or "").lower().strip()
            # Priority: 1) parser-set pr_mode  2) sequence-derived can_state_before  3) swap_with_prev_pull fallback
            _is_swap_sc = (
                _pr_mode_col == "swap"
                or _csb == "empty_can"
                or (_csb not in ("empty_can", "no_can") and bool(int(dict(s).get("swap_with_prev_pull") or 0)))
            )
            if _is_swap_sc:
                _swap_badge = (
                    ' <span title="PR Mode: Swap — driver carries empty can from prior Pull" '
                    'style="font-size:11px;background:rgba(255,107,26,0.15);color:#FF9D5C;'
                    'padding:2px 8px;border-radius:6px;font-weight:700;vertical-align:middle;">'
                    '&#x1F504; PR Mode: Swap</span>'
                )
            else:
                _swap_badge = (
                    ' <span title="PR Mode: Return Same Can — driver boxes out, dumps, returns empty can to site" '
                    'style="font-size:11px;background:rgba(255,107,26,0.18);color:#FF9D5C;'
                    'padding:2px 8px;border-radius:6px;font-weight:700;vertical-align:middle;">'
                    '&#x21A9;&#xFE0F; PR Mode: Return Same Can</span>'
                )
            _swap_warning = ""
        else:
            _swap_badge   = ""
            _swap_warning = ""

        # Build address/service display for this stop
        _s_action_lc   = (dict(s).get("action") or "").lower()
        _is_relocate_s = "relocate" in _s_action_lc
        _is_move_s     = _s_action_lc == "move"

        _dump_ticket_btn = (
            f'<a class="btn secondary" href="{url_for("dump_ticket", stop_id=s["id"])}" style="font-size:13px;">&#x1F9FE; Dump Ticket</a>'
            if (dict(s).get("dump_location") or "").strip() else ""
        )

        if _is_relocate_s:
            _rel_to   = e(dict(s).get("relocate_to_address") or "")
            _ret_dest = e(dict(s).get("return_destination") or "")
            _place_nt = e(dict(s).get("placement_note") or "")
            _addr_block = (
                f'<p><strong>From:</strong> {e(s["address"] or "")} {e(s["city"] or "")} {e(s["state"] or "")}</p>'
                + (f'<p><strong>To:</strong> {_rel_to}</p>' if _rel_to else "")
                + (f'<p><strong>Placement:</strong> {_place_nt}</p>' if _place_nt else "")
                + (f'<p><strong>Return To:</strong> {_ret_dest}</p>' if _ret_dest else "")
            )
        elif _is_move_s:
            _place_nt   = e(dict(s).get("placement_note") or "")
            _addr_block = (
                f'<p><strong>Address:</strong> {e(s["address"] or "")} {e(s["city"] or "")} {e(s["state"] or "")} {e(s["zip_code"] or "")}</p>'
                + (f'<p><strong>Placement:</strong> {_place_nt}</p>' if _place_nt else "")
            )
        else:
            _ret_dest   = e(dict(s).get("return_destination") or "")
            _addr_block = (
                f'<p><strong>Address:</strong> {e(s["address"] or "")} {e(s["city"] or "")} {e(s["state"] or "")} {e(s["zip_code"] or "")}</p>'
                + (f'<p><strong>Return To:</strong> {_ret_dest}</p>' if _ret_dest else "")
            )

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
                    {_dump_ticket_btn}
                    <form class="inline" method="POST" action="{url_for('toggle_stop_complete', stop_id=s['id'])}">
                        <button class="btn green" type="submit">{'Reopen Stop' if s['status']=='completed' else 'Complete Stop'}</button>
                    </form>
                </div>
            </div>
            <p><strong>Customer:</strong> {e(s['customer_name'] or '')}</p>
            {_addr_block}
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
    if has_role("dispatcher"):  # dispatch tooling — dispatcher/owner only (matches the button)
        _dump_locs_json = json.dumps([dl["name"] for dl in dump_locs_for_form])
        paste_panel_block = f"""
        {_PASTE_ROUTE_CSS}
        <div id="paste-route-panel" style="display:none;margin-bottom:24px;">

            <!-- Panel header -->
            <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:18px;padding-bottom:16px;border-bottom:1px solid rgba(255,107,26,.1);">
                <div>
                    <h2 style="margin:0 0 4px;font-size:20px;color:#e5eefc;">&#x1F4CB; Paste Route</h2>
                    <p style="margin:0;font-size:13px;color:#4a6a88;">Paste messy route text &mdash; HAULTRA structures it into stops.</p>
                </div>
                <button id="pr-close-btn" type="button" style="background:rgba(255,255,255,.05);border:1px solid rgba(255,255,255,.1);border-radius:8px;color:#A6A69E;padding:7px 14px;cursor:pointer;font-size:13px;font-family:inherit;">&#x2715; Close</button>
            </div>

            <!-- 2-column grid -->
            <div class="pr-grid">

                <!-- LEFT: Input + Tips -->
                <div>
                    <!-- A: Paste Input -->
                    <div class="pr-card">
                        <h3>Paste Route Text</h3>
                        <p class="pr-sub">Paste one stop per line. HAULTRA will structure the route.</p>
                        <div style="margin-bottom:14px;padding:10px 14px;background:rgba(0,0,0,.2);border-radius:8px;border-left:3px solid rgba(255,107,26,.3);">
                            <div style="font-size:10px;color:#78786F;font-weight:700;text-transform:uppercase;letter-spacing:.5px;margin-bottom:7px;">Examples</div>
                            <div class="pr-tip-code" style="display:block;margin-bottom:4px;">PR 515 central dr talent 30 dom</div>
                            <div class="pr-tip-code" style="display:block;margin-bottom:4px;">P 224 golden maple bartlett 20 wat</div>
                            <div class="pr-tip-code" style="display:block;margin-bottom:4px;">D 900 tidewater quick demo 20</div>
                            <div style="font-size:10px;color:#78786F;font-weight:700;text-transform:uppercase;letter-spacing:.5px;margin:10px 0 5px;">Swap Example</div>
                            <div class="pr-tip-code" style="display:block;margin-bottom:2px;">PR 101 N Dogwood Rd, VB, Bishard 30yd dump dominion and before you return it use it to</div>
                            <div class="pr-tip-code" style="display:block;margin-bottom:4px;">PR 114 Sawyers Creek, Camden, Heartland 30yd dump dominion and return to Dogwood</div>
                            <div style="font-size:10px;color:#78786F;font-weight:700;text-transform:uppercase;letter-spacing:.5px;margin:10px 0 5px;">Relocate Example</div>
                            <div class="pr-tip-code" style="display:block;">Relocate one of the 20s from 224 Golden Maple Dr Chesapeake to 416 Maple Shore Dr Chesapeake place it on the street</div>
                        </div>
                        <textarea id="pr-textarea" rows="8" placeholder="Paste route here &mdash; one stop per line&hellip;" style="width:100%;background:rgba(0,0,0,.4);border:1px solid rgba(255,107,26,.15);border-radius:9px;color:#F5F5F0;padding:12px 14px;font-size:13px;line-height:1.7;resize:vertical;box-sizing:border-box;font-family:monospace;"></textarea>
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
                        <p class="pr-sub" id="pr-preview-sub">Click <strong style="color:#B8B8AE;">Parse Route</strong> to analyze your pasted text.</p>
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
                <p style="margin:10px 0 4px;color:#8C8C82;font-size:11px;">
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
        <div id="optimize-msg" style="font-size:14px; color:#FF9D5C; margin-bottom:24px;">
            Geocoding stops &mdash; this takes about 1 second per stop
        </div>
        <div style="width:240px; background:rgba(255,255,255,0.1); border-radius:999px; height:8px; overflow:hidden;">
            <div id="optimize-progress-bar"
                 style="height:100%; width:0%; border-radius:999px;
                        background:linear-gradient(90deg,#FF9D5C,#FF9D5C);
                        transition:width 1.1s linear;"></div>
        </div>
        <div id="optimize-step" style="font-size:12px; color:#8C8C82; margin-top:10px;"></div>
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
    if session.get("role") != "boss":
        return redirect(url_for("driver_route_detail", route_id=route_id))
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
    if session.get("role") != "boss":
        return redirect(url_for("driver_route_detail", route_id=route_id))
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
    if session.get("role") != "boss":
        return redirect(url_for("driver_route_detail", route_id=route_id))
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
    _edit_photo_count = conn.execute(
        "SELECT COUNT(*) n FROM route_photos WHERE stop_id=?", (stop_id,)
    ).fetchone()["n"]
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
        _pr_mode_edit = (_stop.get("pr_mode") or "").lower().strip()
        # Priority: 1) parser-set pr_mode  2) sequence-derived can_state_before  3) swap_with_prev_pull fallback
        _is_swap_edit = (
            _pr_mode_edit == "swap"
            or _csb_edit == "empty_can"
            or (_csb_edit not in ("empty_can", "no_can") and bool(int(_stop.get("swap_with_prev_pull") or 0)))
        )
        if _is_swap_edit:
            _swap_info_block = """
            <div style="margin-top:16px;padding:14px 16px;
                        background:rgba(255,107,26,0.08);
                        border:1px solid rgba(255,107,26,0.28);border-radius:10px;">
                <p style="margin:0 0 4px;color:#FF9D5C;font-size:13px;font-weight:700;">
                    &#x1F504; PR Mode: Swap
                </p>
                <p style="margin:0;color:#7ab8a8;font-size:12px;">
                    Driver carries an empty can to this stop and swaps it for the full one.
                    Workflow: Arrive &#x2192; Box Out &#x2192; Box In &#x2192; Go To Dump &#x2192; Complete.
                </p>
            </div>"""
        else:
            _swap_info_block = """
            <div style="margin-top:16px;padding:14px 16px;
                        background:rgba(255,107,26,0.07);
                        border:1px solid rgba(255,107,26,0.28);border-radius:10px;">
                <p style="margin:0 0 4px;color:#FF9D5C;font-size:13px;font-weight:700;">
                    &#x21A9;&#xFE0F; PR Mode: Return Same Can
                </p>
                <p style="margin:0;color:#A6A69E;font-size:12px;">
                    Driver boxes out the full can, dumps it, then returns the emptied can to the same site.
                    Workflow: Arrive &#x2192; Box Out &#x2192; Go To Dump &#x2192; Return &amp; Box In &#x2192; Complete.
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

    _photo_indicator = (
        f'<span style="font-size:12px;color:#A6A69E;font-weight:600;">&#128247; {_edit_photo_count} photo{"s" if _edit_photo_count != 1 else ""}</span>'
        if _edit_photo_count else
        '<span style="font-size:12px;color:#55554C;">No photos yet</span>'
    )

    body = f"""
    <div class="card" style="max-width:680px;">
        <div class="row between" style="margin-bottom:18px;">
            <h2 style="margin:0;">Edit Stop</h2>
            {_photo_indicator}
        </div>
        <form method="POST">
            <div class="grid" style="grid-template-columns:1fr 1fr;gap:12px 16px;">
                <div style="grid-column:1/-1;">
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Customer Name</label>
                    <input name="customer_name" value="{e(_stop['customer_name'])}" data-hac="1" autocomplete="off">
                </div>
                <div style="grid-column:1/-1;">
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Address</label>
                    <input name="address" value="{e(_stop['address'])}" data-hac="1" autocomplete="off">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">City</label>
                    <input name="city" value="{e(_stop['city'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">State</label>
                    <input name="state" value="{e(_stop['state'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">ZIP</label>
                    <input name="zip_code" value="{e(_stop['zip_code'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Action</label>
                    <input name="action" value="{e(_stop['action'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Container Size</label>
                    <input name="container_size" value="{e(_stop['container_size'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Ticket Number</label>
                    <input name="ticket_number" value="{e(_stop['ticket_number'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Reference Number</label>
                    <input name="reference_number" value="{e(_stop['reference_number'])}">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Dump Location</label>
                    {_dump_field}
                </div>
                <div style="grid-column:1/-1;">
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Notes</label>
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
    conn.execute("DELETE FROM dump_tickets WHERE stop_id IN (SELECT id FROM stops WHERE route_id=?)", (route_id,))
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
    conn.execute("DELETE FROM dump_tickets WHERE stop_id=?", (stop_id,))
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

    # Optional GPS stamp from the driver's device at the moment of
    # completion — purely best-effort evidence, never required. Bad/missing
    # values just mean no stamp gets stored; completion proceeds either way.
    gps_lat = gps_lng = gps_accuracy = None
    got_gps = False
    if new_status == "completed":
        try:
            _lat = float(request.form.get("gps_lat", ""))
            _lng = float(request.form.get("gps_lng", ""))
            if -90 <= _lat <= 90 and -180 <= _lng <= 180:
                gps_lat, gps_lng = _lat, _lng
                try:
                    gps_accuracy = float(request.form.get("gps_accuracy", ""))
                except (TypeError, ValueError):
                    gps_accuracy = None
                got_gps = True
        except (TypeError, ValueError):
            pass

    conn.execute("""
        UPDATE stops SET status=?, completed_at=?, driver_status=?,
               gps_lat=?, gps_lng=?, gps_accuracy=?, gps_captured_at=?
        WHERE id=?
    """, (new_status, completed_at, new_driver_status,
          gps_lat, gps_lng, gps_accuracy, (now_ts() if got_gps else None),
          stop_id))
    if new_status == "completed":
        update_container_flow(conn, stop_id)
    # Customer Request System: mirror completion/reopen onto a linked request
    # (no-op for normal stops with no request_id).
    cascade_request_from_stop(conn, stop_id)
    conn.commit()

    if new_status == "completed":
        _action_lower = (stop["action"] or "").lower()
        _leaves_container = (
            "delivery" in _action_lower or "drop" in _action_lower
            or "pickup and return" in _action_lower
            or ("swap" in _action_lower and "pull" not in _action_lower)
        )
        # A GPS stamp already gives us the true position — skip the address
        # geocode in that case rather than spend a Nominatim request on
        # data we won't use for positioning.
        if _leaves_container and not got_gps:
            geocode_stop_in_background(stop_id)

    if request.headers.get("X-Requested-With") == "XMLHttpRequest":
        prog      = conn.execute(
            "SELECT COUNT(*) AS total, SUM(status='completed') AS completed FROM stops WHERE route_id=?",
            (stop["route_id"],)
        ).fetchone()
        total, completed = prog["total"], prog["completed"] or 0
        conn.close()
        return jsonify({
            "success": True,
            "stop_id": stop_id,
            "new_status": new_status,
            "completed_at": completed_at or "",
            "progress": {"completed": completed, "total": total},
        })

    conn.close()
    if session.get("role") != "boss":
        return redirect(url_for("driver_route_detail", route_id=stop["route_id"]))
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

    # State machine guard — prevent backwards/invalid transitions.
    # box_in -> going_to_dump covers PR "swap" mode's last step: the driver
    # boxed in the can they just picked up, but it turned out to already be
    # full, so they still need to dump it (see driver_route_detail's
    # is_swap_pr wf_map, which already offers this exact button — this
    # guard just has to allow the transition it triggers).
    _VALID_TRANSITIONS = {
        None:            {"arrived"},
        "pending":       {"arrived"},
        "arrived":       {"box_out", "going_to_dump", "need_box_in", "skip_to_box_in"},
        "box_out":       {"going_to_dump", "need_box_in", "skip_to_box_in"},
        "going_to_dump": {"need_box_in", "skip_to_box_in"},
        "need_box_in":   {"box_in", "skip_to_box_in"},
        "box_in":        {"going_to_dump"},
    }
    current_status = stop["driver_status"]
    allowed = _VALID_TRANSITIONS.get(current_status, set())
    if action not in allowed:
        conn.close()
        if is_replay:
            return jsonify({"conflict": True, "current_status": current_status, "stop_id": stop_id}), 409
        flash(f"Cannot apply '{action}' — stop is already '{current_status}'.", "error")
        return redirect(url_for("driver_route_detail", route_id=stop["rid"]))

    ts = now_ts()

    if action in ("need_box_in", "skip_to_box_in"):
        conn.execute(
            "UPDATE stops SET driver_status='need_box_in' WHERE id=? AND driver_status=?",
            (stop_id, current_status)
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
            f"UPDATE stops SET driver_status=?, {time_col}=? WHERE id=? AND driver_status=?",
            (action, ts, stop_id, current_status)
        )

    if conn.total_changes == 0:
        conn.close()
        if is_replay:
            return jsonify({"conflict": True, "current_status": current_status, "stop_id": stop_id}), 409
        flash(f"Stop was already updated by another action. Current status: '{current_status}'.", "error")
        return redirect(url_for("driver_route_detail", route_id=stop["rid"]))

    # Customer Request System: a driver starting/advancing the stop moves a
    # linked request to 'in_progress' (no-op for normal stops).
    cascade_request_from_stop(conn, stop_id)
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

        # Customer Request System: keep a linked request in sync if this dump
        # step just completed the stop (no-op for normal stops).
        cascade_request_from_stop(conn, stop_id)
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
            <td class="col-num" style="font-weight:700;color:#FF9D5C;">{_w(s['net_tons'])}</td>
            <td class="col-center">{e(s['dump_ticket_number'] or '')}</td>
            <td class="col-center">
                <span class="badge {e(s['status'])}" style="font-size:10px;">{e(s['status'])}</span>
            </td>
        </tr>"""

    body = f"""
    <style>
    .log-tbl {{ width:100%;border-collapse:collapse;font-size:12px;min-width:900px; }}
    .log-tbl th {{
        background:rgba(255,107,26,0.10);color:#FF9D5C;font-size:10px;font-weight:700;
        padding:8px 5px;border-bottom:1px solid rgba(255,107,26,0.22);
        text-align:center;white-space:nowrap;letter-spacing:.4px;
    }}
    .log-tbl td {{ padding:7px 5px;border-bottom:1px solid rgba(255,255,255,0.06);font-size:12px; }}
    .log-tbl tr.row-done td {{ color:#3DDC84;opacity:.85; }}
    .log-tbl tr:hover td {{ background:rgba(255,107,26,0.04); }}
    .col-num   {{ text-align:right;font-family:var(--font-mono, monospace); }}
    .col-time  {{ text-align:center;font-family:var(--font-mono, monospace);color:#D8D8D0; }}
    .col-center{{ text-align:center; }}
    .col-addr  {{ font-size:11px;font-family:var(--font-mono, monospace); }}
    .log-totals-row td {{ border-top:2px solid rgba(255,107,26,0.40);
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

    # Verify no stops were added or deleted during geocoding
    current_stop_ids = {r["id"] for r in conn.execute(
        "SELECT id FROM stops WHERE route_id=?", (route_id,)
    ).fetchall()}
    snapshotted_ids = {s["id"] for s in stops}
    if current_stop_ids != snapshotted_ids:
        conn.close()
        flash("Route was modified while optimizing. Please try again.", "error")
        return redirect(url_for("view_route", route_id=route_id))

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


@app.route("/stop/<int:stop_id>/drop-bin", methods=["POST"])
@login_required
def stop_drop_bin(stop_id):
    """Phase 7B — at a Drop/Delivery completion the driver can optionally label
    the bin ('where I left it') and attach a photo. Resolves the bin the stop
    dropped: the request's existing bin for PR/P/S, else find-or-create one for
    the customer/site of a delivery so it appears on the customer's portal.
    Multipart: label, photo. Both optional."""
    conn = get_db()
    stop = conn.execute(
        """SELECT s.id, s.customer_id, s.request_id, r.assigned_to, r.company_id
             FROM stops s JOIN routes r ON s.route_id=r.id
            WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid()),
    ).fetchone()
    if not stop:
        conn.close()
        abort(404)
    # Driver may only touch their own stop (boss/dispatcher may too).
    if session.get("role") != "boss" and stop["assigned_to"] != session.get("user_id"):
        conn.close()
        abort(403)
    req = None
    if stop["request_id"]:
        req = conn.execute(
            "SELECT id, type, bin_id, site_id, customer_id, size_requested FROM requests WHERE id=?",
            (stop["request_id"],),
        ).fetchone()
    # Resolve target bin.
    bin_id = None
    if req and req["bin_id"]:
        bin_id = req["bin_id"]
    elif req and req["customer_id"] and req["site_id"]:
        existing = conn.execute(
            "SELECT id FROM bins WHERE customer_id=? AND site_id=? AND drop_stop_id=?",
            (req["customer_id"], req["site_id"], stop_id),
        ).fetchone()
        if existing:
            bin_id = existing["id"]
        else:
            cur = conn.cursor()
            cur.execute(
                """INSERT INTO bins (customer_id, site_id, size, dropped_at, drop_stop_id)
                   VALUES (?,?,?,?,?)""",
                (req["customer_id"], req["site_id"], req["size_requested"], today_str(), stop_id),
            )
            bin_id = cur.lastrowid
    if bin_id is None:
        conn.close()
        return jsonify({"error": "no bin to label for this stop"}), 400

    label = _sanitize_bin_label(request.form.get("label"))
    updates, params = [], []
    if request.form.get("label") is not None:
        updates.append("label=?"); params.append(label)
    photo = request.files.get("photo")
    if photo and photo.filename and allowed_file(photo.filename):
        try:
            fname = f"drop_{bin_id}_{secrets.token_hex(6)}_{secure_filename(photo.filename)}"
            photo.save(os.path.join(app.config["UPLOAD_FOLDER"], fname))
            updates.append("drop_photo_path=?"); params.append(os.path.join("static", "uploads", fname))
        except OSError as exc:
            app.logger.warning("drop photo save failed: %s", exc)
    if updates:
        params.append(bin_id)
        conn.execute(f"UPDATE bins SET {', '.join(updates)} WHERE id=?", params)
        conn.commit()
    conn.close()
    return jsonify({"success": True, "bin_id": bin_id, "label": label})


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

    redirect_target = (
        url_for("driver_route_detail", route_id=route_id)
        if session.get("role") != "boss"
        else url_for("view_route", route_id=route_id)
    )

    files = request.files.getlist("photos")
    if not files or all(f.filename == "" for f in files):
        conn.close()
        flash("No file selected.", "error")
        return redirect(redirect_target)

    saved = 0
    try:
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
    except OSError as exc:
        app.logger.error("upload_stop_photo: failed writing to disk for stop %s: %s", stop_id, exc)
        if saved:
            conn.commit()
        conn.close()
        flash(
            f"{saved} photo(s) uploaded before a storage error interrupted the rest — try the remaining ones again."
            if saved else
            "Could not save the photo — try again.",
            "error" if not saved else "warning",
        )
        return redirect(redirect_target)

    if saved:
        conn.commit()
        flash(f"{saved} photo(s) uploaded.", "success")
    else:
        flash("No valid files uploaded.", "error")
    conn.close()
    return redirect(redirect_target)


@app.route("/photo/<int:photo_id>")
@login_required
def serve_stop_photo(photo_id):
    """Serve an uploaded stop photo/PDF — company- and ownership-checked,
    unlike a raw /static/uploads/... URL (which Flask's default static
    handler would serve to anyone, logged in or not, from any company)."""
    conn = get_db()
    photo = conn.execute("""
        SELECT rp.file_path, r.assigned_to
        FROM route_photos rp
        JOIN stops s ON rp.stop_id = s.id
        JOIN routes r ON s.route_id = r.id
        WHERE rp.id=? AND r.company_id=?
    """, (photo_id, cid())).fetchone()
    conn.close()

    if not photo:
        abort(404)
    if session.get("role") != "boss" and photo["assigned_to"] != session["user_id"]:
        abort(403)

    full_path = os.path.join(app.root_path, photo["file_path"])
    if not os.path.isfile(full_path):
        abort(404)
    return send_file(full_path)


# =========================================================
# CSV EXPORT
# =========================================================
@app.route("/export/day")
@boss_required
def export_day_csv():
    conn = get_db()
    stops = conn.execute("""
        SELECT s.*, r.route_name, u.username AS driver_username
        FROM stops s
        JOIN routes r ON s.route_id = r.id
        LEFT JOIN users u ON r.assigned_to = u.id
        WHERE r.company_id=? AND r.route_date=?
        ORDER BY r.id, s.stop_order
    """, (cid(), today_str())).fetchall()
    conn.close()

    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(["Route", "Driver", "Stop", "Customer", "Address", "Action", "Container Size", "Status"])
    for s in stops:
        writer.writerow([
            s["route_name"], s["driver_username"] or "Unassigned", s["stop_order"],
            s["customer_name"], s["address"], s["action"], s["container_size"], s["status"]
        ])
    output.seek(0)

    return send_file(
        io.BytesIO(output.read().encode()),
        mimetype="text/csv",
        as_attachment=True,
        download_name=f"haultra-day-{today_str()}.csv"
    )


@app.route("/route/<int:route_id>/csv")
@login_required
def export_route_csv(route_id):
    conn = get_db()
    route = conn.execute(
        "SELECT id, assigned_to FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone()
    if not route:
        conn.close()
        abort(404)
    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))
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
# AI ROUTE PARSER — Anthropic-backed dispatch text → stops
# =========================================================
_PARSE_SYSTEM_PROMPT = """You parse raw roll-off dispatch text into structured stops for a trucking dispatch system.

Action codes:
  PR = pull & return (pull a full container, return it empty)
  P  = pickup
  D  = drop (deliver an empty container)
  S  = swap (drop an empty, pull a full — one stop)
  R  = relocate (move a container on-site or between addresses)

Rules:
- Treat each instruction / line as exactly one stop.
- For every stop extract: action (one of PR, P, D, S, R), address, container_size
  (e.g. "30yd", or null if not stated), raw (the original line, verbatim), confidence
  ("low" or "high"), and notes (any extra detail worth surfacing, or an empty string).
- Set confidence to "low" whenever the action, address, or destination is ambiguous,
  vague, or only partially stated (e.g. an unclear relocation, a missing address, or a
  vague action word). Otherwise set confidence to "high".
- Respond with ONLY valid JSON — no markdown code fences, no commentary — in exactly
  this shape:
  {"stops":[{"action":"","address":"","container_size":null,"raw":"","confidence":"","notes":""}]}
"""


@app.route("/api/parse", methods=["POST"])
@roles_required("dispatcher", api=True)
def api_parse_dispatch():
    import os as _os

    data = request.get_json(silent=True) or {}
    text = (data.get("text") or "").strip()
    if not text:
        return jsonify({"error": "No dispatch text provided"}), 400

    try:
        import anthropic
    except ImportError:
        return jsonify({"error": "AI package not installed. Add anthropic to requirements.txt."}), 500

    api_key = _os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        return jsonify({"error": "ANTHROPIC_API_KEY not configured on server."}), 500

    try:
        client = anthropic.Anthropic(api_key=api_key, timeout=20.0)
        resp = client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=4096,
            system=_PARSE_SYSTEM_PROMPT,
            messages=[{"role": "user", "content": text}],
        )
        raw_reply = "".join(
            block.text for block in resp.content if getattr(block, "type", None) == "text"
        ).strip()
    except anthropic.APITimeoutError:
        return jsonify({"error": "The AI parser took too long to respond — try again."}), 504
    except anthropic.APIConnectionError:
        return jsonify({"error": "Couldn't reach the AI parser — check your connection and try again."}), 502
    except anthropic.RateLimitError:
        return jsonify({"error": "The AI parser is rate-limited right now — wait a moment and try again."}), 429
    except anthropic.APIStatusError as ex:
        app.logger.warning("api_parse_dispatch: Anthropic API error: %s", ex)
        return jsonify({"error": "The AI parser is temporarily unavailable — try again shortly."}), 502
    except Exception as ex:
        app.logger.warning("api_parse_dispatch: unexpected error: %s", ex)
        return jsonify({"error": "Something went wrong parsing that text — try again."}), 500

    cleaned = raw_reply.strip()
    if cleaned.startswith("```"):
        cleaned = re.sub(r"^```(?:json)?\s*", "", cleaned)
        cleaned = re.sub(r"\s*```\s*$", "", cleaned)

    try:
        parsed = json.loads(cleaned)
    except json.JSONDecodeError:
        return jsonify({"error": "Parser returned invalid format — try re-parsing"}), 502

    stops = parsed.get("stops") if isinstance(parsed, dict) else None
    if not isinstance(stops, list):
        return jsonify({"error": "Parser returned invalid format — try re-parsing"}), 502

    return jsonify({"stops": stops})


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
        email        = request.form.get("email", "").strip()

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

        # Case-insensitive duplicate check — see the matching comment in
        # register() for why this matters now that login is case-insensitive.
        if conn.execute("SELECT id FROM users WHERE username = ? COLLATE NOCASE", (username,)).fetchone():
            conn.close()
            flash("That username is already taken.", "error")
            return redirect(url_for("company_register"))

        try:
            trial_ends = (datetime.now() + timedelta(days=14)).strftime("%Y-%m-%d %H:%M:%S")
            conn.execute(
                """INSERT INTO companies (name, slug, subscription_plan, subscription_status,
                   max_drivers, trial_ends_at, created_at) VALUES (?,?,?,?,?,?,?)""",
                (company_name, slug, "trial", "active", 5, trial_ends, now_ts())
            )
            conn.commit()
            _crow = conn.execute("SELECT id FROM companies WHERE slug=?", (slug,)).fetchone()
            if not _crow:
                conn.close()
                flash("Company creation failed. Please try again.", "error")
                return redirect(url_for("company_register"))
            company_id = _crow["id"]

            conn.execute(
                """INSERT INTO users (username, password_hash, role, role_owner,
                   full_name, phone, email, company_id, created_at)
                   VALUES (?,?,?,1,?,?,?,?,?)""",
                (username, generate_password_hash(password), "boss",
                 full_name, phone, email or None, company_id, now_ts())
            )
            conn.commit()
            _urow = conn.execute("SELECT id FROM users WHERE username=? AND company_id=?",
                                 (username, company_id)).fetchone()
            if not _urow:
                conn.close()
                flash("User creation failed. Please try again.", "error")
                return redirect(url_for("company_register"))
            owner_id = _urow["id"]
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
                <label>Email</label>
                <input type="email" name="email" placeholder="for password reset / recovery">
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
# SETTINGS — merged Company Settings + Subscription
# =========================================================
@app.route("/settings", methods=["GET", "POST"])
@boss_required
def settings_page():
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
        elif action == "photo_proof":
            mode = request.form.get("photo_proof_mode", "encouraged").strip()
            if mode not in ("off", "encouraged", "required"):
                mode = "encouraged"
            conn.execute("UPDATE companies SET photo_proof_mode=? WHERE id=?", (mode, cid()))
            conn.commit()
            flash("Photo proof setting saved.", "success")
        else:
            new_name = request.form.get("company_name", "").strip()
            new_email = request.form.get("email", "").strip()
            if new_name:
                conn.execute("UPDATE companies SET name=? WHERE id=?", (new_name, cid()))
            conn.execute("UPDATE users SET email=? WHERE id=?", (new_email or None, session["user_id"]))
            conn.commit()
            flash("Profile updated.", "success")

        conn.close()
        return redirect(url_for("settings_page"))

    # ── Profile / Yard / Work Hours (GET render) ────────────────────────────
    plan_labels = {
        "trial": ("Trial", "#fbbf24"),
        "starter": ("Starter", "#FF9D5C"),
        "pro": ("Pro", "#3DDC84"),
        "enterprise": ("Enterprise", "#c084fc"),
    }
    _me = conn.execute("SELECT email FROM users WHERE id=?", (session["user_id"],)).fetchone()
    my_email = (_me["email"] if _me else "") or ""

    _co = dict(company) if company else {}
    plan      = _co.get("subscription_plan") or "trial"
    plan_name, plan_color = plan_labels.get(plan, ("Unknown", "#D8D8D0"))
    max_d     = _co.get("max_drivers") or 0
    co_name   = _co.get("name") or ""
    co_slug   = _co.get("slug") or ""
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
    photo_mode = _co.get("photo_proof_mode") or "encouraged"

    _yard_set = bool(yard_addr or yard_city)
    _yard_status = (
        f'<span style="color:#00e87d;font-size:12px;">&#10003; Set — {e(yard_addr)}, {e(yard_city)}, {e(yard_state)} {e(yard_zip)}</span>'
        if _yard_set else
        '<span style="color:#ff9d00;font-size:12px;">&#9888; Not set — route optimization will use stop-to-stop ordering</span>'
    )

    settings_body = f"""
    <div class="card" id="profile">
        <h2>Profile</h2>
        <form method="POST">
            <input type="hidden" name="_action" value="profile">
            <label>Company Name</label>
            <input name="company_name" value="{e(co_name)}" required>
            <label>Your Email</label>
            <input type="email" name="email" value="{e(my_email)}" placeholder="for password reset / recovery">
            <div style="margin-top:10px;">
                <button type="submit" class="btn">Save</button>
            </div>
        </form>
        <p class="muted small" style="margin-top:10px;">Slug: <code>{e(co_slug)}</code></p>
    </div>

    <div class="card" id="yard">
        <h2>&#127968; Yard / Base Location</h2>
        <p style="color:#B8B8AE;font-size:13px;margin-bottom:12px;">
            Used as the starting point when optimizing routes. Stops with notes containing
            <em>end of day</em>, <em>return to yard</em>, or <em>take to yard</em> are automatically
            pinned to the end of the optimized route.
        </p>
        <p style="margin-bottom:14px;">{_yard_status}</p>
        <form method="POST">
            <input type="hidden" name="_action" value="yard">
            <div class="grid" style="grid-template-columns:1fr 1fr;gap:12px 16px;">
                <div style="grid-column:1/-1;">
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Yard / Base Address</label>
                    <input name="yard_address" value="{e(yard_addr)}" placeholder="e.g. 100 Industrial Blvd">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">City</label>
                    <input name="yard_city" value="{e(yard_city)}" placeholder="e.g. Suffolk">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">State</label>
                    <input name="yard_state" value="{e(yard_state)}" placeholder="VA" style="max-width:100px;">
                </div>
                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">ZIP</label>
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
        <p style="color:#B8B8AE;font-size:13px;margin-bottom:16px;">
            Configure your company&rsquo;s pay schedule and how driver day hours are measured.
            These settings apply to all drivers in your company.
        </p>
        <form method="POST">
            <input type="hidden" name="_action" value="work_hours">
            <div class="grid" style="grid-template-columns:1fr 1fr;gap:12px 16px;">

                <div style="grid-column:1/-1;">
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Timezone</label>
                    <select name="timezone">
                        {"".join(f'<option value="{tz}" {"selected" if tz == wh_tz else ""}>{tz}</option>' for tz in [
                            "America/New_York","America/Chicago","America/Denver",
                            "America/Los_Angeles","America/Phoenix","America/Anchorage",
                            "America/Honolulu","UTC"
                        ])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Workweek Starts On</label>
                    <select name="workweek_start_day">
                        {"".join(f'<option value="{d}" {"selected" if d == wh_wstart else ""}>{d.title()}</option>' for d in ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Week Resets On</label>
                    <select name="workweek_reset_day">
                        {"".join(f'<option value="{d}" {"selected" if d == wh_wreset else ""}>{d.title()}</option>' for d in ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Pay Period Type</label>
                    <select name="pay_period_type">
                        {"".join(f'<option value="{pt}" {"selected" if pt == wh_ptype else ""}>{pt.title()}</option>' for pt in ["weekly","biweekly"])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Pay Period Ends On</label>
                    <select name="pay_period_end_day">
                        {"".join(f'<option value="{d}" {"selected" if d == wh_pend else ""}>{d.title()}</option>' for d in ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Payday</label>
                    <select name="payday">
                        {"".join(f'<option value="{d}" {"selected" if d == wh_payday else ""}>{d.title()}</option>' for d in ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"])}
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Driver Day Start</label>
                    <select name="driver_day_start_rule">
                        <option value="first_action" {"selected" if wh_dstart == "first_action" else ""}>First route action (automatic)</option>
                        <option value="manual"       {"selected" if wh_dstart == "manual"       else ""}>Manual clock-in</option>
                    </select>
                </div>

                <div>
                    <label style="display:block;font-size:12px;color:#B8B8AE;margin-bottom:4px;font-weight:600;text-transform:uppercase;letter-spacing:.5px;">Driver Day End</label>
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

    <div class="card" id="photo-proof">
        <h2>&#128247; Photo Proof</h2>
        <p style="color:#B8B8AE;font-size:13px;margin-bottom:16px;">
            Controls whether drivers must attach a photo before completing a stop in Cab View.
        </p>
        <form method="POST">
            <input type="hidden" name="_action" value="photo_proof">
            <div style="display:flex;flex-direction:column;gap:10px;">
                <label style="display:flex;align-items:flex-start;gap:10px;min-height:48px;cursor:pointer;">
                    <input type="radio" name="photo_proof_mode" value="off" {"checked" if photo_mode == "off" else ""} style="margin-top:4px;width:18px;height:18px;">
                    <span><strong>Off</strong><br><span class="muted small">No photo prompt at all — Complete Stop always goes straight through.</span></span>
                </label>
                <label style="display:flex;align-items:flex-start;gap:10px;min-height:48px;cursor:pointer;">
                    <input type="radio" name="photo_proof_mode" value="encouraged" {"checked" if photo_mode == "encouraged" else ""} style="margin-top:4px;width:18px;height:18px;">
                    <span><strong>Encouraged</strong> <span class="muted small">(default)</span><br><span class="muted small">If a driver taps Complete Stop with no photo, a quick confirm nudges them to add one — one tap through either way.</span></span>
                </label>
                <label style="display:flex;align-items:flex-start;gap:10px;min-height:48px;cursor:pointer;">
                    <input type="radio" name="photo_proof_mode" value="required" {"checked" if photo_mode == "required" else ""} style="margin-top:4px;width:18px;height:18px;">
                    <span><strong>Required</strong><br><span class="muted small">Complete Stop stays locked until at least one photo is attached — for companies that bill with photo evidence.</span></span>
                </label>
            </div>
            <div style="margin-top:16px;">
                <button type="submit" class="btn gold">Save Photo Proof Setting</button>
            </div>
        </form>
    </div>
    """

    # ── Subscription (GET render, folded in as its own section) ─────────────
    history = conn.execute(
        "SELECT * FROM subscriptions WHERE company_id=? ORDER BY started_at DESC",
        (cid(),)
    ).fetchall()
    conn.close()

    sub_status = _co.get("subscription_status") or "active"
    trial_ends_at = _co.get("trial_ends_at")

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
            elif sub_status == "active":
                trial_banner = (
                    '<div style="background:rgba(248,113,113,0.15);border:1px solid rgba(248,113,113,0.4);'
                    'border-radius:10px;padding:14px 18px;margin-bottom:18px;">'
                    '&#128274; Your trial has expired. Upgrade to restore full access.</div>'
                )
        except ValueError:
            pass

    plans = [
        ("trial",      "Free",       "$0",    "14 days • up to 5 drivers",                  "#fbbf24"),
        ("starter",    "Starter",    "$49/mo","Up to 10 drivers",                            "#FF9D5C"),
        ("pro",        "Pro",        "$99/mo","Up to 30 drivers • priority support",         "#3DDC84"),
        ("enterprise", "Enterprise", "Custom","Unlimited drivers • dedicated support",       "#c084fc"),
    ]
    plan_labels_full = {"trial": "Free Trial", "starter": "Starter", "pro": "Pro", "enterprise": "Enterprise"}
    plan_label = plan_labels_full.get(plan, plan.title())

    if plan == "trial" and trial_ends_at:
        exp_display = trial_ends_at[:10]
        try:
            ends_dt2 = datetime.strptime(trial_ends_at, "%Y-%m-%d %H:%M:%S")
            days_left2 = (ends_dt2 - datetime.now()).days
            exp_display = f"{trial_ends_at[:10]} ({days_left2}d left)" if days_left2 > 0 else f"{trial_ends_at[:10]} (expired)"
        except ValueError:
            pass
    else:
        exp_display = "—" if sub_status == "active" else "Subscription ended"

    show_upgrade = plan in ("trial", "starter", "pro")
    upgrade_btn = (
        '<button onclick="haultraCheckout(\'starter\',this)" '
        'class="btn" style="background:linear-gradient(135deg,#FF9D5C,#3DDC84);'
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

    conn3 = get_db()
    driver_count = conn3.execute(
        "SELECT COUNT(*) n FROM users WHERE role='driver' AND company_id=?", (cid(),)
    ).fetchone()["n"]
    conn3.close()

    seat_pct = int(driver_count / max_d * 100) if max_d else 0
    bar_color = "#f87171" if seat_pct >= 90 else "#FF9D5C"
    seat_bar = f"""
    <div style="margin-top:6px;">
        <div style="font-size:13px;color:#D8D8D0;margin-bottom:4px;">{driver_count} / {max_d} driver seats used</div>
        <div class="mini-prog-track" style="width:100%;height:10px;">
            <div class="mini-prog-fill" style="width:{seat_pct}%;background:{bar_color};"></div>
        </div>
    </div>"""

    hist_rows = ""
    for h in history:
        plan_hl = plan_labels_full.get(h["plan"], h["plan"].title())
        hist_rows += f"""
        <tr>
            <td>{e(plan_hl)}</td>
            <td><span class="badge">{e(h['status'].title())}</span></td>
            <td>{e(h['started_at'])}</td>
            <td>{e(h['ends_at'] or '—')}</td>
            <td>{e(h['notes'] or '')}</td>
        </tr>"""

    status_color = "#4ade80" if sub_status == "active" else "#f87171"
    plan_color_map = {"trial": "#fbbf24", "starter": "#FF9D5C", "pro": "#3DDC84", "enterprise": "#c084fc"}
    pc = plan_color_map.get(plan, "#D8D8D0")

    subscription_body = f"""
    <div class="card" id="subscription" style="margin-top:8px;">
        <h2 style="margin:0 0 4px;">Subscription &amp; Billing</h2>
        <p style="color:#B8B8AE;font-size:13px;margin-bottom:16px;">Your plan details, usage, and upgrade options.</p>

        {trial_banner}

        <div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:12px;margin-bottom:18px;">
            <h3 style="margin:0;font-size:13px;text-transform:uppercase;letter-spacing:.5px;color:#B8B8AE;">Plan Overview</h3>
            {upgrade_btn}
        </div>
        <div class="grid">
            <div class="stat">
                <div class="muted small">Current Plan</div>
                <div class="num" style="color:{pc};font-size:22px;">{plan_label}</div>
            </div>
            <div class="stat">
                <div class="muted small">Status</div>
                <div class="num" style="color:{status_color};font-size:22px;">{sub_status.title()}</div>
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

        <h3 style="margin:22px 0 12px;font-size:13px;text-transform:uppercase;letter-spacing:.5px;color:#B8B8AE;">Available Plans</h3>
        <div class="grid">{plan_cards}</div>
        <p class="muted small" style="margin-top:14px;">
            Secure checkout powered by Stripe. Cancel anytime.
        </p>

        <h3 style="margin:22px 0 12px;font-size:13px;text-transform:uppercase;letter-spacing:.5px;color:#B8B8AE;">Subscription History</h3>
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

    body = f"""
    <div class="hero">
        <h1>Settings</h1>
        <p>Company profile, yard location, work hours, and subscription — all in one place.</p>
    </div>
    {settings_body}
    {subscription_body}
    """
    return render_template_string(shell_page("Settings", body))


# ── Legacy URLs — redirect to their new home on Settings ────────────────────
@app.route("/company/settings", methods=["GET", "POST"])
@boss_required
def company_settings():
    return redirect(url_for("settings_page") + "#profile")


@app.route("/company/subscription")
@boss_required
def company_subscription():
    return redirect(url_for("settings_page") + "#subscription")



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
        return redirect(url_for("settings_page") + "#subscription")

    price_id = STRIPE_PRICE_IDS.get(plan)
    if not price_id:
        flash("Price ID not configured for this plan.", "error")
        return redirect(url_for("settings_page") + "#subscription")

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


@app.route("/billing")
@boss_required
def billing():
    """Clean /billing URL — same subscription section, now on Settings."""
    return redirect(url_for("settings_page") + "#subscription")


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
        sub_link = f'<a class="btn green" href="{url_for("settings_page")}#subscription" style="margin-top:16px;display:inline-block;font-size:16px;padding:14px 28px;">View Plans &amp; Upgrade</a>'

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
        <p class="muted small">Effective date: <strong style="color:#F5F5F0;">{today}</strong>
        &nbsp;&middot;&nbsp; HAULTRA AI SYSTEMS &nbsp;&middot;&nbsp; Virginia, USA</p>
    </div>

    <div class="card" style="max-width:820px;line-height:1.8;">

        <div style="background:rgba(255,107,26,0.08);border:1px solid rgba(255,107,26,0.20);
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
        <p style="margin-left:18px;color:#D8D8D0;">
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

        <div style="margin-top:28px;padding-top:16px;border-top:1px solid rgba(255,255,255,0.10);
                    font-size:12px;color:#8C8C82;">
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
        <p class="muted small">Effective date: <strong style="color:#F5F5F0;">{today}</strong>
        &nbsp;&middot;&nbsp; HAULTRA AI SYSTEMS &nbsp;&middot;&nbsp; Virginia, USA</p>
    </div>

    <div class="card" style="max-width:820px;line-height:1.8;">

        <div style="background:rgba(255,107,26,0.08);border:1px solid rgba(255,107,26,0.20);
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

        <div style="margin-top:28px;padding-top:16px;border-top:1px solid rgba(255,255,255,0.10);
                    font-size:12px;color:#8C8C82;">
            &copy; {year} HAULTRA AI SYSTEMS &mdash; Virginia, USA. All rights reserved.
        </div>
    </div>
    """
    return render_template_string(shell_page("Terms of Service", body))


# =========================================================
# YARD SETUP — merged Dump Locations + Container Fleet
# =========================================================
def _dump_locations_section_html():
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
                   style="color:#FF9D5C;font-size:12px;margin-right:10px;">Edit</a>
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

    return f"""
    <div class="card" id="dump-locations">
        <div class="row between" style="margin-bottom:16px;">
            <h2 style="margin:0;">&#128465; Dump Locations</h2>
            <a class="btn" href="{url_for('add_dump_location')}">+ Add Location</a>
        </div>
        <p class="muted small" style="margin-bottom:14px;">Disposal sites available for route assignment.</p>
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
        return redirect(url_for("yard_setup_page"))

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
                <a class="btn secondary" href="/yard-setup#dump-locations">Cancel</a>
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
        return redirect(url_for("yard_setup_page"))

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
        return redirect(url_for("yard_setup_page"))

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
                <a class="btn secondary" href="{url_for('yard_setup_page')}">Cancel</a>
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
        return redirect(url_for("yard_setup_page"))
    new_active = 0 if dl["active"] else 1
    conn.execute("UPDATE dump_locations SET active=? WHERE id=?", (new_active, loc_id))
    conn.commit()
    conn.close()
    status_word = "activated" if new_active else "deactivated"
    flash(f"'{dl['name']}' {status_word}.", "success")
    return redirect(url_for("yard_setup_page"))


@app.route("/dump-locations/<int:loc_id>/delete", methods=["POST"])
@boss_required
def delete_dump_location(loc_id):
    conn = get_db()
    dl = conn.execute("SELECT name FROM dump_locations WHERE id=?", (loc_id,)).fetchone()
    if not dl:
        conn.close()
        flash("Location not found.", "error")
        return redirect(url_for("yard_setup_page"))
    # Unlink from any routes that reference this location
    conn.execute("UPDATE routes SET dump_location_id=NULL WHERE dump_location_id=?", (loc_id,))
    conn.execute("DELETE FROM dump_locations WHERE id=?", (loc_id,))
    conn.commit()
    conn.close()
    flash(f"'{dl['name']}' deleted.", "success")
    return redirect(url_for("yard_setup_page"))


# =========================================================
# BIN TRACKER — containers currently out at customer sites
# =========================================================
OVERDUE_RENTAL_DAYS = 10  # UI flagging threshold; not yet a configurable company setting


def _days_out(since_str, asof_date=None):
    if not since_str:
        return None
    try:
        since_date = datetime.strptime(since_str[:10], "%Y-%m-%d").date()
    except Exception:
        return None
    if asof_date:
        try:
            ref_date = datetime.strptime(asof_date[:10], "%Y-%m-%d").date()
        except Exception:
            return None
    else:
        ref_date = datetime.now(_EASTERN).date() if _EASTERN else date.today()
    return (ref_date - since_date).days


@app.route("/bin-tracker")
@boss_required
def bin_tracker():
    conn = get_db()
    out = compute_containers_out(conn, cid())
    conn.close()

    for c in out:
        c["days_out"] = _days_out(c["since"])
    out.sort(key=lambda c: c["days_out"] if c["days_out"] is not None else -1, reverse=True)

    overdue_count = sum(1 for c in out if (c["days_out"] or 0) >= OVERDUE_RENTAL_DAYS)
    geocoded = [c for c in out if c["lat"] is not None and c["lng"] is not None]

    rows_html = ""
    if not out:
        rows_html = '<div class="empty-state">No containers currently out. Delivery and pull history will populate this list as stops are completed.</div>'
    else:
        for c in out:
            days = c["days_out"]
            overdue = days is not None and days >= OVERDUE_RENTAL_DAYS
            if days is None:
                days_label = "&mdash;"
            elif days == 0:
                days_label = "Out today"
            elif days == 1:
                days_label = "1 day out"
            else:
                days_label = f"{days} days out"
            card_cls = "bin-card overdue" if overdue else "bin-card"
            addr_line = e(c["address"]) + (f', {e(c["city"])}' if c["city"] else "")
            has_coords = c["lat"] is not None and c["lng"] is not None
            card_click = (
                f' onclick="panToContainer({c["stop_id"]})" style="cursor:pointer;"'
                if has_coords else ""
            )
            no_map_note = "" if has_coords else '<div class="bin-no-map">&#128205; No map location</div>'
            rows_html += f"""
            <div class="{card_cls}" id="bin-card-{c['stop_id']}"{card_click}>
                <div class="bin-card-top">
                    <span class="bin-days {'overdue' if overdue else ''}">{days_label}</span>
                    {f'<span class="bin-size">{e(c["size"])}</span>' if c["size"] else ''}
                </div>
                <div class="bin-addr">{addr_line}</div>
                {f'<div class="bin-customer">{e(c["customer_name"])}</div>' if c["customer_name"] else ''}
                {f'<div class="bin-overdue-tag">&#9888; OVERDUE &mdash; past {OVERDUE_RENTAL_DAYS}-day window</div>' if overdue else ''}
                {no_map_note}
            </div>
            """

    if not out:
        map_panel = """
        <div class="bin-map-stub">
            <div class="bin-map-stub-icon">&#128506;</div>
            <div class="bin-map-stub-title">Nothing out right now</div>
            <div class="bin-map-stub-sub">The map will populate as soon as a
            delivery, pickup &amp; return, or swap stop is completed.</div>
        </div>
        """
        map_extra_html = ""
        map_head = ""
        map_script = ""
    else:
        map_points = [
            {
                "stop_id":  c["stop_id"],
                "lat":      c["lat"],
                "lng":      c["lng"],
                "address":  c["address"] or "",
                "city":     c["city"] or "",
                "customer": c["customer_name"] or "",
                "size":     c["size"] or "",
                "days_label": (
                    "—" if c["days_out"] is None else
                    "Out today" if c["days_out"] == 0 else
                    f'{c["days_out"]} day{"s" if c["days_out"] != 1 else ""} out'
                ),
                "overdue": bool(c["days_out"] is not None and c["days_out"] >= OVERDUE_RENTAL_DAYS),
                "is_gps": bool(c["is_gps"]),
            }
            for c in geocoded
        ]
        map_panel = '<div id="bin-map" class="bin-map"></div>'
        map_extra_html = (
            '<div class="bin-map-note">Containers are out, but none have map '
            'coordinates yet — new drops geocode automatically, or run the '
            'backfill script to geocode the current ones.</div>'
        ) if not geocoded else ""
        # Leaflet's CSS must load (and cascade) BEFORE shell_page()'s own
        # <style> block, or its default white popup/control styling wins
        # over the dark-theme overrides below — hence extra_head, not body.
        map_head = """
        <link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css"
              integrity="sha256-p4NxAoJBhIIN+hmNHrzRCf9tD/miZyoHS5obTRR9BMY=" crossorigin="" />
        """
        map_script = f"""
        <script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"
                integrity="sha256-20nQCchB9co0qIjJZRGuk2/Z9VM+kNiyxNV1lvTlZBo=" crossorigin=""></script>
        <script>
        (function() {{
            var POINTS = {json.dumps(map_points)};
            var FALLBACK_CENTER = [36.85, -76.28];  // Hampton Roads, VA

            function escHtml(s) {{
                return String(s == null ? '' : s).replace(/[&<>"']/g, function(c) {{
                    return {{'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}}[c];
                }});
            }}

            function makeIcon(overdue) {{
                var color = overdue ? '#FF5252' : '#FF6B1A';
                return L.divIcon({{
                    className: 'bin-map-pin',
                    html: '<div style="width:16px;height:16px;border-radius:50% 50% 50% 0;' +
                          'transform:rotate(-45deg);background:' + color + ';' +
                          'border:2px solid rgba(0,0,0,0.45);box-shadow:0 2px 6px rgba(0,0,0,0.55);"></div>',
                    iconSize: [16, 16],
                    iconAnchor: [8, 16],
                    popupAnchor: [0, -18],
                }});
            }}

            function popupHtml(p) {{
                var overdueBadge = p.overdue
                    ? '<div style="color:#FF5252;font-weight:700;font-size:11px;margin-top:4px;">&#9888; OVERDUE</div>'
                    : '';
                var sourceNote = p.is_gps
                    ? '<div style="color:#3DDC84;font-size:11px;font-weight:700;margin-top:6px;">&#10003; GPS</div>'
                    : '<div style="color:#78786F;font-size:11px;margin-top:6px;">address estimate</div>';
                return '<div style="font-family:var(--font-body,inherit);min-width:170px;">' +
                    '<strong>' + escHtml(p.address) + (p.city ? ', ' + escHtml(p.city) : '') + '</strong>' +
                    (p.customer ? '<div style="margin-top:2px;">' + escHtml(p.customer) + '</div>' : '') +
                    (p.size ? '<div style="color:#A6A69E;font-size:12px;margin-top:2px;">' + escHtml(p.size) + '</div>' : '') +
                    '<div style="font-size:12px;margin-top:4px;">' + escHtml(p.days_label) + '</div>' +
                    overdueBadge +
                    sourceNote +
                    '</div>';
            }}

            var map = L.map('bin-map', {{ scrollWheelZoom: true }}).setView(FALLBACK_CENTER, 11);
            L.tileLayer('https://{{s}}.basemaps.cartocdn.com/dark_all/{{z}}/{{x}}/{{y}}{{r}}.png', {{
                attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> &copy; <a href="https://carto.com/attributions">CARTO</a>',
                subdomains: 'abcd',
                maxZoom: 19,
            }}).addTo(map);

            var markersByStopId = {{}};
            var latLngs = [];
            POINTS.forEach(function(p) {{
                var marker = L.marker([p.lat, p.lng], {{ icon: makeIcon(p.overdue) }}).addTo(map);
                marker.bindPopup(popupHtml(p));
                markersByStopId[p.stop_id] = marker;
                latLngs.push([p.lat, p.lng]);
            }});
            if (latLngs.length > 1) {{
                map.fitBounds(latLngs, {{ padding: [30, 30], maxZoom: 15 }});
            }} else if (latLngs.length === 1) {{
                map.setView(latLngs[0], 14);
            }}

            window.panToContainer = function(stopId) {{
                var marker = markersByStopId[stopId];
                if (!marker) return;
                map.setView(marker.getLatLng(), 15, {{ animate: true }});
                marker.openPopup();
                var card = document.getElementById('bin-card-' + stopId);
                if (card && card.scrollIntoView) {{
                    card.scrollIntoView({{ behavior: 'smooth', block: 'nearest' }});
                }}
            }};
        }})();
        </script>
        """

    body = f"""
    <div class="hero">
        <h1>Bin Tracker</h1>
        <p>Rental clocks for every container currently out at a customer site.</p>
    </div>

    <div class="bin-tracker-grid">
        <div class="bin-map-col">
            {map_panel}
            {map_extra_html}
        </div>
        <div class="bin-list-col">
            <div class="bin-list-header">
                <div>
                    <div class="bin-list-title">RENTAL CLOCKS</div>
                    <div class="bin-list-sub">CONTAINERS OUT</div>
                </div>
                <div class="bin-list-stats">
                    <span class="bin-count">{len(out)}</span> out
                    {f'<span class="bin-overdue-count">&#9888; {overdue_count} overdue</span>' if overdue_count else ''}
                </div>
            </div>
            <div class="bin-list">
                {rows_html}
            </div>
        </div>
    </div>
    {map_script}
    """
    return render_template_string(shell_page("Bin Tracker", body, extra_head=map_head))


# =========================================================
# PHASE 5A — CONTAINER FLEET INVENTORY  (part of /yard-setup)
# =========================================================
def _containers_section_html():
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
        "yard":     "#3DDC84",
        "deployed": "#fbbf24",
        "lost":     "#f87171",
        "retired":  "#6b7280",
    }

    rows_html = ""
    for c in containers:
        _cd   = dict(c)
        _cid  = _cd["id"]
        _sc   = STATUS_COLOR.get(_cd["status"], "#D8D8D0")
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
                   style="color:#FF9D5C;font-size:12px;margin-right:10px;">Edit</a>
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

    return f"""
    <div class="card" id="containers">
        <div class="row between" style="margin-bottom:16px;">
            <h2 style="margin:0;">&#128230; Container Fleet</h2>
            <a class="btn" href="{url_for('add_container')}">+ Add Container</a>
        </div>
        <p class="muted small" style="margin-bottom:14px;">Your roll-off containers by size and status.</p>
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


@app.route("/yard-setup")
@boss_required
def yard_setup_page():
    body = f"""
    <div class="hero">
        <h1>Yard Setup</h1>
        <p>Dump locations and your container fleet, in one place.</p>
    </div>
    {_dump_locations_section_html()}
    {_containers_section_html()}
    """
    return render_template_string(shell_page("Yard Setup", body))


# ── Legacy URLs — redirect to their new home on Yard Setup ──────────────────
@app.route("/dump-locations")
@boss_required
def dump_locations_page():
    return redirect(url_for("yard_setup_page") + "#dump-locations")


@app.route("/boss/containers")
@boss_required
def containers_page():
    return redirect(url_for("yard_setup_page") + "#containers")


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
        return redirect(url_for("yard_setup_page"))

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
                <a class="btn secondary" href="{url_for('yard_setup_page')}">Cancel</a>
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
        return redirect(url_for("yard_setup_page"))

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
                <a class="btn secondary" href="{url_for('yard_setup_page')}">Cancel</a>
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
    return redirect(url_for("yard_setup_page"))


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
        body = f"""
        <div class="hero"><h1>Driver Hours</h1></div>
        <div class="card">
            <p class="muted">No drivers found. Add drivers under
            <a href="{url_for('team_page')}">Team</a> to see hours here.</p>
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
    except Exception as _exc:
        app.logger.error("Manual clock entries fetch failed driver=%s: %s", selected_driver_id, _exc)

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
        except Exception as _exc:
            app.logger.error("Auto clock entries fetch failed driver=%s: %s", selected_driver_id, _exc)

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
                     'background:rgba(255,107,26,0.10);color:#FF9D5C;font-size:11px;">Auto</span>')
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
    settings_url = url_for("settings_page") + "#work-hours"
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
                        <td style="text-align:right;font-weight:900;color:#3DDC84;">%.2f h</td>
                    </tr>
                </tfoot>
            </table>
        </div>
        <div class="small muted" style="margin-top:10px;">
            Start: %s &bull; End: %s &bull;
            <a href="%s#work-hours" style="color:#FF9D5C;">Configure in Company Settings</a>
        </div>
    </div>

    <div class="card">
        <div style="font-size:13px;font-weight:700;color:#FF9D5C;margin-bottom:14px;">
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
        badge_bg = "rgba(0,232,125,0.14)"; badge_color = "#3DDC84"
        badge_text = "&#9899;&nbsp;Clocked In"
    elif has_co:
        badge_bg = "rgba(255,107,26,0.10)"; badge_color = "#FF9D5C"
        badge_text = "&#10003;&nbsp;Day Complete"
    else:
        badge_bg = "rgba(100,120,150,0.08)"; badge_color = "#A6A69E"
        badge_text = "Not Clocked In"

    ci_display = _fmt(_ci) or "&mdash;"
    co_display = _fmt(_co) or "&mdash;"
    ci_color   = "#3DDC84" if has_ci else "#78786F"
    co_color   = "#fbbf24" if has_co else "#78786F"

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
                'background:rgba(255,107,26,0.10);color:#FF9D5C;'
                'border:1px solid rgba(255,107,26,0.20);cursor:pointer;white-space:nowrap;')
    S_TIME   = ('flex:1;padding:10px 12px;background:rgba(255,255,255,0.05);'
                'border:1px solid rgba(255,107,26,0.20);border-radius:8px;'
                'color:#e8f2ff;font-size:15px;font-weight:600;')
    DIVIDER  = '<div style="height:1px;background:rgba(255,107,26,0.10);margin:12px 0;"></div>'
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
        '<div style="display:flex;border:1px solid rgba(255,107,26,0.12);'
        'border-radius:10px;overflow:hidden;">'
        '<div style="flex:1;padding:14px 18px;border-right:1px solid rgba(255,107,26,0.12);">'
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

// --- Firebase Cloud Messaging (background push for Live Dispatch) ---
// This is the ONE service worker for the whole origin — FCM handling lives
// here rather than in a second registered worker to avoid two SWs fighting
// over the '/' scope.
importScripts('https://www.gstatic.com/firebasejs/10.12.0/firebase-app-compat.js');
importScripts('https://www.gstatic.com/firebasejs/10.12.0/firebase-messaging-compat.js');

firebase.initializeApp({
  apiKey: "AIzaSyBAWm08bVHH5uia21H5VPd1mAW0Ei0MnV4",
  authDomain: "haultra-dispatch.firebaseapp.com",
  projectId: "haultra-dispatch",
  storageBucket: "haultra-dispatch.firebasestorage.app",
  messagingSenderId: "66096047367",
  appId: "1:66096047367:web:a7a3da473ba9d0bf5b51a2"
});

const messaging = firebase.messaging();

messaging.onBackgroundMessage((payload) => {
  const { title, body, stopId } = payload.data || {};
  self.registration.showNotification(title || 'New Stop Assigned', {
    body: body || 'You have a new stop. Tap to view.',
    icon: '/static/icon-192.png',
    badge: '/static/icon-192.png',
    tag: stopId || 'haultra-stop',
    data: { stopId }
  });
});

self.addEventListener('notificationclick', (event) => {
  event.notification.close();
  event.waitUntil(
    clients.matchAll({ type: 'window', includeUncontrolled: true }).then((clientList) => {
      for (const client of clientList) {
        if (client.url.includes('/driver') && 'focus' in client) return client.focus();
      }
      if (clients.openWindow) return clients.openWindow('/driver');
    })
  );
});

// --- Offline caching ---
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
@roles_required("dispatcher", api=True)
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
        placement_note     = expand_abbrev(stop.get("placement_note")     or "")
        relocate_to_addr   = expand_abbrev(stop.get("relocate_to_address") or
                                           stop.get("to_address")           or "")
        relocate_to_city   = expand_abbrev(stop.get("relocate_to_city")    or
                                           stop.get("to_city")              or "")
        return_destination = expand_abbrev(stop.get("return_destination")  or "")
        pr_mode            = (stop.get("pr_mode") or "").strip()
        swap_flag          = 1 if stop.get("swap_with_previous_empty") or stop.get("swap_with_prev_pull") else 0
        try:
            conn.execute("""
                INSERT INTO stops (
                    route_id, stop_order, customer_name, address, city, state, zip_code,
                    action, container_size, dump_location,
                    placement_note, relocate_to_address, relocate_to_city,
                    return_destination, pr_mode,
                    swap_with_prev_pull, status, created_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'open', ?)
            """, (route_id, last, customer_name, address, city, state, zip_code,
                  action, container_size, dump_location,
                  placement_note, relocate_to_addr, relocate_to_city,
                  return_destination, pr_mode,
                  swap_flag, now_ts()))
            added += 1
            upsert_saved_address(conn, cid(),
                customer_name, address, city, state, zip_code,
                action, container_size, dump_location)
        except Exception as exc:
            app.logger.warning("add_parsed_stops: insert failed for stop %d: %s", last, exc)
            last -= 1  # reclaim the order slot so next stop doesn't skip a number

    if added:
        conn.commit()
        try:
            compute_can_flow(conn, route_id)
            conn.commit()
        except Exception as exc:
            app.logger.warning("add_parsed_stops: compute_can_flow error: %s", exc)

    conn.close()
    return jsonify({"added": added})


# =========================================================
# AI PARSER — CONFIRM & DISPATCH (creates a route from parsed stops)
# =========================================================
# Maps the AI parser's short action codes to the same canonical action
# labels used everywhere else (is_pull_job, compute_can_flow, Route Board
# badges), so a dispatched route behaves identically to one created via
# Create Route / Paste Boss Text.
_PARSER_ACTION_MAP = {"PR": "Pickup and Return", "P": "Pull", "D": "Delivery", "S": "Swap", "R": "Relocate"}


def _validate_parser_stops(stops_in):
    """Shared validation for AI-parsed stops, used by both /api/dispatch (new route)
    and /api/route/<id>/insert-stops (existing route). Returns (clean_stops, error).
    Each clean stop carries insert_before through unchanged (raw client string, 'end'
    by default) — callers that don't do positional inserts simply ignore it."""
    if not isinstance(stops_in, list) or not stops_in:
        return None, "No stops to dispatch."
    clean_stops = []
    for i, s in enumerate(stops_in, start=1):
        if not isinstance(s, dict):
            return None, f"Stop {i} is malformed."
        action_code = (s.get("action") or "").strip().upper()
        address = expand_abbrev((s.get("address") or "").strip())
        if action_code not in _PARSER_ACTION_MAP:
            return None, f"Stop {i} has an unrecognized action."
        if not address:
            return None, f"Stop {i} is missing an address."
        if s.get("confidence") == "low" and not s.get("reviewed"):
            return None, f"Stop {i} is still flagged for review — mark it reviewed before dispatching."
        clean_stops.append({
            "address": address,
            "action": _PARSER_ACTION_MAP[action_code],
            "container_size": expand_abbrev((s.get("container_size") or "").strip()),
            "notes": expand_abbrev((s.get("notes") or "").strip()),
            "insert_before": str(s.get("insert_before") or "end").strip(),
        })
    return clean_stops, None


@app.route("/api/dispatch", methods=["POST"])
@roles_required("dispatcher", api=True)
def api_dispatch():
    data = request.get_json(silent=True) or {}
    stops_in = data.get("stops")
    driver_id_raw = data.get("driver_id")
    route_date = (data.get("route_date") or today_str()).strip() or today_str()

    clean_stops, err = _validate_parser_stops(stops_in)
    if err:
        return jsonify({"error": err}), 400

    if not driver_id_raw or not str(driver_id_raw).isdigit():
        return jsonify({"error": "Select a driver before dispatching."}), 400
    driver_id = int(driver_id_raw)

    conn = get_db()
    driver = conn.execute(
        "SELECT id, username FROM users WHERE id=? AND company_id=? AND role='driver'",
        (driver_id, cid())
    ).fetchone()
    if not driver:
        conn.close()
        return jsonify({"error": "Selected driver not found."}), 400

    route_name = f"{driver['username']} — {route_date}"
    cur = conn.cursor()
    cur.execute("""
        INSERT INTO routes (route_date, route_name, raw_text, assigned_to, created_by,
                             status, notes, company_id, created_at)
        VALUES (?, ?, '', ?, ?, 'open', '', ?, ?)
    """, (route_date, route_name, driver_id, session["user_id"], cid(), now_ts()))
    route_id = cur.lastrowid

    for idx, s in enumerate(clean_stops, start=1):
        cur.execute("""
            INSERT INTO stops (route_id, stop_order, address, action, container_size, notes,
                                status, created_at)
            VALUES (?, ?, ?, ?, ?, ?, 'open', ?)
        """, (route_id, idx, s["address"], s["action"], s["container_size"], s["notes"], now_ts()))

    conn.commit()
    try:
        compute_can_flow(conn, route_id)
        conn.commit()
    except Exception as exc:
        app.logger.warning("api_dispatch: compute_can_flow error: %s", exc)
    conn.close()

    return jsonify({
        "success": True,
        "route_id": route_id,
        "driver": driver["username"],
        "stop_count": len(clean_stops),
    })


@app.route("/api/route/<int:route_id>/insert-stops", methods=["POST"])
@boss_required
def api_insert_stops(route_id):
    data = request.get_json(silent=True) or {}
    stops_in = data.get("stops")

    clean_stops, err = _validate_parser_stops(stops_in)
    if err:
        return jsonify({"error": err}), 400

    conn = get_db()
    route = conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone()
    if not route:
        conn.close()
        return jsonify({"error": "Route not found."}), 404

    existing = conn.execute(
        "SELECT id, status FROM stops WHERE route_id=? ORDER BY stop_order ASC, id ASC",
        (route_id,)
    ).fetchall()

    current_stop_id = None
    for s in existing:
        if s["status"] != "completed":
            current_stop_id = s["id"]
            break

    # Locked prefix: completed stops + the driver's current in-progress stop, in
    # their original order — never renumbered out of place, never a valid insertion
    # target (enforced here server-side, not just by omitting them from the UI list).
    locked_prefix = []
    working = []
    reached_current = False
    for s in existing:
        if s["status"] == "completed" or (not reached_current and s["id"] == current_stop_id):
            locked_prefix.append(s["id"])
            if s["id"] == current_stop_id:
                reached_current = True
        else:
            working.append(s["id"])

    cur = conn.cursor()
    new_stops = []
    for s in clean_stops:
        cur.execute("""
            INSERT INTO stops (route_id, stop_order, address, action, container_size, notes,
                                status, created_at)
            VALUES (?, 0, ?, ?, ?, ?, 'open', ?)
        """, (route_id, s["address"], s["action"], s["container_size"], s["notes"], now_ts()))
        new_stops.append((cur.lastrowid, s["insert_before"]))

    # Merge new stops into the insertable (unlocked) sequence at their chosen position.
    # Multiple stops targeting the same anchor stack in submission order, immediately
    # before that anchor. Anything targeting "end" or a locked/unknown stop goes last.
    for new_id, insert_before_raw in new_stops:
        target_id = int(insert_before_raw) if insert_before_raw.isdigit() else None
        if target_id is not None and target_id in working:
            working.insert(working.index(target_id), new_id)
        else:
            working.append(new_id)

    final_order = locked_prefix + working
    for pos, sid in enumerate(final_order, start=1):
        cur.execute("UPDATE stops SET stop_order=? WHERE id=?", (pos, sid))

    conn.commit()
    try:
        compute_can_flow(conn, route_id)
        conn.commit()
    except Exception as exc:
        app.logger.warning("api_insert_stops: compute_can_flow error: %s", exc)
    conn.close()

    return jsonify({
        "success": True,
        "route_id": route_id,
        "stop_count": len(clean_stops),
    })


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
    like = "%" + q.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_") + "%"
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
        WHERE sa.company_id=? AND (sa.customer_name LIKE ? ESCAPE '\\' OR sa.address LIKE ? ESCAPE '\\')
        ORDER BY sa.times_used DESC, sa.last_used_at DESC
        LIMIT 10
    """, (cid(), like, like)).fetchall()
    conn.close()
    return jsonify([dict(r) for r in rows])


# =========================================================
# CUSTOMER REQUEST SYSTEM — API (Phase 2)
#
# Customer-facing endpoints are authenticated ONLY by the URL portal token
# (no session, no password). Requests are intent only: creating one never
# creates driver work — the boss approves them in a future phase. All
# validation is server-side. Errors are {"error": "..."} with the right code.
# =========================================================
REQUEST_TYPES     = {"PR", "P", "D", "NEW_BIN", "S"}  # S = Swap (Phase 7B)
REQUEST_SIZES     = ["10yd", "15yd", "20yd", "30yd", "40yd"]
REQUEST_STATUSES  = {"pending", "accepted", "approved", "scheduled", "in_progress", "done", "denied"}
REQUEST_OPEN      = ("pending", "accepted", "approved", "scheduled", "in_progress")  # dupe-guard scope


def _customer_by_token(conn, token):
    """Resolve a portal token to its customer row, or None. Constant-shape
    lookup so a bad token is indistinguishable from an unknown one."""
    if not token:
        return None
    return conn.execute(
        "SELECT * FROM customers WHERE portal_token = ? AND is_active = 1", (token,)
    ).fetchone()


def _not_found():
    """Generic 404 that never reveals whether a token/site was 'close'."""
    return jsonify({"error": "not found"}), 404


@app.route("/api/c/<token>/dashboard")
def customer_dashboard(token):
    conn = get_db()
    customer = _customer_by_token(conn, token)
    if customer is None:
        conn.close()
        return _not_found()

    sites = conn.execute(
        "SELECT id, address, lat, lng, notes, created_at FROM sites "
        "WHERE customer_id = ? ORDER BY id",
        (customer["id"],),
    ).fetchall()

    bins = conn.execute(
        """SELECT b.id, b.customer_id, b.site_id, b.size, b.dropped_at,
                  b.label, b.drop_photo_path,
                  s.address AS site_address
             FROM bins b
             JOIN sites s ON b.site_id = s.id
            WHERE b.customer_id = ?
            ORDER BY b.id""",
        (customer["id"],),
    ).fetchall()

    # Open requests, plus denied and just-completed (<=24h) ones so the
    # customer portal can show "denied — call us" and "Completed ✓" chips.
    # scheduled_date / driver_name come from the linked stop's route (the
    # boss's confirmed schedule), left-joined so unlinked requests still list.
    _now_local = datetime.now(_EASTERN) if _EASTERN else datetime.now()
    _24h_ago = (_now_local - timedelta(hours=24)).strftime("%Y-%m-%d %H:%M:%S")
    reqs = conn.execute(
        """SELECT r.*,
                  ro.route_date AS scheduled_date,
                  u.username     AS driver_name
             FROM requests r
        LEFT JOIN stops  st ON r.stop_id     = st.id
        LEFT JOIN routes ro ON st.route_id   = ro.id
        LEFT JOIN users  u  ON ro.assigned_to = u.id
            WHERE r.customer_id = ?
              AND ( r.status NOT IN ('done','denied')
                    OR r.status = 'denied'
                    OR (r.status = 'done' AND r.updated_at >= ?) )
            ORDER BY r.created_at DESC, r.id DESC""",
        (customer["id"], _24h_ago),
    ).fetchall()
    conn.close()

    return jsonify({
        "customer": {
            "id":            customer["id"],
            "name":          customer["business_name"] or customer["contact_name"],
            "business_name": customer["business_name"],
            "contact_name":  customer["contact_name"],
            "phone":         customer["phone"],
        },
        "sites":    [dict(s) for s in sites],
        "bins":     [
            {**dict(b),
             "drop_photo_url": (url_for("customer_bin_photo", token=token, bin_id=b["id"])
                                if b["drop_photo_path"] else None),
             # never leak the filesystem path to the client
             "drop_photo_path": None}
            for b in bins
        ],
        "requests": [dict(r) for r in reqs],
    })


@app.route("/api/c/<token>/requests", methods=["POST"])
def customer_create_request(token):
    conn = get_db()
    customer = _customer_by_token(conn, token)
    if customer is None:
        conn.close()
        return _not_found()

    def bad(msg):
        conn.close()
        return jsonify({"error": msg}), 400

    data = request.get_json(silent=True)
    if not isinstance(data, dict):
        return bad("invalid or missing JSON body")

    # --- type ---
    rtype = data.get("type")
    if rtype not in REQUEST_TYPES:
        return bad("type must be one of PR, P, D, NEW_BIN")

    # --- site_id: must exist AND belong to this customer (else generic 404) ---
    site_id = data.get("site_id")
    if not isinstance(site_id, int):
        return bad("site_id is required")
    site = conn.execute(
        "SELECT id FROM sites WHERE id = ? AND customer_id = ?",
        (site_id, customer["id"]),
    ).fetchone()
    if site is None:
        conn.close()
        return _not_found()

    bin_id = data.get("bin_id")
    size_requested = data.get("size_requested")

    # --- type-specific requirements ---
    if rtype in ("PR", "P", "S"):  # S (Swap) acts on an existing bin, like PR/P
        if not isinstance(bin_id, int):
            return bad("bin_id is required for PR, P and S requests")
        owned_bin = conn.execute(
            "SELECT id FROM bins WHERE id = ? AND customer_id = ? AND site_id = ?",
            (bin_id, customer["id"], site_id),
        ).fetchone()
        if owned_bin is None:
            return bad("bin_id is not a container at this site")
        size_requested = None  # not used for PR/P/S
    else:  # D or NEW_BIN
        if not isinstance(size_requested, str) or size_requested not in REQUEST_SIZES:
            return bad("size_requested must be one of " + ", ".join(REQUEST_SIZES))
        bin_id = None  # not used for D/NEW_BIN

    # --- preferred_date: "asap" or ISO date today-or-future ---
    preferred_date = data.get("preferred_date")
    if preferred_date != "asap":
        try:
            pd = datetime.strptime(str(preferred_date), "%Y-%m-%d").date()
        except (ValueError, TypeError):
            return bad('preferred_date must be "asap" or an ISO date (YYYY-MM-DD)')
        if pd < datetime.strptime(today_str(), "%Y-%m-%d").date():
            return bad("preferred_date cannot be in the past")

    # --- notes: optional, stripped, <= 500 chars ---
    notes = data.get("notes")
    if notes is not None:
        if not isinstance(notes, str):
            return bad("notes must be text")
        notes = notes.strip()
        if len(notes) > 500:
            return bad("notes must be 500 characters or fewer")
        notes = notes or None

    # --- duplicate guard: one open request per (customer, type, bin) for
    #     PR/P/S, or per (customer, type, site) for D/NEW_BIN ---
    open_ph = ",".join("?" for _ in REQUEST_OPEN)
    if rtype in ("PR", "P", "S"):
        dupe = conn.execute(
            f"""SELECT id FROM requests
                 WHERE customer_id = ? AND type = ? AND bin_id = ?
                   AND status IN ({open_ph})""",
            (customer["id"], rtype, bin_id, *REQUEST_OPEN),
        ).fetchone()
    else:
        dupe = conn.execute(
            f"""SELECT id FROM requests
                 WHERE customer_id = ? AND type = ? AND site_id = ?
                   AND status IN ({open_ph})""",
            (customer["id"], rtype, site_id, *REQUEST_OPEN),
        ).fetchone()
    if dupe is not None:
        conn.close()
        return jsonify({"error": "You already have an open request for this."}), 409

    # --- create ---
    ts = now_ts()
    cur = conn.cursor()
    cur.execute(
        """INSERT INTO requests
               (customer_id, site_id, type, bin_id, size_requested,
                preferred_date, notes, status, stop_id, created_at, updated_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, 'pending', NULL, ?, ?)""",
        (customer["id"], site_id, rtype, bin_id, size_requested,
         preferred_date, notes, ts, ts),
    )
    conn.commit()
    new_row = conn.execute(
        "SELECT * FROM requests WHERE id = ?", (cur.lastrowid,)
    ).fetchone()
    conn.close()
    return jsonify(dict(new_row)), 201


def _sanitize_bin_label(raw):
    """A bin label is short free text the customer/driver/dispatcher can set.
    Strip control chars, collapse whitespace, cap at 40 chars. '' → None."""
    s = str(raw or "").replace("\n", " ").replace("\r", " ").strip()
    s = re.sub(r"\s+", " ", s)
    s = "".join(ch for ch in s if ch >= " ")  # drop control chars
    return s[:40] or None


@app.route("/api/c/<token>/bins/<int:bin_id>/label", methods=["POST"])
def customer_rename_bin(token, bin_id):
    """Customer renames their own bin from the portal (token-authed, CSRF-exempt
    like customer_create_request). Sanitized, max 40 chars."""
    conn = get_db()
    customer = _customer_by_token(conn, token)
    if customer is None:
        conn.close()
        return _not_found()
    owned = conn.execute(
        "SELECT id FROM bins WHERE id=? AND customer_id=?", (bin_id, customer["id"])
    ).fetchone()
    if owned is None:
        conn.close()
        return _not_found()
    data = request.get_json(silent=True) or {}
    label = _sanitize_bin_label(data.get("label"))
    conn.execute("UPDATE bins SET label=? WHERE id=?", (label, bin_id))
    conn.commit()
    conn.close()
    return jsonify({"success": True, "label": label})


@app.route("/api/c/<token>/bin-photo/<int:bin_id>")
def customer_bin_photo(token, bin_id):
    """Serve a bin's 'where we left it' drop photo to the owning customer,
    token-scoped (no session)."""
    conn = get_db()
    customer = _customer_by_token(conn, token)
    if customer is None:
        conn.close()
        return _not_found()
    row = conn.execute(
        "SELECT drop_photo_path FROM bins WHERE id=? AND customer_id=?",
        (bin_id, customer["id"]),
    ).fetchone()
    conn.close()
    if not row or not row["drop_photo_path"]:
        abort(404)
    full = os.path.join(app.root_path, row["drop_photo_path"])
    if not os.path.isfile(full):
        abort(404)
    return send_file(full)


@app.route("/api/bins/<int:bin_id>/label", methods=["POST"])
@login_required
def manage_rename_bin(bin_id):
    """Dispatcher/owner renames a bin from the management side (company-scoped)."""
    if not has_role("dispatcher"):
        return jsonify({"error": "forbidden"}), 403
    conn = get_db()
    owned = conn.execute(
        """SELECT b.id FROM bins b JOIN customers c ON b.customer_id=c.id
            WHERE b.id=? AND c.company_id=?""",
        (bin_id, cid()),
    ).fetchone()
    if owned is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    data = request.get_json(silent=True) or {}
    label = _sanitize_bin_label(data.get("label"))
    conn.execute("UPDATE bins SET label=? WHERE id=?", (label, bin_id))
    conn.commit()
    conn.close()
    return jsonify({"success": True, "label": label})


# =========================================================
# CUSTOMER PORTAL — the page customers actually tap (Phase 4)
#
# Public, token-only, no login. Server renders the styled shell + an embedded
# boot payload; all data/rendering is client-side against the existing
# customer API (GET dashboard, POST requests). Returned as the shell string
# directly (not via render_template_string) so the client JS is emitted
# verbatim without Jinja re-parsing its braces.
# =========================================================
_PORTAL_INVALID_BODY = """
    <div class="hero"><h1>Link not valid</h1></div>
    <div class="empty-state" style="max-width:520px;margin:0 auto;padding:36px 18px;
         font-size:17px;line-height:1.6;text-align:center;">
        This link isn&rsquo;t valid or has expired.<br>
        Please contact your hauler for a new one.
    </div>
"""

_PORTAL_JS = r"""
<style>
  /* Portal buttons use !important to escape the app's aggressive global
     button:not(...) rule (~7-specificity, forces an orange gradient on every
     <button>). Self-contained; no shared CSS is modified. */
  .portal { max-width: 560px; margin: 0 auto; }
  .portal-greeting { margin: 4px 0 20px; }
  .portal-greeting .co { font-family: var(--font-head, inherit); font-size: 13px;
      letter-spacing: 2px; text-transform: uppercase; color: var(--cyan); }
  .portal-greeting .hi { font-size: 26px; font-weight: 800; margin-top: 4px; }
  .p-card { background: var(--bg-card); border: 1px solid var(--border);
      border-radius: 16px; padding: 18px 16px; margin-bottom: 16px; }
  .p-card-head { font-size: 19px; font-weight: 800; }
  .p-card-sub { color: var(--slate); font-size: 14px; margin-top: 2px; }
  .portal .p-btn { display: block; width: 100%; min-height: 62px; margin-top: 12px;
      border: none !important; border-radius: 14px !important; padding: 13px 16px !important;
      cursor: pointer; text-align: left; font-family: inherit; color: #121212 !important;
      box-shadow: none !important; }
  .portal .p-btn .l { display: block; font-size: 17px; font-weight: 800; letter-spacing: .3px; }
  .portal .p-btn .s { display: block; font-size: 13px; font-weight: 600; opacity: .85; margin-top: 3px; }
  .portal .p-btn.pr { background: #FF6B1A !important; }
  .portal .p-btn.p  { background: #FFB27A !important; }
  .portal .p-btn.s  { background: #00E5CC !important; }
  .portal .p-btn.d  { background: #3DDC84 !important; }
  .portal .p-btn:active { transform: translateY(1px); }
  .p-site-head { font-size: 13px; font-weight: 800; text-transform: uppercase; letter-spacing: .6px;
      color: var(--slate); margin: 22px 2px 4px; }
  .portal .p-rename { background: transparent !important; border: none !important; box-shadow: none !important;
      color: var(--cyan) !important; font-size: 13px; font-weight: 800; cursor: pointer; padding: 2px 4px;
      font-family: inherit; white-space: nowrap; min-height: 0 !important; }
  .p-drop-photo { display: block; width: 100%; max-height: 180px; object-fit: cover; border-radius: 12px;
      margin-top: 10px; border: 1px solid var(--border); }
  .portal .p-btn[disabled] { opacity: .45 !important; cursor: default; }
  .chip { display: block; border-radius: 12px; padding: 10px 12px; margin-top: 10px;
      font-size: 14px; font-weight: 700; line-height: 1.35; }
  .chip.orange { background: rgba(255,107,26,0.15); color: #FF8A3D; border: 1px solid rgba(255,107,26,0.4); }
  .chip.green  { background: rgba(61,220,132,0.14); color: #3DDC84; border: 1px solid rgba(61,220,132,0.4); }
  .chip.blue   { background: rgba(0,229,204,0.12);  color: #00E5CC; border: 1px solid rgba(0,229,204,0.4); }
  .chip.red    { background: rgba(255,82,82,0.14);  color: #FF7A7A; border: 1px solid rgba(255,82,82,0.45); }
  .chip.gray   { background: rgba(140,160,179,0.16); color: #ADC0D1; border: 1px solid rgba(140,160,179,0.4); }
  .size-grid { display: grid; gap: 12px; margin-top: 6px; }
  .portal .size-card { display: flex; align-items: center; justify-content: flex-start; gap: 14px;
      width: 100%; min-height: 66px; border: 1px solid var(--border-glow) !important;
      background: var(--bg-card) !important; color: #F5F5F0 !important; border-radius: 14px !important;
      padding: 12px 16px !important; cursor: pointer; text-align: left; font-family: inherit;
      box-shadow: none !important; }
  .portal .size-card:active { transform: translateY(1px); }
  .portal .size-card .sz { font-size: 20px; font-weight: 800; color: var(--cyan) !important; min-width: 64px; }
  .portal .size-card .cue { font-size: 14px; color: #D8D8D0; }
  .p-restate { font-size: 20px; font-weight: 800; line-height: 1.35; margin: 6px 0 18px; }
  .when-row { display: grid; grid-template-columns: 1fr 1fr; gap: 12px; }
  .portal .when-btn { min-height: 56px; border-radius: 14px !important;
      border: 1px solid var(--border-glow) !important; background: var(--bg-card) !important;
      color: #F5F5F0 !important; font-size: 16px; font-weight: 700; cursor: pointer;
      font-family: inherit; box-shadow: none !important; }
  .portal .when-btn.sel { background: var(--cyan) !important; color: #121212 !important;
      border-color: var(--cyan) !important; }
  .p-input, .p-textarea { width: 100%; margin-top: 12px; padding: 14px; font-size: 16px;
      border-radius: 12px; border: 1px solid var(--border); background: rgba(255,255,255,0.04);
      color: #F5F5F0; font-family: inherit; }
  .p-textarea { min-height: 90px; resize: vertical; }
  .portal .p-send { width: 100%; min-height: 60px; margin-top: 18px; border: none !important;
      border-radius: 14px !important; background: var(--cyan) !important; color: #121212 !important;
      font-size: 18px; font-weight: 800; cursor: pointer; font-family: inherit; box-shadow: none !important; }
  .portal .p-send[disabled] { opacity: .5 !important; cursor: default; }
  .portal .p-back { display: block; width: 100%; margin-top: 10px; background: transparent !important;
      border: none !important; box-shadow: none !important; color: var(--slate) !important;
      font-size: 15px; font-weight: 700; padding: 14px; cursor: pointer; font-family: inherit; }
  .p-err { background: rgba(255,82,82,0.14); color: #FF7A7A; border: 1px solid rgba(255,82,82,0.45);
      border-radius: 12px; padding: 12px 14px; margin-top: 14px; font-size: 15px; font-weight: 600; }
  .p-ok { background: rgba(61,220,132,0.14); color: #3DDC84; border: 1px solid rgba(61,220,132,0.4);
      border-radius: 12px; padding: 14px; margin-bottom: 16px; font-size: 16px; font-weight: 700; text-align: center; }
</style>
<script>
(function(){
  var BOOT  = JSON.parse(document.getElementById('portal-boot').textContent);
  var TOKEN = BOOT.token, TODAY = BOOT.today, SIZES = BOOT.sizes;
  var CUES = {'10yd':'Fits a garage cleanout','15yd':'Kitchen remodel','20yd':'Roof tear-off','30yd':'Full house cleanout','40yd':'Construction / commercial'};
  var root  = document.getElementById('portal-root');
  var st = { view:'home', data:null, action:null, when:'asap', date:'', note:'', sending:false, error:'', ok:'' };
  var OPEN = ['pending','accepted','approved','scheduled','in_progress'];

  function esc(s){ return String(s==null?'':s).replace(/[&<>"']/g,function(c){
      return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]; }); }

  function api(path, opts){ return fetch(path, opts); }

  function load(cb){
    api('/api/c/'+encodeURIComponent(TOKEN)+'/dashboard', {headers:{'X-Requested-With':'XMLHttpRequest'}})
      .then(function(r){ if(!r.ok) throw new Error('bad'); return r.json(); })
      .then(function(d){ st.data=d; if(cb) cb(); if(st.view==='home') render(); })
      .catch(function(){ if(!st.data) root.innerHTML = '<div class="p-err">Couldn&rsquo;t load your info &mdash; check your signal and refresh.</div>'; });
  }

  function openReq(type, binId, siteId){
    if(!st.data) return null;
    for(var i=0;i<st.data.requests.length;i++){ var r=st.data.requests[i];
      if(OPEN.indexOf(r.status)<0 || r.type!==type) continue;
      if((type==='PR'||type==='P'||type==='S') && r.bin_id===binId) return r;
      if(type==='D' && r.site_id===siteId) return r;
    }
    return null;
  }
  function infoReqs(binId, siteId){
    if(!st.data) return [];
    return st.data.requests.filter(function(r){
      if(r.status!=='denied' && r.status!=='done') return false;
      return r.bin_id ? (r.bin_id===binId) : (r.site_id===siteId);
    });
  }
  function chip(r){
    var cls='gray', txt=esc(r.status);
    if(r.status==='pending'){ cls='orange'; txt='Request received &mdash; waiting on confirmation'; }
    else if(r.status==='accepted'){ cls='green'; txt='Confirmed &mdash; we&rsquo;re scheduling it'; }
    else if(r.status==='scheduled'){ cls='green'; txt='Scheduled &#10003;'+(r.scheduled_date?(' for '+esc(r.scheduled_date)):'')+(r.driver_name?' &middot; driver assigned':''); }
    else if(r.status==='in_progress'){ cls='blue'; txt='Driver is on it today'; }
    else if(r.status==='done'){ cls='green'; txt='Completed &#10003;'; }
    else if(r.status==='denied'){ cls='red'; txt='We couldn&rsquo;t do this one &mdash; call us'+(r.deny_reason?(': '+esc(r.deny_reason)):''); }
    var typ = r.type==='PR'?'Empty &amp; return':(r.type==='P'?'Pick up':(r.type==='S'?'Swap':'New bin'));
    return '<div class="chip '+cls+'"><span style="opacity:.75;font-weight:800;">'+typ+':</span> '+txt+'</div>';
  }

  function actionBtn(cls, type, label, sub, binId, siteId, onclickIdx){
    var r = openReq(type, binId, siteId);
    if(r) return chip(r);
    return '<button class="p-btn '+cls+'" data-act="'+onclickIdx+'"><span class="l">'+label+'</span><span class="s">'+sub+'</span></button>';
  }

  function render(){
    if(st.view==='home')    return renderHome();
    if(st.view==='size')    return renderSize();
    if(st.view==='confirm') return renderConfirm();
  }

  var acts = []; // click handlers stashed by index for delegation

  function renderHome(){
    acts = [];
    var d = st.data || {bins:[], sites:[], requests:[]};
    var hi = BOOT.contact_name ? ('Hi, '+esc(BOOT.contact_name)) : 'Hi there';
    var html = '<div class="portal-greeting"><div class="co">'+esc(BOOT.company_name)+'</div><div class="hi">'+hi+'</div></div>';
    if(st.ok){ html += '<div class="p-ok">'+esc(st.ok)+'</div>'; st.ok=''; }

    if(d.bins.length){
      // Group bins by site; show a site-address header only when the customer
      // has bins at more than one site (single-site looks unchanged — B5).
      var siteIds = {}; d.bins.forEach(function(b){ siteIds[b.site_id]=1; });
      var multiSite = Object.keys(siteIds).length > 1;
      var lastSite = null;
      d.bins.forEach(function(b){
        if(multiSite && b.site_id!==lastSite){
          html += '<div class="p-site-head">'+esc(b.site_address||'Site')+'</div>';
          lastSite = b.site_id;
        }
        var head = esc(b.size||'Dumpster') + (b.label ? (' &mdash; '+esc(b.label)) : '');
        var iRen = acts.push(function(){ renameBin(b); })-1;
        html += '<div class="p-card">'+
                '<div style="display:flex;justify-content:space-between;align-items:baseline;gap:8px;">'+
                '<div class="p-card-head">'+head+'</div>'+
                '<button class="p-rename" data-act="'+iRen+'">'+(b.label?'Rename':'+ Label')+'</button></div>';
        if(!multiSite){ html += '<div class="p-card-sub">at '+esc(b.site_address||'your site')+'</div>'; }
        if(b.drop_photo_url){
          html += '<a href="'+esc(b.drop_photo_url)+'" target="_blank"><img class="p-drop-photo" src="'+esc(b.drop_photo_url)+'" alt="where we left it"></a>';
        }
        infoReqs(b.id, b.site_id).forEach(function(r){ html += chip(r); });
        var iPR = acts.push(function(){ startPR_P('PR', b); })-1;
        html += actionBtn('pr','PR','EMPTY &amp; RETURN','We dump it and bring the same bin back', b.id, b.site_id, iPR);
        var iP = acts.push(function(){ startPR_P('P', b); })-1;
        html += actionBtn('p','P','PICK UP &mdash; I&rsquo;M DONE','We take the bin away for good', b.id, b.site_id, iP);
        var iS = acts.push(function(){ startPR_P('S', b); })-1;
        html += actionBtn('s','S','SWAP','Empty this one, bring another', b.id, b.site_id, iS);
        var iD = acts.push(function(){ startD(b.site_id, b.site_address); })-1;
        html += actionBtn('d','D','NEED ANOTHER BIN','Bring an additional dumpster to this site', null, b.site_id, iD);
        html += '</div>';
      });
    } else {
      html += '<div class="p-card"><div class="p-card-head">No dumpsters on site</div>'+
              '<div class="p-card-sub">Request one and your hauler will schedule a drop-off.</div>';
      if(d.sites.length){
        var i0 = acts.push(function(){ startNewBin(); })-1;
        html += '<button class="p-btn d" data-act="'+i0+'"><span class="l">REQUEST A BIN</span><span class="s">Pick a size and we&rsquo;ll bring it out</span></button>';
      } else {
        html += '<div class="chip gray">No service address on file &mdash; contact your hauler.</div>';
      }
      html += '</div>';
    }
    root.innerHTML = html;
    wire();
  }

  function startPR_P(type, bin){
    st.action = { type:type, binId:bin.id, siteId:bin.site_id, size:bin.size, address:bin.site_address };
    goConfirm();
  }
  function startD(siteId, address){
    st.action = { type:'D', binId:null, siteId:siteId, size:null, address:address };
    st.view='size'; st.error=''; render();
  }
  function startNewBin(){
    var sites = st.data.sites;
    if(sites.length===1){ startD(sites[0].id, sites[0].address); return; }
    // multiple sites: pick one first
    st.view='sitepick'; st.error=''; renderSitePick();
  }

  function renderSitePick(){
    acts=[];
    var html = '<div class="p-restate">Which site needs a bin?</div>';
    st.data.sites.forEach(function(s){
      var i = acts.push(function(){ startD(s.id, s.address); })-1;
      html += '<button class="size-card" data-act="'+i+'"><span class="cue">'+esc(s.address)+'</span></button>';
    });
    var bi = acts.push(function(){ st.view='home'; render(); })-1;
    html += '<button class="p-back" data-act="'+bi+'">&larr; Back</button>';
    root.innerHTML = html; wire();
  }

  function renderSize(){
    acts=[];
    var html = '<div class="p-restate">What size dumpster?</div><div class="size-grid">';
    SIZES.forEach(function(sz){
      var i = acts.push(function(){ st.action.size=sz; goConfirm(); })-1;
      html += '<button class="size-card" data-act="'+i+'"><span class="sz">'+esc(sz)+'</span><span class="cue">'+esc(CUES[sz]||'')+'</span></button>';
    });
    html += '</div>';
    var bi = acts.push(function(){ st.view='home'; render(); })-1;
    html += '<button class="p-back" data-act="'+bi+'">&larr; Back</button>';
    root.innerHTML = html; wire();
  }

  function goConfirm(){ st.view='confirm'; st.when='asap'; st.date=''; st.note=''; st.error=''; st.sending=false; render(); }

  function restate(a){
    var sz = a.size ? (esc(a.size)+' ') : '';
    if(a.type==='PR') return 'Empty the '+sz+'dumpster at '+esc(a.address)+' and bring it back';
    if(a.type==='P')  return 'Pick up the '+sz+'dumpster at '+esc(a.address);
    if(a.type==='S')  return 'Swap the '+sz+'dumpster at '+esc(a.address)+' &mdash; empty this one and leave a replacement';
    return 'Drop off a '+sz+'dumpster at '+esc(a.address);
  }
  function renameBin(bin){
    var cur = bin.label || '';
    var v = window.prompt('Label this dumpster so everyone knows which is which (e.g. "by the front gate"):', cur);
    if(v===null) return;
    api('/api/c/'+encodeURIComponent(TOKEN)+'/bins/'+bin.id+'/label', {
      method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({label:v})
    }).then(function(r){ return r.json(); }).then(function(){ load(function(){}); render(); })
      .catch(function(){ st.error='Could not save the label — try again.'; render(); });
  }

  function renderConfirm(){
    acts=[];
    var a = st.action;
    var html = '<div class="p-restate">'+restate(a)+'</div>';
    html += '<div style="font-size:13px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:6px;">When?</div>';
    html += '<div class="when-row">'+
            '<button class="when-btn '+(st.when==='asap'?'sel':'')+'" data-act="'+(acts.push(function(){ st.when='asap'; render(); })-1)+'">ASAP</button>'+
            '<button class="when-btn '+(st.when==='date'?'sel':'')+'" data-act="'+(acts.push(function(){ st.when='date'; render(); })-1)+'">Pick a day</button>'+
            '</div>';
    if(st.when==='date'){
      html += '<input class="p-input" type="date" id="p-date" min="'+TODAY+'" value="'+(st.date||TODAY)+'">';
    }
    html += '<textarea class="p-textarea" id="p-note" maxlength="500" placeholder="Gate code, bin location, anything the driver should know">'+esc(st.note)+'</textarea>';
    if(st.error){ html += '<div class="p-err">'+st.error+'</div>'; }
    html += '<button class="p-send" id="p-send" data-act="'+(acts.push(submit)-1)+'"'+(st.sending?' disabled':'')+'>'+(st.sending?'Sending&hellip;':'SEND REQUEST')+'</button>';
    html += '<button class="p-back" data-act="'+(acts.push(function(){ st.view='home'; render(); })-1)+'">Cancel</button>';
    root.innerHTML = html; wire();
  }

  function captureConfirmInputs(){
    var dt = document.getElementById('p-date'); if(dt) st.date = dt.value;
    var nt = document.getElementById('p-note'); if(nt) st.note = nt.value;
  }

  function submit(){
    captureConfirmInputs();
    if(st.sending) return;
    var a = st.action;
    var pref = 'asap';
    if(st.when==='date'){
      if(!st.date || st.date < TODAY){ st.error = 'Please pick today or a later day.'; render(); return; }
      pref = st.date;
    }
    var body = { type:a.type, site_id:a.siteId, preferred_date:pref };
    if(a.type==='PR' || a.type==='P' || a.type==='S') body.bin_id = a.binId;
    else body.size_requested = a.size;
    if(st.note && st.note.trim()) body.notes = st.note.trim();

    st.sending=true; st.error=''; render();
    api('/api/c/'+encodeURIComponent(TOKEN)+'/requests', {
      method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify(body)
    }).then(function(r){
      return r.json().then(function(j){ return {ok:r.ok, status:r.status, j:j}; });
    }).then(function(res){
      st.sending=false;
      if(res.ok){ st.ok='Request sent! Your hauler will confirm shortly.'; st.view='home'; load(function(){ /* refreshed */ }); render(); return; }
      if(res.status===409){ st.error='You&rsquo;ve already got an open request for this bin.'; render(); return; }
      st.error = (res.j && res.j.error) ? esc(res.j.error) : 'Something went wrong. Please try again.';
      render();
    }).catch(function(){
      st.sending=false;
      st.error='Couldn&rsquo;t send &mdash; check your signal and try again.';
      render();
    });
  }

  function wire(){
    // capture typed values before any re-render triggered by taps
    root.querySelectorAll('[data-act]').forEach(function(el){
      el.addEventListener('click', function(){
        if(st.view==='confirm') captureConfirmInputs();
        var fn = acts[parseInt(el.getAttribute('data-act'),10)];
        if(typeof fn==='function') fn();
      });
    });
  }

  // first paint from embedded boot (fast), then live data + polling
  renderHome();
  load();
  setInterval(function(){ if(st.view==='home' && !st.sending) load(); }, 35000);
})();
</script>
"""


@app.route("/c/<token>")
def customer_portal(token):
    """Public token-only portal page. No login. Renders the styled shell with
    an embedded boot payload; the client renders/refreshes from the existing
    customer API. Invalid token -> friendly page, no data leak."""
    conn = get_db()
    customer = _customer_by_token(conn, token)
    if customer is None:
        conn.close()
        return shell_page("Link not valid", _PORTAL_INVALID_BODY), 404
    co = conn.execute(
        "SELECT name FROM companies WHERE id = ?", (customer["company_id"],)
    ).fetchone()
    conn.close()

    boot = {
        "token":         token,
        "company_name":  (co["name"] if co and co["name"] else "HAULTRA"),
        "contact_name":  customer["contact_name"] or "",
        "sizes":         REQUEST_SIZES,
        "today":         today_str(),
    }
    body = (
        '<div id="portal-root" class="portal"></div>'
        '<script id="portal-boot" type="application/json">'
        + json.dumps(boot) + '</script>'
        + _PORTAL_JS
    )
    return shell_page("Request Service", body)


@app.route("/api/requests")
@boss_required
def boss_list_requests():
    """Read-only for now: list requests (default pending) for the boss's
    company, joined with customer/site/bin so the future UI renders cards
    with no extra calls. Uses the existing session-based boss auth."""
    status = (request.args.get("status") or "pending").strip()
    if status not in REQUEST_STATUSES:
        return jsonify({"error": "invalid status filter"}), 400

    conn = get_db()
    rows = conn.execute(
        """SELECT r.*,
                  c.business_name  AS customer_business_name,
                  c.contact_name   AS customer_contact_name,
                  c.phone          AS customer_phone,
                  s.address        AS site_address,
                  b.size           AS bin_size,
                  b.dropped_at     AS bin_dropped_at
             FROM requests r
             JOIN customers c ON r.customer_id = c.id
             JOIN sites     s ON r.site_id     = s.id
        LEFT JOIN bins      b ON r.bin_id      = b.id
            WHERE c.company_id = ? AND r.status = ?
            ORDER BY r.created_at DESC, r.id DESC""",
        (cid(), status),
    ).fetchall()
    conn.close()
    return jsonify([dict(r) for r in rows])


# =========================================================
# CUSTOMER REQUEST SYSTEM — boss approval flow (Phase 3)
#
# Approving a request creates a real stop via the same route/stop shape the
# AI dispatcher uses (api_dispatch), so it renders on the Route Board and the
# driver side like any other stop. The request is then linked to that stop
# and its status tracks the stop's lifecycle (scheduled -> in_progress ->
# done) via cascade_request_from_stop, wired into the existing completion and
# driver-action handlers. Denying just closes the request out.
# =========================================================

# Request type -> AI-parser action code -> canonical action label. NEW_BIN is
# a fresh drop, so it maps to a Delivery like a plain D.
# S (Swap) reuses the PR ("Pickup and Return") stop path plus a flagged note,
# rather than inventing new stop mechanics (per spec).
_REQUEST_TO_PARSER_CODE = {"PR": "PR", "P": "P", "D": "D", "NEW_BIN": "D", "S": "PR"}


def cascade_request_from_stop(conn, stop_id):
    """Keep a linked customer request's status in sync with its stop, derived
    from the stop's authoritative state. No-op for stops with no request_id
    (i.e. every normal parsed/boss stop), so existing driver/boss completion
    behavior is unchanged. Idempotent — safe to call after any stop mutation.

        stop completed              -> request 'done'
        stop started (driver_status past 'pending') -> request 'in_progress'
        otherwise (open, not started, e.g. reopened) -> request 'scheduled'
    """
    row = conn.execute(
        "SELECT request_id, status, driver_status FROM stops WHERE id=?", (stop_id,)
    ).fetchone()
    if not row or not row["request_id"]:
        return
    if row["status"] == "completed":
        new_status = "done"
    elif (row["driver_status"] or "pending") != "pending":
        new_status = "in_progress"
    else:
        new_status = "scheduled"
    conn.execute(
        "UPDATE requests SET status=?, updated_at=? WHERE id=? AND status != ?",
        (new_status, now_ts(), row["request_id"], new_status),
    )


def _load_request_for_assignment(conn, req_id):
    """Fetch a request joined with the fields assignment needs, company-scoped.
    None if not found / not this company."""
    return conn.execute(
        """SELECT r.*, c.business_name, c.contact_name,
                  s.address AS site_address, b.size AS bin_size
             FROM requests r
             JOIN customers c ON r.customer_id = c.id
             JOIN sites     s ON r.site_id     = s.id
        LEFT JOIN bins      b ON r.bin_id      = b.id
            WHERE r.id = ? AND c.company_id = ?""",
        (req_id, cid()),
    ).fetchone()


def _perform_assignment(conn, req, req_id, data):
    """Shared core for one-click approve (Accept & Assign) and the two-stage
    assign: validate driver + date + optional overrides, create the stop via
    the same route/stop shape api_dispatch uses, link it, and set the request
    to 'scheduled' — atomically. Returns (payload, None) on success or
    (None, (http_code, message)) on failure. Caller owns conn + the status
    precondition. Identical stop-creation to the original approve so the Route
    Board / driver side see it exactly as before."""
    # --- driver: required, must exist and be a driver in this company ---
    driver_id_raw = data.get("driver_id")
    if not (isinstance(driver_id_raw, int) or (isinstance(driver_id_raw, str) and driver_id_raw.isdigit())):
        return None, (400, "driver_id is required")
    driver_id = int(driver_id_raw)
    driver = conn.execute(
        "SELECT id, username FROM users WHERE id=? AND company_id=? AND role='driver'",
        (driver_id, cid()),
    ).fetchone()
    if not driver:
        return None, (400, "selected driver not found")

    # --- scheduled_date: dispatcher's choice wins; default from preferred_date
    #     ("asap" -> today). Must be a valid ISO date, today or later. ---
    scheduled_date = (data.get("scheduled_date") or "").strip()
    if not scheduled_date:
        scheduled_date = today_str() if req["preferred_date"] == "asap" else req["preferred_date"]
    try:
        sd = datetime.strptime(scheduled_date, "%Y-%m-%d").date()
    except (ValueError, TypeError):
        return None, (400, "scheduled_date must be an ISO date (YYYY-MM-DD)")
    if sd < datetime.strptime(today_str(), "%Y-%m-%d").date():
        return None, (400, "scheduled_date cannot be in the past")

    # --- optional overrides (address / size / notes) ---
    address = (str(data.get("address") or "").strip()) or (req["site_address"] or "")
    if not address:
        return None, (400, "no address on the site — provide an address override")
    size = (str(data.get("size") or "").strip()) or (req["size_requested"] or req["bin_size"] or "")
    if "notes" in data and data.get("notes") is not None:
        notes = str(data.get("notes")).strip()[:500]
    else:
        notes = req["notes"] or ""

    action_label  = _PARSER_ACTION_MAP[_REQUEST_TO_PARSER_CODE[req["type"]]]
    # Swap reuses the Pickup-and-Return stop path; flag the note so the driver
    # knows to bring an empty to replace the one being pulled.
    if req["type"] == "S":
        notes = ("[SWAP — empty this one, leave a replacement] " + notes).strip()
    customer_name = req["business_name"] or req["contact_name"] or ""

    try:
        cur = conn.cursor()
        route = conn.execute(
            """SELECT id FROM routes
                WHERE company_id=? AND assigned_to=? AND route_date=?
                  AND status IN ('open','in_progress')
                ORDER BY id LIMIT 1""",
            (cid(), driver_id, scheduled_date),
        ).fetchone()
        if route:
            route_id = route["id"]
        else:
            cur.execute(
                """INSERT INTO routes (route_date, route_name, raw_text, assigned_to,
                                       created_by, status, notes, company_id, created_at)
                   VALUES (?, ?, '', ?, ?, 'open', '', ?, ?)""",
                (scheduled_date, f"{driver['username']} — {scheduled_date}",
                 driver_id, session["user_id"], cid(), now_ts()),
            )
            route_id = cur.lastrowid

        next_order = conn.execute(
            "SELECT COALESCE(MAX(stop_order), 0) + 1 AS n FROM stops WHERE route_id=?",
            (route_id,),
        ).fetchone()["n"]

        cur.execute(
            """INSERT INTO stops (route_id, stop_order, customer_name, address, action,
                                  container_size, notes, status, request_id, customer_id,
                                  created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, 'open', ?, ?, ?)""",
            (route_id, next_order, customer_name, address, action_label, size, notes,
             req_id, req["customer_id"], now_ts()),
        )
        stop_id = cur.lastrowid

        conn.execute(
            "UPDATE requests SET status='scheduled', stop_id=?, updated_at=? WHERE id=?",
            (stop_id, now_ts(), req_id),
        )
        conn.commit()
    except Exception as exc:
        conn.rollback()
        app.logger.warning("assign request %s failed: %s", req_id, exc)
        return None, (500, "could not assign request")

    # Best-effort, same as api_dispatch — a can-flow hiccup must not undo the
    # assignment that already committed above.
    try:
        compute_can_flow(conn, route_id)
        conn.commit()
    except Exception as exc:
        app.logger.warning("assign request: compute_can_flow error: %s", exc)

    return {"success": True, "request_id": req_id, "stop_id": stop_id,
            "route_id": route_id, "status": "scheduled"}, None


@app.route("/api/requests/<int:req_id>/approve", methods=["PATCH"])
@login_required
def approve_request(req_id):
    """Accept & Assign in ONE click — the solo-operator path, unchanged from
    Phase 3/4. Requires holding BOTH management roles (owner holds both). A
    pending request goes straight to 'scheduled', creating the stop now."""
    if not (has_role("customer_manager") and has_role("dispatcher")):
        return jsonify({"error": "forbidden"}), 403
    data = request.get_json(silent=True) or {}
    conn = get_db()
    req = _load_request_for_assignment(conn, req_id)
    if req is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    if req["status"] != "pending":
        conn.close()
        return jsonify({"error": "request is not pending"}), 409
    payload, err = _perform_assignment(conn, req, req_id, data)
    conn.close()
    if err:
        return jsonify({"error": err[1]}), err[0]
    return jsonify(payload)


@app.route("/api/requests/<int:req_id>/accept", methods=["PATCH"])
@login_required
def accept_request(req_id):
    """Stage 1 (customer_manager/owner): confirm a pending request WITHOUT
    scheduling it — no driver, no date, no stop. It becomes 'accepted' and
    drops into Unassigned Work. Optional note-to-customer stored for the
    portal."""
    if not has_role("customer_manager"):
        return jsonify({"error": "forbidden"}), 403
    data = request.get_json(silent=True) or {}
    note = data.get("note")
    if note is not None:
        note = str(note).strip()[:500] or None
    conn = get_db()
    req = conn.execute(
        """SELECT r.id, r.status FROM requests r
             JOIN customers c ON r.customer_id = c.id
            WHERE r.id = ? AND c.company_id = ?""",
        (req_id, cid()),
    ).fetchone()
    if req is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    if req["status"] != "pending":
        conn.close()
        return jsonify({"error": "request is not pending"}), 409
    conn.execute(
        "UPDATE requests SET status='accepted', customer_note=?, updated_at=? WHERE id=?",
        (note, now_ts(), req_id),
    )
    conn.commit()
    conn.close()
    return jsonify({"success": True, "request_id": req_id, "status": "accepted"})


@app.route("/api/requests/<int:req_id>/assign", methods=["PATCH"])
@login_required
def assign_request(req_id):
    """Stage 2 (dispatcher/owner): assign an accepted request to a driver +
    date, creating the stop via the exact shared approve path."""
    if not has_role("dispatcher"):
        return jsonify({"error": "forbidden"}), 403
    data = request.get_json(silent=True) or {}
    conn = get_db()
    req = _load_request_for_assignment(conn, req_id)
    if req is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    if req["status"] != "accepted":
        conn.close()
        return jsonify({"error": "request is not awaiting assignment"}), 409
    payload, err = _perform_assignment(conn, req, req_id, data)
    conn.close()
    if err:
        return jsonify({"error": err[1]}), err[0]
    return jsonify(payload)


@app.route("/api/requests/<int:req_id>/deny", methods=["PATCH"])
@boss_required
def deny_request(req_id):
    """Deny a pending request; optionally store a reason (<=300 chars)."""
    data = request.get_json(silent=True) or {}
    reason = data.get("reason")
    if reason is not None:
        reason = str(reason).strip()
        if len(reason) > 300:
            return jsonify({"error": "reason must be 300 characters or fewer"}), 400
        reason = reason or None

    conn = get_db()
    req = conn.execute(
        """SELECT r.id, r.status FROM requests r
             JOIN customers c ON r.customer_id = c.id
            WHERE r.id = ? AND c.company_id = ?""",
        (req_id, cid()),
    ).fetchone()
    if req is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    if req["status"] != "pending":
        conn.close()
        return jsonify({"error": "request is not pending"}), 409

    conn.execute(
        "UPDATE requests SET status='denied', deny_reason=?, updated_at=? WHERE id=?",
        (reason, now_ts(), req_id),
    )
    conn.commit()
    conn.close()
    return jsonify({"success": True, "request_id": req_id, "status": "denied"})


# Requests page client script. Plain (non-f) string — its JS braces must not
# collide with the page's f-string. Approve/Deny call the PATCH endpoints and
# remove the card on success; errors render inline per card.
_REQUESTS_PAGE_JS = """
<script>
(function(){
  var CSRF = (document.querySelector('meta[name=csrf-token]')||{}).content || '';
  function hideForms(id){
    var ac=document.getElementById('accept-form-'+id); if(ac) ac.hidden=true;
    var a=document.getElementById('approve-form-'+id); if(a) a.hidden=true;
    var d=document.getElementById('deny-form-'+id); if(d) d.hidden=true;
    var e=document.getElementById('err-'+id); if(e){ e.hidden=true; e.textContent=''; }
  }
  window.hideReqForms = hideForms;
  window.showAccept=function(id){ hideForms(id); var ac=document.getElementById('accept-form-'+id); if(ac) ac.hidden=false; };
  window.showApprove=function(id){ hideForms(id); var a=document.getElementById('approve-form-'+id); if(a) a.hidden=false; };
  window.showDeny=function(id){ hideForms(id); var d=document.getElementById('deny-form-'+id); if(d) d.hidden=false; };
  function err(id,msg){ var e=document.getElementById('err-'+id); if(e){ e.textContent=msg; e.hidden=false; } }
  function removeCard(id){
    var c=document.getElementById('req-card-'+id); if(c) c.remove();
    var list=document.getElementById('req-list');
    if(list && !list.querySelector('.bin-card')){
      var empty=document.getElementById('req-empty'); if(empty) empty.hidden=false;
    }
    var badge=document.getElementById('req-nav-badge');
    if(badge){ var n=parseInt(badge.textContent||'0',10)-1;
      if(n>0){ badge.textContent=n; } else { badge.hidden=true; badge.textContent=''; } }
  }
  function patch(url, body, id){
    fetch(url, {method:'PATCH', headers:{'Content-Type':'application/json','X-CSRF-Token':CSRF},
                body:JSON.stringify(body)})
      .then(function(r){ return r.json().then(function(j){ return {ok:r.ok, j:j}; }); })
      .then(function(res){ if(res.ok){ removeCard(id); }
                           else { err(id, (res.j && res.j.error) || 'Something went wrong.'); } })
      .catch(function(){ err(id, 'Network error — try again.'); });
  }
  window.submitAccept=function(id){
    var note=(document.getElementById('note-'+id)||{value:''}).value || '';
    patch('/api/requests/'+id+'/accept', {note: note}, id);
  };
  window.submitApprove=function(id){
    var drv=document.getElementById('drv-'+id).value;
    var date=document.getElementById('date-'+id).value;
    if(!drv){ err(id,'Pick a driver.'); return; }
    patch('/api/requests/'+id+'/approve', {driver_id: parseInt(drv,10), scheduled_date: date}, id);
  };
  window.submitDeny=function(id){
    var reason=(document.getElementById('reason-'+id)||{value:''}).value || '';
    patch('/api/requests/'+id+'/deny', {reason: reason}, id);
  };
})();
</script>
"""


# Unassigned Work client script. Plain (non-f) string. Assign calls the same
# PATCH /assign endpoint the two-stage flow uses; on success the card leaves
# the queue and the nav badge ticks down.
_UNASSIGNED_PAGE_JS = """
<script>
(function(){
  var CSRF = (document.querySelector('meta[name=csrf-token]')||{}).content || '';
  function hideForm(id){
    var f=document.getElementById('assign-form-'+id); if(f) f.hidden=true;
    var e=document.getElementById('err-'+id); if(e){ e.hidden=true; e.textContent=''; }
  }
  window.hideAssign = hideForm;
  window.showAssign=function(id){ hideForm(id); var f=document.getElementById('assign-form-'+id); if(f) f.hidden=false; };
  function err(id,msg){ var e=document.getElementById('err-'+id); if(e){ e.textContent=msg; e.hidden=false; } }
  function removeCard(id){
    var c=document.getElementById('uw-card-'+id); if(c) c.remove();
    var list=document.getElementById('uw-list');
    if(list && !list.querySelector('.bin-card')){
      var empty=document.getElementById('uw-empty'); if(empty) empty.hidden=false;
    }
    var badge=document.getElementById('unassigned-nav-badge');
    if(badge){ var n=parseInt(badge.textContent||'0',10)-1;
      if(n>0){ badge.textContent=n; } else { badge.hidden=true; badge.textContent=''; } }
  }
  window.submitAssign=function(id){
    var drv=document.getElementById('drv-'+id).value;
    var date=document.getElementById('date-'+id).value;
    if(!drv){ err(id,'Pick a driver.'); return; }
    fetch('/api/requests/'+id+'/assign', {method:'PATCH',
        headers:{'Content-Type':'application/json','X-CSRF-Token':CSRF},
        body:JSON.stringify({driver_id: parseInt(drv,10), scheduled_date: date})})
      .then(function(r){ return r.json().then(function(j){ return {ok:r.ok, j:j}; }); })
      .then(function(res){ if(res.ok){ removeCard(id); }
                           else { err(id, (res.j && res.j.error) || 'Something went wrong.'); } })
      .catch(function(){ err(id, 'Network error — try again.'); });
  };
})();
</script>
"""


@app.route("/unassigned")
@roles_required("dispatcher")
def unassigned_work():
    """Dispatcher/owner: accepted-but-unassigned jobs, oldest/most-urgent
    first, each assignable to a driver + date in place."""
    conn = get_db()
    reqs = conn.execute(
        """SELECT r.*,
                  c.business_name AS customer_business_name,
                  c.contact_name  AS customer_contact_name,
                  s.address       AS site_address,
                  b.size          AS bin_size
             FROM requests r
             JOIN customers c ON r.customer_id = c.id
             JOIN sites     s ON r.site_id     = s.id
        LEFT JOIN bins      b ON r.bin_id      = b.id
            WHERE c.company_id = ? AND r.status = 'accepted'""",
        (cid(),),
    ).fetchall()
    drivers = conn.execute(
        "SELECT id, username FROM users WHERE role='driver' AND company_id=? ORDER BY username",
        (cid(),),
    ).fetchall()
    conn.close()

    today = today_str()

    def eff_date(r):
        # "asap" is the most urgent — sort it as today so it leads the queue.
        return today if r["preferred_date"] == "asap" else (r["preferred_date"] or "9999-12-31")

    # Preferred date ascending, then oldest request first.
    reqs = sorted(reqs, key=lambda r: (eff_date(r), r["created_at"] or "", r["id"]))

    driver_options = '<option value="">Select driver…</option>' + "".join(
        f'<option value="{d["id"]}">{e(d["username"])}</option>' for d in drivers
    )

    _TYPE_LABEL = {"PR": "PR · Pull & Return", "P": "P · Pickup",
                   "D": "D · Drop", "NEW_BIN": "NEW BIN", "S": "S · Swap"}

    def age_label(created_at):
        """Whole days since the request came in, e.g. 'new', '3d old'."""
        if not created_at:
            return ""
        try:
            then = datetime.strptime(created_at[:10], "%Y-%m-%d").date()
        except (ValueError, TypeError):
            return ""
        days = (datetime.strptime(today, "%Y-%m-%d").date() - then).days
        if days <= 0:
            return "new today"
        return f"{days}d old"

    cards = ""
    for r in reqs:
        rid  = r["id"]
        name = e(r["customer_business_name"] or r["customer_contact_name"] or "Customer")
        addr = e(r["site_address"] or "—")
        size = r["bin_size"] if r["type"] in ("PR", "P") else r["size_requested"]
        size_html = (f'<div style="color:var(--slate);font-size:13px;margin-top:2px;">📦 {e(size)}</div>'
                     if size else "")
        pref = r["preferred_date"]
        ed = eff_date(r)
        if pref == "asap":
            pref_label, flag = "ASAP", "today"
        else:
            pref_label = e(pref)
            flag = "overdue" if ed < today else ("today" if ed == today else "")
        if flag == "overdue":
            flag_html = ('<span style="color:#FF7A7A;font-weight:800;font-size:11px;'
                         'text-transform:uppercase;letter-spacing:.5px;">Overdue</span>')
            date_color = "#FF7A7A"
        elif flag == "today":
            flag_html = ('<span style="color:var(--cyan);font-weight:800;font-size:11px;'
                         'text-transform:uppercase;letter-spacing:.5px;">Today</span>')
            date_color = "var(--cyan)"
        else:
            flag_html = ""
            date_color = "var(--slate)"
        notes_html = (
            f'<div style="margin-top:8px;padding:8px 10px;background:rgba(255,255,255,0.03);'
            f'border-radius:8px;font-size:13px;color:#C9C9C2;">{e(r["notes"])}</div>'
        ) if r["notes"] else ""
        default_date = today if pref == "asap" else e(pref)
        type_badge = (
            f'<span style="display:inline-block;padding:3px 10px;border-radius:999px;'
            f'font-size:10px;font-weight:800;letter-spacing:.6px;text-transform:uppercase;'
            f'background:var(--cyan-dim);color:var(--cyan);border:1px solid var(--border-glow);">'
            f'{e(_TYPE_LABEL.get(r["type"], r["type"]))}</span>'
        )
        age = age_label(r["created_at"])
        cards += f"""
        <div class="bin-card" id="uw-card-{rid}" style="padding:16px;">
            <div style="display:flex;justify-content:space-between;align-items:center;gap:10px;">
                {type_badge}
                <span style="color:{date_color};font-size:12px;white-space:nowrap;">📅 {pref_label} {flag_html}</span>
            </div>
            <div style="font-weight:700;font-size:15px;margin-top:8px;">{name}</div>
            <div style="color:var(--slate);font-size:13px;margin-top:2px;">📍 {addr}</div>
            {size_html}
            <div style="color:var(--slate);font-size:12px;margin-top:4px;">🕑 {age}</div>
            {notes_html}
            <div style="margin-top:12px;">
                <button class="btn green" style="width:100%;" onclick="showAssign({rid})">Assign</button>
            </div>
            <div id="err-{rid}" hidden style="color:#FF5252;font-size:12px;margin-top:8px;"></div>
            <div id="assign-form-{rid}" hidden style="margin-top:12px;border-top:1px solid var(--border);padding-top:12px;">
                <label style="display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;">Driver</label>
                <select id="drv-{rid}" style="width:100%;margin-bottom:10px;">{driver_options}</select>
                <label style="display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;">Scheduled date</label>
                <input type="date" id="date-{rid}" value="{default_date}" style="width:100%;margin-bottom:12px;">
                <div style="display:flex;gap:8px;">
                    <button class="btn green" style="flex:1;" onclick="submitAssign({rid})">Confirm &amp; schedule</button>
                    <button class="btn secondary" onclick="hideAssign({rid})">Cancel</button>
                </div>
            </div>
        </div>
        """

    empty_hidden = "" if not reqs else " hidden"
    body = f"""
    <div class="hero">
        <h1>Unassigned Work</h1>
        <p>Accepted jobs waiting to be routed. Assign one to a driver and date to schedule it.</p>
    </div>
    <div id="uw-empty" class="empty-state" style="padding:32px 0;"{empty_hidden}>No unassigned work — everything's routed.</div>
    <div id="uw-list" class="bin-list" style="display:grid;gap:12px;max-width:640px;">
        {cards}
    </div>
    """ + _UNASSIGNED_PAGE_JS
    return render_template_string(shell_page("Unassigned Work", body))


def _new_portal_token(conn):
    """A URL-safe token guaranteed unique across customers."""
    for _ in range(8):
        tok = secrets.token_urlsafe(32)
        if not conn.execute(
            "SELECT 1 FROM customers WHERE portal_token=?", (tok,)
        ).fetchone():
            return tok
    return secrets.token_urlsafe(48)  # astronomically unlikely fallback


def _portal_url(token):
    return url_for("customer_portal", token=token, _external=True)


def _load_customer_scoped(conn, customer_id):
    """An active customer in the session's company, or None."""
    return conn.execute(
        "SELECT * FROM customers WHERE id=? AND company_id=? AND is_active=1",
        (customer_id, cid()),
    ).fetchone()


@app.route("/customers")
@roles_required("customer_manager")
def customers_page():
    """Customer_manager/owner: active customers with at-a-glance counts, plus
    an Add Customer form."""
    conn = get_db()
    rows = conn.execute(
        """SELECT c.id, c.business_name, c.contact_name, c.phone,
                  (SELECT COUNT(*) FROM bins b WHERE b.customer_id = c.id) AS bin_count,
                  (SELECT COUNT(*) FROM requests r
                     WHERE r.customer_id = c.id
                       AND r.status IN ('pending','accepted','approved','scheduled','in_progress')
                  ) AS open_count
             FROM customers c
            WHERE c.company_id = ? AND c.is_active = 1
            ORDER BY LOWER(COALESCE(c.business_name, c.contact_name, '')), c.id""",
        (cid(),),
    ).fetchall()
    conn.close()

    size_opts = "".join(f'<option value="{s}">{s}</option>' for s in REQUEST_SIZES)

    cards = ""
    for c in rows:
        name = e(c["business_name"] or c["contact_name"] or "Customer")
        contact = e(c["contact_name"] or "")
        phone = e(c["phone"] or "")
        meta_bits = " · ".join(b for b in [contact, phone] if b)
        meta_html = (f'<div style="color:var(--slate);font-size:13px;margin-top:2px;">{meta_bits}</div>'
                     if meta_bits else "")
        open_badge = (
            f'<span style="display:inline-block;padding:2px 9px;border-radius:999px;'
            f'font-size:11px;font-weight:800;background:var(--cyan-dim);color:var(--cyan);'
            f'border:1px solid var(--border-glow);">{c["open_count"]} open</span>'
        ) if c["open_count"] else ""
        cards += f"""
        <a class="bin-card" href="{url_for('customer_detail_page', customer_id=c['id'])}"
           style="padding:16px;display:block;text-decoration:none;color:inherit;">
            <div style="display:flex;justify-content:space-between;align-items:center;gap:10px;">
                <div style="font-weight:700;font-size:15px;">{name}</div>
                {open_badge}
            </div>
            {meta_html}
            <div style="color:var(--slate);font-size:12px;margin-top:6px;">
                🗑️ {c["bin_count"]} active bin{"" if c["bin_count"]==1 else "s"}
            </div>
        </a>
        """

    empty_hidden = "" if not rows else " hidden"
    body = f"""
    <div class="hero">
        <h1>Customers</h1>
        <p>Everyone you serve. Add a customer to generate their self-service portal link.</p>
    </div>
    <div style="max-width:640px;margin-bottom:16px;">
        <button class="btn green" id="add-cust-toggle" onclick="toggleAdd()">+ Add Customer</button>
        <div id="add-cust-form" hidden class="bin-card" style="padding:16px;margin-top:12px;">
            <div id="add-err" hidden style="color:#FF5252;font-size:12px;margin-bottom:8px;"></div>
            <label class="uw-lbl">Business name</label>
            <input id="ac-business" style="width:100%;margin-bottom:10px;" placeholder="ABC Demolition">
            <label class="uw-lbl">Contact name</label>
            <input id="ac-contact" style="width:100%;margin-bottom:10px;" placeholder="Sam Rivera">
            <label class="uw-lbl">Phone</label>
            <input id="ac-phone" style="width:100%;margin-bottom:10px;" placeholder="757-555-0142">
            <label class="uw-lbl">Site address</label>
            <input id="ac-address" style="width:100%;margin-bottom:10px;" placeholder="1200 Industrial Blvd, Norfolk, VA">
            <label class="uw-lbl">Initial bin size (optional)</label>
            <select id="ac-size" style="width:100%;margin-bottom:12px;"><option value="">None yet</option>{size_opts}</select>
            <div style="display:flex;gap:8px;">
                <button class="btn green" style="flex:1;" onclick="submitAdd()">Create customer</button>
                <button class="btn secondary" onclick="toggleAdd()">Cancel</button>
            </div>
        </div>
    </div>
    <div id="cust-empty" class="empty-state" style="padding:32px 0;"{empty_hidden}>No customers yet — add your first one above.</div>
    <div class="bin-list" style="display:grid;gap:12px;max-width:640px;">
        {cards}
    </div>
    <style>.uw-lbl{{display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;}}</style>
    """ + _CUSTOMERS_PAGE_JS
    return render_template_string(shell_page("Customers", body))


_CUSTOMERS_PAGE_JS = """
<script>
(function(){
  var CSRF = (document.querySelector('meta[name=csrf-token]')||{}).content || '';
  window.toggleAdd=function(){
    var f=document.getElementById('add-cust-form');
    if(f) f.hidden=!f.hidden;
  };
  function err(msg){ var e=document.getElementById('add-err'); if(e){ e.textContent=msg; e.hidden=false; } }
  window.submitAdd=function(){
    var body={
      business_name:(document.getElementById('ac-business')||{}).value||'',
      contact_name:(document.getElementById('ac-contact')||{}).value||'',
      phone:(document.getElementById('ac-phone')||{}).value||'',
      site_address:(document.getElementById('ac-address')||{}).value||'',
      bin_size:(document.getElementById('ac-size')||{}).value||''
    };
    if(!body.business_name.trim() && !body.contact_name.trim()){ err('Enter a business or contact name.'); return; }
    fetch('/api/customers', {method:'POST',
        headers:{'Content-Type':'application/json','X-CSRF-Token':CSRF},
        body:JSON.stringify(body)})
      .then(function(r){ return r.json().then(function(j){ return {ok:r.ok, j:j}; }); })
      .then(function(res){ if(res.ok && res.j.id){ window.location='/customers/'+res.j.id; }
                           else { err((res.j && res.j.error) || 'Could not create customer.'); } })
      .catch(function(){ err('Network error — try again.'); });
  };
})();
</script>
"""


@app.route("/api/customers", methods=["POST"])
@login_required
def create_customer():
    """Create a customer (+ optional first site and bin) and mint a portal
    token. customer_manager/owner only."""
    if not has_role("customer_manager"):
        return jsonify({"error": "forbidden"}), 403
    data = request.get_json(silent=True) or {}
    business = str(data.get("business_name") or "").strip()[:200]
    contact  = str(data.get("contact_name") or "").strip()[:200]
    phone    = str(data.get("phone") or "").strip()[:50]
    address  = str(data.get("site_address") or "").strip()[:300]
    bin_size = str(data.get("bin_size") or "").strip()
    if not business and not contact:
        return jsonify({"error": "a business or contact name is required"}), 400
    if bin_size and bin_size not in REQUEST_SIZES:
        return jsonify({"error": "invalid bin size"}), 400
    if bin_size and not address:
        return jsonify({"error": "a site address is required to add a bin"}), 400

    conn = get_db()
    try:
        token = _new_portal_token(conn)
        ts = now_ts()
        cur = conn.cursor()
        cur.execute(
            """INSERT INTO customers (company_id, business_name, contact_name, phone,
                                      portal_token, is_active, created_at)
               VALUES (?, ?, ?, ?, ?, 1, ?)""",
            (cid(), business or None, contact or None, phone or None, token, ts),
        )
        customer_id = cur.lastrowid
        if address:
            cur.execute(
                "INSERT INTO sites (customer_id, address, created_at) VALUES (?, ?, ?)",
                (customer_id, address, ts),
            )
            site_id = cur.lastrowid
            if bin_size:
                cur.execute(
                    "INSERT INTO bins (customer_id, site_id, size, dropped_at) VALUES (?, ?, ?, ?)",
                    (customer_id, site_id, bin_size, today_str()),
                )
        conn.commit()
    except Exception as exc:
        conn.rollback()
        conn.close()
        app.logger.warning("create customer failed: %s", exc)
        return jsonify({"error": "could not create customer"}), 500
    conn.close()
    return jsonify({"success": True, "id": customer_id, "portal_token": token})


@app.route("/api/customers/<int:customer_id>", methods=["PATCH"])
@login_required
def update_customer(customer_id):
    """Edit a customer's business name / contact / phone. cm/owner only."""
    if not has_role("customer_manager"):
        return jsonify({"error": "forbidden"}), 403
    data = request.get_json(silent=True) or {}
    conn = get_db()
    cust = _load_customer_scoped(conn, customer_id)
    if cust is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    business = str(data.get("business_name") or "").strip()[:200]
    contact  = str(data.get("contact_name") or "").strip()[:200]
    phone    = str(data.get("phone") or "").strip()[:50]
    if not business and not contact:
        conn.close()
        return jsonify({"error": "a business or contact name is required"}), 400
    conn.execute(
        "UPDATE customers SET business_name=?, contact_name=?, phone=? WHERE id=?",
        (business or None, contact or None, phone or None, customer_id),
    )
    conn.commit()
    conn.close()
    return jsonify({"success": True})


@app.route("/api/customers/<int:customer_id>/regenerate-token", methods=["POST"])
@login_required
def regenerate_customer_token(customer_id):
    """Mint a fresh portal token, invalidating the old link. cm/owner only."""
    if not has_role("customer_manager"):
        return jsonify({"error": "forbidden"}), 403
    conn = get_db()
    cust = _load_customer_scoped(conn, customer_id)
    if cust is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    token = _new_portal_token(conn)
    conn.execute("UPDATE customers SET portal_token=? WHERE id=?", (token, customer_id))
    conn.commit()
    conn.close()
    return jsonify({"success": True, "portal_token": token, "portal_url": _portal_url(token)})


@app.route("/api/customers/<int:customer_id>/deactivate", methods=["POST"])
@login_required
def deactivate_customer(customer_id):
    """Soft-delete: hide from lists and kill portal access. History is kept.
    cm/owner only."""
    if not has_role("customer_manager"):
        return jsonify({"error": "forbidden"}), 403
    conn = get_db()
    cust = _load_customer_scoped(conn, customer_id)
    if cust is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    conn.execute("UPDATE customers SET is_active=0 WHERE id=?", (customer_id,))
    conn.commit()
    conn.close()
    return jsonify({"success": True})


@app.route("/customers/<int:customer_id>")
@roles_required("customer_manager")
def customer_detail_page(customer_id):
    """One customer: info, sites, bins, request history, and the portal link
    with copy / text / regenerate controls."""
    conn = get_db()
    cust = _load_customer_scoped(conn, customer_id)
    if cust is None:
        conn.close()
        flash("Customer not found.", "error")
        return redirect(url_for("customers_page"))

    sites = conn.execute(
        "SELECT id, address, notes FROM sites WHERE customer_id=? ORDER BY id",
        (customer_id,),
    ).fetchall()
    bins = conn.execute(
        """SELECT b.id, b.size, b.dropped_at, b.label, s.address AS site_address
             FROM bins b LEFT JOIN sites s ON b.site_id = s.id
            WHERE b.customer_id=? ORDER BY b.id""",
        (customer_id,),
    ).fetchall()
    reqs = conn.execute(
        """SELECT r.id, r.type, r.status, r.preferred_date, r.created_at,
                  ro.route_date AS scheduled_date
             FROM requests r
        LEFT JOIN stops st ON r.stop_id = st.id
        LEFT JOIN routes ro ON st.route_id = ro.id
            WHERE r.customer_id=? ORDER BY r.created_at DESC, r.id DESC""",
        (customer_id,),
    ).fetchall()
    conn.close()

    portal_url = _portal_url(cust["portal_token"])
    company_name = session.get("company_name") or "HAULTRA"
    name = e(cust["business_name"] or cust["contact_name"] or "Customer")
    contact = cust["contact_name"] or ""
    # SMS body: greeting uses contact if we have one.
    greet = f"Hi {contact}, " if contact else "Hi, "
    sms_body = (f"{greet}here's your {company_name} service portal — request pickups, "
                f"swaps, or extra bins anytime: {portal_url}")
    sms_href = ("sms:" + (e(cust["phone"]) if cust["phone"] else "")
                + "?&body=" + urllib.parse.quote(sms_body))

    _TYPE_LABEL = {"PR": "PR · Pull & Return", "P": "P · Pickup",
                   "D": "D · Drop", "NEW_BIN": "NEW BIN", "S": "S · Swap"}
    _STATUS_LABEL = {"pending": "Pending", "accepted": "Accepted",
                     "approved": "Approved", "scheduled": "Scheduled",
                     "in_progress": "In progress", "done": "Done", "denied": "Denied"}

    _site_rows = []
    for s in sites:
        note = (f'<div style="color:var(--slate);font-size:12px;margin-top:2px;">{e(s["notes"])}</div>'
                if s["notes"] else "")
        _site_rows.append(
            f'<div style="padding:8px 0;border-bottom:1px solid var(--border);">'
            f'📍 {e(s["address"] or "—")}{note}</div>'
        )
    sites_html = "".join(_site_rows) or '<div style="color:var(--slate);font-size:13px;">No sites yet.</div>'

    _can_rename = has_role("dispatcher")
    _bin_rows = []
    for b in bins:
        dropped = f' · dropped {e(b["dropped_at"])}' if b["dropped_at"] else ""
        label_html = (f' <span style="color:var(--cyan);font-weight:700;">— {e(b["label"])}</span>'
                      if b["label"] else "")
        rename_btn = (f'<button class="btn secondary" style="padding:2px 10px;font-size:11px;" '
                      f'onclick="renameBin({b["id"]}, {e(json.dumps(b["label"] or ""))})">Label</button>'
                      if _can_rename else "")
        _bin_rows.append(
            f'<div style="display:flex;justify-content:space-between;align-items:center;gap:8px;'
            f'padding:8px 0;border-bottom:1px solid var(--border);">'
            f'<div>🗑️ {e(b["size"] or "Dumpster")}{label_html} '
            f'<span style="color:var(--slate);font-size:12px;">at {e(b["site_address"] or "—")}{dropped}</span></div>'
            f'{rename_btn}</div>'
        )
    bins_html = "".join(_bin_rows) or '<div style="color:var(--slate);font-size:13px;">No active bins.</div>'

    def _status_chip(st):
        color = {"denied": "#FF7A7A", "done": "#3DDC84", "pending": "#FF8A3D"}.get(st, "var(--cyan)")
        return (f'<span style="color:{color};font-weight:700;font-size:12px;">'
                f'{e(_STATUS_LABEL.get(st, st))}</span>')

    reqs_html = "".join(
        f'<div style="display:flex;justify-content:space-between;gap:10px;padding:8px 0;border-bottom:1px solid var(--border);">'
        f'<span style="font-size:13px;">{e(_TYPE_LABEL.get(r["type"], r["type"]))}'
        f'<span style="color:var(--slate);"> · {e((r["created_at"] or "")[:10])}</span></span>'
        f'{_status_chip(r["status"])}</div>'
        for r in reqs
    ) or '<div style="color:var(--slate);font-size:13px;">No requests yet.</div>'

    body = f"""
    <div class="hero" style="display:flex;justify-content:space-between;align-items:flex-start;gap:12px;">
        <div>
            <h1 style="margin-bottom:4px;">{name}</h1>
            <p style="margin:0;">Customer details &amp; portal link.</p>
        </div>
        <a class="btn secondary" href="{url_for('customers_page')}" style="white-space:nowrap;">← All customers</a>
    </div>

    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
        <div style="display:flex;justify-content:space-between;align-items:center;">
            <h2 style="font-size:15px;margin:0;">Info</h2>
            <button class="btn secondary" onclick="toggleEdit()" style="padding:4px 12px;font-size:12px;">Edit</button>
        </div>
        <div id="cust-view" style="margin-top:10px;">
            <div style="font-size:14px;">👤 {e(contact) or "—"}</div>
            <div style="font-size:14px;color:var(--slate);margin-top:4px;">📞 {e(cust["phone"] or "—")}</div>
        </div>
        <div id="cust-edit" hidden style="margin-top:10px;">
            <div id="edit-err" hidden style="color:#FF5252;font-size:12px;margin-bottom:8px;"></div>
            <label class="uw-lbl">Business name</label>
            <input id="ed-business" style="width:100%;margin-bottom:10px;" value="{e(cust["business_name"] or "")}">
            <label class="uw-lbl">Contact name</label>
            <input id="ed-contact" style="width:100%;margin-bottom:10px;" value="{e(cust["contact_name"] or "")}">
            <label class="uw-lbl">Phone</label>
            <input id="ed-phone" style="width:100%;margin-bottom:12px;" value="{e(cust["phone"] or "")}">
            <div style="display:flex;gap:8px;">
                <button class="btn green" style="flex:1;" onclick="submitEdit()">Save</button>
                <button class="btn secondary" onclick="toggleEdit()">Cancel</button>
            </div>
        </div>
    </div>

    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
        <h2 style="font-size:15px;margin:0 0 10px;">Portal link</h2>
        <div id="portal-url-box" style="word-break:break-all;font-size:13px;color:var(--cyan);
             background:rgba(255,255,255,0.03);border-radius:8px;padding:10px;">{e(portal_url)}</div>
        <div style="display:flex;gap:8px;flex-wrap:wrap;margin-top:10px;">
            <button class="btn secondary" onclick="copyLink()" style="flex:1;min-width:110px;">Copy link</button>
            <a class="btn secondary" href="{sms_href}" style="flex:1;min-width:110px;text-align:center;">Text link</a>
            <button class="btn secondary" onclick="regen()" style="flex:1;min-width:110px;">Regenerate</button>
        </div>
        <div id="portal-msg" hidden style="font-size:12px;margin-top:8px;color:var(--slate);"></div>
    </div>

    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
        <h2 style="font-size:15px;margin:0 0 6px;">Sites</h2>
        {sites_html}
    </div>
    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
        <h2 style="font-size:15px;margin:0 0 6px;">Bins</h2>
        {bins_html}
    </div>
    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
        <h2 style="font-size:15px;margin:0 0 6px;">Request history</h2>
        {reqs_html}
    </div>
    <div style="max-width:640px;margin-bottom:24px;">
        <button class="btn red" onclick="deactivate()" style="width:100%;">Deactivate customer</button>
        <div style="color:var(--slate);font-size:12px;margin-top:6px;text-align:center;">
            Hides them from lists and disables their portal link. History is kept.
        </div>
    </div>
    <style>.uw-lbl{{display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;}}</style>
    {_customer_detail_js(customer_id)}
    """
    return render_template_string(shell_page("Customer", body))


def _customer_detail_js(customer_id):
    """Per-customer detail script. f-string only interpolates the id and the
    customers list URL; all JS braces are doubled."""
    list_url = url_for("customers_page")
    return f"""
<script>
(function(){{
  var CSRF = (document.querySelector('meta[name=csrf-token]')||{{}}).content || '';
  var CID = {customer_id};
  function msg(t){{ var m=document.getElementById('portal-msg'); if(m){{ m.textContent=t; m.hidden=false; }} }}
  window.renameBin=function(binId, cur){{
    var v=window.prompt('Label this bin (e.g. "by the front gate"):', cur||'');
    if(v===null) return;
    fetch('/api/bins/'+binId+'/label', {{method:'POST',
        headers:{{'Content-Type':'application/json','X-CSRF-Token':CSRF}},
        body:JSON.stringify({{label:v}})}})
      .then(function(r){{ return r.json().then(function(j){{ return {{ok:r.ok,j:j}}; }}); }})
      .then(function(res){{ if(res.ok){{ window.location.reload(); }} else {{ alert((res.j&&res.j.error)||'Could not save.'); }} }})
      .catch(function(){{ alert('Network error — try again.'); }});
  }};
  window.toggleEdit=function(){{
    var v=document.getElementById('cust-view'), ed=document.getElementById('cust-edit');
    if(v&&ed){{ var show=ed.hidden; ed.hidden=!show; v.hidden=show; }}
  }};
  window.submitEdit=function(){{
    var body={{business_name:(document.getElementById('ed-business')||{{}}).value||'',
              contact_name:(document.getElementById('ed-contact')||{{}}).value||'',
              phone:(document.getElementById('ed-phone')||{{}}).value||''}};
    fetch('/api/customers/'+CID, {{method:'PATCH',
        headers:{{'Content-Type':'application/json','X-CSRF-Token':CSRF}},
        body:JSON.stringify(body)}})
      .then(function(r){{ return r.json().then(function(j){{ return {{ok:r.ok,j:j}}; }}); }})
      .then(function(res){{ if(res.ok){{ window.location.reload(); }}
        else {{ var e=document.getElementById('edit-err'); if(e){{ e.textContent=(res.j&&res.j.error)||'Could not save.'; e.hidden=false; }} }} }})
      .catch(function(){{ var e=document.getElementById('edit-err'); if(e){{ e.textContent='Network error.'; e.hidden=false; }} }});
  }};
  window.copyLink=function(){{
    var url=(document.getElementById('portal-url-box')||{{}}).textContent||'';
    if(navigator.clipboard&&navigator.clipboard.writeText){{
      navigator.clipboard.writeText(url).then(function(){{ msg('Link copied.'); }},
        function(){{ msg('Copy failed — select and copy manually.'); }});
    }} else {{ msg('Copy not supported — select the link manually.'); }}
  }};
  window.regen=function(){{
    if(!confirm('Regenerate the portal link? The current link will stop working immediately.')) return;
    fetch('/api/customers/'+CID+'/regenerate-token', {{method:'POST',
        headers:{{'Content-Type':'application/json','X-CSRF-Token':CSRF}}}})
      .then(function(r){{ return r.json().then(function(j){{ return {{ok:r.ok,j:j}}; }}); }})
      .then(function(res){{ if(res.ok&&res.j.portal_url){{
          var box=document.getElementById('portal-url-box'); if(box) box.textContent=res.j.portal_url;
          msg('New link generated — the old one no longer works.');
        }} else {{ msg((res.j&&res.j.error)||'Could not regenerate.'); }} }})
      .catch(function(){{ msg('Network error — try again.'); }});
  }};
  window.deactivate=function(){{
    if(!confirm('Deactivate this customer? They disappear from your lists and their portal link stops working. History is kept.')) return;
    fetch('/api/customers/'+CID+'/deactivate', {{method:'POST',
        headers:{{'Content-Type':'application/json','X-CSRF-Token':CSRF}}}})
      .then(function(r){{ return r.json().then(function(j){{ return {{ok:r.ok,j:j}}; }}); }})
      .then(function(res){{ if(res.ok){{ window.location='{list_url}'; }}
        else {{ msg((res.j&&res.j.error)||'Could not deactivate.'); }} }})
      .catch(function(){{ msg('Network error — try again.'); }});
  }};
}})();
</script>
"""


# =========================================================
# Phase 6 — DVIR: Trucks, Inspections, Defects/Maintenance, History
# Access model (mirrors Phase 5): any management role may VIEW; only
# owner/dispatcher may ACTION (add/edit trucks, resolve defects, clear OOS).
# Drivers run inspections and see only their own. All checks are server-side.
# =========================================================

def _is_management():
    """Any boss/management role (owner, customer_manager, dispatcher)."""
    return bool(session_roles().intersection(("owner", "customer_manager", "dispatcher"))) \
        or session.get("is_superadmin")


def _can_action_fleet():
    """Owner/dispatcher may mutate trucks, resolve defects, clear OOS. Owner
    expands to include dispatcher, so this one check covers both."""
    return has_role("dispatcher")


def _truck_oos_badge(row):
    """Red OUT OF SERVICE pill shown anywhere a flagged truck appears."""
    d = dict(row) if row is not None else {}
    if not d.get("out_of_service"):
        return ""
    return ('<span style="display:inline-block;padding:2px 9px;border-radius:999px;'
            'font-size:10px;font-weight:800;letter-spacing:.5px;text-transform:uppercase;'
            'background:rgba(255,82,82,0.16);color:#FF7A7A;border:1px solid rgba(255,82,82,0.45);'
            'margin-left:6px;">⛔ Out of service</span>')


def _load_truck_scoped(conn, truck_id, active_only=False):
    """A truck in the session's company (any status), or None."""
    q = "SELECT * FROM trucks WHERE id=? AND company_id=?"
    if active_only:
        q += " AND is_active=1"
    return conn.execute(q, (truck_id, cid())).fetchone()


def _open_defect_count(conn):
    return conn.execute(
        """SELECT COUNT(*) AS n
             FROM inspection_items ii
             JOIN inspections i ON ii.inspection_id = i.id
            WHERE i.company_id = ? AND ii.result='defect' AND ii.defect_status='open'""",
        (cid(),),
    ).fetchone()["n"]


# ── Phase 7A maintenance-log helpers ──────────────────────────────────────
def _save_maintenance_receipts(conn, files, defect_item_id=None, manual_entry_id=None):
    """Persist any uploaded receipt photos (reuses the stop-photo pipeline:
    filesystem + web-relative path row). Returns count saved. Skips silently on
    a disk error so a receipt hiccup never rolls back the maintenance write."""
    saved = 0
    for f in files or []:
        if not f or not f.filename or not allowed_file(f.filename):
            continue
        try:
            fname = f"mnt_{secrets.token_hex(8)}_{secure_filename(f.filename)}"
            f.save(os.path.join(app.config["UPLOAD_FOLDER"], fname))
            conn.execute(
                """INSERT INTO maintenance_photos (company_id, defect_item_id,
                       manual_entry_id, file_path, uploaded_at, uploaded_by)
                   VALUES (?,?,?,?,?,?)""",
                (cid(), defect_item_id, manual_entry_id,
                 os.path.join("static", "uploads", fname), now_ts(), session.get("user_id")),
            )
            saved += 1
        except OSError as exc:
            app.logger.warning("maintenance receipt save failed: %s", exc)
    return saved


def _maintenance_receipts(conn, defect_item_id=None, manual_entry_id=None):
    """Rows of receipt photos for one record (company-scoped)."""
    if defect_item_id is not None:
        return conn.execute(
            "SELECT * FROM maintenance_photos WHERE company_id=? AND defect_item_id=? ORDER BY id",
            (cid(), defect_item_id)).fetchall()
    return conn.execute(
        "SELECT * FROM maintenance_photos WHERE company_id=? AND manual_entry_id=? ORDER BY id",
        (cid(), manual_entry_id)).fetchall()


def _receipt_thumbs_html(rows):
    """Small thumbnail gallery for receipt photos (management views only)."""
    if not rows:
        return ""
    imgs = "".join(
        f'<a href="{url_for("serve_maintenance_photo", photo_id=r["id"])}" target="_blank">'
        f'<img src="{url_for("serve_maintenance_photo", photo_id=r["id"])}" loading="lazy" '
        f'style="width:54px;height:54px;object-fit:cover;border-radius:8px;border:1px solid var(--border);"></a>'
        for r in rows
    )
    return f'<div style="display:flex;gap:6px;flex-wrap:wrap;margin-top:8px;">{imgs}</div>'


def _truck_maintenance_log(conn, truck_id, date_from=None, date_to=None, category=None):
    """Merged chronological maintenance log for one truck: repaired inspection
    defects + manual entries. Returns a list of uniform dicts (newest first).
    cost_cents is None when not recorded. Voided manual entries are included but
    flagged (and excluded from spend totals by the caller)."""
    # Repaired defects — dated by resolved_at.
    defects = conn.execute(
        """SELECT ii.id AS ref_id, ii.label, ii.resolution_note, ii.cost_cents,
                  ii.vendor_id, ii.resolved_at, i.truck_id, i.id AS inspection_id
             FROM inspection_items ii
             JOIN inspections i ON ii.inspection_id = i.id
            WHERE i.company_id=? AND i.truck_id=? AND ii.result='defect'
              AND ii.defect_status='repaired'""",
        (cid(), truck_id),
    ).fetchall()
    manuals = conn.execute(
        "SELECT * FROM maintenance_entries WHERE company_id=? AND truck_id=?",
        (cid(), truck_id),
    ).fetchall()
    vmap = _vendor_map(conn)

    rows = []
    for d in defects:
        rows.append({
            "source": "defect", "ref_id": d["ref_id"], "inspection_id": d["inspection_id"],
            "date": (d["resolved_at"] or "")[:10],
            "sort_key": d["resolved_at"] or "",
            "category": "Repair",
            "description": d["label"] + (f" — {d['resolution_note']}" if d["resolution_note"] else ""),
            "cost_cents": d["cost_cents"], "vendor": vmap.get(d["vendor_id"]),
            "at_vendor": 0, "voided": 0,
        })
    for m in manuals:
        md = dict(m)
        rows.append({
            "source": "manual", "ref_id": m["id"],
            "date": m["entry_date"] or "",
            "sort_key": (m["entry_date"] or "") + " " + (m["created_at"] or ""),
            "category": m["category"],
            "description": m["description"],
            "cost_cents": m["cost_cents"], "vendor": vmap.get(md.get("vendor_id")),
            "at_vendor": md.get("at_vendor") or 0, "voided": m["voided"],
        })

    def _keep(r):
        if date_from and r["date"] and r["date"] < date_from:
            return False
        if date_to and r["date"] and r["date"] > date_to:
            return False
        if category and r["category"] != category:
            return False
        return True

    rows = [r for r in rows if _keep(r)]
    rows.sort(key=lambda r: r["sort_key"], reverse=True)
    return rows


def _truck_spend(conn, truck_id):
    """(month, year, lifetime) spend in cents for a truck across repaired
    defects + non-voided manual entries. Voided entries never count."""
    today = today_str()
    month_prefix = today[:7]   # YYYY-MM
    year_prefix = today[:4]    # YYYY
    d_rows = conn.execute(
        """SELECT ii.cost_cents AS c, substr(ii.resolved_at,1,10) AS dt
             FROM inspection_items ii JOIN inspections i ON ii.inspection_id=i.id
            WHERE i.company_id=? AND i.truck_id=? AND ii.result='defect'
              AND ii.defect_status='repaired' AND ii.cost_cents IS NOT NULL""",
        (cid(), truck_id)).fetchall()
    m_rows = conn.execute(
        """SELECT cost_cents AS c, entry_date AS dt FROM maintenance_entries
            WHERE company_id=? AND truck_id=? AND voided=0 AND cost_cents IS NOT NULL""",
        (cid(), truck_id)).fetchall()
    month = year = life = 0
    for r in list(d_rows) + list(m_rows):
        c = r["c"] or 0
        dt = r["dt"] or ""
        life += c
        if dt[:4] == year_prefix:
            year += c
        if dt[:7] == month_prefix:
            month += c
    return month, year, life


# ── Phase 7A revision: vendors + "at vendor" state ────────────────────────
def _company_vendors(conn):
    return conn.execute(
        "SELECT id, name, phone, notes FROM vendors WHERE company_id=? AND is_active=1 ORDER BY LOWER(name), id",
        (cid(),)).fetchall()


def _vendor_map(conn):
    return {v["id"]: v["name"] for v in conn.execute(
        "SELECT id, name FROM vendors WHERE company_id=?", (cid(),)).fetchall()}


def _vendor_options_html(vendors, selected_id=None):
    """<option>s for a vendor picker; leading blank == in-house / none."""
    opts = ['<option value="">In-house / none</option>']
    for v in vendors:
        sel = " selected" if selected_id is not None and v["id"] == selected_id else ""
        opts.append(f'<option value="{v["id"]}"{sel}>{e(v["name"])}</option>')
    return "".join(opts)


def _clean_vendor_id(conn, raw):
    """Validate an incoming vendor_id against the company's active vendors.
    '' / None → None (in-house). Bad id → None (treated as in-house, never a
    cross-company leak). Returns int|None."""
    s = str(raw or "").strip()
    if not s.isdigit():
        return None
    row = conn.execute("SELECT id FROM vendors WHERE id=? AND company_id=?",
                       (int(s), cid())).fetchone()
    return int(s) if row else None


def _recompute_truck_at_vendor(conn, truck_id):
    """Set trucks.at_vendor = 1 iff any open defect or active manual entry for
    the truck is currently 'sent to vendor'. Called after every send/repair
    transition so the informational flag is always accurate."""
    d = conn.execute(
        """SELECT 1 FROM inspection_items ii JOIN inspections i ON ii.inspection_id=i.id
            WHERE i.company_id=? AND i.truck_id=? AND ii.result='defect'
              AND ii.defect_status='open' AND ii.at_vendor=1 LIMIT 1""",
        (cid(), truck_id)).fetchone()
    m = conn.execute(
        """SELECT 1 FROM maintenance_entries
            WHERE company_id=? AND truck_id=? AND voided=0 AND at_vendor=1
              AND completed_at IS NULL LIMIT 1""",
        (cid(), truck_id)).fetchone()
    conn.execute("UPDATE trucks SET at_vendor=? WHERE id=?",
                 (1 if (d or m) else 0, truck_id))


def _truck_at_vendor_badge(row):
    """Yellow, informational (non-blocking) 'At vendor' pill — mirrors the OOS
    badge shape. Shown wherever a truck currently out at a shop appears."""
    d = dict(row) if row is not None else {}
    if not d.get("at_vendor") or d.get("out_of_service"):
        return ""  # OOS takes visual precedence
    return ('<span style="display:inline-block;padding:2px 9px;border-radius:999px;'
            'font-size:10px;font-weight:800;letter-spacing:.5px;text-transform:uppercase;'
            'background:rgba(245,180,60,0.16);color:#F5B43C;border:1px solid rgba(245,180,60,0.45);'
            'margin-left:6px;">🔧 At vendor</span>')


def _truck_status_badges(row):
    """OOS (blocking) + At-vendor (informational) badges, in priority order."""
    return _truck_oos_badge(row) + _truck_at_vendor_badge(row)


def _company_has_costs(conn):
    """True if ANY maintenance record (repaired defect or non-voided manual
    entry) in the company carries a cost — decides spend-table vs event-count."""
    d = conn.execute(
        """SELECT 1 FROM inspection_items ii JOIN inspections i ON ii.inspection_id=i.id
            WHERE i.company_id=? AND ii.cost_cents IS NOT NULL LIMIT 1""", (cid(),)).fetchone()
    if d:
        return True
    m = conn.execute(
        "SELECT 1 FROM maintenance_entries WHERE company_id=? AND voided=0 AND cost_cents IS NOT NULL LIMIT 1",
        (cid(),)).fetchone()
    return bool(m)


def _truck_event_counts(conn, truck_id):
    """(month, year, lifetime) COUNT of maintenance events for a truck — the
    fallback metric when no costs are tracked. Repaired defects + non-voided
    manual entries."""
    today = today_str()
    mp, yp = today[:7], today[:4]
    d_rows = conn.execute(
        """SELECT substr(ii.resolved_at,1,10) AS dt FROM inspection_items ii
             JOIN inspections i ON ii.inspection_id=i.id
            WHERE i.company_id=? AND i.truck_id=? AND ii.result='defect' AND ii.defect_status='repaired'""",
        (cid(), truck_id)).fetchall()
    m_rows = conn.execute(
        "SELECT entry_date AS dt FROM maintenance_entries WHERE company_id=? AND truck_id=? AND voided=0",
        (cid(), truck_id)).fetchall()
    month = year = life = 0
    for r in list(d_rows) + list(m_rows):
        dt = r["dt"] or ""
        life += 1
        if dt[:4] == yp: year += 1
        if dt[:7] == mp: month += 1
    return month, year, life


@app.route("/trucks")
@roles_required("owner", "customer_manager", "dispatcher")
def trucks_page():
    """Fleet list. Any management role views; owner/dispatcher can add/edit."""
    conn = get_db()
    rows = conn.execute(
        """SELECT t.*,
                  (SELECT COUNT(*) FROM inspection_items ii
                     JOIN inspections i ON ii.inspection_id=i.id
                    WHERE i.truck_id=t.id AND ii.result='defect'
                      AND ii.defect_status='open') AS open_defects
             FROM trucks t
            WHERE t.company_id=? AND t.is_active=1
            ORDER BY t.out_of_service DESC, LOWER(t.name), t.id""",
        (cid(),),
    ).fetchall()
    conn.close()
    can_action = _can_action_fleet()

    cards = ""
    for t in rows:
        name = e(t["name"])
        sub_bits = " · ".join(b for b in [e(t["make_model"] or ""), e(t["plate"] or "")] if b)
        sub = f'<div style="color:var(--slate);font-size:13px;margin-top:2px;">{sub_bits}</div>' if sub_bits else ""
        defect_badge = (
            f'<span style="display:inline-block;padding:2px 9px;border-radius:999px;font-size:11px;'
            f'font-weight:800;background:rgba(255,82,82,0.16);color:#FF7A7A;'
            f'border:1px solid rgba(255,82,82,0.45);">{t["open_defects"]} open</span>'
        ) if t["open_defects"] else ""
        cards += f"""
        <a class="bin-card" href="{url_for('truck_detail_page', truck_id=t['id'])}"
           style="padding:16px;display:block;text-decoration:none;color:inherit;">
            <div style="display:flex;justify-content:space-between;align-items:center;gap:10px;">
                <div style="font-weight:700;font-size:15px;">🚛 {name}{_truck_status_badges(t)}</div>
                {defect_badge}
            </div>
            {sub}
        </a>
        """

    add_form = ""
    if can_action:
        add_form = f"""
        <div style="max-width:640px;margin-bottom:16px;">
            <button class="btn green" onclick="toggleAddTruck()">+ Add Truck</button>
            <div id="add-truck-form" hidden class="bin-card" style="padding:16px;margin-top:12px;">
                <div id="add-truck-err" hidden style="color:#FF5252;font-size:12px;margin-bottom:8px;"></div>
                <label class="uw-lbl">Name / number</label>
                <input id="tk-name" style="width:100%;margin-bottom:10px;" placeholder="Truck 3">
                <label class="uw-lbl">Make &amp; model (optional)</label>
                <input id="tk-make" style="width:100%;margin-bottom:10px;" placeholder="2019 Peterbilt 348">
                <label class="uw-lbl">Plate (optional)</label>
                <input id="tk-plate" style="width:100%;margin-bottom:12px;" placeholder="VA ABC-1234">
                <div style="display:flex;gap:8px;">
                    <button class="btn green" style="flex:1;" onclick="submitAddTruck()">Create truck</button>
                    <button class="btn secondary" onclick="toggleAddTruck()">Cancel</button>
                </div>
            </div>
        </div>"""

    empty_hidden = "" if not rows else " hidden"
    body = f"""
    <div class="hero">
        <h1>Trucks</h1>
        <p>Your fleet. Drivers run pre/post-trip inspections against these vehicles.</p>
    </div>
    {add_form}
    <div id="truck-empty" class="empty-state" style="padding:32px 0;"{empty_hidden}>No trucks yet{'' if can_action else ' — an owner or dispatcher can add them'}.</div>
    <div class="bin-list" style="display:grid;gap:12px;max-width:640px;">
        {cards}
    </div>
    <style>.uw-lbl{{display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;}}</style>
    {_TRUCKS_PAGE_JS}
    """
    return render_template_string(shell_page("Trucks", body))


_TRUCKS_PAGE_JS = """
<script>
(function(){
  var CSRF = (document.querySelector('meta[name=csrf-token]')||{}).content || '';
  window.toggleAddTruck=function(){ var f=document.getElementById('add-truck-form'); if(f) f.hidden=!f.hidden; };
  function err(m){ var e=document.getElementById('add-truck-err'); if(e){ e.textContent=m; e.hidden=false; } }
  window.submitAddTruck=function(){
    var body={ name:(document.getElementById('tk-name')||{}).value||'',
               make_model:(document.getElementById('tk-make')||{}).value||'',
               plate:(document.getElementById('tk-plate')||{}).value||'' };
    if(!body.name.trim()){ err('Enter a name or number.'); return; }
    fetch('/api/trucks', {method:'POST',
        headers:{'Content-Type':'application/json','X-CSRF-Token':CSRF}, body:JSON.stringify(body)})
      .then(function(r){ return r.json().then(function(j){ return {ok:r.ok,j:j}; }); })
      .then(function(res){ if(res.ok && res.j.id){ window.location='/trucks/'+res.j.id; }
                           else { err((res.j&&res.j.error)||'Could not create truck.'); } })
      .catch(function(){ err('Network error — try again.'); });
  };
})();
</script>
"""


@app.route("/api/trucks", methods=["POST"])
@login_required
def create_truck():
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    data = request.get_json(silent=True) or {}
    name = str(data.get("name") or "").strip()[:80]
    make_model = str(data.get("make_model") or "").strip()[:120] or None
    plate = str(data.get("plate") or "").strip()[:40] or None
    if not name:
        return jsonify({"error": "a name or number is required"}), 400
    conn = get_db()
    cur = conn.cursor()
    cur.execute(
        """INSERT INTO trucks (company_id, name, make_model, plate, is_active, created_at)
           VALUES (?, ?, ?, ?, 1, ?)""",
        (cid(), name, make_model, plate, now_ts()),
    )
    truck_id = cur.lastrowid
    conn.commit()
    conn.close()
    return jsonify({"success": True, "id": truck_id})


@app.route("/api/trucks/<int:truck_id>", methods=["PATCH"])
@login_required
def update_truck(truck_id):
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    data = request.get_json(silent=True) or {}
    conn = get_db()
    truck = _load_truck_scoped(conn, truck_id, active_only=True)
    if truck is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    name = str(data.get("name") or "").strip()[:80]
    if not name:
        conn.close()
        return jsonify({"error": "a name or number is required"}), 400
    conn.execute(
        "UPDATE trucks SET name=?, make_model=?, plate=? WHERE id=?",
        (name, str(data.get("make_model") or "").strip()[:120] or None,
         str(data.get("plate") or "").strip()[:40] or None, truck_id),
    )
    conn.commit()
    conn.close()
    return jsonify({"success": True})


@app.route("/api/trucks/<int:truck_id>/deactivate", methods=["POST"])
@login_required
def deactivate_truck(truck_id):
    """Soft delete: hide from pickers/lists, keep inspection history."""
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    conn = get_db()
    truck = _load_truck_scoped(conn, truck_id, active_only=True)
    if truck is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    conn.execute("UPDATE trucks SET is_active=0 WHERE id=?", (truck_id,))
    conn.commit()
    conn.close()
    return jsonify({"success": True})


@app.route("/api/trucks/<int:truck_id>/clear-oos", methods=["POST"])
@login_required
def clear_truck_oos(truck_id):
    """Owner/dispatcher clears an OUT OF SERVICE flag, with a required note."""
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    data = request.get_json(silent=True) or {}
    note = str(data.get("note") or "").strip()[:500]
    if not note:
        return jsonify({"error": "a note is required to clear out-of-service"}), 400
    conn = get_db()
    truck = _load_truck_scoped(conn, truck_id)
    if truck is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    if not truck["out_of_service"]:
        conn.close()
        return jsonify({"error": "truck is not out of service"}), 409
    conn.execute(
        """UPDATE trucks SET out_of_service=0, oos_cleared_note=?, oos_cleared_at=?,
                            oos_cleared_by=? WHERE id=?""",
        (note, now_ts(), session["user_id"], truck_id),
    )
    conn.commit()
    conn.close()
    return jsonify({"success": True})


@app.route("/trucks/<int:truck_id>")
@roles_required("owner", "customer_manager", "dispatcher")
def truck_detail_page(truck_id):
    """Truck info + OOS status + inspection history (date-range filter). The
    'DOT auditor is here' screen for one truck."""
    conn = get_db()
    truck = _load_truck_scoped(conn, truck_id, active_only=True)
    if truck is None:
        conn.close()
        flash("Truck not found.", "error")
        return redirect(url_for("trucks_page"))

    date_from = (request.args.get("from") or "").strip()
    date_to   = (request.args.get("to") or "").strip()
    where = ["i.company_id=?", "i.truck_id=?"]
    params = [cid(), truck_id]
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", date_from):
        where.append("substr(i.created_at,1,10) >= ?")
        params.append(date_from)
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", date_to):
        where.append("substr(i.created_at,1,10) <= ?")
        params.append(date_to)
    insps = conn.execute(
        f"""SELECT i.*,
                   COALESCE(u.username,'—') AS driver_name,
                   (SELECT COUNT(*) FROM inspection_items ii
                     WHERE ii.inspection_id=i.id AND ii.result='defect') AS defect_count
              FROM inspections i
         LEFT JOIN users u ON i.driver_id=u.id
             WHERE {' AND '.join(where)}
             ORDER BY i.created_at DESC, i.id DESC""",
        params,
    ).fetchall()

    # Phase 7A — spend totals + merged maintenance log (same from/to filter,
    # plus a category filter).
    cat_filter = (request.args.get("cat") or "").strip()
    if cat_filter not in MAINTENANCE_CATEGORIES:
        cat_filter = ""
    _df = date_from if re.fullmatch(r"\d{4}-\d{2}-\d{2}", date_from) else None
    _dt = date_to if re.fullmatch(r"\d{4}-\d{2}-\d{2}", date_to) else None
    mlog = _truck_maintenance_log(conn, truck_id, date_from=_df, date_to=_dt, category=(cat_filter or None))
    # receipt thumbs per log row
    mlog_thumbs = {}
    for r in mlog:
        rc = (_maintenance_receipts(conn, defect_item_id=r["ref_id"]) if r["source"] == "defect"
              else _maintenance_receipts(conn, manual_entry_id=r["ref_id"]))
        mlog_thumbs[(r["source"], r["ref_id"])] = rc
    truck_has_costs = _company_has_costs(conn)
    if truck_has_costs:
        spend_month, spend_year, spend_life = _truck_spend(conn, truck_id)
    else:
        spend_month, spend_year, spend_life = _truck_event_counts(conn, truck_id)
    vendors = _company_vendors(conn)
    vmap = _vendor_map(conn)
    vendor_opts = _vendor_options_html(vendors)
    conn.close()
    can_action = _can_action_fleet()

    _OVR_COLOR = {"safe": "#3DDC84", "defects_safe": "#FF8A3D", "out_of_service": "#FF7A7A"}
    rows_html = ""
    for i in insps:
        color = _OVR_COLOR.get(i["overall"], "var(--slate)")
        rows_html += f"""
        <a class="bin-card" href="{url_for('inspection_report', inspection_id=i['id'])}"
           style="padding:14px;display:block;text-decoration:none;color:inherit;">
            <div style="display:flex;justify-content:space-between;gap:10px;">
                <span style="font-weight:700;font-size:14px;">{e((i["created_at"] or "")[:16])}</span>
                <span style="color:{color};font-weight:800;font-size:12px;">{e(_INSPECTION_OVERALL_LABEL.get(i["overall"], i["overall"]))}</span>
            </div>
            <div style="color:var(--slate);font-size:13px;margin-top:4px;">
                {e(_INSPECTION_TYPE_LABEL.get(i["type"], i["type"]))} · {e(i["driver_name"])}
                {(' · ' + str(i["defect_count"]) + ' defect' + ('' if i["defect_count"]==1 else 's')) if i["defect_count"] else ''}
            </div>
        </a>"""
    if not insps:
        rows_html = '<div class="empty-state" style="padding:24px 0;">No inspections in this range.</div>'

    oos_html = ""
    if truck["out_of_service"]:
        clear_btn = ('<button class="btn secondary" style="margin-top:10px;" onclick="clearOOS()">Clear out-of-service</button>'
                     if can_action else "")
        oos_html = f"""
        <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;border:1px solid rgba(255,82,82,0.45);">
            <div style="color:#FF7A7A;font-weight:800;">⛔ OUT OF SERVICE</div>
            <div style="font-size:13px;color:#C9C9C2;margin-top:6px;">{e(truck["oos_note"] or "Flagged unsafe by an inspection.")}</div>
            <div style="font-size:12px;color:var(--slate);margin-top:4px;">Flagged {e(truck["oos_at"] or "")}</div>
            <div id="oos-msg" hidden style="font-size:12px;margin-top:8px;color:var(--slate);"></div>
            {clear_btn}
        </div>"""

    edit_block = ""
    if can_action:
        edit_block = f"""
        <div id="truck-edit" hidden class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
            <div id="edit-truck-err" hidden style="color:#FF5252;font-size:12px;margin-bottom:8px;"></div>
            <label class="uw-lbl">Name / number</label>
            <input id="te-name" style="width:100%;margin-bottom:10px;" value="{e(truck["name"])}">
            <label class="uw-lbl">Make &amp; model</label>
            <input id="te-make" style="width:100%;margin-bottom:10px;" value="{e(truck["make_model"] or "")}">
            <label class="uw-lbl">Plate</label>
            <input id="te-plate" style="width:100%;margin-bottom:12px;" value="{e(truck["plate"] or "")}">
            <div style="display:flex;gap:8px;">
                <button class="btn green" style="flex:1;" onclick="submitEditTruck()">Save</button>
                <button class="btn secondary" onclick="toggleEditTruck()">Cancel</button>
            </div>
        </div>
        <div style="max-width:640px;margin-bottom:16px;">
            <button class="btn red" onclick="deactivateTruck()" style="width:100%;">Deactivate truck</button>
            <div style="color:var(--slate);font-size:12px;margin-top:6px;text-align:center;">
                Hides it from inspection pickers. Inspection history is kept.
            </div>
        </div>"""

    edit_toggle = ('<button class="btn secondary" onclick="toggleEditTruck()" style="padding:4px 12px;font-size:12px;">Edit</button>'
                   if can_action else "")
    sub_bits = " · ".join(b for b in [e(truck["make_model"] or ""), e(truck["plate"] or "")] if b) or "—"

    # ── Phase 7A: totals card — spend when costs exist, else event counts ──
    _tfmt = (lambda v: format_cents(v)) if truck_has_costs else (lambda v: str(v))
    _tlabel = "Maintenance spend" if truck_has_costs else "Maintenance events"
    totals_card = f"""
    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
        <h2 style="font-size:15px;margin:0 0 10px;">{_tlabel}</h2>
        <div style="display:flex;gap:10px;text-align:center;">
            <div style="flex:1;"><div style="color:var(--slate);font-size:11px;text-transform:uppercase;letter-spacing:.5px;">This month</div><div style="font-weight:800;font-size:18px;margin-top:2px;">{e(_tfmt(spend_month))}</div></div>
            <div style="flex:1;"><div style="color:var(--slate);font-size:11px;text-transform:uppercase;letter-spacing:.5px;">This year</div><div style="font-weight:800;font-size:18px;margin-top:2px;">{e(_tfmt(spend_year))}</div></div>
            <div style="flex:1;"><div style="color:var(--slate);font-size:11px;text-transform:uppercase;letter-spacing:.5px;">Lifetime</div><div style="font-weight:800;font-size:18px;margin-top:2px;">{e(_tfmt(spend_life))}</div></div>
        </div>
    </div>"""

    # ── Phase 7A: add manual maintenance (owner/dispatcher) ──
    add_maint = ""
    if can_action:
        cat_opts = "".join(f'<option value="{e(c)}">{e(c)}</option>' for c in MAINTENANCE_CATEGORIES)
        add_maint = f"""
        <div style="max-width:640px;margin-bottom:12px;">
            <button class="btn green" onclick="toggleAddMaint()">+ Log maintenance</button>
            <div id="add-maint-form" hidden class="bin-card" style="padding:16px;margin-top:12px;">
                <div id="add-maint-err" hidden style="color:#FF5252;font-size:12px;margin-bottom:8px;"></div>
                <div style="display:flex;gap:8px;">
                    <div style="flex:1;"><label class="uw-lbl">Date</label><input id="tm-date" type="date" value="{today_str()}" style="width:100%;"></div>
                    <div style="flex:1;"><label class="uw-lbl">Category</label><select id="tm-cat" style="width:100%;">{cat_opts}</select></div>
                </div>
                <label class="uw-lbl" style="margin-top:10px;">Description</label>
                <textarea id="tm-desc" rows="2" style="width:100%;margin-bottom:8px;" placeholder="e.g. Oil change + filter"></textarea>
                <label class="uw-lbl">Vendor</label>
                <select id="tm-vendor" style="width:100%;margin-bottom:8px;">{vendor_opts}</select>
                <label style="display:flex;align-items:center;gap:8px;font-size:13px;color:var(--slate);margin-bottom:8px;">
                    <input id="tm-sent" type="checkbox"> Truck is currently at this vendor
                </label>
                <details style="margin-bottom:10px;">
                    <summary style="color:var(--slate);font-size:12px;cursor:pointer;">Add cost / receipt (optional)</summary>
                    <div style="margin-top:8px;">
                        <label class="uw-lbl">Cost</label><input id="tm-cost" inputmode="decimal" placeholder="89.00" style="width:100%;margin-bottom:8px;">
                        <label class="uw-lbl">Receipt photo(s)</label>
                        <input id="tm-receipts" type="file" accept=".png,.jpg,.jpeg,.webp,.pdf" multiple capture="environment" style="width:100%;">
                    </div>
                </details>
                <div style="display:flex;gap:8px;">
                    <button class="btn green" style="flex:1;" onclick="submitMaint({truck_id})">Save</button>
                    <button class="btn secondary" onclick="toggleAddMaint()">Cancel</button>
                </div>
            </div>
        </div>"""

    # ── Phase 7A: merged maintenance log ──
    _SRC_BADGE = {
        "defect": ('<span style="display:inline-block;padding:2px 8px;border-radius:999px;font-size:10px;'
                   'font-weight:800;background:var(--cyan-dim);color:var(--cyan);border:1px solid var(--border-glow);">From inspection</span>'),
        "manual": ('<span style="display:inline-block;padding:2px 8px;border-radius:999px;font-size:10px;'
                   'font-weight:800;background:rgba(140,160,179,0.16);color:#ADC0D1;border:1px solid rgba(140,160,179,0.4);">Manual</span>'),
    }
    mlog_rows = ""
    for r in mlog:
        thumbs = _receipt_thumbs_html(mlog_thumbs.get((r["source"], r["ref_id"])))
        cost_html = (f'<span style="font-weight:800;font-size:14px;">{e(format_cents(r["cost_cents"]))}</span>'
                     if r["cost_cents"] is not None else "")
        vendor = f' · {e(r["vendor"])}' if r["vendor"] else ""
        voided_tag = (' <span style="color:#FF7A7A;font-weight:800;font-size:11px;">VOID</span>'
                      if r["voided"] else "")
        at_vendor_tag = (' <span style="color:#F5B43C;font-weight:800;font-size:11px;">🔧 AT VENDOR</span>'
                         if r.get("at_vendor") and not r["voided"] else "")
        href = (url_for("inspection_report", inspection_id=r["inspection_id"]) if r["source"] == "defect"
                else url_for("maintenance_entry_detail", entry_id=r["ref_id"]))
        desc_style = "text-decoration:line-through;opacity:.6;" if r["voided"] else ""
        mlog_rows += f"""
        <a class="bin-card" href="{href}" style="padding:14px;display:block;text-decoration:none;color:inherit;">
            <div style="display:flex;justify-content:space-between;gap:10px;align-items:center;">
                <span style="font-weight:700;font-size:14px;{desc_style}">{e(r["date"])} · {e(r["category"])}{voided_tag}{at_vendor_tag}</span>
                {cost_html}
            </div>
            <div style="color:#C9C9C2;font-size:13px;margin-top:4px;{desc_style}">{e(r["description"])}{vendor}</div>
            <div style="margin-top:6px;">{_SRC_BADGE.get(r["source"], "")}</div>
            {thumbs}
        </a>"""
    if not mlog:
        mlog_rows = '<div class="empty-state" style="padding:24px 0;">No maintenance in this range.</div>'

    cat_filter_opts = '<option value="">All categories</option>' + "".join(
        f'<option value="{e(c)}"{" selected" if c==cat_filter else ""}>{e(c)}</option>' for c in MAINTENANCE_CATEGORIES)
    maint_section = f"""
    {totals_card}
    {add_maint}
    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:8px;">
        <h2 style="font-size:15px;margin:0 0 10px;">Maintenance log</h2>
        <form method="GET" style="display:flex;gap:8px;flex-wrap:wrap;align-items:end;margin-bottom:6px;">
            <div><label class="uw-lbl">From</label><input type="date" name="from" value="{e(date_from)}"></div>
            <div><label class="uw-lbl">To</label><input type="date" name="to" value="{e(date_to)}"></div>
            <div><label class="uw-lbl">Category</label><select name="cat">{cat_filter_opts}</select></div>
            <button class="btn secondary" type="submit" style="padding:8px 14px;">Filter</button>
            <a class="btn secondary" href="{url_for('truck_detail_page', truck_id=truck_id)}" style="padding:8px 14px;">Reset</a>
        </form>
    </div>
    <div class="bin-list" style="display:grid;gap:10px;max-width:640px;margin-bottom:16px;">
        {mlog_rows}
    </div>"""

    body = f"""
    <div class="hero" style="display:flex;justify-content:space-between;align-items:flex-start;gap:12px;">
        <div>
            <h1 style="margin-bottom:4px;">🚛 {e(truck["name"])}{_truck_status_badges(truck)}</h1>
            <p style="margin:0;">{sub_bits}</p>
        </div>
        <a class="btn secondary" href="{url_for('trucks_page')}" style="white-space:nowrap;">← All trucks</a>
    </div>
    {oos_html}
    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
        <div style="display:flex;justify-content:space-between;align-items:center;">
            <h2 style="font-size:15px;margin:0;">Truck info</h2>
            {edit_toggle}
        </div>
        <div id="truck-view" style="margin-top:10px;color:var(--slate);font-size:14px;">{sub_bits}</div>
    </div>
    {edit_block}
    {maint_section}
    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:8px;">
        <h2 style="font-size:15px;margin:0 0 10px;">Inspection history</h2>
        <form method="GET" style="display:flex;gap:8px;flex-wrap:wrap;align-items:end;margin-bottom:6px;">
            <div><label class="uw-lbl">From</label><input type="date" name="from" value="{e(date_from)}"></div>
            <div><label class="uw-lbl">To</label><input type="date" name="to" value="{e(date_to)}"></div>
            <button class="btn secondary" type="submit" style="padding:8px 14px;">Filter</button>
            <a class="btn secondary" href="{url_for('truck_detail_page', truck_id=truck_id)}" style="padding:8px 14px;">Reset</a>
        </form>
    </div>
    <div class="bin-list" style="display:grid;gap:10px;max-width:640px;">
        {rows_html}
    </div>
    <style>.uw-lbl{{display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;}}</style>
    {_truck_detail_js(truck_id)}
    """
    return render_template_string(shell_page("Truck", body))


def _truck_detail_js(truck_id):
    list_url = url_for("trucks_page")
    return f"""
<script>
(function(){{
  var CSRF=(document.querySelector('meta[name=csrf-token]')||{{}}).content||'';
  var TID={truck_id};
  function msg(t){{ var m=document.getElementById('oos-msg'); if(m){{ m.textContent=t; m.hidden=false; }} }}
  window.toggleEditTruck=function(){{ var v=document.getElementById('truck-view'),ed=document.getElementById('truck-edit');
    if(ed){{ ed.hidden=!ed.hidden; }} }};
  window.submitEditTruck=function(){{
    var body={{name:(document.getElementById('te-name')||{{}}).value||'',
              make_model:(document.getElementById('te-make')||{{}}).value||'',
              plate:(document.getElementById('te-plate')||{{}}).value||''}};
    fetch('/api/trucks/'+TID,{{method:'PATCH',headers:{{'Content-Type':'application/json','X-CSRF-Token':CSRF}},body:JSON.stringify(body)}})
      .then(function(r){{return r.json().then(function(j){{return {{ok:r.ok,j:j}};}});}})
      .then(function(res){{ if(res.ok){{ window.location.reload(); }}
        else {{ var e=document.getElementById('edit-truck-err'); if(e){{e.textContent=(res.j&&res.j.error)||'Could not save.';e.hidden=false;}} }} }})
      .catch(function(){{ var e=document.getElementById('edit-truck-err'); if(e){{e.textContent='Network error.';e.hidden=false;}} }});
  }};
  window.deactivateTruck=function(){{
    if(!confirm('Deactivate this truck? It disappears from inspection pickers. History is kept.')) return;
    fetch('/api/trucks/'+TID+'/deactivate',{{method:'POST',headers:{{'Content-Type':'application/json','X-CSRF-Token':CSRF}}}})
      .then(function(r){{return r.json().then(function(j){{return {{ok:r.ok,j:j}};}});}})
      .then(function(res){{ if(res.ok){{ window.location='{list_url}'; }} else {{ alert((res.j&&res.j.error)||'Could not deactivate.'); }} }})
      .catch(function(){{ alert('Network error — try again.'); }});
  }};
  window.clearOOS=function(){{
    var note=prompt('Clear OUT OF SERVICE for this truck. Add a note (what was fixed / why it is safe):');
    if(note===null) return;
    if(!note.trim()){{ msg('A note is required.'); return; }}
    fetch('/api/trucks/'+TID+'/clear-oos',{{method:'POST',headers:{{'Content-Type':'application/json','X-CSRF-Token':CSRF}},body:JSON.stringify({{note:note}})}})
      .then(function(r){{return r.json().then(function(j){{return {{ok:r.ok,j:j}};}});}})
      .then(function(res){{ if(res.ok){{ window.location.reload(); }} else {{ msg((res.j&&res.j.error)||'Could not clear.'); }} }})
      .catch(function(){{ msg('Network error — try again.'); }});
  }};
  window.toggleAddMaint=function(){{ var f=document.getElementById('add-maint-form'); if(f) f.hidden=!f.hidden; }};
  window.submitMaint=function(tid){{
    var desc=(document.getElementById('tm-desc')||{{}}).value||'';
    var eb=document.getElementById('add-maint-err');
    if(!desc.trim()){{ if(eb){{eb.textContent='A description is required.';eb.hidden=false;}} return; }}
    var fd=new FormData();
    fd.append('_csrf_token', CSRF);
    fd.append('truck_id',tid);
    fd.append('entry_date',(document.getElementById('tm-date')||{{}}).value||'');
    fd.append('category',(document.getElementById('tm-cat')||{{}}).value||'');
    fd.append('description',desc);
    fd.append('cost',(document.getElementById('tm-cost')||{{}}).value||'');
    fd.append('vendor_id',(document.getElementById('tm-vendor')||{{}}).value||'');
    if((document.getElementById('tm-sent')||{{}}).checked){{ fd.append('sent','1'); }}
    var files=(document.getElementById('tm-receipts')||{{}}).files||[];
    for(var i=0;i<files.length;i++){{ fd.append('receipts', files[i]); }}
    fetch('/api/maintenance/entries',{{method:'POST',headers:{{'X-CSRF-Token':CSRF}},body:fd}})
      .then(function(r){{return r.json().then(function(j){{return {{ok:r.ok,j:j}};}});}})
      .then(function(res){{ if(res.ok){{ window.location.reload(); }} else {{ if(eb){{eb.textContent=(res.j&&res.j.error)||'Could not save.';eb.hidden=false;}} }} }})
      .catch(function(){{ if(eb){{eb.textContent='Network error — try again.';eb.hidden=false;}} }});
  }};
}})();
</script>
"""


def _active_checklist(conn):
    """The checklist a driver fills in: the company's own items if it has any,
    else the shared default template. (company customization is future-ready —
    the column exists — but today only the NULL template is seeded.)"""
    rows = conn.execute(
        "SELECT * FROM checklist_items WHERE company_id=? AND is_active=1 ORDER BY sort_order, id",
        (cid(),),
    ).fetchall()
    if rows:
        return rows
    return conn.execute(
        "SELECT * FROM checklist_items WHERE company_id IS NULL AND is_active=1 ORDER BY sort_order, id"
    ).fetchall()


@app.route("/inspection", methods=["GET"])
@driver_required
def inspection_new():
    """Driver: start a pre/post-trip inspection. Preselects the truck this
    driver used last so a clean pre-trip is a fast tap-through."""
    conn = get_db()
    trucks = conn.execute(
        "SELECT * FROM trucks WHERE company_id=? AND is_active=1 ORDER BY LOWER(name), id",
        (cid(),),
    ).fetchall()
    last = conn.execute(
        "SELECT truck_id FROM inspections WHERE driver_id=? AND company_id=? ORDER BY id DESC LIMIT 1",
        (session["user_id"], cid()),
    ).fetchone()
    last_truck_id = last["truck_id"] if last else None
    items = _active_checklist(conn)
    conn.close()

    user = get_current_user()
    default_sig = e((user["full_name"] if user and user["full_name"] else user["username"]) if user else "")

    if not trucks:
        body = """
        <div class="hero"><h1>Inspection</h1></div>
        <div class="empty-state" style="padding:32px 0;">
            No trucks are set up yet. Ask an owner or dispatcher to add your truck before running an inspection.
        </div>"""
        return render_template_string(shell_page("Inspection", body))

    truck_opts = "".join(
        f'<option value="{t["id"]}"{" selected" if t["id"]==last_truck_id else ""}>'
        f'{e(t["name"])}{" — OUT OF SERVICE" if t["out_of_service"] else ""}</option>'
        for t in trucks
    )

    rows_html = ""
    for it in items:
        iid = it["id"]
        hint = f'<div style="color:var(--slate);font-size:12px;margin-top:2px;">{e(it["hint"])}</div>' if it["hint"] else ""
        rows_html += f"""
        <div class="insp-row" data-iid="{iid}" style="border-top:1px solid var(--border);padding:14px 0;">
            <input type="hidden" name="result_{iid}" id="result_{iid}" value="">
            <input type="hidden" name="label_{iid}" value="{e(it["label"])}">
            <div style="font-weight:700;font-size:15px;">{e(it["label"])}</div>
            {hint}
            <div style="display:flex;gap:8px;margin-top:10px;">
                <button type="button" class="insp-btn pass" data-r="pass"  onclick="setResult({iid},'pass',this)">PASS</button>
                <button type="button" class="insp-btn defect" data-r="defect" onclick="setResult({iid},'defect',this)">DEFECT</button>
                <button type="button" class="insp-btn na" data-r="na"   onclick="setResult({iid},'na',this)">N/A</button>
            </div>
            <div class="insp-defect" id="defect_{iid}" hidden style="margin-top:10px;">
                <textarea name="note_{iid}" rows="2" style="width:100%;" placeholder="What's wrong? (required for a defect)"></textarea>
                <label class="insp-photo-btn" style="display:inline-flex;align-items:center;gap:6px;margin-top:8px;padding:10px 14px;border:1px solid var(--border-glow);border-radius:10px;cursor:pointer;color:var(--cyan);font-weight:700;">
                    📷 Add photo
                    <input type="file" name="photo_{iid}" accept=".png,.jpg,.jpeg,.webp" capture="environment" style="display:none;" onchange="photoPicked(this)">
                </label>
                <span class="insp-photo-name" style="font-size:12px;color:var(--slate);margin-left:8px;"></span>
            </div>
        </div>"""

    body = f"""
    <div class="hero">
        <h1>Inspection</h1>
        <p>Tap Pass, Defect, or N/A for each item. A clean pre-trip takes under a minute.</p>
    </div>
    <form method="POST" action="{url_for('inspection_submit')}" enctype="multipart/form-data"
          id="insp-form" style="max-width:640px;" onsubmit="return prepSubmit()">
        <input type="hidden" name="_csrf_token" value="{get_csrf_token()}">
        <div class="bin-card" style="padding:16px;margin-bottom:12px;">
            <label class="uw-lbl">Truck</label>
            <select name="truck_id" style="width:100%;margin-bottom:12px;">{truck_opts}</select>
            <label class="uw-lbl">Inspection type</label>
            <div style="display:flex;gap:8px;">
                <button type="button" class="insp-type active" data-t="pre_trip" onclick="setType('pre_trip',this)">Pre-trip</button>
                <button type="button" class="insp-type" data-t="post_trip" onclick="setType('post_trip',this)">Post-trip</button>
            </div>
            <input type="hidden" name="type" id="insp-type" value="pre_trip">
        </div>

        <div class="bin-card" style="padding:4px 16px 12px;margin-bottom:12px;">
            {rows_html}
        </div>

        <div class="bin-card" style="padding:16px;margin-bottom:12px;">
            <label class="uw-lbl">Overall judgment</label>
            <div style="display:grid;gap:8px;">
                <button type="button" class="insp-overall safe" data-o="safe" onclick="setOverall('safe',this)">✅ Safe to operate</button>
                <button type="button" class="insp-overall warn" data-o="defects_safe" onclick="setOverall('defects_safe',this)">⚠️ Defects — safe to operate</button>
                <button type="button" class="insp-overall stop" data-o="out_of_service" onclick="setOverall('out_of_service',this)">⛔ OUT OF SERVICE (unsafe)</button>
            </div>
            <input type="hidden" name="overall" id="insp-overall" value="">
        </div>

        <div class="bin-card" style="padding:16px;margin-bottom:12px;">
            <label class="uw-lbl">Signature — type your full name</label>
            <input name="signature_name" id="insp-sig" style="width:100%;" value="{default_sig}" placeholder="Your full name">
            <div style="color:var(--slate);font-size:12px;margin-top:6px;">By submitting you certify this inspection is accurate. Submitted reports can't be edited — corrections are a new inspection.</div>
        </div>

        <div id="insp-err" hidden style="color:#FF5252;font-size:13px;margin-bottom:10px;"></div>
        <button type="submit" class="btn green" style="width:100%;padding:16px;font-size:16px;">Submit inspection</button>
    </form>
    {_INSPECTION_FORM_CSS}
    {_INSPECTION_FORM_JS}
    """
    return render_template_string(shell_page("Inspection", body))


_INSPECTION_FORM_CSS = """
<style>
  /* Every rule is scoped under #insp-form so its id-level specificity (1,x,0)
     beats the global button:not(...) rule (0,7,1) that would otherwise force an
     orange gradient onto these buttons and hide the selected state. No
     !important needed. appearance:none + explicit background make iOS Safari /
     standalone PWA render our fill instead of native button chrome, and the
     selected state is a persistent class (not :hover/:active), so it survives
     scrolling and taps. */
  #insp-form .uw-lbl{display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:6px;}
  #insp-form .insp-btn,
  #insp-form .insp-type,
  #insp-form .insp-overall{
    -webkit-appearance:none;appearance:none;
    -webkit-tap-highlight-color:transparent;
    padding:16px 8px;border-radius:12px;font-weight:800;font-size:15px;
    border:2px solid rgba(255,255,255,0.16);
    background:rgba(255,255,255,0.04);color:var(--slate);
    cursor:pointer;text-align:center;transition:none;box-shadow:none;
  }
  #insp-form .insp-btn{flex:1;}
  #insp-form .insp-type{flex:1;padding:14px;}
  #insp-form .insp-overall{padding:14px;}
  /* Selected = solid, high-contrast fill with white text. */
  #insp-form .insp-btn.pass.on{background:#1f9d57;color:#fff;border-color:#1f9d57;}
  #insp-form .insp-btn.defect.on{background:#e5484d;color:#fff;border-color:#e5484d;}
  #insp-form .insp-btn.na.on{background:#64748b;color:#fff;border-color:#64748b;}
  #insp-form .insp-type.active{background:#FF6B1A;color:#1A1000;border-color:#FF6B1A;}
  #insp-form .insp-overall.safe.on{background:#1f9d57;color:#fff;border-color:#1f9d57;}
  #insp-form .insp-overall.warn.on{background:#f5842a;color:#1A1000;border-color:#f5842a;}
  #insp-form .insp-overall.stop.on{background:#e5484d;color:#fff;border-color:#e5484d;}
</style>
"""

_INSPECTION_FORM_JS = """
<script>
(function(){
  window.setResult=function(iid,val,btn){
    document.getElementById('result_'+iid).value=val;
    var row=btn.closest('.insp-row');
    row.querySelectorAll('.insp-btn').forEach(function(b){ b.classList.remove('on'); });
    btn.classList.add('on');
    var d=document.getElementById('defect_'+iid);
    if(d) d.hidden = (val!=='defect');
  };
  window.setType=function(val,btn){
    document.getElementById('insp-type').value=val;
    document.querySelectorAll('.insp-type').forEach(function(b){ b.classList.remove('active'); });
    btn.classList.add('active');
  };
  window.setOverall=function(val,btn){
    document.getElementById('insp-overall').value=val;
    document.querySelectorAll('.insp-overall').forEach(function(b){ b.classList.remove('on'); });
    btn.classList.add('on');
  };
  window.photoPicked=function(inp){
    var name=(inp.files&&inp.files[0])?inp.files[0].name:'';
    var span=inp.closest('.insp-defect').querySelector('.insp-photo-name');
    if(span) span.textContent = name ? ('✓ '+name) : '';
  };
  function err(m){ var e=document.getElementById('insp-err'); if(e){ e.textContent=m; e.hidden=false; window.scrollTo(0,e.offsetTop-80); } }
  window.prepSubmit=function(){
    var rows=document.querySelectorAll('.insp-row'); var unanswered=0; var missingNote=null;
    rows.forEach(function(r){
      var iid=r.getAttribute('data-iid');
      var v=document.getElementById('result_'+iid).value;
      if(!v){ unanswered++; }
      if(v==='defect'){
        var note=r.querySelector('textarea[name=note_'+iid+']');
        if(note && !note.value.trim() && missingNote===null){ missingNote=r; }
      }
    });
    if(unanswered>0){ err('Answer every item ('+unanswered+' left).'); return false; }
    if(missingNote){ err('Every defect needs a note.'); return false; }
    if(!document.getElementById('insp-overall').value){ err('Pick an overall judgment.'); return false; }
    if(!document.getElementById('insp-sig').value.trim()){ err('Type your name to sign.'); return false; }
    return true;
  };
})();
</script>
"""


@app.route("/inspection", methods=["POST"])
@driver_required
def inspection_submit():
    """Driver submit → immutable inspection + items (+ optional defect photos).
    An OUT OF SERVICE overall flags the truck until an owner/dispatcher clears
    it. Server-side validation mirrors the client so a crafted POST can't slip
    through."""
    conn = get_db()
    truck = None
    try:
        truck_id = request.form.get("truck_id", "")
        truck = _load_truck_scoped(conn, int(truck_id), active_only=True) if truck_id.isdigit() else None
        if truck is None:
            conn.close()
            flash("Pick a valid truck.", "error")
            return redirect(url_for("inspection_new"))

        itype = request.form.get("type", "")
        overall = request.form.get("overall", "")
        signature = (request.form.get("signature_name") or "").strip()[:120]
        if itype not in INSPECTION_TYPES or overall not in INSPECTION_OVERALL or not signature:
            conn.close()
            flash("Fill in type, overall judgment, and signature.", "error")
            return redirect(url_for("inspection_new"))

        items = _active_checklist(conn)
        if not items:
            conn.close()
            flash("No checklist configured.", "error")
            return redirect(url_for("inspection_new"))

        # Validate every item before writing anything.
        answers = []
        for it in items:
            iid = it["id"]
            result = request.form.get(f"result_{iid}", "")
            if result not in ("pass", "defect", "na"):
                conn.close()
                flash("Answer every checklist item before submitting.", "error")
                return redirect(url_for("inspection_new"))
            note = (request.form.get(f"note_{iid}") or "").strip()[:1000]
            if result == "defect" and not note:
                conn.close()
                flash("Every defect needs a note.", "error")
                return redirect(url_for("inspection_new"))
            answers.append((it, result, note))

        cur = conn.cursor()
        cur.execute(
            """INSERT INTO inspections (company_id, truck_id, driver_id, type, overall,
                                        signature_name, created_at)
               VALUES (?,?,?,?,?,?,?)""",
            (cid(), truck["id"], session["user_id"], itype, overall, signature, now_ts()),
        )
        inspection_id = cur.lastrowid

        for it, result, note in answers:
            iid = it["id"]
            photo_db_path = None
            if result == "defect":
                photo = request.files.get(f"photo_{iid}")
                if photo and photo.filename and allowed_file(photo.filename):
                    fname = f"insp_{inspection_id}_{iid}_{secrets.token_hex(6)}_{secure_filename(photo.filename)}"
                    try:
                        photo.save(os.path.join(app.config["UPLOAD_FOLDER"], fname))
                        photo_db_path = os.path.join("static", "uploads", fname)
                    except OSError as exc:
                        app.logger.warning("inspection photo save failed: %s", exc)
                        photo_db_path = None
            cur.execute(
                """INSERT INTO inspection_items (inspection_id, checklist_item_id, label,
                       result, note, photo_path, defect_status)
                   VALUES (?,?,?,?,?,?,?)""",
                (inspection_id, iid, it["label"], result, note or None, photo_db_path,
                 "open" if result == "defect" else None),
            )

        if overall == "out_of_service":
            cur.execute(
                """UPDATE trucks SET out_of_service=1, oos_note=?, oos_at=?, oos_by=?,
                                     oos_inspection_id=? WHERE id=?""",
                (f"Flagged by {signature} on a {_INSPECTION_TYPE_LABEL[itype].lower()} inspection.",
                 now_ts(), session["user_id"], inspection_id, truck["id"]),
            )
        conn.commit()
    except Exception as exc:
        conn.rollback()
        conn.close()
        app.logger.warning("inspection submit failed: %s", exc)
        flash("Could not save the inspection — try again.", "error")
        return redirect(url_for("inspection_new"))
    conn.close()
    flash("Inspection submitted.", "success")
    return redirect(url_for("inspection_report", inspection_id=inspection_id))


@app.route("/my-inspections")
@driver_required
def my_inspections():
    """A driver's own inspection history, newest first."""
    conn = get_db()
    rows = conn.execute(
        """SELECT i.*, t.name AS truck_name, t.out_of_service, t.at_vendor,
                  (SELECT COUNT(*) FROM inspection_items ii
                    WHERE ii.inspection_id=i.id AND ii.result='defect') AS defect_count
             FROM inspections i
             JOIN trucks t ON i.truck_id=t.id
            WHERE i.driver_id=? AND i.company_id=?
            ORDER BY i.created_at DESC, i.id DESC""",
        (session["user_id"], cid()),
    ).fetchall()
    conn.close()

    _OVR_COLOR = {"safe": "#3DDC84", "defects_safe": "#FF8A3D", "out_of_service": "#FF7A7A"}
    cards = ""
    for i in rows:
        color = _OVR_COLOR.get(i["overall"], "var(--slate)")
        cards += f"""
        <a class="bin-card" href="{url_for('inspection_report', inspection_id=i['id'])}"
           style="padding:14px;display:block;text-decoration:none;color:inherit;">
            <div style="display:flex;justify-content:space-between;gap:10px;">
                <span style="font-weight:700;">🚛 {e(i["truck_name"])}{_truck_status_badges(i)}</span>
                <span style="color:{color};font-weight:800;font-size:12px;">{e(_INSPECTION_OVERALL_LABEL.get(i["overall"], i["overall"]))}</span>
            </div>
            <div style="color:var(--slate);font-size:13px;margin-top:4px;">
                {e((i["created_at"] or "")[:16])} · {e(_INSPECTION_TYPE_LABEL.get(i["type"], i["type"]))}
                {(' · ' + str(i["defect_count"]) + ' defect' + ('' if i["defect_count"]==1 else 's')) if i["defect_count"] else ''}
            </div>
        </a>"""
    empty = "" if rows else '<div class="empty-state" style="padding:32px 0;">No inspections yet. Tap Inspection to run your first one.</div>'
    body = f"""
    <div class="hero"><h1>My Inspections</h1><p>Your submitted reports. Read-only.</p></div>
    {empty}
    <div class="bin-list" style="display:grid;gap:10px;max-width:640px;">{cards}</div>
    """
    return render_template_string(shell_page("My Inspections", body))


@app.route("/inspection/<int:inspection_id>")
@login_required
def inspection_report(inspection_id):
    """Read-only full report. Management sees any; a driver sees only their own."""
    conn = get_db()
    insp = conn.execute(
        """SELECT i.*, t.name AS truck_name, t.make_model, t.plate, t.out_of_service, t.at_vendor,
                  COALESCE(u.username,'—') AS driver_name,
                  COALESCE(u.full_name,'') AS driver_full
             FROM inspections i
             JOIN trucks t ON i.truck_id=t.id
        LEFT JOIN users  u ON i.driver_id=u.id
            WHERE i.id=? AND i.company_id=?""",
        (inspection_id, cid()),
    ).fetchone()
    if insp is None:
        conn.close()
        abort(404)
    if not _is_management() and insp["driver_id"] != session.get("user_id"):
        conn.close()
        abort(403)
    items = conn.execute(
        "SELECT * FROM inspection_items WHERE inspection_id=? ORDER BY id",
        (inspection_id,),
    ).fetchall()
    # Cost data (cost/vendor/receipts) is MANAGEMENT-ONLY — a driver viewing
    # their own report never sees it.
    is_mgmt = _is_management()
    receipts_by_item = {}
    vmap = {}
    if is_mgmt:
        vmap = _vendor_map(conn)
        for it in items:
            if it["result"] == "defect":
                rc = _maintenance_receipts(conn, defect_item_id=it["id"])
                if rc:
                    receipts_by_item[it["id"]] = rc
    conn.close()

    _RES = {
        "pass": ("PASS", "#3DDC84"),
        "defect": ("DEFECT", "#FF7A7A"),
        "na": ("N/A", "#ADC0D1"),
    }
    _DEF_STATUS = {"open": ("Open", "#FF7A7A"), "repaired": ("Repaired", "#3DDC84"),
                   "deferred": ("Deferred", "#FF8A3D")}
    rows_html = ""
    for it in items:
        label_txt, color = _RES.get(it["result"], (it["result"], "var(--slate)"))
        note = f'<div style="font-size:13px;color:#C9C9C2;margin-top:4px;">{e(it["note"])}</div>' if it["note"] else ""
        photo = ""
        if it["photo_path"]:
            purl = url_for("serve_inspection_photo", item_id=it["id"])
            photo = (f'<a href="{purl}" target="_blank"><img src="{purl}" loading="lazy" '
                     f'style="margin-top:8px;max-width:160px;border-radius:8px;border:1px solid var(--border);"></a>')
        defstat = ""
        if it["result"] == "defect" and it["defect_status"]:
            dlabel, dcolor = _DEF_STATUS.get(it["defect_status"], (it["defect_status"], "var(--slate)"))
            # "Sent to vendor" is an open-but-out state (management sees the shop).
            if it["defect_status"] == "open" and is_mgmt and dict(it).get("at_vendor"):
                vn = vmap.get(dict(it).get("sent_vendor_id"), "vendor")
                dlabel, dcolor = (f"Sent to {vn}", "#F5B43C")
            res_note = f' — {e(it["resolution_note"])}' if it["resolution_note"] else ""
            defstat = (f'<div style="font-size:12px;margin-top:4px;color:{dcolor};font-weight:700;">'
                       f'{e(dlabel)}{res_note}</div>')
        cost_block = ""
        if is_mgmt and it["result"] == "defect":
            _vn = vmap.get(dict(it).get("vendor_id"))
            _bits = []
            if it["cost_cents"] is not None:
                _bits.append(f'💵 {e(format_cents(it["cost_cents"]))}')
            if _vn:
                _bits.append(e(_vn))
            if _bits:
                cost_block = (f'<div style="font-size:12px;margin-top:4px;color:var(--slate);">'
                              f'{" · ".join(_bits)}</div>')
        receipts_block = _receipt_thumbs_html(receipts_by_item.get(it["id"])) if is_mgmt else ""
        rows_html += f"""
        <div style="border-top:1px solid var(--border);padding:12px 0;">
            <div style="display:flex;justify-content:space-between;gap:10px;">
                <span style="font-weight:700;font-size:14px;">{e(it["label"])}</span>
                <span style="color:{color};font-weight:800;font-size:12px;">{label_txt}</span>
            </div>
            {note}{photo}{defstat}{cost_block}{receipts_block}
        </div>"""

    _OVR_COLOR = {"safe": "#3DDC84", "defects_safe": "#FF8A3D", "out_of_service": "#FF7A7A"}
    ov_color = _OVR_COLOR.get(insp["overall"], "var(--slate)")
    back = (url_for("truck_detail_page", truck_id=insp["truck_id"]) if _is_management()
            else url_for("my_inspections"))
    body = f"""
    <div class="hero" style="display:flex;justify-content:space-between;align-items:flex-start;gap:12px;">
        <div>
            <h1 style="margin-bottom:4px;">🚛 {e(insp["truck_name"])}{_truck_status_badges(insp)}</h1>
            <p style="margin:0;">{e(_INSPECTION_TYPE_LABEL.get(insp["type"], insp["type"]))} inspection · {e((insp["created_at"] or ""))}</p>
        </div>
        <a class="btn secondary" href="{back}" style="white-space:nowrap;">← Back</a>
    </div>
    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
        <div style="font-weight:800;color:{ov_color};font-size:16px;">{e(_INSPECTION_OVERALL_LABEL.get(insp["overall"], insp["overall"]))}</div>
        <div style="color:var(--slate);font-size:13px;margin-top:6px;">
            Driver: {e(insp["driver_full"] or insp["driver_name"])}
        </div>
    </div>
    <div class="bin-card" style="padding:4px 16px 12px;max-width:640px;margin-bottom:12px;">
        {rows_html}
    </div>
    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:24px;">
        <div style="font-size:12px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;">Signature</div>
        <div style="font-weight:700;font-size:16px;margin-top:4px;">✍️ {e(insp["signature_name"])}</div>
        <div style="color:var(--slate);font-size:12px;margin-top:2px;">{e(insp["created_at"])} · immutable record</div>
    </div>
    """
    return render_template_string(shell_page("Inspection Report", body))


@app.route("/inspection-photo/<int:item_id>")
@login_required
def serve_inspection_photo(item_id):
    """Serve a defect photo — company-scoped; management sees any, a driver only
    their own inspection's photos (mirrors serve_stop_photo)."""
    conn = get_db()
    row = conn.execute(
        """SELECT ii.photo_path, i.driver_id
             FROM inspection_items ii
             JOIN inspections i ON ii.inspection_id=i.id
            WHERE ii.id=? AND i.company_id=?""",
        (item_id, cid()),
    ).fetchone()
    conn.close()
    if not row or not row["photo_path"]:
        abort(404)
    if not _is_management() and row["driver_id"] != session.get("user_id"):
        abort(403)
    full_path = os.path.join(app.root_path, row["photo_path"])
    if not os.path.isfile(full_path):
        abort(404)
    return send_file(full_path)


@app.route("/api/defects/open-count")
@login_required
def defects_open_count():
    """Live count for the Maintenance nav badge. Any management role."""
    if not _is_management():
        return jsonify({"error": "forbidden"}), 403
    conn = get_db()
    n = _open_defect_count(conn)
    conn.close()
    return jsonify({"count": n})


@app.route("/maintenance")
@roles_required("owner", "customer_manager", "dispatcher")
def maintenance_page():
    """Open defects across the fleet. Any management role views; owner/dispatcher
    can mark Repaired (closes) or Deferred."""
    conn = get_db()
    defects = conn.execute(
        """SELECT ii.id AS item_id, ii.label, ii.note, ii.photo_path, ii.defect_status,
                  ii.at_vendor AS item_at_vendor, ii.sent_vendor_id,
                  i.id AS inspection_id, i.type, i.created_at, i.truck_id,
                  t.name AS truck_name, t.out_of_service, t.at_vendor,
                  COALESCE(u.username,'—') AS reporter
             FROM inspection_items ii
             JOIN inspections i ON ii.inspection_id=i.id
             JOIN trucks t ON i.truck_id=t.id
        LEFT JOIN users u ON i.driver_id=u.id
            WHERE i.company_id=? AND ii.result='defect' AND ii.defect_status='open'
            ORDER BY t.out_of_service DESC, i.created_at ASC, ii.id ASC""",
        (cid(),),
    ).fetchall()
    vendors = _company_vendors(conn)
    vmap = _vendor_map(conn)
    has_costs = _company_has_costs(conn)
    # Per-truck totals — spend when costs exist, else event counts (A4 revision).
    trucks = conn.execute(
        "SELECT id, name, out_of_service, at_vendor FROM trucks WHERE company_id=? AND is_active=1 ORDER BY LOWER(name), id",
        (cid(),),
    ).fetchall()
    total_rows = []
    fleet_month = fleet_year = 0
    for t in trucks:
        if has_costs:
            m, y, _ = _truck_spend(conn, t["id"])
        else:
            m, y, _ = _truck_event_counts(conn, t["id"])
        fleet_month += m
        fleet_year += y
        total_rows.append((t, m, y))
    conn.close()
    can_action = _can_action_fleet()
    vendor_opts = _vendor_options_html(vendors)

    cards = ""
    for d in defects:
        thumb = ""
        if d["photo_path"]:
            purl = url_for("serve_inspection_photo", item_id=d["item_id"])
            thumb = (f'<a href="{purl}" target="_blank"><img src="{purl}" loading="lazy" '
                     f'style="width:64px;height:64px;object-fit:cover;border-radius:8px;border:1px solid var(--border);"></a>')
        note = f'<div style="font-size:13px;color:#C9C9C2;margin-top:4px;">{e(d["note"])}</div>' if d["note"] else ""
        sent_chip = ""
        if d["item_at_vendor"]:
            vn = vmap.get(d["sent_vendor_id"], "a vendor")
            sent_chip = (f'<div style="margin-top:6px;"><span style="display:inline-block;padding:2px 9px;'
                         f'border-radius:999px;font-size:11px;font-weight:800;background:rgba(245,180,60,0.16);'
                         f'color:#F5B43C;border:1px solid rgba(245,180,60,0.45);">🔧 Sent to {e(vn)}</span></div>')
        repair_form = ""
        actions = ""
        if can_action:
            _iid = d["item_id"]
            _send_btn = ("" if d["item_at_vendor"] else
                         f'<button class="btn secondary" style="flex:1;" onclick="showSend({_iid})">Send to vendor</button>')
            actions = f"""
            <div style="display:flex;gap:8px;margin-top:10px;flex-wrap:wrap;">
                <button class="btn green" style="flex:1;min-width:90px;" onclick="showRepair({d['item_id']})">Repaired</button>
                {_send_btn}
                <button class="btn secondary" style="flex:1;min-width:70px;" onclick="deferDefect({d['item_id']})">Defer</button>
            </div>"""
            repair_form = f"""
            <div id="send-form-{d['item_id']}" hidden style="margin-top:12px;border-top:1px solid var(--border);padding-top:12px;">
                <label class="uw-lbl">Vendor</label>
                <select id="sd-vendor-{d['item_id']}" style="width:100%;margin-bottom:10px;">{vendor_opts}</select>
                <div style="display:flex;gap:8px;">
                    <button class="btn green" style="flex:1;" onclick="submitSend({d['item_id']})">Mark sent</button>
                    <button class="btn secondary" onclick="hideSend({d['item_id']})">Cancel</button>
                </div>
            </div>
            <div id="repair-form-{d['item_id']}" hidden style="margin-top:12px;border-top:1px solid var(--border);padding-top:12px;">
                <label class="uw-lbl">What was done (required)</label>
                <textarea id="rp-note-{d['item_id']}" rows="2" style="width:100%;margin-bottom:8px;" placeholder="e.g. Replaced front brake pads"></textarea>
                <label class="uw-lbl">Vendor</label>
                <select id="rp-vendor-{d['item_id']}" style="width:100%;margin-bottom:8px;">{vendor_opts}</select>
                <details style="margin-bottom:10px;">
                    <summary style="color:var(--slate);font-size:12px;cursor:pointer;">Add cost / receipt (optional)</summary>
                    <div style="margin-top:8px;">
                        <label class="uw-lbl">Cost</label><input id="rp-cost-{d['item_id']}" inputmode="decimal" placeholder="149.99" style="width:100%;margin-bottom:8px;">
                        <label class="uw-lbl">Receipt photo(s)</label>
                        <input id="rp-receipts-{d['item_id']}" type="file" accept=".png,.jpg,.jpeg,.webp,.pdf" multiple capture="environment" style="width:100%;">
                    </div>
                </details>
                <div style="display:flex;gap:8px;">
                    <button class="btn green" style="flex:1;" onclick="submitRepair({d['item_id']})">Save repair</button>
                    <button class="btn secondary" onclick="hideRepair({d['item_id']})">Cancel</button>
                </div>
            </div>"""
        cards += f"""
        <div class="bin-card" id="defect-{d['item_id']}" style="padding:16px;">
            <div style="display:flex;justify-content:space-between;gap:10px;align-items:center;">
                <div style="font-weight:700;font-size:15px;">🚛 {e(d["truck_name"])}{_truck_status_badges(d)}</div>
                <a href="{url_for('inspection_report', inspection_id=d['inspection_id'])}"
                   style="font-size:12px;color:var(--cyan);white-space:nowrap;">View report →</a>
            </div>
            <div style="font-weight:700;font-size:14px;margin-top:8px;color:#FF7A7A;">⚠ {e(d["label"])}</div>
            {note}{sent_chip}
            <div style="display:flex;gap:10px;align-items:center;margin-top:8px;">
                {thumb}
                <div style="color:var(--slate);font-size:12px;">
                    {e(_INSPECTION_TYPE_LABEL.get(d["type"], d["type"]))} · {e(d["reporter"])}<br>{e((d["created_at"] or "")[:16])}
                </div>
            </div>
            <div id="defect-err-{d['item_id']}" hidden style="color:#FF5252;font-size:12px;margin-top:8px;"></div>
            {actions}{repair_form}
        </div>"""

    # Totals table — spend (when any cost recorded) or event counts otherwise.
    def _fmt(v):
        return format_cents(v) if has_costs else str(v)
    metric_label = "Spend" if has_costs else "Events"
    rows_out = ""
    for t, m, y in total_rows:
        rows_out += f"""
        <tr style="border-top:1px solid var(--border);">
            <td style="padding:8px 6px;"><a href="{url_for('truck_detail_page', truck_id=t['id'])}" style="color:inherit;">🚛 {e(t['name'])}{_truck_status_badges(t)}</a></td>
            <td style="padding:8px 6px;text-align:right;">{e(_fmt(m))}</td>
            <td style="padding:8px 6px;text-align:right;">{e(_fmt(y))}</td>
        </tr>"""
    if not total_rows:
        rows_out = '<tr><td colspan="3" style="padding:12px 6px;color:var(--slate);">No trucks yet.</td></tr>'
    totals_hint = "" if has_costs else '<div style="color:var(--slate);font-size:12px;margin-bottom:6px;">No costs entered — showing event counts. Add a cost to any record to switch to spend.</div>'
    totals_table = f"""
    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:16px;">
        <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:6px;">
            <h2 style="font-size:15px;margin:0;">{metric_label}</h2>
            <a href="{url_for('vendors_page')}" style="font-size:12px;color:var(--cyan);">Vendors →</a>
        </div>
        {totals_hint}
        <table style="width:100%;border-collapse:collapse;font-size:13px;">
            <thead><tr style="color:var(--slate);text-align:left;font-size:11px;text-transform:uppercase;letter-spacing:.5px;">
                <th style="padding:4px 6px;">Truck</th><th style="padding:4px 6px;text-align:right;">This month</th><th style="padding:4px 6px;text-align:right;">This year</th>
            </tr></thead>
            <tbody>{rows_out}</tbody>
            <tfoot><tr style="border-top:2px solid var(--border-glow);font-weight:800;">
                <td style="padding:8px 6px;">Fleet total</td>
                <td style="padding:8px 6px;text-align:right;">{e(_fmt(fleet_month))}</td>
                <td style="padding:8px 6px;text-align:right;">{e(_fmt(fleet_year))}</td>
            </tr></tfoot>
        </table>
    </div>"""

    # Add-manual-entry form (owner/dispatcher)
    add_entry_block = ""
    if can_action:
        truck_opts = "".join(f'<option value="{t["id"]}">{e(t["name"])}</option>' for t in trucks)
        cat_opts = "".join(f'<option value="{e(c)}">{e(c)}</option>' for c in MAINTENANCE_CATEGORIES)
        add_entry_block = f"""
        <div style="max-width:640px;margin-bottom:16px;">
            <button class="btn green" onclick="toggleAddEntry()">+ Log maintenance</button>
            <div id="add-entry-form" hidden class="bin-card" style="padding:16px;margin-top:12px;">
                <div id="add-entry-err" hidden style="color:#FF5252;font-size:12px;margin-bottom:8px;"></div>
                <label class="uw-lbl">Truck</label>
                <select id="me-truck" style="width:100%;margin-bottom:10px;">{truck_opts}</select>
                <div style="display:flex;gap:8px;">
                    <div style="flex:1;"><label class="uw-lbl">Date</label><input id="me-date" type="date" value="{today_str()}" style="width:100%;"></div>
                    <div style="flex:1;"><label class="uw-lbl">Category</label><select id="me-cat" style="width:100%;">{cat_opts}</select></div>
                </div>
                <label class="uw-lbl" style="margin-top:10px;">Description</label>
                <textarea id="me-desc" rows="2" style="width:100%;margin-bottom:8px;" placeholder="e.g. Oil change + filter"></textarea>
                <label class="uw-lbl">Vendor</label>
                <select id="me-vendor" style="width:100%;margin-bottom:8px;">{vendor_opts}</select>
                <label style="display:flex;align-items:center;gap:8px;font-size:13px;color:var(--slate);margin-bottom:8px;">
                    <input id="me-sent" type="checkbox"> Truck is currently at this vendor
                </label>
                <details style="margin-bottom:10px;">
                    <summary style="color:var(--slate);font-size:12px;cursor:pointer;">Add cost / receipt (optional)</summary>
                    <div style="margin-top:8px;">
                        <label class="uw-lbl">Cost</label><input id="me-cost" inputmode="decimal" placeholder="89.00" style="width:100%;margin-bottom:8px;">
                        <label class="uw-lbl">Receipt photo(s)</label>
                        <input id="me-receipts" type="file" accept=".png,.jpg,.jpeg,.webp,.pdf" multiple capture="environment" style="width:100%;">
                    </div>
                </details>
                <div style="display:flex;gap:8px;">
                    <button class="btn green" style="flex:1;" onclick="submitEntry()">Save</button>
                    <button class="btn secondary" onclick="toggleAddEntry()">Cancel</button>
                </div>
            </div>
        </div>"""

    empty_hidden = "" if defects else " hidden"
    view_note = "" if can_action else '<p style="color:var(--slate);font-size:13px;">View-only — an owner or dispatcher resolves defects and logs maintenance.</p>'
    body = f"""
    <div class="hero">
        <h1>Maintenance</h1>
        <p>Which truck, which vendor, what, when — and is it back in service. Costs optional.</p>
        {view_note}
    </div>
    {totals_table}
    {add_entry_block}
    <h2 style="font-size:15px;margin:0 0 8px;max-width:640px;">Open defects</h2>
    <div id="maint-empty" class="empty-state" style="padding:24px 0;"{empty_hidden}>No open defects — the fleet's clean. 🛠️</div>
    <div id="maint-list" class="bin-list" style="display:grid;gap:12px;max-width:640px;">
        {cards}
    </div>
    <style>.uw-lbl{{display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;}}</style>
    {_MAINTENANCE_PAGE_JS}
    """
    return render_template_string(shell_page("Maintenance", body))


_MAINTENANCE_PAGE_JS = """
<script>
(function(){
  var CSRF=(document.querySelector('meta[name=csrf-token]')||{}).content||'';
  function err(id,m){ var e=document.getElementById('defect-err-'+id); if(e){ e.textContent=m; e.hidden=false; } }
  function bump(){ var badge=document.getElementById('maint-nav-badge');
    if(badge){ var n=parseInt(badge.textContent||'0',10)-1;
      if(n>0){ badge.textContent=n; } else { badge.hidden=true; badge.textContent=''; } } }
  function removeCard(id){
    var c=document.getElementById('defect-'+id); if(c) c.remove();
    var list=document.getElementById('maint-list');
    if(list && !list.querySelector('.bin-card')){ var em=document.getElementById('maint-empty'); if(em) em.hidden=false; }
    bump();
  }
  window.showRepair=function(id){ var f=document.getElementById('repair-form-'+id); if(f) f.hidden=false; };
  window.hideRepair=function(id){ var f=document.getElementById('repair-form-'+id); if(f) f.hidden=true; };
  window.showSend=function(id){ var f=document.getElementById('send-form-'+id); if(f) f.hidden=false; };
  window.hideSend=function(id){ var f=document.getElementById('send-form-'+id); if(f) f.hidden=true; };
  window.submitSend=function(id){
    fetch('/api/defects/'+id+'/resolve',{method:'POST',
        headers:{'Content-Type':'application/json','X-CSRF-Token':CSRF},
        body:JSON.stringify({action:'sent', vendor_id:(document.getElementById('sd-vendor-'+id)||{}).value||''})})
      .then(function(r){ return r.json().then(function(j){ return {ok:r.ok,j:j}; }); })
      .then(function(res){ if(res.ok){ window.location.reload(); } else { err(id,(res.j&&res.j.error)||'Could not update.'); } })
      .catch(function(){ err(id,'Network error — try again.'); });
  };
  window.submitRepair=function(id){
    var note=(document.getElementById('rp-note-'+id)||{}).value||'';
    if(!note.trim()){ err(id,'A note is required.'); return; }
    var fd=new FormData();
    fd.append('_csrf_token', CSRF);
    fd.append('action','repaired'); fd.append('note',note);
    fd.append('cost',(document.getElementById('rp-cost-'+id)||{}).value||'');
    fd.append('vendor_id',(document.getElementById('rp-vendor-'+id)||{}).value||'');
    var files=(document.getElementById('rp-receipts-'+id)||{}).files||[];
    for(var i=0;i<files.length;i++){ fd.append('receipts', files[i]); }
    fetch('/api/defects/'+id+'/resolve',{method:'POST',headers:{'X-CSRF-Token':CSRF},body:fd})
      .then(function(r){ return r.json().then(function(j){ return {ok:r.ok,j:j}; }); })
      .then(function(res){ if(res.ok){ removeCard(id); } else { err(id,(res.j&&res.j.error)||'Could not save.'); } })
      .catch(function(){ err(id,'Network error — try again.'); });
  };
  window.deferDefect=function(id){
    var note=prompt('Defer this defect. Add a note (why):');
    if(note===null) return;
    if(!note.trim()){ err(id,'A note is required.'); return; }
    fetch('/api/defects/'+id+'/resolve',{method:'POST',
        headers:{'Content-Type':'application/json','X-CSRF-Token':CSRF},
        body:JSON.stringify({action:'deferred', note:note})})
      .then(function(r){ return r.json().then(function(j){ return {ok:r.ok,j:j}; }); })
      .then(function(res){ if(res.ok){ removeCard(id); } else { err(id,(res.j&&res.j.error)||'Could not update.'); } })
      .catch(function(){ err(id,'Network error — try again.'); });
  };
  window.toggleAddEntry=function(){ var f=document.getElementById('add-entry-form'); if(f) f.hidden=!f.hidden; };
  function eerr(m){ var e=document.getElementById('add-entry-err'); if(e){ e.textContent=m; e.hidden=false; } }
  window.submitEntry=function(){
    var desc=(document.getElementById('me-desc')||{}).value||'';
    if(!desc.trim()){ eerr('A description is required.'); return; }
    var fd=new FormData();
    fd.append('_csrf_token', CSRF);
    fd.append('truck_id',(document.getElementById('me-truck')||{}).value||'');
    fd.append('entry_date',(document.getElementById('me-date')||{}).value||'');
    fd.append('category',(document.getElementById('me-cat')||{}).value||'');
    fd.append('description',desc);
    fd.append('cost',(document.getElementById('me-cost')||{}).value||'');
    fd.append('vendor_id',(document.getElementById('me-vendor')||{}).value||'');
    if((document.getElementById('me-sent')||{}).checked){ fd.append('sent','1'); }
    var files=(document.getElementById('me-receipts')||{}).files||[];
    for(var i=0;i<files.length;i++){ fd.append('receipts', files[i]); }
    fetch('/api/maintenance/entries',{method:'POST',headers:{'X-CSRF-Token':CSRF},body:fd})
      .then(function(r){ return r.json().then(function(j){ return {ok:r.ok,j:j}; }); })
      .then(function(res){ if(res.ok){ window.location.reload(); } else { eerr((res.j&&res.j.error)||'Could not save.'); } })
      .catch(function(){ eerr('Network error — try again.'); });
  };
})();
</script>
"""


@app.route("/api/defects/<int:item_id>/resolve", methods=["POST"])
@login_required
def resolve_defect(item_id):
    """Owner/dispatcher marks a defect Repaired (closes) or Deferred, with a
    required note. Repaired accepts optional cost (integer cents), vendor, and
    receipt photos (multipart). Only the defect lifecycle + cost fields change —
    the driver's inspection report content stays immutable, and cost data is
    never shown to the driver (see inspection_report / serve_maintenance_photo).
    Accepts multipart (with receipts) or JSON."""
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    # Read from form (multipart) first, else JSON.
    src = request.form if request.form else (request.get_json(silent=True) or {})
    action = src.get("action")
    note = str(src.get("note") or "").strip()[:500]
    # 'sent' = intermediate "sent to vendor" state (stays open, flags the truck);
    # 'repaired' closes it; 'deferred' postpones it.
    if action not in ("repaired", "deferred", "sent"):
        return jsonify({"error": "invalid action"}), 400
    if action != "sent" and not note:
        return jsonify({"error": "a note is required"}), 400
    conn = get_db()
    vendor_id = _clean_vendor_id(conn, src.get("vendor_id"))
    cost_cents = None
    if action == "repaired":
        cost_cents, cost_err = parse_cost_cents(src.get("cost"))
        if cost_err:
            conn.close()
            return jsonify({"error": cost_err}), 400
    row = conn.execute(
        """SELECT ii.id, ii.defect_status, i.truck_id
             FROM inspection_items ii
             JOIN inspections i ON ii.inspection_id=i.id
            WHERE ii.id=? AND i.company_id=? AND ii.result='defect'""",
        (item_id, cid()),
    ).fetchone()
    if row is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    if row["defect_status"] != "open":
        conn.close()
        return jsonify({"error": "defect is not open"}), 409

    if action == "sent":
        # Out to a shop — still an open defect, but flag the truck "at vendor".
        conn.execute(
            """UPDATE inspection_items SET at_vendor=1, sent_vendor_id=?, sent_at=?,
                       vendor_id=COALESCE(?, vendor_id) WHERE id=?""",
            (vendor_id, now_ts(), vendor_id, item_id),
        )
    else:
        conn.execute(
            """UPDATE inspection_items SET defect_status=?, resolution_note=?,
                       resolved_by=?, resolved_at=?, cost_cents=?, vendor_id=?,
                       at_vendor=0 WHERE id=?""",
            (action, note, session["user_id"], now_ts(), cost_cents, vendor_id, item_id),
        )
        if action == "repaired":
            _save_maintenance_receipts(conn, request.files.getlist("receipts"),
                                       defect_item_id=item_id)
    _recompute_truck_at_vendor(conn, row["truck_id"])
    conn.commit()
    conn.close()
    return jsonify({"success": True, "status": action})


@app.route("/maintenance-photo/<int:photo_id>")
@login_required
def serve_maintenance_photo(photo_id):
    """Serve a receipt photo — MANAGEMENT ONLY (cost data). Drivers get 403
    even for their own inspection's defect receipts."""
    if not _is_management():
        abort(403)
    conn = get_db()
    row = conn.execute(
        "SELECT file_path FROM maintenance_photos WHERE id=? AND company_id=?",
        (photo_id, cid()),
    ).fetchone()
    conn.close()
    if not row:
        abort(404)
    full = os.path.join(app.root_path, row["file_path"])
    if not os.path.isfile(full):
        abort(404)
    return send_file(full)


@app.route("/api/maintenance/entries", methods=["POST"])
@login_required
def create_maintenance_entry():
    """Owner/dispatcher logs a manual (non-inspection) maintenance record.
    Multipart: truck_id, entry_date, category, description, cost, vendor,
    receipts[]. cost/vendor/receipts optional."""
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    src = request.form if request.form else (request.get_json(silent=True) or {})
    truck_id_raw = str(src.get("truck_id") or "")
    if not truck_id_raw.isdigit():
        return jsonify({"error": "truck is required"}), 400
    conn = get_db()
    truck = _load_truck_scoped(conn, int(truck_id_raw), active_only=True)
    if truck is None:
        conn.close()
        return jsonify({"error": "truck not found"}), 404
    entry_date = (str(src.get("entry_date") or "").strip()) or today_str()
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", entry_date):
        conn.close()
        return jsonify({"error": "date must be YYYY-MM-DD"}), 400
    category = str(src.get("category") or "").strip()
    if category not in MAINTENANCE_CATEGORIES:
        conn.close()
        return jsonify({"error": "invalid category"}), 400
    description = str(src.get("description") or "").strip()[:1000]
    if not description:
        conn.close()
        return jsonify({"error": "a description is required"}), 400
    cost_cents, cost_err = parse_cost_cents(src.get("cost"))
    if cost_err:
        conn.close()
        return jsonify({"error": cost_err}), 400
    vendor_id = _clean_vendor_id(conn, src.get("vendor_id"))
    # Optional: log it already "sent to vendor" (flags the truck at-vendor).
    sent = str(src.get("sent") or "").strip() in ("1", "true", "on", "yes")
    at_vendor = 1 if (sent and vendor_id) else 0
    cur = conn.cursor()
    cur.execute(
        """INSERT INTO maintenance_entries (company_id, truck_id, entry_date, category,
               description, cost_cents, vendor_id, at_vendor, sent_vendor_id, sent_at,
               created_by, created_at)
           VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""",
        (cid(), truck["id"], entry_date, category, description, cost_cents, vendor_id,
         at_vendor, (vendor_id if at_vendor else None), (now_ts() if at_vendor else None),
         session["user_id"], now_ts()),
    )
    entry_id = cur.lastrowid
    _save_maintenance_receipts(conn, request.files.getlist("receipts"), manual_entry_id=entry_id)
    if at_vendor:
        _recompute_truck_at_vendor(conn, truck["id"])
    conn.commit()
    conn.close()
    return jsonify({"success": True, "id": entry_id})


def _load_manual_entry(conn, entry_id):
    return conn.execute(
        "SELECT * FROM maintenance_entries WHERE id=? AND company_id=?",
        (entry_id, cid()),
    ).fetchone()


def _entry_editable(entry):
    """A manual entry is editable by owner/dispatcher only within the edit
    window after creation, and never once voided."""
    if entry["voided"]:
        return False
    try:
        created = datetime.strptime(entry["created_at"], "%Y-%m-%d %H:%M:%S")
    except (ValueError, TypeError):
        return False
    now = datetime.strptime(now_ts(), "%Y-%m-%d %H:%M:%S")
    return (now - created).total_seconds() <= MAINTENANCE_EDIT_WINDOW_SECONDS


@app.route("/api/maintenance/entries/<int:entry_id>/edit", methods=["POST"])
@login_required
def edit_maintenance_entry(entry_id):
    """Edit a manual entry — owner/dispatcher, only within the edit window."""
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    conn = get_db()
    entry = _load_manual_entry(conn, entry_id)
    if entry is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    if not _entry_editable(entry):
        conn.close()
        return jsonify({"error": "this entry is locked (edit window has passed or it is voided)"}), 409
    src = request.form if request.form else (request.get_json(silent=True) or {})
    entry_date = (str(src.get("entry_date") or "").strip()) or entry["entry_date"]
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", entry_date):
        conn.close()
        return jsonify({"error": "date must be YYYY-MM-DD"}), 400
    category = str(src.get("category") or "").strip()
    if category not in MAINTENANCE_CATEGORIES:
        conn.close()
        return jsonify({"error": "invalid category"}), 400
    description = str(src.get("description") or "").strip()[:1000]
    if not description:
        conn.close()
        return jsonify({"error": "a description is required"}), 400
    cost_cents, cost_err = parse_cost_cents(src.get("cost"))
    if cost_err:
        conn.close()
        return jsonify({"error": cost_err}), 400
    vendor_id = _clean_vendor_id(conn, src.get("vendor_id"))
    conn.execute(
        """UPDATE maintenance_entries SET entry_date=?, category=?, description=?,
               cost_cents=?, vendor_id=?, updated_at=? WHERE id=?""",
        (entry_date, category, description, cost_cents, vendor_id, now_ts(), entry_id),
    )
    _save_maintenance_receipts(conn, request.files.getlist("receipts"), manual_entry_id=entry_id)
    conn.commit()
    conn.close()
    return jsonify({"success": True})


@app.route("/api/maintenance/entries/<int:entry_id>/send", methods=["POST"])
@login_required
def send_maintenance_entry(entry_id):
    """Mark a manual entry 'sent to [vendor]' — flags the truck at-vendor."""
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    conn = get_db()
    entry = _load_manual_entry(conn, entry_id)
    if entry is None or entry["voided"]:
        conn.close()
        return jsonify({"error": "not found"}), 404
    src = request.form if request.form else (request.get_json(silent=True) or {})
    vendor_id = _clean_vendor_id(conn, src.get("vendor_id"))
    conn.execute(
        """UPDATE maintenance_entries SET at_vendor=1, sent_vendor_id=?, sent_at=?,
               vendor_id=COALESCE(?, vendor_id), completed_at=NULL WHERE id=?""",
        (vendor_id, now_ts(), vendor_id, entry_id),
    )
    _recompute_truck_at_vendor(conn, entry["truck_id"])
    conn.commit()
    conn.close()
    return jsonify({"success": True})


@app.route("/api/maintenance/entries/<int:entry_id>/back", methods=["POST"])
@login_required
def back_maintenance_entry(entry_id):
    """Mark a sent manual entry back/repaired — clears the truck at-vendor flag."""
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    conn = get_db()
    entry = _load_manual_entry(conn, entry_id)
    if entry is None or entry["voided"]:
        conn.close()
        return jsonify({"error": "not found"}), 404
    conn.execute(
        "UPDATE maintenance_entries SET at_vendor=0, completed_at=? WHERE id=?",
        (now_ts(), entry_id),
    )
    _recompute_truck_at_vendor(conn, entry["truck_id"])
    conn.commit()
    conn.close()
    return jsonify({"success": True})


@app.route("/api/maintenance/entries/<int:entry_id>/void", methods=["POST"])
@login_required
def void_maintenance_entry(entry_id):
    """Void (never delete) a manual entry — owner/dispatcher, required note.
    Voided entries drop out of spend totals and are flagged in the log."""
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    src = request.form if request.form else (request.get_json(silent=True) or {})
    note = str(src.get("note") or "").strip()[:500]
    if not note:
        return jsonify({"error": "a note is required to void"}), 400
    conn = get_db()
    entry = _load_manual_entry(conn, entry_id)
    if entry is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    if entry["voided"]:
        conn.close()
        return jsonify({"error": "already voided"}), 409
    conn.execute(
        "UPDATE maintenance_entries SET voided=1, void_note=?, voided_by=?, voided_at=? WHERE id=?",
        (note, session["user_id"], now_ts(), entry_id),
    )
    _recompute_truck_at_vendor(conn, entry["truck_id"])
    conn.commit()
    conn.close()
    return jsonify({"success": True})


# ── Vendors CRUD (owner/dispatcher manage; any management views) ──────────
@app.route("/vendors")
@roles_required("owner", "customer_manager", "dispatcher")
def vendors_page():
    conn = get_db()
    vendors = _company_vendors(conn)
    conn.close()
    can_action = _can_action_fleet()
    rows = ""
    for v in vendors:
        sub = " · ".join(b for b in [e(v["phone"] or ""), e(v["notes"] or "")] if b)
        del_btn = (f'<button class="btn secondary" style="padding:4px 12px;font-size:12px;" '
                   f'onclick="delVendor({v["id"]})">Remove</button>') if can_action else ""
        rows += f"""
        <div class="bin-card" id="vendor-{v['id']}" style="padding:14px;display:flex;justify-content:space-between;align-items:center;gap:10px;">
            <div><div style="font-weight:700;">{e(v["name"])}</div>
                 <div style="color:var(--slate);font-size:13px;">{sub or "—"}</div></div>
            {del_btn}
        </div>"""
    if not vendors:
        rows = '<div class="empty-state" style="padding:24px 0;">No vendors yet.</div>'
    add = ""
    if can_action:
        add = """
        <div style="max-width:640px;margin-bottom:16px;">
            <button class="btn green" onclick="toggleAddVendor()">+ Add vendor</button>
            <div id="add-vendor-form" hidden class="bin-card" style="padding:16px;margin-top:12px;">
                <div id="add-vendor-err" hidden style="color:#FF5252;font-size:12px;margin-bottom:8px;"></div>
                <label class="uw-lbl">Name</label>
                <input id="vn-name" style="width:100%;margin-bottom:10px;" placeholder="Bob's Truck Repair">
                <label class="uw-lbl">Phone (optional)</label>
                <input id="vn-phone" style="width:100%;margin-bottom:10px;" placeholder="757-555-0100">
                <label class="uw-lbl">Notes (optional)</label>
                <input id="vn-notes" style="width:100%;margin-bottom:12px;" placeholder="Account #1234">
                <div style="display:flex;gap:8px;">
                    <button class="btn green" style="flex:1;" onclick="submitVendor()">Save</button>
                    <button class="btn secondary" onclick="toggleAddVendor()">Cancel</button>
                </div>
            </div>
        </div>"""
    body = f"""
    <div class="hero" style="display:flex;justify-content:space-between;align-items:flex-start;gap:12px;">
        <div><h1 style="margin-bottom:4px;">Vendors</h1><p style="margin:0;">Shops &amp; accounts you send trucks to.</p></div>
        <a class="btn secondary" href="{url_for('maintenance_page')}" style="white-space:nowrap;">← Maintenance</a>
    </div>
    {add}
    <div class="bin-list" style="display:grid;gap:10px;max-width:640px;">{rows}</div>
    <style>.uw-lbl{{display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;}}</style>
    {_VENDORS_PAGE_JS}
    """
    return render_template_string(shell_page("Vendors", body))


_VENDORS_PAGE_JS = """
<script>
(function(){
  var CSRF=(document.querySelector('meta[name=csrf-token]')||{}).content||'';
  window.toggleAddVendor=function(){ var f=document.getElementById('add-vendor-form'); if(f) f.hidden=!f.hidden; };
  function verr(m){ var e=document.getElementById('add-vendor-err'); if(e){ e.textContent=m; e.hidden=false; } }
  window.submitVendor=function(){
    var name=(document.getElementById('vn-name')||{}).value||'';
    if(!name.trim()){ verr('A name is required.'); return; }
    fetch('/api/vendors',{method:'POST',headers:{'Content-Type':'application/json','X-CSRF-Token':CSRF},
        body:JSON.stringify({name:name,phone:(document.getElementById('vn-phone')||{}).value||'',notes:(document.getElementById('vn-notes')||{}).value||''})})
      .then(function(r){ return r.json().then(function(j){ return {ok:r.ok,j:j}; }); })
      .then(function(res){ if(res.ok){ window.location.reload(); } else { verr((res.j&&res.j.error)||'Could not save.'); } })
      .catch(function(){ verr('Network error — try again.'); });
  };
  window.delVendor=function(id){
    if(!confirm('Remove this vendor? Past records keep its name.')) return;
    fetch('/api/vendors/'+id+'/deactivate',{method:'POST',headers:{'Content-Type':'application/json','X-CSRF-Token':CSRF}})
      .then(function(r){ return r.json().then(function(j){ return {ok:r.ok,j:j}; }); })
      .then(function(res){ if(res.ok){ var c=document.getElementById('vendor-'+id); if(c) c.remove(); } else { alert((res.j&&res.j.error)||'Could not remove.'); } })
      .catch(function(){ alert('Network error — try again.'); });
  };
})();
</script>
"""


@app.route("/api/vendors", methods=["POST"])
@login_required
def create_vendor():
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    data = request.get_json(silent=True) or {}
    name = str(data.get("name") or "").strip()[:120]
    if not name:
        return jsonify({"error": "a name is required"}), 400
    conn = get_db()
    cur = conn.cursor()
    cur.execute(
        "INSERT INTO vendors (company_id, name, phone, notes, is_active, created_at) VALUES (?,?,?,?,1,?)",
        (cid(), name, str(data.get("phone") or "").strip()[:50] or None,
         str(data.get("notes") or "").strip()[:200] or None, now_ts()),
    )
    vid = cur.lastrowid
    conn.commit()
    conn.close()
    return jsonify({"success": True, "id": vid})


@app.route("/api/vendors/<int:vendor_id>/deactivate", methods=["POST"])
@login_required
def deactivate_vendor(vendor_id):
    if not _can_action_fleet():
        return jsonify({"error": "forbidden"}), 403
    conn = get_db()
    row = conn.execute("SELECT id FROM vendors WHERE id=? AND company_id=?", (vendor_id, cid())).fetchone()
    if row is None:
        conn.close()
        return jsonify({"error": "not found"}), 404
    conn.execute("UPDATE vendors SET is_active=0 WHERE id=?", (vendor_id,))
    conn.commit()
    conn.close()
    return jsonify({"success": True})


@app.route("/maintenance/entry/<int:entry_id>")
@roles_required("owner", "customer_manager", "dispatcher")
def maintenance_entry_detail(entry_id):
    """Full detail of a manual maintenance entry. Any management role views;
    owner/dispatcher can edit (within the window) or void."""
    conn = get_db()
    entry = _load_manual_entry(conn, entry_id)
    if entry is None:
        conn.close()
        flash("Maintenance entry not found.", "error")
        return redirect(url_for("maintenance_page"))
    truck = conn.execute("SELECT id, name, out_of_service, at_vendor FROM trucks WHERE id=? AND company_id=?",
                         (entry["truck_id"], cid())).fetchone()
    receipts = _maintenance_receipts(conn, manual_entry_id=entry_id)
    creator = conn.execute("SELECT COALESCE(full_name, username) AS n FROM users WHERE id=?",
                           (entry["created_by"],)).fetchone()
    vendors = _company_vendors(conn)
    vmap = _vendor_map(conn)
    conn.close()

    ed = dict(entry)
    entry_vendor_name = vmap.get(ed.get("vendor_id"))
    entry_at_vendor = ed.get("at_vendor") and not entry["voided"]

    can_action = _can_action_fleet()
    editable = can_action and _entry_editable(entry)
    truck_link = (f'<a href="{url_for("truck_detail_page", truck_id=truck["id"])}" style="color:inherit;">🚛 {e(truck["name"])}{_truck_status_badges(truck)}</a>'
                  if truck else "—")
    # Send-to-vendor / mark-back controls (owner/dispatcher, non-voided).
    sent_ui = ""
    if can_action and not entry["voided"]:
        if entry_at_vendor:
            sent_ui = (f'<div style="max-width:640px;margin-bottom:12px;">'
                       f'<div style="color:#F5B43C;font-size:13px;font-weight:700;margin-bottom:6px;">🔧 At '
                       f'{e(entry_vendor_name or "vendor")}</div>'
                       f'<button class="btn green" style="width:100%;" onclick="markBack()">Mark back / repaired</button></div>')
        else:
            _vo = _vendor_options_html(vendors, selected_id=ed.get("vendor_id"))
            sent_ui = (f'<div class="bin-card" style="padding:14px;max-width:640px;margin-bottom:12px;">'
                       f'<label class="uw-lbl">Send truck to a vendor</label>'
                       f'<div style="display:flex;gap:8px;"><select id="snd-vendor" style="flex:1;">{_vo}</select>'
                       f'<button class="btn secondary" onclick="markSent()">Send</button></div></div>')
    voided_banner = ""
    if entry["voided"]:
        voided_banner = f"""
        <div class="bin-card" style="padding:14px;max-width:640px;margin-bottom:12px;border:1px solid rgba(255,82,82,0.45);">
            <div style="color:#FF7A7A;font-weight:800;">VOIDED</div>
            <div style="font-size:13px;color:#C9C9C2;margin-top:4px;">{e(entry["void_note"] or "")}</div>
            <div style="font-size:12px;color:var(--slate);margin-top:4px;">{e(entry["voided_at"] or "")}</div>
        </div>"""

    edit_ui = ""
    if editable:
        cat_opts = "".join(
            f'<option value="{e(c)}"{" selected" if c==entry["category"] else ""}>{e(c)}</option>'
            for c in MAINTENANCE_CATEGORIES)
        cost_val = "" if entry["cost_cents"] is None else f'{entry["cost_cents"]//100}.{entry["cost_cents"]%100:02d}'
        edit_ui = f"""
        <div style="max-width:640px;margin-bottom:12px;display:flex;gap:8px;">
            <button class="btn secondary" style="flex:1;" onclick="toggleEdit()">Edit</button>
            <button class="btn red" style="flex:1;" onclick="voidEntry()">Void</button>
        </div>
        <div id="edit-form" hidden class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
            <div id="edit-err" hidden style="color:#FF5252;font-size:12px;margin-bottom:8px;"></div>
            <div style="display:flex;gap:8px;">
                <div style="flex:1;"><label class="uw-lbl">Date</label><input id="ed-date" type="date" value="{e(entry["entry_date"])}" style="width:100%;"></div>
                <div style="flex:1;"><label class="uw-lbl">Category</label><select id="ed-cat" style="width:100%;">{cat_opts}</select></div>
            </div>
            <label class="uw-lbl" style="margin-top:10px;">Description</label>
            <textarea id="ed-desc" rows="2" style="width:100%;margin-bottom:8px;">{e(entry["description"])}</textarea>
            <label class="uw-lbl">Vendor</label>
            <select id="ed-vendor" style="width:100%;margin-bottom:8px;">{_vendor_options_html(vendors, selected_id=ed.get("vendor_id"))}</select>
            <details style="margin-bottom:10px;">
                <summary style="color:var(--slate);font-size:12px;cursor:pointer;">Cost / receipt (optional)</summary>
                <div style="margin-top:8px;">
                    <label class="uw-lbl">Cost</label><input id="ed-cost" inputmode="decimal" value="{cost_val}" style="width:100%;margin-bottom:8px;">
                    <label class="uw-lbl">Add receipt photo(s)</label>
                    <input id="ed-receipts" type="file" accept=".png,.jpg,.jpeg,.webp,.pdf" multiple capture="environment" style="width:100%;">
                </div>
            </details>
            <div style="display:flex;gap:8px;">
                <button class="btn green" style="flex:1;" onclick="submitEdit()">Save</button>
                <button class="btn secondary" onclick="toggleEdit()">Cancel</button>
            </div>
        </div>"""
    elif can_action and not entry["voided"]:
        edit_ui = ('<div style="max-width:640px;margin-bottom:12px;">'
                   '<div style="color:var(--slate);font-size:12px;margin-bottom:8px;">Edit window has passed — this entry is locked. It can still be voided.</div>'
                   '<button class="btn red" style="width:100%;" onclick="voidEntry()">Void</button></div>')

    body = f"""
    <div class="hero" style="display:flex;justify-content:space-between;align-items:flex-start;gap:12px;">
        <div><h1 style="margin-bottom:4px;">Maintenance</h1><p style="margin:0;">{truck_link}</p></div>
        <a class="btn secondary" href="{url_for('truck_detail_page', truck_id=entry['truck_id'])}" style="white-space:nowrap;">← Truck</a>
    </div>
    {voided_banner}
    <div class="bin-card" style="padding:16px;max-width:640px;margin-bottom:12px;">
        <div style="display:flex;justify-content:space-between;gap:10px;">
            <span style="font-weight:800;font-size:16px;">{e(entry["entry_date"])} · {e(entry["category"])}</span>
            {('<span style="font-weight:800;font-size:16px;">' + e(format_cents(entry["cost_cents"])) + '</span>') if entry["cost_cents"] is not None else ''}
        </div>
        <div style="color:#C9C9C2;font-size:14px;margin-top:8px;">{e(entry["description"])}</div>
        <div style="color:var(--slate);font-size:13px;margin-top:8px;">
            {('Vendor: ' + e(entry_vendor_name) + '<br>') if entry_vendor_name else ''}
            Logged by {e(creator["n"] if creator else "—")} · {e(entry["created_at"])}
        </div>
        {_receipt_thumbs_html(receipts)}
    </div>
    {sent_ui}
    {edit_ui}
    <style>.uw-lbl{{display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;}}</style>
    {_maintenance_entry_js(entry_id, entry["truck_id"])}
    """
    return render_template_string(shell_page("Maintenance", body))


def _maintenance_entry_js(entry_id, truck_id):
    truck_url = url_for("truck_detail_page", truck_id=truck_id)
    return f"""
<script>
(function(){{
  var CSRF=(document.querySelector('meta[name=csrf-token]')||{{}}).content||'';
  var EID={entry_id};
  window.toggleEdit=function(){{ var f=document.getElementById('edit-form'); if(f) f.hidden=!f.hidden; }};
  function eerr(m){{ var e=document.getElementById('edit-err'); if(e){{ e.textContent=m; e.hidden=false; }} }}
  window.submitEdit=function(){{
    var desc=(document.getElementById('ed-desc')||{{}}).value||'';
    if(!desc.trim()){{ eerr('A description is required.'); return; }}
    var fd=new FormData();
    fd.append('_csrf_token', CSRF);
    fd.append('entry_date',(document.getElementById('ed-date')||{{}}).value||'');
    fd.append('category',(document.getElementById('ed-cat')||{{}}).value||'');
    fd.append('description',desc);
    fd.append('cost',(document.getElementById('ed-cost')||{{}}).value||'');
    fd.append('vendor_id',(document.getElementById('ed-vendor')||{{}}).value||'');
    var files=(document.getElementById('ed-receipts')||{{}}).files||[];
    for(var i=0;i<files.length;i++){{ fd.append('receipts', files[i]); }}
    fetch('/api/maintenance/entries/'+EID+'/edit',{{method:'POST',headers:{{'X-CSRF-Token':CSRF}},body:fd}})
      .then(function(r){{return r.json().then(function(j){{return {{ok:r.ok,j:j}};}});}})
      .then(function(res){{ if(res.ok){{ window.location.reload(); }} else {{ eerr((res.j&&res.j.error)||'Could not save.'); }} }})
      .catch(function(){{ eerr('Network error — try again.'); }});
  }};
  window.markSent=function(){{
    fetch('/api/maintenance/entries/'+EID+'/send',{{method:'POST',
        headers:{{'Content-Type':'application/json','X-CSRF-Token':CSRF}},
        body:JSON.stringify({{vendor_id:(document.getElementById('snd-vendor')||{{}}).value||''}})}})
      .then(function(r){{return r.json().then(function(j){{return {{ok:r.ok,j:j}};}});}})
      .then(function(res){{ if(res.ok){{ window.location.reload(); }} else {{ alert((res.j&&res.j.error)||'Could not update.'); }} }})
      .catch(function(){{ alert('Network error — try again.'); }});
  }};
  window.markBack=function(){{
    fetch('/api/maintenance/entries/'+EID+'/back',{{method:'POST',
        headers:{{'Content-Type':'application/json','X-CSRF-Token':CSRF}}}})
      .then(function(r){{return r.json().then(function(j){{return {{ok:r.ok,j:j}};}});}})
      .then(function(res){{ if(res.ok){{ window.location.reload(); }} else {{ alert((res.j&&res.j.error)||'Could not update.'); }} }})
      .catch(function(){{ alert('Network error — try again.'); }});
  }};
  window.voidEntry=function(){{
    var note=prompt('Void this entry? Add a note (required):');
    if(note===null) return;
    if(!note.trim()){{ alert('A note is required.'); return; }}
    fetch('/api/maintenance/entries/'+EID+'/void',{{method:'POST',
        headers:{{'Content-Type':'application/json','X-CSRF-Token':CSRF}},body:JSON.stringify({{note:note}})}})
      .then(function(r){{return r.json().then(function(j){{return {{ok:r.ok,j:j}};}});}})
      .then(function(res){{ if(res.ok){{ window.location.reload(); }} else {{ alert((res.j&&res.j.error)||'Could not void.'); }} }})
      .catch(function(){{ alert('Network error — try again.'); }});
  }};
}})();
</script>
"""


@app.route("/requests")
@roles_required("customer_manager")
def requests_page():
    """Customer_manager/owner: pending customer requests as accept/deny cards."""
    conn = get_db()
    reqs = conn.execute(
        """SELECT r.*,
                  c.business_name AS customer_business_name,
                  c.contact_name  AS customer_contact_name,
                  s.address       AS site_address,
                  b.size          AS bin_size
             FROM requests r
             JOIN customers c ON r.customer_id = c.id
             JOIN sites     s ON r.site_id     = s.id
        LEFT JOIN bins      b ON r.bin_id      = b.id
            WHERE c.company_id = ? AND r.status = 'pending'
            ORDER BY r.created_at DESC, r.id DESC""",
        (cid(),),
    ).fetchall()
    drivers = conn.execute(
        "SELECT id, username FROM users WHERE role='driver' AND company_id=? ORDER BY username",
        (cid(),),
    ).fetchall()
    conn.close()

    driver_options = '<option value="">Select driver…</option>' + "".join(
        f'<option value="{d["id"]}">{e(d["username"])}</option>' for d in drivers
    )

    # Only a user who also holds the dispatcher role (owner, or someone with
    # both roles) can schedule in one click — the solo-operator path. A
    # customer-manager-only user accepts, and a dispatcher assigns later.
    can_assign = has_role("dispatcher")

    _TYPE_LABEL = {"PR": "PR · Pull & Return", "P": "P · Pickup",
                   "D": "D · Drop", "NEW_BIN": "NEW BIN", "S": "S · Swap"}

    cards = ""
    for r in reqs:
        rid  = r["id"]
        name = e(r["customer_business_name"] or r["customer_contact_name"] or "Customer")
        addr = e(r["site_address"] or "—")
        size = r["bin_size"] if r["type"] in ("PR", "P") else r["size_requested"]
        size_html = f'<div style="color:var(--slate);font-size:13px;margin-top:2px;">{e(size)}</div>' if size else ""
        pref = r["preferred_date"]
        pref_label = "ASAP" if pref == "asap" else e(pref)
        default_date = today_str() if pref == "asap" else e(pref)
        notes_html = (
            f'<div style="margin-top:8px;padding:8px 10px;background:rgba(255,255,255,0.03);'
            f'border-radius:8px;font-size:13px;color:#C9C9C2;">{e(r["notes"])}</div>'
        ) if r["notes"] else ""
        type_badge = (
            f'<span style="display:inline-block;padding:3px 10px;border-radius:999px;'
            f'font-size:10px;font-weight:800;letter-spacing:.6px;text-transform:uppercase;'
            f'background:var(--cyan-dim);color:var(--cyan);border:1px solid var(--border-glow);">'
            f'{e(_TYPE_LABEL.get(r["type"], r["type"]))}</span>'
        )
        assign_btn = (
            f'<button class="btn green" style="flex:1;min-width:120px;" '
            f'onclick="showApprove({rid})">Accept &amp; Assign</button>'
        ) if can_assign else ""
        cards += f"""
        <div class="bin-card" id="req-card-{rid}" style="padding:16px;">
            <div style="display:flex;justify-content:space-between;align-items:center;gap:10px;">
                {type_badge}
                <span style="color:var(--slate);font-size:12px;white-space:nowrap;">📅 {pref_label}</span>
            </div>
            <div style="font-weight:700;font-size:15px;margin-top:8px;">{name}</div>
            <div style="color:var(--slate);font-size:13px;margin-top:2px;">📍 {addr}</div>
            {size_html}
            {notes_html}
            <div style="display:flex;gap:8px;margin-top:12px;flex-wrap:wrap;">
                <button class="btn green" style="flex:1;min-width:90px;" onclick="showAccept({rid})">Accept</button>
                {assign_btn}
                <button class="btn red" style="flex:1;min-width:90px;" onclick="showDeny({rid})">Deny</button>
            </div>
            <div id="err-{rid}" hidden style="color:#FF5252;font-size:12px;margin-top:8px;"></div>
            <div id="accept-form-{rid}" hidden style="margin-top:12px;border-top:1px solid var(--border);padding-top:12px;">
                <label style="display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;">Note to customer (optional)</label>
                <textarea id="note-{rid}" maxlength="500" rows="2" style="width:100%;margin-bottom:6px;" placeholder="e.g. We'll have you scheduled within a day or two."></textarea>
                <div style="font-size:12px;color:var(--slate);margin-bottom:12px;">Confirms the request without scheduling — it moves to Unassigned Work for a dispatcher to route.</div>
                <div style="display:flex;gap:8px;">
                    <button class="btn green" style="flex:1;" onclick="submitAccept({rid})">Confirm accept</button>
                    <button class="btn secondary" onclick="hideReqForms({rid})">Cancel</button>
                </div>
            </div>
            <div id="approve-form-{rid}" hidden style="margin-top:12px;border-top:1px solid var(--border);padding-top:12px;">
                <label style="display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;">Driver</label>
                <select id="drv-{rid}" style="width:100%;margin-bottom:10px;">{driver_options}</select>
                <label style="display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;">Scheduled date</label>
                <input type="date" id="date-{rid}" value="{default_date}" style="width:100%;margin-bottom:12px;">
                <div style="display:flex;gap:8px;">
                    <button class="btn green" style="flex:1;" onclick="submitApprove({rid})">Confirm &amp; schedule</button>
                    <button class="btn secondary" onclick="hideReqForms({rid})">Cancel</button>
                </div>
            </div>
            <div id="deny-form-{rid}" hidden style="margin-top:12px;border-top:1px solid var(--border);padding-top:12px;">
                <label style="display:block;font-size:11px;color:var(--slate);text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px;">Reason (optional)</label>
                <textarea id="reason-{rid}" maxlength="300" rows="2" style="width:100%;margin-bottom:12px;" placeholder="Why is this being denied?"></textarea>
                <div style="display:flex;gap:8px;">
                    <button class="btn red" style="flex:1;" onclick="submitDeny({rid})">Confirm deny</button>
                    <button class="btn secondary" onclick="hideReqForms({rid})">Cancel</button>
                </div>
            </div>
        </div>
        """

    accept_assign_hint = (
        "; <strong>Accept &amp; Assign</strong> schedules it to a driver in one step"
        if can_assign else ""
    )
    empty_hidden = "" if not reqs else " hidden"
    body = f"""
    <div class="hero">
        <h1>Requests</h1>
        <p>Customer requests awaiting your review. <strong>Accept</strong> confirms the job and sends it to Unassigned Work for scheduling{accept_assign_hint}.</p>
    </div>
    <div id="req-empty" class="empty-state" style="padding:32px 0;"{empty_hidden}>No pending requests.</div>
    <div id="req-list" class="bin-list" style="display:grid;gap:12px;max-width:640px;">
        {cards}
    </div>
    """ + _REQUESTS_PAGE_JS
    return render_template_string(shell_page("Requests", body))


# =========================================================
# DEBUG — temporary DB inspection route
# =========================================================
@app.route("/debug/db")
@superadmin_required
def debug_db():
    from flask import jsonify
    conn = get_db()
    total = conn.execute(
        "SELECT COUNT(*) FROM routes WHERE company_id=?", (cid(),)
    ).fetchone()[0]
    rows  = conn.execute(
        "SELECT id, route_date, route_name, status FROM routes WHERE company_id=? ORDER BY route_date DESC, id DESC",
        (cid(),)
    ).fetchall()
    conn.close()
    return jsonify({
        "total_routes":  total,
        "routes": [
            {"id": r["id"], "date": r["route_date"], "name": r["route_name"], "status": r["status"]}
            for r in rows
        ],
    })


# =========================================================
# STARTUP — initialize DB before gunicorn serves any request
# =========================================================

# =========================================================
# DISPATCH ROUTES — Firebase live dispatch feature
# =========================================================
@app.route('/dispatch')
def dispatch_view():
    return send_from_directory('static', 'dispatch.html')

@app.route('/route')
def route_view():
    return send_from_directory('static', 'route.html')

@app.route('/parser')
@roles_required("dispatcher")
def parser_view():
    route_id_arg = (request.args.get('route_id') or '').strip()
    route_mode_js = "null"
    route_seq_html = ""

    if route_id_arg.isdigit():
        if session.get("role") != "boss":
            abort(403)
        conn = get_db()
        route_row = conn.execute(
            """SELECT r.id, r.route_name, u.username AS driver_username
               FROM routes r LEFT JOIN users u ON r.assigned_to = u.id
               WHERE r.id=? AND r.company_id=?""",
            (int(route_id_arg), cid())
        ).fetchone()
        if not route_row:
            conn.close()
            abort(404)
        existing_stops = conn.execute(
            """SELECT id, address, city, action, status FROM stops
               WHERE route_id=? ORDER BY stop_order ASC, id ASC""",
            (route_row["id"],)
        ).fetchall()
        conn.close()

        current_stop_id = None
        for s in existing_stops:
            if s["status"] != "completed":
                current_stop_id = s["id"]
                break

        seq_rows_html = ""
        insertable_options = ""
        for s in existing_stops:
            letter, group = _board_action_badge(s["action"])
            addr_text = ", ".join(p for p in [s["address"] or "", s["city"] or ""] if p) or "Stop"
            is_locked = (s["status"] == "completed") or (s["id"] == current_stop_id)
            if s["status"] == "completed":
                state_label, state_cls = "Done", "seq-done"
            elif s["id"] == current_stop_id:
                state_label, state_cls = "Current", "seq-current"
            else:
                state_label, state_cls = "Pending", "seq-pending"
            seq_rows_html += (
                f'<div class="seq-row {state_cls}">'
                f'<span class="stop-mini-badge {group}">{e(letter)}</span>'
                f'<span class="seq-addr">{e(addr_text)}</span>'
                f'<span class="seq-state">{state_label}</span>'
                f'</div>'
            )
            if not is_locked:
                insertable_options += f'<option value="{s["id"]}">Before: {e(addr_text)}</option>'

        route_seq_html = f"""
        <div class="route-ctx-banner">
            <div class="route-ctx-title">Adding stops to {e(route_row['driver_username'] or 'Unassigned')}&rsquo;s route</div>
            <div class="route-ctx-sub">{e(route_row['route_name'])} &mdash; completed and in-progress stops are locked in place</div>
            <div class="seq-list">{seq_rows_html or '<div class="muted small">No stops yet.</div>'}</div>
        </div>
        """
        route_mode_js = json.dumps({
            "route_id": route_row["id"],
            "insert_options_html": insertable_options,
        })
        assign_html = f'<input type="hidden" id="insert-route-id" value="{route_row["id"]}">'
    else:
        conn = get_db()
        drivers = conn.execute(
            "SELECT id, username, full_name FROM users WHERE role='driver' AND company_id=? ORDER BY username",
            (cid(),)
        ).fetchall()
        conn.close()

        if drivers:
            options = "".join(
                f'<option value="{d["id"]}">{e(d["full_name"] or d["username"])}</option>'
                for d in drivers
            )
            assign_html = (
                '<label for="driver-select">Assign to</label>'
                '<select id="driver-select" class="driver-select">'
                f'<option value="">Select a driver&hellip;</option>{options}</select>'
            )
        else:
            assign_html = (
                '<div class="no-drivers-msg">No drivers yet &mdash; '
                f'<a href="{url_for("team_page")}">add one in Team</a>.</div>'
            )

    path = os.path.join(app.root_path, 'static', 'parser.html')
    with open(path, encoding='utf-8') as f:
        html = f.read()
    html = html.replace('__CSRF_TOKEN__', get_csrf_token())
    html = html.replace('<!--ASSIGN_SLOT-->', assign_html)
    html = html.replace('<!--ROUTE_SEQ_SLOT-->', route_seq_html)
    html = html.replace('__ROUTE_MODE_JSON__', route_mode_js)
    return html

# =========================================================
# CAPACITOR APP LINKS — Universal Links (iOS) / App Links (Android)
# so haultra-systems.com links open the app instead of a browser tab
# (see @capacitor/app in package.json and STORE_LAUNCH.md).
#
# PLACEHOLDER VALUES — these must be filled in with real credentials
# before deep-linking will actually work; until then these routes are
# harmless (the OS just won't verify the app for these domains):
#   - REPLACE_WITH_APPLE_TEAM_ID: your 10-character Apple Developer Team ID
#   - REPLACE_WITH_ANDROID_SHA256_FINGERPRINT: your release keystore's
#     SHA-256 signing certificate fingerprint
# See STORE_LAUNCH.md for exactly where to find both.
# =========================================================
@app.route('/.well-known/apple-app-site-association')
def apple_app_site_association():
    return jsonify({
        "applinks": {
            "apps": [],
            "details": [
                {
                    "appID": "REPLACE_WITH_APPLE_TEAM_ID.com.rockkstaar.haultra",
                    "paths": ["*"],
                }
            ],
        }
    })


@app.route('/.well-known/assetlinks.json')
def android_asset_links():
    return jsonify([
        {
            "relation": ["delegate_permission/common.handle_all_urls"],
            "target": {
                "namespace": "android_app",
                "package_name": "com.rockkstaar.haultra",
                "sha256_cert_fingerprints": ["REPLACE_WITH_ANDROID_SHA256_FINGERPRINT"],
            },
        }
    ])


init_db()
print("Startup complete. DATABASE_PATH =", DATABASE, flush=True)

# =========================================================
# RUN APP
# =========================================================
if __name__ == "__main__":
    debug = os.environ.get("FLASK_DEBUG", "0") == "1"
    port  = int(os.environ.get("PORT", 5001))
    app.run(host="0.0.0.0", port=port, debug=debug)
