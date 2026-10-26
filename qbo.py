"""QuickBooks Online invoice sync — v1.

HAULTRA is field truth; QuickBooks stays the official books. This module is
the bridge: it pushes a finished HAULTRA invoice into the boss's QuickBooks
company, once. It does NOT do accounting (no chart of accounts, no tax
engine, no payments) and never edits invoice creation, surcharge billing
flags, routes/stops, the parser, or the chain resolver.

Pieces:
  * OAuth 2.0 connect / callback / disconnect for the boss (one QuickBooks
    company per HAULTRA company). Tokens are encrypted at rest and
    auto-refreshed; Intuit rotates the refresh token, so every refresh
    stores the new one. Tokens are never logged or put in error messages.
  * Customer matching by name (case/space-insensitive). A QuickBooks
    customer is created only when no match exists; the QB customer ID is
    recorded per (company, QB company, name) so it is never created twice.
  * "Send to QuickBooks" on the invoice page. Pushes every line (surcharges
    stay their own lines, ticket number in the description), stores the QB
    invoice ID and sets qb_sync_status to synced / failed. An invoice that
    already has a QB invoice ID for the connected QB company is skipped.

Wiring (app.py): `qbo.init_tables(conn)` inside init_db, `qbo.init_app(...)`
once, `qbo.invoice_panel(d)` on the invoice page, `qbo.settings_card()` on
Settings.

Config (env vars only, never in code):
  QB_CLIENT_ID, QB_CLIENT_SECRET   Intuit app keys (Development = sandbox)
  QB_REDIRECT_URI                  must match the Intuit portal exactly
  QB_ENVIRONMENT                   "sandbox" (default) or "production"
  QB_TOKEN_KEY                     optional Fernet key for token encryption;
                                   when unset a key is derived from SECRET_KEY
"""
import base64
import hashlib
import logging
import os
import re
import secrets
import time
import urllib.parse
import uuid
from datetime import datetime, timezone

import requests
from flask import Blueprint, flash as _flask_flash, redirect, request, session, url_for

# Local dev: pick up a .env next to app.py. No-op on Render (no file there)
# and never overrides variables that are already set.
try:
    from dotenv import load_dotenv
    load_dotenv(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".env"),
                override=False)
except ImportError:  # pragma: no cover — python-dotenv is in requirements
    pass

log = logging.getLogger("haultra.qbo")

AUTH_URL = "https://appcenter.intuit.com/connect/oauth2"
TOKEN_URL = "https://oauth.platform.intuit.com/oauth2/v1/tokens/bearer"
REVOKE_URL = "https://developer.api.intuit.com/v2/oauth2/tokens/revoke"
API_BASE = {
    "sandbox": "https://sandbox-quickbooks.api.intuit.com",
    "production": "https://quickbooks.api.intuit.com",
}
SCOPE = "com.intuit.quickbooks.accounting"   # accounting only — never payments
MINOR_VERSION = "75"                         # Intuit requires >= 75
HTTP_TIMEOUT = 30
REFRESH_MARGIN_S = 300      # refresh the access token 5 min before it expires
SYNC_STALE_S = 180          # a 'syncing' claim older than this can be retried
SENDABLE_STATUSES = ("draft", "sent")

# Line kinds a boss can point at their own QuickBooks product/service.
# '*' is the required default; the rest are optional overrides.
ITEM_KINDS = (
    ("*", "Default (all lines)"),
    ("haul", "Haul / delivery / pull / swap"),
    ("overage", "Tonnage overage"),
    ("surcharge", "Landfill surcharge"),
    ("fee", "Field fees"),
    ("extra_day", "Extra days"),
    ("custom", "Other / custom lines"),
)
_KIND_ALIASES = {"delivery": "haul", "swap": "haul", "pull": "haul"}

_deps = {}


# ─────────────────────────────────────────────────────────────────────────────
# Errors
# ─────────────────────────────────────────────────────────────────────────────
class QBError(Exception):
    """A sync problem with a boss-readable message (never contains tokens)."""


class QBNotConnected(QBError):
    pass


class QBAuthError(QBError):
    def __init__(self, code, tid=None):
        super().__init__(f"QuickBooks sign-in error ({code})")
        self.code = code
        self.tid = tid


class QBApiError(QBError):
    def __init__(self, message, status=None, code=None, tid=None):
        super().__init__(message)
        self.status = status
        self.code = code
        self.tid = tid


# ─────────────────────────────────────────────────────────────────────────────
# Config
# ─────────────────────────────────────────────────────────────────────────────
def _env(name):
    return (os.environ.get(name) or "").strip()


def environment():
    return "production" if _env("QB_ENVIRONMENT").lower() == "production" else "sandbox"


def is_configured():
    return bool(_env("QB_CLIENT_ID") and _env("QB_CLIENT_SECRET") and _env("QB_REDIRECT_URI"))


def _client_auth():
    return (_env("QB_CLIENT_ID"), _env("QB_CLIENT_SECRET"))


def _fernet():
    from cryptography.fernet import Fernet
    key = _env("QB_TOKEN_KEY")
    if key:
        return Fernet(key.encode())
    secret = os.environ.get("SECRET_KEY", "")
    if not secret:
        raise QBError("Set QB_TOKEN_KEY (or SECRET_KEY) so QuickBooks tokens can be stored encrypted.")
    derived = base64.urlsafe_b64encode(
        hashlib.sha256(b"haultra-qbo-token-key:" + secret.encode()).digest())
    return Fernet(derived)


def _enc(value):
    return _fernet().encrypt(value.encode()).decode()


def _dec(value):
    from cryptography.fernet import InvalidToken
    try:
        return _fernet().decrypt((value or "").encode()).decode()
    except (InvalidToken, ValueError):
        raise QBNotConnected("Stored QuickBooks connection can't be read (key changed). Reconnect QuickBooks.")


def _now():
    return int(time.time())


def _nobraces(text):
    """App pages are rendered with render_template_string, so text that came
    from QuickBooks (names, error details) must never carry Jinja syntax."""
    return (text or "").replace("{", "(").replace("}", ")")


def flash(message, category="message"):
    _flask_flash(_nobraces(message), category)


def _utc_stamp():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")


# ─────────────────────────────────────────────────────────────────────────────
# Schema — called from app.init_db() after the invoices table exists
# ─────────────────────────────────────────────────────────────────────────────
_INVOICE_QB_COLUMNS = (
    ("qb_invoice_id", "TEXT"),
    ("qb_realm_id", "TEXT"),
    ("qb_doc_number", "TEXT"),
    ("qb_sync_error", "TEXT"),
    ("qb_synced_at", "TEXT"),
    ("qb_synced_total_cents", "INTEGER"),   # HAULTRA total at the moment of push
    ("qb_total_cents", "INTEGER"),          # total QuickBooks reported back
    ("qb_sync_started_at", "INTEGER"),      # epoch; guards double-taps / two workers
)


def init_tables(conn):
    conn.execute("""
    CREATE TABLE IF NOT EXISTS qb_connections (
        company_id         INTEGER PRIMARY KEY,
        realm_id           TEXT NOT NULL,
        environment        TEXT NOT NULL,
        company_name       TEXT NOT NULL DEFAULT '',
        access_token_enc   TEXT,
        refresh_token_enc  TEXT,
        access_expires_at  INTEGER NOT NULL DEFAULT 0,
        refresh_expires_at INTEGER NOT NULL DEFAULT 0,
        status             TEXT NOT NULL DEFAULT 'connected',
        connected_by       INTEGER,
        connected_at       INTEGER,
        updated_at         INTEGER
    )""")
    conn.execute("""
    CREATE TABLE IF NOT EXISTS qb_customer_map (
        company_id      INTEGER NOT NULL,
        realm_id        TEXT NOT NULL,
        name_key        TEXT NOT NULL,
        qb_customer_id  TEXT NOT NULL,
        qb_display_name TEXT NOT NULL DEFAULT '',
        created_at      INTEGER,
        PRIMARY KEY (company_id, realm_id, name_key)
    )""")
    conn.execute("""
    CREATE TABLE IF NOT EXISTS qb_item_map (
        company_id INTEGER NOT NULL,
        realm_id   TEXT NOT NULL,
        kind       TEXT NOT NULL,
        item_id    TEXT NOT NULL,
        item_name  TEXT NOT NULL DEFAULT '',
        PRIMARY KEY (company_id, realm_id, kind)
    )""")
    # Connect-from-the-app handoff. The native app's WebView holds the HAULTRA
    # login, but Intuit's sign-in opens in the system browser, which doesn't.
    # A single-use, short-lived handoff (stored hashed) carries "which company
    # started this" to the callback, and the person who approved at Intuit must
    # confirm the HAULTRA company name in that same browser before tokens are
    # saved (the confirm secret only ever appears in that browser).
    conn.execute("""
    CREATE TABLE IF NOT EXISTS qb_oauth_handoff (
        token_hash      TEXT PRIMARY KEY,
        company_id      INTEGER NOT NULL,
        user_id         INTEGER,
        stage           TEXT NOT NULL DEFAULT 'started',
        created_at      INTEGER NOT NULL,
        expires_at      INTEGER NOT NULL,
        realm_id        TEXT,
        qb_company_name TEXT NOT NULL DEFAULT '',
        tokens_enc      TEXT,
        nonce_hash      TEXT,
        auth_expires_at INTEGER
    )""")
    have = {r[1] for r in conn.execute("PRAGMA table_info(invoices)").fetchall()}
    for col, ddl in _INVOICE_QB_COLUMNS:
        if col not in have:
            conn.execute(f"ALTER TABLE invoices ADD COLUMN {col} {ddl}")


# ─────────────────────────────────────────────────────────────────────────────
# Tokens
# ─────────────────────────────────────────────────────────────────────────────
def _safe_json(resp):
    try:
        return resp.json()
    except ValueError:
        return {}


def _token_request(data):
    """POST to Intuit's token endpoint. Errors carry only the OAuth error
    code and intuit_tid — never the response body (it can hold tokens)."""
    resp = requests.post(TOKEN_URL, data=data, auth=_client_auth(),
                         headers={"Accept": "application/json"}, timeout=HTTP_TIMEOUT)
    tid = resp.headers.get("intuit_tid")
    if resp.status_code != 200:
        code = _safe_json(resp).get("error") or f"HTTP {resp.status_code}"
        log.warning("qbo token request failed: %s (intuit_tid=%s)", code, tid)
        raise QBAuthError(code, tid)
    body = _safe_json(resp)
    if not body.get("access_token") or not body.get("refresh_token"):
        raise QBAuthError("malformed token response", tid)
    return body


def _write_tokens(conn, company_id, tok):
    now = _now()
    conn.execute(
        """UPDATE qb_connections SET access_token_enc=?, refresh_token_enc=?,
               access_expires_at=?, refresh_expires_at=?, status='connected', updated_at=?
           WHERE company_id=?""",
        (_enc(tok["access_token"]), _enc(tok["refresh_token"]),
         now + int(tok.get("expires_in") or 3600),
         now + int(tok.get("x_refresh_token_expires_in") or 0),
         now, company_id))


def connection(conn, company_id):
    """The company's QuickBooks connection row as a dict, or None."""
    row = conn.execute("SELECT * FROM qb_connections WHERE company_id=?", (company_id,)).fetchone()
    return dict(row) if row else None


def usable_connection(conn, company_id):
    """Connection that matches the configured environment and is connected."""
    c = connection(conn, company_id)
    if not c or c["status"] != "connected" or c["environment"] != environment():
        return None
    return c


def get_access_token(get_db, company_id):
    """(access_token, realm_id, environment). Refreshes when close to expiry.

    The refresh runs under BEGIN IMMEDIATE so two gunicorn workers can't both
    spend the same refresh token — Intuit rotates it, and a second use of a
    rotated token would disconnect the company."""
    conn = get_db()
    try:
        c = connection(conn, company_id)
        if not c or c["status"] != "connected":
            raise QBNotConnected("QuickBooks isn't connected. Connect it in Settings → QuickBooks.")
        if c["environment"] != environment():
            raise QBNotConnected(
                f"QuickBooks is connected to {c['environment']}, but HAULTRA is set to "
                f"{environment()}. Reconnect QuickBooks.")
        if c["access_expires_at"] - _now() > REFRESH_MARGIN_S:
            return _dec(c["access_token_enc"]), c["realm_id"], c["environment"]

        conn.execute("BEGIN IMMEDIATE")
        c = connection(conn, company_id)        # re-read under the write lock
        if not c or c["status"] != "connected":
            conn.rollback()
            raise QBNotConnected("QuickBooks isn't connected. Connect it in Settings → QuickBooks.")
        if c["access_expires_at"] - _now() > REFRESH_MARGIN_S:
            conn.rollback()                     # another worker just refreshed
            return _dec(c["access_token_enc"]), c["realm_id"], c["environment"]
        try:
            tok = _token_request({"grant_type": "refresh_token",
                                  "refresh_token": _dec(c["refresh_token_enc"])})
        except QBAuthError as ex:
            if ex.code == "invalid_grant":
                conn.execute(
                    """UPDATE qb_connections SET status='reconnect_needed', access_token_enc=NULL,
                           refresh_token_enc=NULL, access_expires_at=0, updated_at=?
                       WHERE company_id=?""", (_now(), company_id))
                conn.commit()
                raise QBNotConnected("The QuickBooks connection expired or was revoked. Reconnect QuickBooks.")
            conn.rollback()
            raise
        except Exception:
            conn.rollback()
            raise
        _write_tokens(conn, company_id, tok)
        conn.commit()
        log.info("qbo access token refreshed for company %s", company_id)
        return tok["access_token"], c["realm_id"], c["environment"]
    finally:
        conn.close()


def _save_connection(get_db, company_id, realm, tok, user_id):
    """Store a fresh connection + tokens, then look up the QB company name.
    Returns the company name ('' if the lookup failed)."""
    conn = get_db()
    try:
        conn.execute(
            """INSERT INTO qb_connections (company_id, realm_id, environment, status,
                   connected_by, connected_at, updated_at)
               VALUES (?, ?, ?, 'connected', ?, ?, ?)
               ON CONFLICT(company_id) DO UPDATE SET realm_id=excluded.realm_id,
                   environment=excluded.environment, status='connected', company_name='',
                   connected_by=excluded.connected_by, connected_at=excluded.connected_at,
                   updated_at=excluded.updated_at""",
            (company_id, realm, environment(), user_id, _now(), _now()))
        _write_tokens(conn, company_id, tok)
        conn.commit()
    finally:
        conn.close()
    name = ""
    try:
        name = QBClient(get_db, company_id).company_info(realm).get("CompanyName") or ""
        conn = get_db()
        try:
            conn.execute("UPDATE qb_connections SET company_name=? WHERE company_id=?",
                         (_nobraces(name), company_id))
            conn.commit()
        finally:
            conn.close()
    except Exception as ex:
        log.warning("qbo companyinfo lookup failed: %s", type(ex).__name__)
    log.info("qbo connected company %s to realm %s (%s)", company_id, realm, environment())
    return name


def _company_name_with_token(access_token, realm):
    """CompanyInfo lookup before a connection row exists (handoff confirm page)."""
    try:
        resp = requests.get(
            f"{API_BASE[environment()]}/v3/company/{realm}/companyinfo/{realm}",
            params={"minorversion": MINOR_VERSION}, timeout=HTTP_TIMEOUT,
            headers={"Authorization": f"Bearer {access_token}", "Accept": "application/json"})
        if resp.status_code == 200:
            return ((_safe_json(resp).get("CompanyInfo") or {}).get("CompanyName") or "")
    except Exception as ex:
        log.warning("qbo companyinfo (handoff) failed: %s", type(ex).__name__)
    return ""


def _revoke(refresh_token):
    try:
        requests.post(REVOKE_URL, json={"token": refresh_token}, auth=_client_auth(),
                      headers={"Accept": "application/json"}, timeout=HTTP_TIMEOUT)
    except Exception as ex:   # best effort
        log.warning("qbo revoke failed: %s", type(ex).__name__)


def _hash(value):
    return hashlib.sha256((value or "").encode()).hexdigest()


HANDOFF_PREFIX = "h."
HANDOFF_TTL_S = 900        # app tap → Intuit approval
HANDOFF_CONFIRM_TTL_S = 600  # Intuit approval → confirm tap


def _expire_access_token(get_db, company_id):
    conn = get_db()
    try:
        conn.execute("UPDATE qb_connections SET access_expires_at=0 WHERE company_id=?", (company_id,))
        conn.commit()
    finally:
        conn.close()


# ─────────────────────────────────────────────────────────────────────────────
# API client
# ─────────────────────────────────────────────────────────────────────────────
def _fault_message(body, status):
    errs = ((body or {}).get("Fault") or {}).get("Error") or []
    if errs:
        e0 = errs[0]
        msg = e0.get("Message") or "QuickBooks error"
        detail = e0.get("Detail") or ""
        return (f"{msg}: {detail}" if detail and detail != msg else msg), str(e0.get("code") or "")
    return f"QuickBooks returned HTTP {status}", ""


def q_escape(value):
    """Escape a value for a QuickBooks query string literal."""
    return (value or "").replace("\\", "\\\\").replace("'", "\\'")


class QBClient:
    def __init__(self, get_db, company_id):
        self.get_db = get_db
        self.company_id = company_id

    def _request(self, method, path, params=None, json_body=None, _retried=False):
        token, realm, env = get_access_token(self.get_db, self.company_id)
        url = f"{API_BASE[env]}/v3/company/{realm}/{path}"
        p = dict(params or {})
        p["minorversion"] = MINOR_VERSION
        resp = requests.request(
            method, url, params=p, json=json_body, timeout=HTTP_TIMEOUT,
            headers={"Authorization": f"Bearer {token}", "Accept": "application/json",
                     "Content-Type": "application/json"})
        tid = resp.headers.get("intuit_tid")
        if resp.status_code == 401 and not _retried:
            _expire_access_token(self.get_db, self.company_id)
            return self._request(method, path, params, json_body, _retried=True)
        if resp.status_code >= 400:
            msg, code = _fault_message(_safe_json(resp), resp.status_code)
            log.warning("qbo %s %s -> %s code=%s (intuit_tid=%s)",
                        method, path.split("?")[0], resp.status_code, code, tid)
            raise QBApiError(msg, resp.status_code, code, tid)
        return _safe_json(resp)

    @property
    def realm_id(self):
        return get_access_token(self.get_db, self.company_id)[1]

    def query(self, q):
        return self._request("GET", "query", params={"query": q}).get("QueryResponse") or {}

    def create(self, entity, payload, requestid=None):
        params = {"requestid": requestid} if requestid else None
        body = self._request("POST", entity.lower(), params=params, json_body=payload)
        return body.get(entity[0].upper() + entity[1:]) or {}

    def company_info(self, realm_id):
        return self._request("GET", f"companyinfo/{realm_id}").get("CompanyInfo") or {}


# ─────────────────────────────────────────────────────────────────────────────
# Customers
# ─────────────────────────────────────────────────────────────────────────────
def display_name(name):
    return re.sub(r"\s+", " ", (name or "").strip())


def name_key(name):
    return display_name(name).casefold()


def _find_customer(client, name, op="="):
    key = name_key(name)
    rows = client.query(
        f"select Id, DisplayName, Active from Customer where DisplayName {op} "
        f"'{q_escape(display_name(name))}' and Active in (true, false)").get("Customer") or []
    for r in rows:
        if name_key(r.get("DisplayName")) == key:
            return r
    return None


def resolve_customer(client, conn, company_id, realm_id, name):
    """QB customer ID for this HAULTRA customer name. Map → find → create."""
    key = name_key(name)
    if not key:
        raise QBError("This invoice has no customer name.")
    row = conn.execute(
        "SELECT qb_customer_id FROM qb_customer_map WHERE company_id=? AND realm_id=? AND name_key=?",
        (company_id, realm_id, key)).fetchone()
    if row:
        return row["qb_customer_id"]

    found = _find_customer(client, name)
    if not found:
        try:
            found = client.create("Customer", {"DisplayName": display_name(name)[:500]})
        except QBApiError as ex:
            if ex.code != "6240":        # 6240 = Duplicate Name Exists
                raise
            found = _find_customer(client, name, op="like")
            if not found:
                raise QBError(
                    f'QuickBooks already uses the name "{display_name(name)}" for a vendor, '
                    "employee, or other name. Rename the customer (here or in QuickBooks) and retry.")
    if not found.get("Id"):
        raise QBError("QuickBooks didn't return a customer ID.")
    conn.execute(
        """INSERT OR IGNORE INTO qb_customer_map
           (company_id, realm_id, name_key, qb_customer_id, qb_display_name, created_at)
           VALUES (?, ?, ?, ?, ?, ?)""",
        (company_id, realm_id, key, str(found["Id"]), found.get("DisplayName") or "", _now()))
    conn.commit()
    if found.get("Active") is False:
        raise QBError(f'Customer "{found.get("DisplayName")}" is inactive in QuickBooks. '
                      "Make it active in QuickBooks, then retry.")
    return str(found["Id"])


# ─────────────────────────────────────────────────────────────────────────────
# Products / services
# ─────────────────────────────────────────────────────────────────────────────
def list_items(client):
    rows = client.query("select * from Item where Active = true maxresults 1000").get("Item") or []
    items = [{"id": str(r["Id"]), "name": r.get("FullyQualifiedName") or r.get("Name") or "",
              "type": r.get("Type") or ""}
             for r in rows if r.get("Type") in ("Service", "NonInventory")]
    return sorted(items, key=lambda i: i["name"].casefold())


def item_map(conn, company_id, realm_id):
    return {r["kind"]: dict(r) for r in conn.execute(
        "SELECT kind, item_id, item_name FROM qb_item_map WHERE company_id=? AND realm_id=?",
        (company_id, realm_id)).fetchall()}


def _item_for(mapping, kind):
    kind = _KIND_ALIASES.get(kind, kind)
    hit = mapping.get(kind) or mapping.get("*")
    return hit["item_id"] if hit else None


# ─────────────────────────────────────────────────────────────────────────────
# Invoice push
# ─────────────────────────────────────────────────────────────────────────────
def _marker(company_id, invoice_id):
    return f"HAULTRA-SYNC c{company_id} i{invoice_id}"


def _valid_day(s):
    try:
        datetime.strptime(s or "", "%Y-%m-%d")
        return True
    except ValueError:
        return False


def _money(cents):
    return round(int(cents or 0) / 100.0, 2)


def build_invoice_payload(inv, lines, customer_id, mapping, company_id):
    out_lines = []
    for ln in lines:
        item_id = _item_for(mapping, ln["kind"] or "custom")
        if not item_id:
            raise QBError("Pick a default QuickBooks product/service on the QuickBooks settings page first.")
        amount = int(ln["amount_cents"] or 0)
        qty = float(ln["qty"] or 0)
        unit = int(ln["unit_cents"] or 0)
        if not (qty > 0 and round(qty * unit) == amount):
            qty, unit = 1, amount       # keep Qty × UnitPrice == Amount, as QB requires
        out_lines.append({
            "DetailType": "SalesItemLineDetail",
            "Amount": _money(amount),
            "Description": (ln["description"] or "")[:4000],
            "SalesItemLineDetail": {
                "ItemRef": {"value": item_id},
                "Qty": qty,
                "UnitPrice": _money(unit),
                "TaxCodeRef": {"value": "NON"},   # HAULTRA doesn't do tax
            },
        })
    payload = {
        "CustomerRef": {"value": customer_id},
        "DocNumber": (inv["invoice_number"] or "")[:21],
        "PrivateNote": _marker(company_id, inv["id"]),
        "Line": out_lines,
    }
    if _valid_day(inv["issued_at"]):
        payload["TxnDate"] = inv["issued_at"]
    if _valid_day(inv["due_at"]):
        payload["DueDate"] = inv["due_at"]
    if (inv["notes"] or "").strip():
        payload["CustomerMemo"] = {"value": inv["notes"].strip()[:1000]}
    return payload


def _find_pushed_invoice(client, customer_id, company_id, invoice_id):
    """An invoice this HAULTRA invoice already created in QB (e.g. QB saved
    it but the response was lost) — found by the marker in PrivateNote."""
    mark = _marker(company_id, invoice_id)
    rows = client.query(
        f"select * from Invoice where CustomerRef = '{q_escape(customer_id)}' "
        "orderby MetaData.CreateTime desc maxresults 100").get("Invoice") or []
    for r in rows:
        if (r.get("PrivateNote") or "").startswith(mark):
            return r
    return None


def _cents(amount):
    try:
        return int(round(float(amount) * 100))
    except (TypeError, ValueError):
        return None


def push_invoice(get_db, company_id, invoice_id):
    """Send one invoice to QuickBooks. Returns (category, message) for flash.

    Never pushes the same invoice twice: an existing QB invoice ID for the
    connected QB company short-circuits; a DB claim stops double-taps and
    parallel workers; and before creating, QB is searched for an invoice this
    one already made (lost-response case)."""
    conn = get_db()
    try:
        conn_row = usable_connection(conn, company_id)
        if not conn_row:
            return "error", "Connect QuickBooks first (Settings → QuickBooks)."
        realm = conn_row["realm_id"]
        inv = conn.execute("SELECT * FROM invoices WHERE id=? AND company_id=?",
                           (invoice_id, company_id)).fetchone()
        if not inv:
            return "error", "Invoice not found."
        if inv["qb_invoice_id"] and inv["qb_realm_id"] == realm:
            return "info", f"Already in QuickBooks (invoice #{inv['qb_doc_number'] or inv['qb_invoice_id']}) — skipped."
        if inv["status"] not in SENDABLE_STATUSES:
            return "error", "Only draft or sent invoices can be sent to QuickBooks."

        now = _now()
        claimed = conn.execute(
            """UPDATE invoices SET qb_sync_status='syncing', qb_sync_started_at=?, qb_sync_error=NULL
               WHERE id=? AND company_id=?
                 AND NOT (qb_invoice_id IS NOT NULL AND qb_realm_id = ?)
                 AND (qb_sync_status != 'syncing' OR COALESCE(qb_sync_started_at, 0) < ?)""",
            (now, invoice_id, company_id, realm, now - SYNC_STALE_S)).rowcount
        conn.commit()
        if not claimed:
            return "info", "This invoice is already being sent to QuickBooks — refresh in a moment."

        try:
            lines = conn.execute(
                "SELECT * FROM invoice_line_items WHERE invoice_id=? ORDER BY sort_order, id",
                (invoice_id,)).fetchall()
            if not lines:
                raise QBError("This invoice has no lines to send.")
            mapping = item_map(conn, company_id, realm)
            if not mapping.get("*"):
                raise QBError("Pick a default QuickBooks product/service on the QuickBooks settings page first.")
            client = QBClient(get_db, company_id)
            cust_id = resolve_customer(client, conn, company_id, realm, inv["customer_name"])
            qb_inv = _find_pushed_invoice(client, cust_id, company_id, invoice_id)
            recovered = bool(qb_inv)
            if not qb_inv:
                payload = build_invoice_payload(inv, lines, cust_id, mapping, company_id)
                qb_inv = client.create("Invoice", payload, requestid=uuid.uuid4().hex)
            if not qb_inv.get("Id"):
                raise QBError("QuickBooks didn't return an invoice ID.")
        except Exception as ex:
            _mark_failed(conn, invoice_id, ex)
            return "error", "QuickBooks sync failed: " + _failure_text(ex)

        pushed_total = sum(int(ln["amount_cents"] or 0) for ln in lines)
        qb_total = _cents(qb_inv.get("TotalAmt"))
        conn.execute(
            """UPDATE invoices SET qb_sync_status='synced', qb_invoice_id=?, qb_realm_id=?,
                   qb_doc_number=?, qb_sync_error=NULL, qb_synced_at=?, qb_synced_total_cents=?,
                   qb_total_cents=?, qb_sync_started_at=NULL
               WHERE id=?""",
            (str(qb_inv["Id"]), realm, qb_inv.get("DocNumber") or "", _utc_stamp(),
             pushed_total, qb_total, invoice_id))
        conn.commit()
        log.info("qbo invoice %s pushed for company %s (qb id %s%s)",
                 invoice_id, company_id, qb_inv["Id"], ", recovered" if recovered else "")
        if qb_total is not None and qb_total != pushed_total:
            return "warning", (f"Sent to QuickBooks, but QuickBooks shows {_fmt(qb_total)} vs HAULTRA "
                               f"{_fmt(pushed_total)} — check sales tax on it in QuickBooks.")
        return "success", "Sent to QuickBooks."
    finally:
        conn.close()


def _failure_text(ex):
    if isinstance(ex, QBError):
        return str(ex)
    if isinstance(ex, requests.RequestException):
        return ("Couldn't reach QuickBooks. Retry — HAULTRA checks QuickBooks first, "
                "so a retry won't create a duplicate.")
    return "Unexpected error. Retry, and if it keeps failing, contact support."


def _mark_failed(conn, invoice_id, ex):
    msg = _failure_text(ex)
    tid = getattr(ex, "tid", None)
    if tid:
        msg += f" (Intuit ref {tid})"
    if not isinstance(ex, (QBError, requests.RequestException)):
        log.error("qbo push of invoice %s failed: %s", invoice_id, type(ex).__name__)
    conn.execute(
        """UPDATE invoices SET qb_sync_status='failed', qb_sync_error=?, qb_sync_started_at=NULL
           WHERE id=?""", (_nobraces(msg)[:1000], invoice_id))
    conn.commit()


def _fmt(cents):
    fn = _deps.get("fmt_money")
    return fn(cents) if fn else "$%.2f" % (int(cents or 0) / 100.0)


# ─────────────────────────────────────────────────────────────────────────────
# UI fragments (rendered inside app.py pages)
# ─────────────────────────────────────────────────────────────────────────────
def _esc(v):
    return _deps["e"](v).replace("{", "&#123;").replace("}", "&#125;")


def _csrf_field():
    return f'<input type="hidden" name="_csrf_token" value="{_esc(_deps["csrf_token"]())}">'


def invoice_panel(inv):
    """QuickBooks block for the invoice detail page. `inv` is the invoice dict."""
    try:
        return _invoice_panel(inv)
    except Exception:
        log.exception("qbo invoice panel failed")
        return '<p class="muted small" style="margin-top:12px;">QuickBooks: status unavailable.</p>'


def _invoice_panel(inv):
    if not is_configured():
        return '<p class="muted small" style="margin-top:12px;">QuickBooks sync isn\'t set up on this server.</p>'
    conn = _deps["get_db"]()
    try:
        c = usable_connection(conn, inv["company_id"])
    finally:
        conn.close()
    settings_link = url_for("qbo.settings")
    wrap = '<div style="margin-top:14px;padding-top:12px;border-top:1px solid rgba(255,255,255,0.08);">{}</div>'
    if not c:
        return wrap.format(f'<p class="muted small">QuickBooks: not connected. '
                           f'<a href="{settings_link}">Connect QuickBooks</a> to send invoices.</p>')

    def send_btn(label):
        return (f'<form class="inline" method="POST" action="{url_for("qbo.invoice_push", invoice_id=inv["id"])}">'
                f'{_csrf_field()}<button class="btn gold" type="submit">{label}</button></form>')

    status = inv.get("qb_sync_status") or "not_synced"
    synced_here = bool(inv.get("qb_invoice_id")) and inv.get("qb_realm_id") == c["realm_id"]
    if synced_here:
        notes = []
        pushed = inv.get("qb_synced_total_cents")
        qb_total = inv.get("qb_total_cents")
        if qb_total is not None and pushed is not None and qb_total != pushed:
            notes.append(f"QuickBooks total is {_fmt(qb_total)} vs HAULTRA {_fmt(pushed)} — "
                         "check sales tax on it in QuickBooks.")
        if pushed is not None and (inv.get("total_cents") or 0) != pushed:
            notes.append("Lines changed in HAULTRA after it was sent. HAULTRA won't push it again — "
                         "update the invoice in QuickBooks.")
        if inv.get("status") == "void":
            notes.append("Voided in HAULTRA — void it in QuickBooks too.")
        warn = "".join(f'<p class="small" style="color:#FF9D5C;margin:6px 0 0;">&#9888; {_esc(n)}</p>'
                       for n in notes)
        return wrap.format(
            f'<p class="small" style="margin:0;"><span class="badge completed">In QuickBooks</span> '
            f'Invoice #{_esc(inv.get("qb_doc_number") or inv.get("qb_invoice_id"))} &middot; '
            f'<span class="muted">synced {_esc(inv.get("qb_synced_at") or "")}</span></p>{warn}')

    if inv.get("status") not in SENDABLE_STATUSES:
        return wrap.format('<p class="muted small">QuickBooks: only draft or sent invoices can be sent.</p>')
    if status == "syncing" and (inv.get("qb_sync_started_at") or 0) > _now() - SYNC_STALE_S:
        return wrap.format('<p class="muted small">Sending to QuickBooks… refresh in a moment.</p>')
    if status == "failed":
        return wrap.format(
            f'<p class="small" style="color:#FF6B6B;margin:0 0 8px;"><strong>QuickBooks sync failed:</strong> '
            f'{_esc(inv.get("qb_sync_error") or "unknown error")}</p>{send_btn("Retry")}')
    elsewhere = ('<p class="muted small" style="margin:0 0 8px;">Previously sent to a different QuickBooks '
                 'company (e.g. the sandbox).</p>' if inv.get("qb_invoice_id") else "")
    return wrap.format(f'{elsewhere}{send_btn("Send to QuickBooks")}')


def settings_card():
    """Small status card for the Settings page; details live on /quickbooks."""
    try:
        if not is_configured():
            state = "Not set up on this server (QB_CLIENT_ID / QB_CLIENT_SECRET / QB_REDIRECT_URI)."
        else:
            conn = _deps["get_db"]()
            try:
                c = connection(conn, _deps["cid"]())
            finally:
                conn.close()
            if c and c["status"] == "connected" and c["environment"] == environment():
                state = f"Connected to {_esc(c['company_name'] or c['realm_id'])} ({c['environment']})."
            elif c:
                state = "Needs reconnecting."
            else:
                state = "Not connected."
        return f"""
    <div class="card" id="quickbooks" style="margin-top:8px;">
        <h2 style="margin:0 0 4px;">QuickBooks</h2>
        <p class="muted small" style="margin-bottom:12px;">Send finished invoices to QuickBooks Online. QuickBooks stays your books.</p>
        <p style="margin:0 0 12px;">{state}</p>
        <a class="btn secondary" href="{url_for('qbo.settings')}">QuickBooks settings</a>
    </div>"""
    except Exception:
        log.exception("qbo settings card failed")
        return ""


# ─────────────────────────────────────────────────────────────────────────────
# Routes
# ─────────────────────────────────────────────────────────────────────────────
def init_app(app, *, get_db, cid, boss_required, shell_page, csrf_token, e, fmt_money,
             is_native=None, csrf_exempt=None):
    is_native = is_native or (lambda: False)
    _deps.update(get_db=get_db, cid=cid, boss_required=boss_required, shell_page=shell_page,
                 csrf_token=csrf_token, e=e, fmt_money=fmt_money, is_native=is_native)
    if csrf_exempt is not None:
        # Finished in the system browser, which has no HAULTRA session/CSRF
        # cookie; it's protected by the single-use handoff + confirm secret.
        csrf_exempt.add("qbo.handoff_finish")
    bp = Blueprint("qbo", __name__)

    def boss(fn):
        return boss_required(fn)

    def render(title, body):
        from flask import render_template_string
        return render_template_string(shell_page(title, body))

    @bp.route("/quickbooks")
    @boss
    def settings():
        body = _settings_page_body(get_db, cid())
        return render("QuickBooks", body)

    @bp.route("/quickbooks/connect", methods=["POST"])
    @boss
    def connect():
        if not is_configured():
            flash("QuickBooks isn't set up on this server yet.", "error")
            return redirect(url_for("qbo.settings"))
        if is_native():
            # Intuit opens in the system browser, outside the app's login.
            token = secrets.token_urlsafe(32)
            conn = get_db()
            try:
                conn.execute("DELETE FROM qb_oauth_handoff WHERE expires_at < ?", (_now() - 86400,))
                conn.execute(
                    """INSERT INTO qb_oauth_handoff (token_hash, company_id, user_id, stage,
                           created_at, expires_at) VALUES (?, ?, ?, 'started', ?, ?)""",
                    (_hash(token), cid(), session.get("user_id"), _now(), _now() + HANDOFF_TTL_S))
                conn.commit()
            finally:
                conn.close()
            state = HANDOFF_PREFIX + token
        else:
            state = secrets.token_urlsafe(24)
            session["qbo_oauth"] = {"state": state, "company_id": cid(), "ts": _now()}
        q = urllib.parse.urlencode({
            "client_id": _env("QB_CLIENT_ID"), "response_type": "code", "scope": SCOPE,
            "redirect_uri": _env("QB_REDIRECT_URI"), "state": state})
        return redirect(f"{AUTH_URL}?{q}")

    @bp.route("/quickbooks/callback")
    def callback():
        state = request.args.get("state", "")
        if state.startswith(HANDOFF_PREFIX):
            return _handoff_callback(get_db, state[len(HANDOFF_PREFIX):])
        return boss_required(_session_callback)()

    def _session_callback():
        pending = session.pop("qbo_oauth", None) or {}
        state = request.args.get("state", "")
        if (not pending or not state or not secrets.compare_digest(state, pending.get("state", ""))
                or pending.get("company_id") != cid() or _now() - int(pending.get("ts") or 0) > 900):
            flash("QuickBooks connection couldn't be verified. Please try again.", "error")
            return redirect(url_for("qbo.settings"))
        if request.args.get("error"):
            flash("QuickBooks connection was cancelled.", "info")
            return redirect(url_for("qbo.settings"))
        code, realm = request.args.get("code", ""), request.args.get("realmId", "")
        if not code or not realm:
            flash("QuickBooks didn't return a company. Please try again.", "error")
            return redirect(url_for("qbo.settings"))
        try:
            tok = _token_request({"grant_type": "authorization_code", "code": code,
                                  "redirect_uri": _env("QB_REDIRECT_URI")})
        except QBError as ex:
            flash(f"QuickBooks connection failed: {ex}", "error")
            return redirect(url_for("qbo.settings"))
        name = _save_connection(get_db, cid(), realm, tok, session.get("user_id"))
        flash(f"QuickBooks connected{(' to ' + name) if name else ''}. "
              "Next: pick the product/service invoice lines should use.", "success")
        return redirect(url_for("qbo.settings"))

    @bp.route("/quickbooks/handoff/<token>", methods=["POST"])
    def handoff_finish(token):
        return _handoff_finish(get_db, token)

    @bp.route("/quickbooks/disconnect", methods=["POST"])
    @boss
    def disconnect():
        conn = get_db()
        try:
            c = connection(conn, cid())
            if c and c.get("refresh_token_enc"):
                try:
                    requests.post(REVOKE_URL, json={"token": _dec(c["refresh_token_enc"])},
                                  auth=_client_auth(), headers={"Accept": "application/json"},
                                  timeout=HTTP_TIMEOUT)
                except Exception as ex:   # best effort; the local tokens are deleted regardless
                    log.warning("qbo revoke failed: %s", type(ex).__name__)
            conn.execute("DELETE FROM qb_connections WHERE company_id=?", (cid(),))
            conn.commit()
        finally:
            conn.close()
        flash("QuickBooks disconnected.", "success")
        return redirect(url_for("qbo.settings"))

    @bp.route("/quickbooks/items", methods=["POST"])
    @boss
    def save_items():
        conn = get_db()
        try:
            c = usable_connection(conn, cid())
            if not c:
                flash("Connect QuickBooks first.", "error")
                return redirect(url_for("qbo.settings"))
            try:
                items = {i["id"]: i["name"] for i in list_items(QBClient(get_db, cid()))}
            except QBError as ex:
                flash(f"Couldn't load QuickBooks products/services: {ex}", "error")
                return redirect(url_for("qbo.settings"))
            default = request.form.get("item_*", "")
            if default not in items:
                flash("Pick a default product/service.", "error")
                return redirect(url_for("qbo.settings"))
            conn.execute("DELETE FROM qb_item_map WHERE company_id=? AND realm_id=?", (cid(), c["realm_id"]))
            for kind, _label in ITEM_KINDS:
                item_id = request.form.get(f"item_{kind}", "")
                if item_id in items:
                    conn.execute(
                        "INSERT INTO qb_item_map (company_id, realm_id, kind, item_id, item_name) VALUES (?,?,?,?,?)",
                        (cid(), c["realm_id"], kind, item_id, items[item_id]))
            conn.commit()
        finally:
            conn.close()
        flash("QuickBooks products/services saved.", "success")
        return redirect(url_for("qbo.settings"))

    @bp.route("/invoices/<int:invoice_id>/quickbooks", methods=["POST"])
    @boss
    def invoice_push(invoice_id):
        category, message = push_invoice(get_db, cid(), invoice_id)
        flash(message, category)
        return redirect(url_for("invoice_detail", invoice_id=invoice_id))

    app.register_blueprint(bp)
    return bp


# ─────────────────────────────────────────────────────────────────────────────
# Connect from the native app (finished in the system browser)
# ─────────────────────────────────────────────────────────────────────────────
def _browser_page(title, body_html, status=200):
    """Standalone page for the system browser (no HAULTRA session there).
    Plain HTML response, never rendered as a template."""
    from flask import Response
    html = f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{_esc(title)} · HAULTRA</title>
<style>
 body{{margin:0;background:#121212;color:#F2F2EC;font:16px/1.5 -apple-system,system-ui,sans-serif;}}
 main{{max-width:460px;margin:0 auto;padding:40px 20px;}}
 h1{{font-size:24px;margin:0 0 12px;}} p{{color:#C9C9BF;}} strong{{color:#fff;}}
 .card{{background:#1E1E1E;border:1px solid #3a2a1e;border-radius:16px;padding:20px;margin-top:16px;}}
 button{{width:100%;min-height:52px;border-radius:12px;border:0;font-size:17px;font-weight:700;margin-top:12px;}}
 .go{{background:#C8692F;color:#111;}} .no{{background:#2a2a2a;color:#eee;}}
 .muted{{color:#8f8f86;font-size:14px;}}
</style></head><body><main>{body_html}</main></body></html>"""
    return Response(html, status=status, mimetype="text/html",
                    headers={"Cache-Control": "no-store", "Referrer-Policy": "no-referrer"})


_BACK_TO_APP = ('<p class="muted">If this page is in Safari, go back to the HAULTRA app '
                '(tap <strong>&#9664; HAULTRA</strong> at the top left).</p>'
                '<p><a href="/quickbooks" style="color:#E08A4F;font-weight:700;">'
                'Open QuickBooks settings &rarr;</a></p>')

# In the native app. The app owns every haultra-systems.com link (universal /
# app links), so Intuit's redirect back to /quickbooks/callback can reopen the
# app instead of finishing in Safari. Capacitor reports that as appUrlOpen but
# doesn't load it, so load it here (same-site /quickbooks/ paths only). If the
# user simply switches back, reload so the page shows the new status.
# No doubled braces: this text goes through render_template_string.
_APP_RETURN_SCRIPT = """<script>
(function () {
  var t = null, going = false;
  var cap = window.Capacitor && window.Capacitor.Plugins && window.Capacitor.Plugins.App;
  if (cap && cap.addListener) {
    cap.addListener('appUrlOpen', function (ev) {
      try {
        var u = new URL(ev && ev.url);
        if (u.host === location.host && u.pathname.indexOf('/quickbooks/') === 0) {
          // The link can arrive before or after the page becomes visible;
          // either way, never let the return-reload replace it.
          going = true;
          if (t) { clearTimeout(t); t = null; }
          location.replace(u.pathname + u.search);
        }
      } catch (e) {}
    });
  }
  document.addEventListener('visibilitychange', function () {
    if (document.hidden || going) { return; }
    if (t) { clearTimeout(t); }
    t = setTimeout(function () { if (!going) { location.reload(); } }, 2500);
  });
})();
</script>"""


def _handoff_row(conn, token):
    row = conn.execute("SELECT * FROM qb_oauth_handoff WHERE token_hash=?", (_hash(token),)).fetchone()
    return dict(row) if row else None


def _company_label(conn, company_id):
    try:
        r = conn.execute("SELECT name FROM companies WHERE id=?", (company_id,)).fetchone()
        return (r[0] if r else "") or f"company #{company_id}"
    except Exception:
        return f"company #{company_id}"


def _handoff_callback(get_db, token):
    """Intuit redirected the system browser back. Exchange the code, hold the
    tokens encrypted, and ask this browser to confirm the HAULTRA company."""
    expired = _browser_page("Link expired", "<h1>That link expired</h1><p>Open the HAULTRA app and "
                            "tap <strong>Connect QuickBooks</strong> again.</p>", 400)
    conn = get_db()
    try:
        row = _handoff_row(conn, token) if token else None
        if not row or row["expires_at"] < _now():
            log.warning("qbo handoff callback: unknown or expired handoff")
            return expired
        log.info("qbo handoff callback reached for company %s (stage %s)", row["company_id"], row["stage"])
        claimed = conn.execute(
            "UPDATE qb_oauth_handoff SET stage='authorizing' WHERE token_hash=? AND stage='started'",
            (_hash(token),)).rowcount
        conn.commit()
        if not claimed:
            log.warning("qbo handoff callback: already used (stage %s)", row["stage"])
            return expired
        if request.args.get("error"):
            conn.execute("UPDATE qb_oauth_handoff SET stage='cancelled' WHERE token_hash=?", (_hash(token),))
            conn.commit()
            return _browser_page("Cancelled", "<h1>QuickBooks wasn't connected</h1>"
                                 "<p>You cancelled on Intuit's page.</p>" + _BACK_TO_APP)
        code, realm = request.args.get("code", ""), request.args.get("realmId", "")
        if not code or not realm:
            conn.execute("UPDATE qb_oauth_handoff SET stage='failed' WHERE token_hash=?", (_hash(token),))
            conn.commit()
            return _browser_page("Try again", "<h1>QuickBooks didn't return a company</h1>"
                                 "<p>Go back to the app and tap Connect QuickBooks again.</p>", 400)
        try:
            tok = _token_request({"grant_type": "authorization_code", "code": code,
                                  "redirect_uri": _env("QB_REDIRECT_URI")})
        except QBError as ex:
            conn.execute("UPDATE qb_oauth_handoff SET stage='failed' WHERE token_hash=?", (_hash(token),))
            conn.commit()
            return _browser_page("Connection failed", f"<h1>QuickBooks connection failed</h1>"
                                 f"<p>{_esc(ex)}</p>" + _BACK_TO_APP, 400)
        import json
        qb_name = _nobraces(_company_name_with_token(tok["access_token"], realm))
        nonce = secrets.token_urlsafe(24)
        conn.execute(
            """UPDATE qb_oauth_handoff SET stage='authorized', realm_id=?, qb_company_name=?,
                   tokens_enc=?, nonce_hash=?, auth_expires_at=? WHERE token_hash=?""",
            (realm, qb_name, _enc(json.dumps({k: tok[k] for k in (
                "access_token", "refresh_token", "expires_in", "x_refresh_token_expires_in") if k in tok})),
             _hash(nonce), _now() + HANDOFF_CONFIRM_TTL_S, _hash(token)))
        conn.commit()
        log.info("qbo handoff authorized for company %s; waiting for confirm", row["company_id"])
        haultra_name = _company_label(conn, row["company_id"])
    finally:
        conn.close()

    action = url_for("qbo.handoff_finish", token=token)
    hidden = f'<input type="hidden" name="nonce" value="{_esc(nonce)}">'
    body = f"""<h1>Connect QuickBooks?</h1>
<div class="card">
 <p>QuickBooks company<br><strong>{_esc(qb_name or 'Your QuickBooks company')}</strong></p>
 <p>will send invoices from HAULTRA account<br><strong>{_esc(haultra_name)}</strong></p>
</div>
<p class="muted">Only continue if this is your HAULTRA company. If you didn't start this from your
own HAULTRA app, tap Cancel.</p>
<form method="POST" action="{action}">{hidden}<input type="hidden" name="action" value="confirm">
 <button class="go" type="submit">Connect</button></form>
<form method="POST" action="{action}">{hidden}<input type="hidden" name="action" value="cancel">
 <button class="no" type="submit">Cancel</button></form>"""
    return _browser_page("Connect QuickBooks", body)


def _handoff_finish(get_db, token):
    """Confirm or cancel in the system browser. Needs the confirm secret that
    was only shown on the page Intuit redirected this browser to."""
    import json
    expired = _browser_page("Link expired", "<h1>That link expired</h1><p>Open the HAULTRA app and "
                            "tap <strong>Connect QuickBooks</strong> again.</p>", 400)
    nonce = request.form.get("nonce", "")
    conn = get_db()
    try:
        row = _handoff_row(conn, token)
        if (not row or row["stage"] != "authorized" or (row["auth_expires_at"] or 0) < _now()
                or not nonce or not secrets.compare_digest(_hash(nonce), row["nonce_hash"] or "")):
            return expired
        claimed = conn.execute(
            "UPDATE qb_oauth_handoff SET stage='finishing' WHERE token_hash=? AND stage='authorized'",
            (_hash(token),)).rowcount
        conn.commit()
        if not claimed:
            return expired
        tok = json.loads(_dec(row["tokens_enc"]))
        if request.form.get("action") != "confirm":
            _revoke(tok.get("refresh_token", ""))
            conn.execute("UPDATE qb_oauth_handoff SET stage='cancelled', tokens_enc=NULL WHERE token_hash=?",
                         (_hash(token),))
            conn.commit()
            return _browser_page("Cancelled", "<h1>QuickBooks wasn't connected</h1>" + _BACK_TO_APP)
        conn.execute("UPDATE qb_oauth_handoff SET stage='done', tokens_enc=NULL WHERE token_hash=?",
                     (_hash(token),))
        conn.commit()
        company_id, user_id, realm = row["company_id"], row["user_id"], row["realm_id"]
    finally:
        conn.close()
    name = _save_connection(get_db, company_id, realm, tok, user_id)
    log.info("qbo handoff confirmed for company %s", company_id)
    return _browser_page("Connected", f"<h1>&#10003; QuickBooks connected</h1>"
                         f"<p>{_esc(name or 'Your QuickBooks company')} is connected to HAULTRA.</p>"
                         + _BACK_TO_APP)


def _settings_page_body(get_db, company_id):
    hero = """<div class="hero"><h1>QuickBooks</h1>
    <p>Send finished HAULTRA invoices to QuickBooks Online. QuickBooks stays your official books.</p></div>"""
    if not is_configured():
        return hero + """<div class="card"><p>QuickBooks isn't set up on this server yet. The server
        needs <code>QB_CLIENT_ID</code>, <code>QB_CLIENT_SECRET</code> and <code>QB_REDIRECT_URI</code>.</p></div>"""

    conn = get_db()
    try:
        raw = connection(conn, company_id)
        c = usable_connection(conn, company_id)
        mapping = item_map(conn, company_id, c["realm_id"]) if c else {}
    finally:
        conn.close()

    env_badge = f'<span class="badge">{_esc(environment().title())}</span>'
    connect_form = (f'<form class="inline" method="POST" action="{url_for("qbo.connect")}">{_csrf_field()}'
                    '<button class="btn gold" type="submit">{label}</button></form>')
    if not c:
        msg = "Not connected."
        if raw and raw["status"] != "connected":
            msg = "The QuickBooks connection expired or was revoked."
        elif raw and raw["environment"] != environment():
            msg = f"Connected to {raw['environment']}, but this server is set to {environment()}."
        app_note, app_script = "", ""
        if _deps.get("is_native", lambda: False)():
            app_note = ('<p class="muted small">Intuit opens in your browser. Approve there, tap '
                        '<strong>Connect</strong> on the HAULTRA confirm page, then come back here.</p>')
            app_script = _APP_RETURN_SCRIPT
        return hero + f"""<div class="card"><p>{env_badge} {msg}</p>
            <p class="muted small">You'll sign in to Intuit and choose which QuickBooks company to connect.
            HAULTRA asks for accounting access only — it never collects payments.</p>
            {app_note}
            {connect_form.format(label="Connect QuickBooks" if not raw else "Reconnect QuickBooks")}</div>{app_script}"""

    status = f"""<div class="card">
        <p>{env_badge} Connected to <strong>{_esc(c['company_name'] or c['realm_id'])}</strong></p>
        <div class="row" style="gap:8px;flex-wrap:wrap;">
            {connect_form.format(label="Reconnect")}
            <form class="inline" method="POST" action="{url_for('qbo.disconnect')}"
                  onsubmit="return confirm('Disconnect QuickBooks? Invoices already sent stay in QuickBooks.')">
                {_csrf_field()}<button class="btn red" type="submit">Disconnect</button></form>
        </div></div>"""

    try:
        items = list_items(QBClient(get_db, company_id))
        load_err = ""
    except QBError as ex:
        items, load_err = [], str(ex)
    except requests.RequestException:
        items, load_err = [], "Couldn't reach QuickBooks."
    if load_err:
        picker = f'<div class="card"><p class="small" style="color:#FF6B6B;">Couldn\'t load products/services: {_esc(load_err)}</p></div>'
        return hero + status + picker
    if not items:
        picker = """<div class="card"><h3 style="margin:0 0 8px;">Products / services</h3>
            <p>Your QuickBooks company has no active Service or Non-inventory products. Create one in
            QuickBooks (for example "Roll-off hauling"), then reload this page.</p></div>"""
        return hero + status + picker

    rows = ""
    for kind, label in ITEM_KINDS:
        current = (mapping.get(kind) or {}).get("item_id", "")
        opts = "" if kind == "*" else '<option value="">— use default —</option>'
        if kind == "*" and not current:
            opts = '<option value="">— pick one —</option>'
        opts += "".join(
            f'<option value="{_esc(i["id"])}"{" selected" if i["id"] == current else ""}>{_esc(i["name"])}</option>'
            for i in items)
        rows += f"""<label>{_esc(label)}{' <span style="color:#FF9D5C;">*</span>' if kind == '*' else ''}</label>
            <select name="item_{_esc(kind)}" style="width:100%;margin-bottom:12px;"{' required' if kind == '*' else ''}>{opts}</select>"""
    picker = f"""<div class="card"><h3 style="margin:0 0 4px;">Products / services</h3>
        <p class="muted small" style="margin-bottom:12px;">Every QuickBooks invoice line needs a product/service.
        Pick a default; override by line type only if you track them separately. Lines are sent non-taxable.</p>
        <form method="POST" action="{url_for('qbo.save_items')}">{_csrf_field()}{rows}
        <button class="btn gold" type="submit" style="width:100%;">Save</button></form></div>"""
    return hero + status + picker
