"""QuickBooks Online invoice sync (qbo.py) — deterministic, no network.

A fake Intuit (token endpoint + QBO REST) replaces `requests` inside qbo, so
this runs in CI with no keys. Guarantees checked:
  * OAuth connect/callback stores encrypted tokens (state is verified)
  * refresh rotates + stores the new refresh token; invalid_grant → reconnect
  * customers matched by name, created once, never duplicated
  * surcharge lines go as their own lines with the ticket number
  * an invoice is never pushed twice (ID skip, double-tap claim, lost response)
  * failed → error stored → Retry works
  * tokens never appear in logs or stored errors
  * invoice creation / surcharge billed flags are untouched

Run:  python tests/test_qbo_sync.py
"""
import io
import json
import logging
import os
import sys
import tempfile
import urllib.parse

TMPDIR = tempfile.mkdtemp(prefix="haultra-qbo-")
os.environ["DATABASE_PATH"] = os.path.join(TMPDIR, "qbo.db")
os.environ["SECRET_KEY"] = "testsecret123"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMPDIR, "uploads")
os.environ["QB_CLIENT_ID"] = "test-client-id"
os.environ["QB_CLIENT_SECRET"] = "test-client-secret"
os.environ["QB_REDIRECT_URI"] = "http://localhost:5001/quickbooks/callback"
os.environ["QB_ENVIRONMENT"] = "sandbox"
os.environ.pop("QB_TOKEN_KEY", None)
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import app  # noqa: E402
import qbo  # noqa: E402

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


# ── Capture every log line so we can prove tokens never leak ────────────────
LOG = io.StringIO()
_h = logging.StreamHandler(LOG)
_h.setLevel(logging.DEBUG)
logging.getLogger().addHandler(_h)
logging.getLogger().setLevel(logging.DEBUG)
app.app.logger.addHandler(_h)


# ── Fake Intuit ─────────────────────────────────────────────────────────────
class Resp:
    def __init__(self, status, body, tid="tid-123"):
        self.status_code = status
        self._body = body
        self.headers = {"intuit_tid": tid}
        self.text = json.dumps(body)

    def json(self):
        return self._body


class FakeIntuit:
    def __init__(self):
        self.n = 0
        self.customers = {}       # id -> dict
        self.invoices = {}        # id -> dict
        self.vendor_names = set()
        self.valid_refresh = None
        self.valid_access = set()
        self.issued = []          # every token value ever issued
        self.calls = []
        self.fail_next_invoice = None       # Resp to return instead of creating
        self.lose_next_invoice_response = False
        self.refresh_calls = 0
        self.revoke_calls = 0

    def _tokens(self):
        self.n += 1
        a, r = f"ACCESS-SECRET-{self.n}", f"REFRESH-SECRET-{self.n}"
        self.valid_access.add(a)
        self.valid_refresh = r
        self.issued += [a, r]
        return {"access_token": a, "refresh_token": r, "expires_in": 3600,
                "x_refresh_token_expires_in": 8726400, "token_type": "bearer"}

    # requests.post
    def post(self, url, data=None, json=None, auth=None, headers=None, timeout=None):
        assert auth == ("test-client-id", "test-client-secret")
        if url == qbo.REVOKE_URL:
            self.revoke_calls += 1
            return Resp(200, {})
        assert url == qbo.TOKEN_URL
        if data["grant_type"] == "authorization_code":
            assert data["code"] == "AUTH-CODE" and data["redirect_uri"] == os.environ["QB_REDIRECT_URI"]
            return Resp(200, self._tokens())
        self.refresh_calls += 1
        if data["refresh_token"] != self.valid_refresh:
            return Resp(400, {"error": "invalid_grant"})
        return Resp(200, self._tokens())

    # requests.request
    def request(self, method, url, params=None, json=None, headers=None, timeout=None):
        tok = headers["Authorization"].split(" ", 1)[1]
        if tok not in self.valid_access:
            return Resp(401, {"Fault": {"Error": [{"Message": "AuthenticationFailed", "code": "3200"}]}})
        assert params["minorversion"] == qbo.MINOR_VERSION
        assert url.startswith(qbo.API_BASE["sandbox"] + "/v3/company/REALM1/")
        path = url.split("/v3/company/REALM1/", 1)[1]
        self.calls.append((method, path, params, json))
        if path.startswith("companyinfo/"):
            return Resp(200, {"CompanyInfo": {"CompanyName": "Sandbox Hauling Co"}})
        if path == "query":
            return Resp(200, {"QueryResponse": self._query(params["query"])})
        if method == "POST" and path == "customer":
            name = json["DisplayName"]
            if name.casefold() in {v.casefold() for v in self.vendor_names} or \
               any(c["DisplayName"].casefold() == name.casefold() for c in self.customers.values()):
                return Resp(400, {"Fault": {"Error": [{"Message": "Duplicate Name Exists Error",
                                                        "Detail": "The name supplied already exists.",
                                                        "code": "6240"}]}})
            self.n += 1
            cid = str(1000 + self.n)
            self.customers[cid] = {"Id": cid, "DisplayName": name, "Active": True}
            return Resp(200, {"Customer": self.customers[cid]})
        if method == "POST" and path == "invoice":
            assert params.get("requestid")
            if self.fail_next_invoice:
                r, self.fail_next_invoice = self.fail_next_invoice, None
                return r
            self.n += 1
            iid = str(5000 + self.n)
            total = round(sum(l["Amount"] for l in json["Line"]), 2)
            inv = dict(json, Id=iid, TotalAmt=total)
            self.invoices[iid] = inv
            if self.lose_next_invoice_response:
                self.lose_next_invoice_response = False
                raise qbo.requests.ConnectionError("connection reset")
            return Resp(200, {"Invoice": inv})
        raise AssertionError("unexpected call " + method + " " + path)

    def _query(self, q):
        if q.startswith("select * from Item"):
            return {"Item": [{"Id": "1", "Name": "Hauling", "Type": "Service"},
                             {"Id": "2", "Name": "Landfill Surcharge", "Type": "Service"},
                             {"Id": "3", "Name": "Hours", "Type": "Category"}]}
        if q.startswith("select Id, DisplayName, Active from Customer"):
            name = q.split("'", 1)[1].rsplit("'", 1)[0].replace("\\'", "'").replace("\\\\", "\\")
            hits = [c for c in self.customers.values() if c["DisplayName"].casefold() == name.casefold()]
            return {"Customer": hits} if hits else {}
        if q.startswith("select * from Invoice where CustomerRef"):
            cust = q.split("'", 2)[1]
            hits = [i for i in self.invoices.values() if i["CustomerRef"]["value"] == cust]
            return {"Invoice": hits} if hits else {}
        raise AssertionError("unexpected query " + q)


FAKE = FakeIntuit()
qbo.requests.post = FAKE.post
qbo.requests.request = FAKE.request


# ── Seed: company, boss, completed route with a fee + 2 surcharges ──────────
app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts(); today = app.today_str()
cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at)"
            " VALUES (?,?,?,?,?,?)", ("QBCo", "qbco", "pro", "active", 10, ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at)"
            " VALUES (?,?,?,?,?)", ("qb_boss", "x", "boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,status,created_at)"
            " VALUES (?,?,?,?,'completed',?)", (co, today, "R-qb", boss, ts)); rid = cur.lastrowid
cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,city,state,action,
               container_size,status,driver_status,created_at)
               VALUES (?,1,'Acme Builders','1 Main','Norfolk','VA','Pull','30yd','completed','done',?)""",
            (rid, ts)); sid = cur.lastrowid
for svc, cents in (("pull", 45000), ("delivery", 40000), ("swap", 50000)):
    cur.execute("INSERT OR REPLACE INTO rate_cards (company_id,service,tier,cents) VALUES (?,?,'standard',?)",
                (co, svc, cents))
cur.execute("INSERT INTO stop_fees (company_id,stop_id,kind,description,amount_cents,created_at)"
            " VALUES (?,?,'dry_run','Dry run',15000,?)", (co, sid, ts))
sc_cols = {r[1] for r in cur.execute("PRAGMA table_info(ticket_surcharges)").fetchall()}
for tk, mat, amt in (("T-9001", "Tires", 2500), ("T-9002", "Mattress", 3000)):
    vals = {"company_id": co, "stop_id": sid, "material": mat, "ticket_number": tk,
            "amount_cents": amt, "billed": 0, "created_at": ts}
    vals = {k: v for k, v in vals.items() if k in sc_cols}
    cur.execute(f"INSERT INTO ticket_surcharges ({','.join(vals)}) VALUES ({','.join('?' * len(vals))})",
                tuple(vals.values()))
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"],
             username="qb_boss", _csrf_token="tok")


def db():
    return app.get_db()


def inv_row(iid):
    c = db()
    try:
        return dict(c.execute("SELECT * FROM invoices WHERE id=?", (iid,)).fetchone())
    finally:
        c.close()


def make_invoice(customer="Acme Builders", route=True):
    r = cl.post("/invoices", data={"_csrf_token": "tok", "route_id": str(rid) if route else "",
                                   "customer_name": customer, "terms": "net_30", "issued_at": today})
    assert r.status_code == 302, r.status_code
    return int(r.headers["Location"].rstrip("/").split("/")[-1])


def push(iid):
    return cl.post(f"/invoices/{iid}/quickbooks", data={"_csrf_token": "tok"})


# ── Schema ──────────────────────────────────────────────────────────────────
c = db()
cols = {r[1] for r in c.execute("PRAGMA table_info(invoices)").fetchall()}
ok({"qb_sync_status", "qb_invoice_id", "qb_realm_id", "qb_sync_error"} <= cols, "invoices has qb columns")
tables = {r[0] for r in c.execute("SELECT name FROM sqlite_master WHERE type='table'").fetchall()}
ok({"qb_connections", "qb_customer_map", "qb_item_map"} <= tables, "qb tables created")
c.close()

# ── Invoice creation is untouched: surcharges billed once, status not_synced ─
inv1 = make_invoice()
d1 = inv_row(inv1)
ok(d1["qb_sync_status"] == "not_synced", "new invoice defaults to not_synced")
c = db()
ok(c.execute("SELECT COUNT(*) FROM ticket_surcharges WHERE billed=0").fetchone()[0] == 0,
   "invoice creation still marks surcharges billed")
lines1 = c.execute("SELECT * FROM invoice_line_items WHERE invoice_id=?", (inv1,)).fetchall()
c.close()
ok(sum(1 for l in lines1 if l["kind"] == "surcharge") == 2, "route invoice has 2 surcharge lines")

# ── Not connected: page shows Connect; push refused without changing state ──
r = cl.get(f"/invoices/{inv1}")
ok(b"Connect QuickBooks" in r.data and b"phase 2" not in r.data, "invoice page offers Connect, placeholder gone")
r = push(inv1)
ok(inv_row(inv1)["qb_sync_status"] == "not_synced", "push while disconnected leaves status alone")
ok(b"QuickBooks" in cl.get("/settings").data, "Settings page shows QuickBooks card")

# ── OAuth ───────────────────────────────────────────────────────────────────
r = cl.post("/quickbooks/connect", data={"_csrf_token": "tok"})
loc = r.headers.get("Location", "")
q = dict(urllib.parse.parse_qsl(urllib.parse.urlparse(loc).query))
ok(loc.startswith(qbo.AUTH_URL) and q["scope"] == "com.intuit.quickbooks.accounting",
   "connect redirects to Intuit with accounting scope only")
ok(q["redirect_uri"] == os.environ["QB_REDIRECT_URI"] and q["client_id"] == "test-client-id",
   "connect sends client_id + redirect_uri from env")
r = cl.get("/quickbooks/callback?code=AUTH-CODE&realmId=REALM1&state=WRONG")
c = db(); ok(c.execute("SELECT COUNT(*) FROM qb_connections").fetchone()[0] == 0, "bad state rejected"); c.close()

cl.post("/quickbooks/connect", data={"_csrf_token": "tok"})
with cl.session_transaction() as s:
    state = s["qbo_oauth"]["state"]
r = cl.get(f"/quickbooks/callback?code=AUTH-CODE&realmId=REALM1&state={state}")
c = db()
row = dict(c.execute("SELECT * FROM qb_connections WHERE company_id=?", (co,)).fetchone())
c.close()
ok(row["realm_id"] == "REALM1" and row["environment"] == "sandbox" and row["status"] == "connected",
   "callback stores realm + sandbox connection")
ok("SECRET" not in (row["access_token_enc"] + row["refresh_token_enc"]), "tokens encrypted at rest")
ok(row["company_name"] == "Sandbox Hauling Co", "company name fetched")

# ── Item picker ─────────────────────────────────────────────────────────────
r = cl.get("/quickbooks")
ok(b"Hauling" in r.data and b"Landfill Surcharge" in r.data and b">Hours<" not in r.data,
   "settings lists Service items only")
push(inv1)
d1 = inv_row(inv1)
ok(d1["qb_sync_status"] == "failed" and "product/service" in (d1["qb_sync_error"] or ""),
   "push without a default item fails with a clear message")
ok(b"Retry" in cl.get(f"/invoices/{inv1}").data, "failed invoice shows Retry")
cl.post("/quickbooks/items", data={"_csrf_token": "tok", "item_*": "1", "item_surcharge": "2"})

# ── Push: success ───────────────────────────────────────────────────────────
r = push(inv1)
d1 = inv_row(inv1)
ok(d1["qb_sync_status"] == "synced" and d1["qb_invoice_id"], "retry succeeds → synced + QB invoice id stored")
ok(d1["qb_sync_error"] is None and d1["qb_realm_id"] == "REALM1", "error cleared, realm recorded")
qb_inv = FAKE.invoices[d1["qb_invoice_id"]]
ok(len(qb_inv["Line"]) == len(lines1), "every HAULTRA line pushed as its own QB line")
sur = [l for l in qb_inv["Line"] if "Landfill surcharge" in l["Description"]]
ok(len(sur) == 2 and all(l["SalesItemLineDetail"]["ItemRef"]["value"] == "2" for l in sur),
   "surcharges are separate lines on the surcharge item")
ok(any("Ticket #T-9001" in l["Description"] for l in sur) and any("Ticket #T-9002" in l["Description"] for l in sur),
   "ticket numbers in surcharge descriptions")
ok(all(l["SalesItemLineDetail"]["TaxCodeRef"]["value"] == "NON" for l in qb_inv["Line"]), "lines non-taxable")
ok(all(abs(l["SalesItemLineDetail"]["Qty"] * l["SalesItemLineDetail"]["UnitPrice"] - l["Amount"]) < 0.005
       for l in qb_inv["Line"]), "Qty × UnitPrice == Amount on every line")
ok(round(qb_inv["TotalAmt"] * 100) == d1["total_cents"], "QB total equals HAULTRA total")
ok(qb_inv["DocNumber"] == d1["invoice_number"] and qb_inv["TxnDate"] == today, "doc number + date carried")
ok(len(FAKE.customers) == 1, "customer created once")
c = db()
ok(c.execute("SELECT COUNT(*) FROM ticket_surcharges WHERE billed=0").fetchone()[0] == 0,
   "sync does not touch surcharge billed flags")
c.close()
ok(b"In QuickBooks" in cl.get(f"/invoices/{inv1}").data, "invoice page shows In QuickBooks")

# ── Never push twice ────────────────────────────────────────────────────────
n_before = len(FAKE.invoices)
push(inv1); push(inv1)
ok(len(FAKE.invoices) == n_before, "pushing a synced invoice again is skipped")

# second invoice, same customer name with different case/spacing → reuse
inv2 = make_invoice(customer="  acme   BUILDERS ", route=False)
cl.post(f"/invoices/{inv2}/lines", data={"_csrf_token": "tok", "description": "Relocation", "amount": "100", "kind": "fee"})
push(inv2)
d2 = inv_row(inv2)
ok(d2["qb_sync_status"] == "synced" and len(FAKE.customers) == 1, "customer matched by name, not duplicated")

# customer that already exists in QuickBooks (not created by HAULTRA) → matched
FAKE.customers["777"] = {"Id": "777", "DisplayName": "O'Neil Roofing", "Active": True}
inv3 = make_invoice(customer="O'Neil Roofing", route=False)
cl.post(f"/invoices/{inv3}/lines", data={"_csrf_token": "tok", "description": "Haul", "amount": "300", "kind": "haul"})
push(inv3)
d3 = inv_row(inv3)
ok(d3["qb_sync_status"] == "synced" and FAKE.invoices[d3["qb_invoice_id"]]["CustomerRef"]["value"] == "777",
   "existing QB customer (with apostrophe) matched")
c = db()
ok(c.execute("SELECT qb_customer_id FROM qb_customer_map WHERE name_key=?", ("o'neil roofing",)).fetchone()[0] == "777",
   "QB customer id recorded in map")
c.close()

# double-tap: a live 'syncing' claim blocks a second push
inv4 = make_invoice(customer="Beta Demo", route=False)
cl.post(f"/invoices/{inv4}/lines", data={"_csrf_token": "tok", "description": "Haul", "amount": "200", "kind": "haul"})
c = db(); c.execute("UPDATE invoices SET qb_sync_status='syncing', qb_sync_started_at=? WHERE id=?",
                    (qbo._now(), inv4)); c.commit(); c.close()
n_before = len(FAKE.invoices)
push(inv4)
ok(len(FAKE.invoices) == n_before and inv_row(inv4)["qb_sync_status"] == "syncing",
   "in-flight claim blocks a concurrent push")
# stale claim (worker died) can be retried
c = db(); c.execute("UPDATE invoices SET qb_sync_started_at=? WHERE id=?", (qbo._now() - 999, inv4)); c.commit(); c.close()
push(inv4)
ok(inv_row(inv4)["qb_sync_status"] == "synced", "stale claim is retried and syncs")

# lost response: QB created it but we never heard back → retry adopts it, no duplicate
inv5 = make_invoice(customer="Gamma Lost", route=False)
cl.post(f"/invoices/{inv5}/lines", data={"_csrf_token": "tok", "description": "Haul", "amount": "250", "kind": "haul"})
FAKE.lose_next_invoice_response = True
push(inv5)
d5 = inv_row(inv5)
ok(d5["qb_sync_status"] == "failed" and "won't create a duplicate" in d5["qb_sync_error"],
   "network loss marks failed with a safe-retry message")
n_before = len(FAKE.invoices)
push(inv5)
d5 = inv_row(inv5)
ok(d5["qb_sync_status"] == "synced" and len(FAKE.invoices) == n_before,
   "retry finds the invoice QB already made — no duplicate")

# QB validation error → failed + message + intuit ref, then retry works
inv6 = make_invoice(customer="Delta Err", route=False)
cl.post(f"/invoices/{inv6}/lines", data={"_csrf_token": "tok", "description": "Haul", "amount": "99", "kind": "haul"})
FAKE.fail_next_invoice = Resp(400, {"Fault": {"Error": [{"Message": "Business Validation Error",
                                                         "Detail": "Item is inactive", "code": "6000"}]}}, tid="tid-err-1")
push(inv6)
d6 = inv_row(inv6)
ok(d6["qb_sync_status"] == "failed" and "Item is inactive" in d6["qb_sync_error"] and "tid-err-1" in d6["qb_sync_error"],
   "QB error stored with message + Intuit ref")
push(inv6)
ok(inv_row(inv6)["qb_sync_status"] == "synced", "Retry after fixing succeeds")

# QB text is never evaluated as a template (pages use render_template_string)
inv_t = make_invoice(customer="Tmpl Co", route=False)
cl.post(f"/invoices/{inv_t}/lines", data={"_csrf_token": "tok", "description": "Haul", "amount": "1", "kind": "haul"})
FAKE.fail_next_invoice = Resp(400, {"Fault": {"Error": [{"Message": "Bad", "Detail": "{{ 7*7 }} {% if 1 %}X{% endif %}",
                                                         "code": "6000"}]}})
r = push(inv_t)
page = cl.get(f"/invoices/{inv_t}").data
ok(r.status_code == 302 and b"( 7*7 )" in page and b"{{" not in page and b"{%" not in page,
   "QuickBooks error text can't inject template syntax")

# name used by a vendor → clear failure
FAKE.vendor_names.add("Supply Vendor Inc")
inv7 = make_invoice(customer="Supply Vendor Inc", route=False)
cl.post(f"/invoices/{inv7}/lines", data={"_csrf_token": "tok", "description": "Haul", "amount": "10", "kind": "haul"})
push(inv7)
ok("vendor" in (inv_row(inv7)["qb_sync_error"] or ""), "vendor-name clash explained")

# void invoices can't be sent
inv8 = make_invoice(customer="Void Co", route=False)
cl.post(f"/invoices/{inv8}/status", data={"_csrf_token": "tok", "status": "void"})
n_before = len(FAKE.invoices)
push(inv8)
ok(len(FAKE.invoices) == n_before and inv_row(inv8)["qb_sync_status"] == "not_synced", "void invoice not sent")

# lines changed after sync → warning shown, no re-push
cl.post(f"/invoices/{inv2}/lines", data={"_csrf_token": "tok", "description": "Extra", "amount": "5", "kind": "fee"})
r = cl.get(f"/invoices/{inv2}")
ok(b"changed in HAULTRA after it was sent" in r.data, "post-sync edits flagged on invoice page")

# ── Token refresh + rotation ────────────────────────────────────────────────
old_refresh = FAKE.valid_refresh
c = db(); c.execute("UPDATE qb_connections SET access_expires_at=? WHERE company_id=?", (qbo._now() + 10, co)); c.commit(); c.close()
refresh_before = FAKE.refresh_calls
cl.get("/quickbooks")
ok(FAKE.refresh_calls == refresh_before + 1 and FAKE.valid_refresh != old_refresh, "near-expiry token refreshed")
c = db()
stored = qbo._dec(c.execute("SELECT refresh_token_enc FROM qb_connections WHERE company_id=?", (co,)).fetchone()[0])
c.close()
ok(stored == FAKE.valid_refresh, "rotated refresh token stored")

# 401 mid-call → refresh once and retry
FAKE.valid_access.clear()
r = cl.get("/quickbooks")
ok(b"Hauling" in r.data, "401 triggers a refresh and the call succeeds")

# refresh token revoked → reconnect needed, push fails cleanly
FAKE.valid_refresh = "nope"
c = db(); c.execute("UPDATE qb_connections SET access_expires_at=0 WHERE company_id=?", (co,)); c.commit(); c.close()
inv9 = make_invoice(customer="Epsilon", route=False)
cl.post(f"/invoices/{inv9}/lines", data={"_csrf_token": "tok", "description": "Haul", "amount": "10", "kind": "haul"})
push(inv9)
c = db(); st = c.execute("SELECT status FROM qb_connections WHERE company_id=?", (co,)).fetchone()[0]; c.close()
ok(st == "reconnect_needed" and "Reconnect" in (inv_row(inv9)["qb_sync_error"] or ""),
   "invalid_grant marks reconnect_needed and explains")
ok(b"Reconnect QuickBooks" in cl.get("/quickbooks").data, "settings offers Reconnect")

# environment switch: sandbox connection is not used when set to production
os.environ["QB_ENVIRONMENT"] = "production"
c = db(); ok(qbo.usable_connection(c, co) is None, "sandbox connection ignored in production mode"); c.close()
os.environ["QB_ENVIRONMENT"] = "sandbox"

# disconnect
cl.post("/quickbooks/disconnect", data={"_csrf_token": "tok"})
c = db(); ok(c.execute("SELECT COUNT(*) FROM qb_connections").fetchone()[0] == 0, "disconnect removes tokens"); c.close()

# ── Connect from the native app (finished in the system browser) ────────────
import re  # noqa: E402

qbo.requests.get = lambda url, params=None, timeout=None, headers=None: FAKE.request(
    "GET", url, params=params, headers=headers)
FAKE.valid_refresh = None
APP_UA = {"User-Agent": "Mozilla/5.0 (iPhone) HaultraNativeApp"}


def app_connect():
    r = cl.post("/quickbooks/connect", data={"_csrf_token": "tok"}, headers=APP_UA)
    q = dict(urllib.parse.parse_qsl(urllib.parse.urlparse(r.headers.get("Location", "")).query))
    return q.get("state", "")


def conn_count():
    c = db()
    try:
        return c.execute("SELECT COUNT(*) FROM qb_connections WHERE company_id=?", (co,)).fetchone()[0]
    finally:
        c.close()


ok(b"Intuit opens in your browser" in cl.get("/quickbooks", headers=APP_UA).data,
   "app shows browser-handoff note")
ok(b"Intuit opens in your browser" not in cl.get("/quickbooks").data, "web page has no app note")

state_a = app_connect()
ok(state_a.startswith("h."), "app connect uses a handoff state")
with cl.session_transaction() as s:
    ok("qbo_oauth" not in s, "app connect doesn't rely on the WebView session")

browser = app.app.test_client()         # Safari: no HAULTRA login, no cookies
r = browser.get(f"/quickbooks/callback?code=AUTH-CODE&realmId=REALM1&state={state_a}")
page = r.data.decode()
ok(r.status_code == 200 and "Connect QuickBooks?" in page, "browser callback shows confirm page without login")
ok("QBCo" in page and "Sandbox Hauling Co" in page, "confirm page names both companies")
ok(conn_count() == 0, "nothing saved before confirm")
ok(not any(t in page for t in FAKE.issued), "no token in confirm page")
ok(browser.get(f"/quickbooks/callback?code=AUTH-CODE&realmId=REALM1&state={state_a}").status_code == 400,
   "handoff callback is single-use")
token_a = state_a[2:]
nonce_a = re.search(r'name="nonce" value="([^"]+)"', page).group(1)
attacker = app.app.test_client()
ok(attacker.post(f"/quickbooks/handoff/{token_a}", data={"action": "confirm"}).status_code == 400,
   "confirm without the browser's secret is refused")
ok(attacker.post(f"/quickbooks/handoff/{token_a}", data={"action": "confirm", "nonce": "x" * 32}).status_code == 400,
   "confirm with a wrong secret is refused")
ok(conn_count() == 0, "refused confirms saved nothing")

revokes = FAKE.revoke_calls
r = browser.post(f"/quickbooks/handoff/{token_a}", data={"action": "cancel", "nonce": nonce_a})
ok(r.status_code == 200 and b"wasn't connected" in r.data and conn_count() == 0, "cancel saves nothing")
ok(FAKE.revoke_calls == revokes + 1, "cancel revokes the tokens at Intuit")

state_b = app_connect()
page = browser.get(f"/quickbooks/callback?code=AUTH-CODE&realmId=REALM1&state={state_b}").data.decode()
nonce_b = re.search(r'name="nonce" value="([^"]+)"', page).group(1)
r = browser.post(f"/quickbooks/handoff/{state_b[2:]}", data={"action": "confirm", "nonce": nonce_b})
ok(r.status_code == 200 and b"QuickBooks connected" in r.data, "confirm (no CSRF cookie) connects")
c = db()
row = dict(c.execute("SELECT * FROM qb_connections WHERE company_id=?", (co,)).fetchone())
left = c.execute("SELECT COUNT(*) FROM qb_oauth_handoff WHERE tokens_enc IS NOT NULL").fetchone()[0]
c.close()
ok(row["status"] == "connected" and row["connected_by"] == boss and row["company_name"] == "Sandbox Hauling Co",
   "app-started connection saved to the right company + user")
ok(left == 0, "no tokens left behind in handoff rows")
ok(browser.post(f"/quickbooks/handoff/{state_b[2:]}", data={"action": "confirm", "nonce": nonce_b}).status_code == 400,
   "confirm is single-use")
ok(b"Sandbox Hauling Co" in cl.get("/quickbooks", headers=APP_UA).data, "app page shows connected after return")

state_c = app_connect()
c = db(); c.execute("UPDATE qb_oauth_handoff SET expires_at=0 WHERE stage='started'"); c.commit(); c.close()
ok(browser.get(f"/quickbooks/callback?code=AUTH-CODE&realmId=REALM1&state={state_c}").status_code == 400,
   "expired handoff refused")
ok(browser.get("/quickbooks/callback?code=AUTH-CODE&realmId=REALM1&state=h.made-up").status_code == 400,
   "unknown handoff refused")
r = browser.get("/quickbooks/callback?code=AUTH-CODE&realmId=REALM1&state=web-state")
ok(r.status_code == 302 and "login" in r.headers.get("Location", ""), "web callback still requires login")

# ── Secrets never leak ──────────────────────────────────────────────────────
logs = LOG.getvalue()
ok(not any(t in logs for t in FAKE.issued), "no token value in any log line")
ok("test-client-secret" not in logs, "client secret never logged")
c = db()
errs = " ".join(r[0] or "" for r in c.execute("SELECT qb_sync_error FROM invoices").fetchall())
c.close()
ok(not any(t in errs for t in FAKE.issued), "no token value in stored errors")
src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "qbo.py")).read()
ok("test-client" not in src and "ABcd" not in src, "no credentials in code")

print()
if FAILURES:
    print(f"{len(FAILURES)} FAILURE(S):")
    for f in FAILURES:
        print("  -", f)
    sys.exit(1)
print("ALL QBO SYNC TESTS PASSED")
