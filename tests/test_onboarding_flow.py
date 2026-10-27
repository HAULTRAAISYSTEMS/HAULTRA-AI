"""New-company onboarding (2026-10-27): two-screen sign-up that signs you in,
the guided setup walkthrough, the redesigned checklist, the driver invite
page — plus the template-injection fix found while building it.

Run:  python tests/test_onboarding_flow.py
"""
import os
import re
import sys
import tempfile
import urllib.parse

TMPDIR = tempfile.mkdtemp(prefix="haultra-onb-")
os.environ["DATABASE_PATH"] = os.path.join(TMPDIR, "o.db")
os.environ["SECRET_KEY"] = "onboarding-secret-key-1234567890"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMPDIR, "uploads")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import app  # noqa: E402

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


app.init_db()
app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s["_csrf_token"] = "tok"


def post(path, data, client=None):
    d = dict(data); d["_csrf_token"] = "tok"
    return (client or cl).post(path, data=d)


def db(sql, *a):
    c = app.get_db()
    try:
        return c.execute(sql, a).fetchall()
    finally:
        c.close()


# ── sign-up ────────────────────────────────────────────────────────────────
page = cl.get("/register-company").get_data(as_text=True)
ok('id="rg-p1"' in page and 'id="rg-p2"' in page and "Your company" in page and "Your login" in page,
   "sign-up is two short screens")
ok("no credit card required" in page.lower(), "sign-up still says no card is needed")

r = post("/register-company", {"company_name": "Acme Roll-Off", "full_name": "Tim Brown", "phone": "7575550100",
                               "username": "acme", "email": "t@acme.test",
                               "password": "Password12345!", "password_confirm": "nope-nope-nope"})
h = r.get_data(as_text=True)
ok(r.status_code == 200 and "Passwords do not match" in h, "a mismatch shows the error on the page")
ok('value="Acme Roll-Off"' in h and 'value="Tim Brown"' in h and 'data-step="2"' in h,
   "what you typed is kept and you land back on screen 2")

r = post("/register-company", {"company_name": "Acme Roll-Off", "full_name": "Tim Brown", "phone": "7575550100",
                               "username": "acme", "email": "t@acme.test",
                               "password": "Password12345!", "password_confirm": "Password12345!"})
ok(r.status_code == 302 and r.location.endswith("/onboarding/start"), "new owner goes straight into setup")
with cl.session_transaction() as s:
    ok(s.get("role") == "boss" and s.get("company_name") == "Acme Roll-Off", "and is already signed in")
    s["_csrf_token"] = "tok"
co = db("SELECT id FROM companies WHERE name='Acme Roll-Off'")[0]["id"]

r = cl.get("/onboarding/start")
ok(r.status_code == 302 and r.location.endswith("/onboarding/start/yard"), "walkthrough opens the first unfinished step")

# ── walkthrough ────────────────────────────────────────────────────────────
y = cl.get("/onboarding/start/yard").get_data(as_text=True)
ok("Where&rsquo;s your yard?" in y and "Step 1 of 5" in y and "Skip for now" in y, "yard step renders")
r = post("/onboarding/start/yard", {"act": "next", "yard_address": "", "yard_city": "Suffolk"})
ok(r.status_code == 200 and "street address" in r.get_data(as_text=True), "blank yard address asks again")
r = post("/onboarding/start/yard", {"act": "next", "yard_address": "100 Industrial Blvd", "yard_city": "Suffolk",
                                    "yard_state": "va", "yard_zip": "23434"})
ok(r.status_code == 302 and r.location.endswith("/prices"), "yard saves and moves on")
row = db("SELECT yard_address, yard_city, yard_state, yard_zip FROM companies WHERE id=?", co)[0]
ok(tuple(row) == ("100 Industrial Blvd", "Suffolk", "VA", "23434"), "yard lands on the company (Settings shows it)")

r = post("/onboarding/start/prices", {"act": "next", "rate_delivery": "$400", "rate_pull": "450.50", "rate_swap": "abc"})
ok(r.status_code == 200 and "swap" in r.get_data(as_text=True).lower(), "a bad price is flagged, good ones kept")
rates = {x["service"]: x["cents"] for x in db("SELECT service, cents FROM rate_cards WHERE company_id=? AND tier='standard'", co)}
ok(rates.get("delivery") == 40000 and rates.get("pull") == 45050 and "swap" not in rates, "prices saved to the rate card")
r = post("/onboarding/start/prices", {"act": "next", "rate_swap": "500"})
ok(r.status_code == 302 and r.location.endswith("/trucks"), "prices move on")

for nm in ("Truck 8", "truck 8", "Truck 1"):
    post("/onboarding/start/trucks", {"act": "add", "truck_name": nm})
names = [x["name"] for x in db("SELECT name FROM trucks WHERE company_id=? ORDER BY id", co)]
ok(names == ["Truck 8", "Truck 1"], "trucks add one at a time, no duplicates (got %s)" % names)
t = cl.get("/onboarding/start/trucks").get_data(as_text=True)
ok("&#128666; Truck 8" in t and "+ Truck 2" in t, "added trucks show as chips with quick-add suggestions")

r = post("/onboarding/start/drivers", {"act": "add", "full_name": "Dave Jones", "phone": "(757) 555-0199"})
d = r.get_data(as_text=True)
ok(r.status_code == 200 and "Invite ready for Dave" in d and "Text invite" in d, "driver invite created from the walkthrough")
m = re.search(r'href="(sms:[^"]+)"', d)
body = urllib.parse.unquote(m.group(1).replace("&amp;", "&")) if m else ""
ok(m and body.startswith("sms:7575550199") and "/invite/" in body and "Acme Roll-Off" in body,
   "Text invite opens Messages with the link")
token = re.search(r"/invite/([A-Za-z0-9_\-]+)", body).group(1)
r = post("/onboarding/start/drivers", {"act": "add", "full_name": "No Phone", "phone": "12"})
ok("10-digit" in r.get_data(as_text=True), "bad phone is explained")
ok(db("SELECT COUNT(*) n FROM users WHERE company_id=? AND role='driver'", co)[0]["n"] == 1, "no half-made driver left behind")

disp = cl.get("/onboarding/start/dispatch").get_data(as_text=True)
ok("Build my first route" in disp and "haultra_prefill" in disp and "/parser" in disp, "dispatch step hands text to the parser")
parser = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "static", "parser.html")).read()
ok("sessionStorage.getItem('haultra_prefill')" in parser, "parser picks up the handed-over text")

done = cl.get("/onboarding/start/done").get_data(as_text=True)
ok("You&rsquo;re in!" in done and "Yard set" in done and "Open my Route Board" in done, "finish screen with summary")

ck = cl.get("/onboarding/setup").get_data(as_text=True)
ok("ck2-ring" in ck and "Up next" in ck and "Walk me through it" in ck, "checklist has the ring, Up next and the walkthrough link")
ok('class="ck2-chip"' in ck and "Company base" in ck, "finished steps collapse to chips")

# ── driver accepts the invite ─────────────────────────────────────────────
dcl = app.app.test_client()
with dcl.session_transaction() as s:
    s["_csrf_token"] = "tok"
iv = dcl.get("/invite/" + token).get_data(as_text=True)
ok("Welcome, Dave!" in iv and "Acme Roll-Off" in iv and "Create my account" in iv, "invite page greets the driver")
r = post("/invite/" + token, {"username": "davej", "password": "Password12345!", "password_confirm": "Password12345!"}, dcl)
h = r.get_data(as_text=True)
ok(r.status_code == 200 and "You&rsquo;re all set, Dave!" in h and "davej" in h, "accepting shows the username to use in the app")
with dcl.session_transaction() as s:
    ok(s.get("role") == "driver" and s.get("username") == "davej", "driver is signed in")
ok(db("SELECT is_active FROM users WHERE username='davej'")[0]["is_active"] == 1, "driver account is active")

# ── template injection (found while building this) ──────────────────────
evil = app.app.test_client()
with evil.session_transaction() as s:
    s["_csrf_token"] = "tok"
post("/register-company", {"company_name": "{{ config.SECRET_KEY }}", "username": "evil1",
                           "password": "Password12345!", "password_confirm": "Password12345!"}, evil)
leak = False
for path in ("/settings", "/dashboard", "/onboarding/start/done", "/onboarding/setup", "/team"):
    if "onboarding-secret-key" in evil.get(path).get_data(as_text=True):
        leak = True
ok(not leak, "a company named {{ config.SECRET_KEY }} cannot read the secret key")
with evil.session_transaction() as s:
    s["_csrf_token"] = "tok"
post("/onboarding/start/trucks", {"act": "add", "truck_name": "{{ 7*7 }}"}, evil)
tp = evil.get("/onboarding/start/trucks").get_data(as_text=True)
ok("{{ 7*7 }}" in tp and ">49<" not in tp, "user text with braces is shown, never evaluated")

print()
if FAILURES:
    print(f"{len(FAILURES)} FAILURE(S):")
    for f in FAILURES:
        print("  -", f)
    sys.exit(1)
print("ALL ONBOARDING TESTS PASSED")
