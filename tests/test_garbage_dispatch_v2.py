"""Garbage dispatch v2 (2026-10-10): redesigned page, back button,
saved route templates, recent dispatches, live preview."""
import json
import os
import sys
import tempfile

TMP = tempfile.mkdtemp(prefix="haultra-gd2-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "t.db")
os.environ["SECRET_KEY"] = "t"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, "/home/hatch/workspace/haultra")
import app
from werkzeug.security import generate_password_hash

FAILURES = []
def ok(cond, label):
    print(("PASS" if cond else "FAIL"), "-", label)
    if not cond:
        FAILURES.append(label)

app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
pw = generate_password_hash("x")
cur.execute("INSERT INTO companies (name, slug, created_at) VALUES (?,?,?)", ("C", "c", ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, is_active, created_at)"
            " VALUES (?,?,?,?,?,?,?)", ("aboss", pw, "boss", "Boss", co, 1, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, is_active, created_at)"
            " VALUES (?,?,?,?,?,?,?)", ("adrv", pw, "driver", "Driver", co, 1, ts))
drv = cur.lastrowid
conn.commit()
conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()

def login_as(uid, role):
    roles = [role]
    if role == "boss":
        roles = ["boss", "owner", "dispatcher", "customer_manager"]
    with cl.session_transaction() as s:
        s.clear()
        s.update(user_id=uid, company_id=co, role=role, roles=roles, _csrf_token="tok")

def post(url, payload, method="POST"):
    return cl.open(url, method=method, json=payload, headers={"X-CSRF-Token": "tok"})

def delete(url):
    return cl.delete(url, json={}, headers={"X-CSRF-Token": "tok"})

login_as(boss, "boss")

# ── Page renders with new elements ────────────────────────────────────
gp = cl.get("/garbage-dispatch").get_data(as_text=True)
ok('href="/routes"' in gp, "page has back button to route board")
ok("Scan a paper route sheet" in gp, "page has prominent scan button")
ok("Saved routes" in gp, "page has saved routes section")
ok("Recent dispatches" in gp, "page has recent dispatches section")
ok("gd-preview" in gp, "page has live preview container")
ok("day-chips" in gp, "page has day quick chips")
ok("Dispatch Route" in gp, "page has dispatch button")
ok("linear-gradient(135deg" in gp, "page uses HAULTRA gradient styling")

# ── Template CRUD ────────────────────────────────────────────────────
stops = [
    {"service_type": "toter", "address": "1 Main St", "city": "VB", "notes": "", "not_before": ""},
    {"service_type": "hpu", "address": "2 Oak Ave", "city": "VB", "notes": "132 units", "not_before": "7am"},
    {"service_type": "landfill", "address": "GFL", "city": "Chesapeake", "notes": "", "not_before": ""},
]
r = post("/api/garbage/templates", {"name": "Friday — Driver", "driver_id": drv, "stops": stops})
d = r.get_json()
ok(r.status_code == 200 and d.get("success") and d.get("stop_count") == 3, "save template")
tid = d["id"]

r = cl.get("/api/garbage/templates")
d = r.get_json()
ok(len(d["templates"]) == 1 and d["templates"][0]["name"] == "Friday — Driver", "list templates")
ok(d["templates"][0]["driver_id"] == drv, "template keeps driver")

# bad inputs
r = post("/api/garbage/templates", {"name": "", "stops": stops})
ok(r.status_code == 400, "template needs a name")
r = post("/api/garbage/templates", {"name": "x", "stops": []})
ok(r.status_code == 400, "template needs stops")
r = post("/api/garbage/templates", {"name": "x", "stops": [{"service_type": "bogus", "address": "y"}]})
ok(r.status_code == 400, "template rejects bad stop types")

# ── Dispatch from template ───────────────────────────────────────────
r = post(f"/api/garbage/templates/{tid}/dispatch", {"driver_id": drv, "route_date": "2026-10-10"})
d = r.get_json()
ok(r.status_code == 200 and d.get("success") and d.get("stop_count") == 3, "dispatch from template")
rid = d["route_id"]

conn = app.get_db()
rt = conn.execute("SELECT COALESCE(route_type,'rolloff') AS t FROM routes WHERE id=?", (rid,)).fetchone()["t"]
n = conn.execute("SELECT COUNT(*) AS n FROM stops WHERE route_id=?", (rid,)).fetchone()["n"]
acts = [r2["action"] for r2 in conn.execute("SELECT action FROM stops WHERE route_id=? ORDER BY stop_order", (rid,))]
uc = conn.execute("SELECT use_count FROM garbage_templates WHERE id=?", (tid,)).fetchone()["use_count"]
conn.close()
ok(rt == "garbage", "template dispatch creates garbage route")
ok(n == 3, "template dispatch creates all stops")
ok(acts == ["Toter", "Hand Pickup", "Landfill"], "template dispatch maps actions")
ok(uc == 1, "template use_count increments")

# ── Recent ───────────────────────────────────────────────────────────
r = cl.get("/api/garbage/recent")
d = r.get_json()
ok(len(d["recent"]) == 1 and d["recent"][0]["id"] == rid, "recent lists the dispatch")

# ── Delete ───────────────────────────────────────────────────────────
r = delete(f"/api/garbage/templates/{tid}")
ok(r.status_code == 200 and r.get_json().get("success"), "delete template")
r = cl.get("/api/garbage/templates")
ok(len(r.get_json()["templates"]) == 0, "template gone after delete")

# ── Driver cannot touch templates ────────────────────────────────────
login_as(drv, "driver")
r = cl.get("/api/garbage/templates")
ok(r.status_code in (401, 403), "driver blocked from templates")
r = cl.get("/garbage-dispatch")
# page guards redirect (302) rather than 403 — either way the driver is out
ok(r.status_code in (301, 302, 401, 403) and b"Garbage Dispatch" not in r.data,
   "driver blocked from dispatch page")

print()
if FAILURES:
    print("FAILURES (%d):" % len(FAILURES))
    for f in FAILURES:
        print("  -", f)
    sys.exit(1)
print("ALL CHECKS PASSED")
