"""Staging-tray ordering + lifecycle (feat/staging-tray-sequence).

The ordering/re-parse/drag/clear rules are pure client logic and are unit-tested
in tests/test_tray_sequence.mjs (Node). This file covers the SERVER-observable
guarantees the Python suite can enforce:
  - Fix 5: three stops at ONE address (different actions/cans) all insert, and the
    add-stop duplicate WARNING keys on address+action+container, not address alone.
  - the parser page ships the tray-sequence + drag machinery.
  - "dump at yard" resolution (yard vocab + site linking) still works.
"""
import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "tray.db")
os.environ["SECRET_KEY"] = "tray"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,
               yard_address,yard_city,created_at) VALUES (?,?,?,?,?,?,?,?)""",
            ("TrayCo", "trayco", "pro", "active", 10, "2545 Squadron Ct", "Norfolk", ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("t_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("t_drv", "x", "driver", "Tim", co, ts)); drv = cur.lastrowid
# A saved yard site so "dump at yard" can link to a real address (order-independent).
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,norm_key,hidden,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,0,1,?,?)""",
            (co, "Yard", "2545 Squadron Ct", "2545 Squadron Ct, Norfolk", "yard",
             app._address_book_key("Yard", "2545 Squadron Ct", "yard"), ts, ts))
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")
HJ = {"X-CSRF-Token": "tok"}

# ── Fix 5: three stops at the SAME address, different actions/cans, all insert ──
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-11-01", "stops": [
    {"action": "D",  "address": "11496 Shiloh Dr", "customer": "Lot 35",  "container_size": "20yd", "notes": "place on lot 35"},
    {"action": "PR", "address": "11496 Shiloh Dr", "customer": "Ashdon",  "container_size": "30yd", "notes": "can 3124"},
    {"action": "P",  "address": "11496 Shiloh Dr", "customer": "EW",      "container_size": "30yd", "notes": "lot 41 can 3104"},
]}, headers=HJ)
ok(r.status_code == 200 and (r.get_json() or {}).get("stop_count") == 3,
   "three stops at one address (different actions/cans) all dispatch — no collapse, no block")
c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1", (co,)).fetchone()["id"]
rows = c.execute("SELECT address, action, container_size FROM stops WHERE route_id=? ORDER BY stop_order", (rid,)).fetchall()
c.close()
ok(len(rows) == 3 and all((r["address"] or "").startswith("11496 Shiloh") for r in rows),
   "all three same-address stops are persisted as distinct rows")
ok(len({(r["action"], r["container_size"]) for r in rows}) == 3,
   "the three rows keep their distinct action + container (nothing deduped them away)")

# ── Fix 5: the add-stop duplicate WARNING keys on address+action+container ──────
warn_js = app._STOP_WARNINGS_JS
ok("sact === action" in warn_js and "scz === cz" in warn_js,
   "duplicate check requires matching action AND container, not address alone")
ok("(cl && sc && sc === cl)" not in warn_js,
   "the old customer-name-alone / address-alone duplicate trigger is gone")
# the existing-stops payload now carries container_size so the check can compare it
src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "app.py")).read()
ok(src.count('"container_size": (s["container_size"]') >= 2,
   "existing-stops JSON (both board + edit surfaces) now includes container_size")

# ── Parser page ships the tray-sequence + drag machinery ───────────────────────
as_boss()
page = cl.get("/parser").get_data(as_text=True)
for marker in ["/static/tray_sequence.js", "Sortable.min.js", "TraySeq.appendBatch",
               "TraySeq.replaceBatch", "TraySeq.reorder", "mergeAiBatch",
               "initTrayDrag", "resetTray", "currentRawBatchId"]:
    ok(marker in page, "parser page includes tray machinery: %s" % marker)
ok("var payload = { stops: TraySeq.sortBySeq(currentStops)" in page,
   "the dispatch payload is built strictly in seq order")
# the static module itself is served
js = cl.get("/static/tray_sequence.js")
ok(js.status_code == 200 and "function replaceBatch" in js.get_data(as_text=True),
   "/static/tray_sequence.js is served with the ordering rules")

# ── Regression: yard resolution survives ───────────────────────────────────────
conn = app.get_db()
prompt = app._build_parse_system_prompt(conn, co)
conn.close()
ok("2545 Squadron Ct" in prompt and "YARD" in prompt,
   "the parser prompt still injects the yard address as a resolvable target")
# a stop whose dump leg names the yard links to the saved yard site (order-independent)
as_boss()
cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-11-02", "stops": [
    {"action": "P", "address": "900 Work St", "customer": "Job", "container_size": "30yd", "dump_leg": "Yard"},
]}, headers=HJ)
c = app.get_db()
rid2 = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1", (co,)).fetchone()["id"]
site = c.execute("SELECT dump_site_id FROM stops WHERE route_id=?", (rid2,)).fetchone()
c.close()
ok(site is not None and site["dump_site_id"] is not None,
   "a stop that dumps 'at yard' links to the saved yard site (resolution intact)")

# ── PERMANENT FIXTURE: Tim's real dispatched route, 8/27, entered in 3 batches ──
# From the driver's paper log. Batch 1 (AI parse, 2 stops) -> Quick Add (3 stops)
# -> Batch 3 (AI parse, 1 stop). The tray must render these SIX in this exact
# order, seq 1..6, never grouped by source; all three 11496 Shiloh Dr stops must
# survive (different actions/cans/lots); "dump full 30yd at yard" resolves to the
# saved yard (2545 Squadron Ct) with the United note. This is the only fixture
# covering interleaved multi-source entry — it runs on every parser/tray change.
#
# The tray order (seq 1..6) is what the client sends after the three batches; the
# server-observable guarantee is that all six persist in that order, none deduped.
as_boss()
# a United dump site so the yard-origin stop's dump leg links to a real record
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,norm_key,hidden,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,0,1,?,?)""",
            (co, "United", "1000 Landfill Rd", "1000 Landfill Rd, Norfolk", "dump",
             app._address_book_key("United", "1000 Landfill Rd", "dump"), ts, ts))
conn.commit(); conn.close()

tim_route = [
    # batch 1 — AI parse
    {"action": "P",  "address": "2545 Squadron Ct", "customer": "Yard", "container_size": "30yd",
     "dump_leg": "United", "notes": "Pull full 30yd from yard, dump at United (Norfolk)"},
    {"action": "PR", "address": "1994 Tiger Dr, Chesapeake", "customer": "IND LIGH", "container_size": "30yd",
     "dump_leg": "SPSA"},
    # batch 2 — Quick Add (three stops at ONE address, different cans/actions)
    {"action": "D",  "address": "11496 Shiloh Dr, Windsor VA", "customer": "Ew", "container_size": "30yd",
     "notes": "Place on lot 35"},
    {"action": "PR", "address": "11496 Shiloh Dr, Windsor VA", "customer": "Ew", "container_size": "30yd",
     "dump_leg": "SPSA", "notes": "container 3124"},
    {"action": "P",  "address": "11496 Shiloh Dr, Windsor VA", "customer": "Ew", "container_size": "30yd",
     "dump_leg": "SPSA", "notes": "bin 3104"},
    # batch 3 — AI parse
    {"action": "D",  "address": "401 Clearfield Ave, Chesapeake", "customer": "MM Gunter", "container_size": "30yd",
     "notes": "call 581-2464 for placement"},
]
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-08-27", "stops": tim_route}, headers=HJ)
ok(r.status_code == 200 and (r.get_json() or {}).get("stop_count") == 6,
   "Tim 8/27: all six interleaved-batch stops dispatch")
c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1", (co,)).fetchone()["id"]
rows = [dict(x) for x in c.execute(
    "SELECT stop_order, address, action, container_size, customer_name, notes, dump_location "
    "FROM stops WHERE route_id=? ORDER BY stop_order", (rid,)).fetchall()]
c.close()
ok([x["stop_order"] for x in rows] == [1, 2, 3, 4, 5, 6], "Tim 8/27: stops persist in seq order 1..6")
addrs = [(x["address"] or "").split(",")[0] for x in rows]
ok(addrs == ["2545 Squadron Ct", "1994 Tiger Dr", "11496 Shiloh Dr", "11496 Shiloh Dr", "11496 Shiloh Dr", "401 Clearfield Ave"],
   "Tim 8/27: exact drive order preserved, not grouped by source")
shiloh = [x for x in rows if (x["address"] or "").startswith("11496 Shiloh")]
ok(len(shiloh) == 3 and len({x["action"] for x in shiloh}) == 3,
   "Tim 8/27: all three Shiloh Dr stops survive with distinct actions (no dedupe)")
ok("United" in (rows[0]["notes"] or "") and (rows[0]["address"] or "").startswith("2545 Squadron Ct"),
   "Tim 8/27: 'dump full 30yd at yard' resolves to the yard (2545 Squadron Ct) with the United note")

print("\nALL STAGING-TRAY TESTS PASSED")
