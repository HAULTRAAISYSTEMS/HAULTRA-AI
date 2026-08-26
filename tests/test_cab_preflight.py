import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "pf.db")
os.environ["SECRET_KEY"] = "pf"
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
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at)
               VALUES (?,?,?,?,?,?)""", ("PfCo", "pfco", "pro", "active", 10, ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES (?,?,?,?,?)",
            ("pf_boss", "x", "boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("pf_drv", "x", "driver", "Dave", co, ts)); drv = cur.lastrowid

# Each route gets a DISTINCT date so _merge_duplicate_open_routes never collapses
# these same-driver test routes into one lane.
_dseq = [0]
def mkroute(status="open", started=None, created=None):
    _dseq[0] += 1
    cur.execute("""INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at)
                   VALUES (?,?,?,?,?,?,?,?)""",
                (co, "2026-07-%02d" % _dseq[0], "R", boss, drv, status, started, created or ts))
    return cur.lastrowid
def mkstop(rid, order, addr, size="20yd", dump="", status="open", ds="pending"):
    cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,city,action,container_size,dump_location,status,driver_status,created_at)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?)""",
                (rid, order, "Cust %d" % order, addr, "Norfolk", "Delivery", size, dump, status, ds, ts))

r_fresh = mkroute("open")
mkstop(r_fresh, 1, "1 A St", "20yd")
mkstop(r_fresh, 2, "2 B St", "30yd", "Holland Transfer")
mkstop(r_fresh, 3, "3 C St", "10yd")
r_zero = mkroute("open")                       # 0 stops → stat tiles must not crash
r_active = mkroute("open", created=ts)         # open + a completed stop → backfill promotes it
mkstop(r_active, 1, "5 Done St", status="completed", ds="completed")
mkstop(r_active, 2, "6 Next St")
r_noact = mkroute("open")                      # open, only pending stop → stays not-started
mkstop(r_noact, 1, "7 Pend St")
conn.commit(); conn.close()

# Backfill runs inside init_db; run twice more to prove idempotency.
app.init_db(); app.init_db()

conn = app.get_db()
def rstat(rid):
    return conn.execute("SELECT status, started_at FROM routes WHERE id=?", (rid,)).fetchone()
ok(rstat(r_active)["status"] == "in_progress", "backfill promotes an active 'open' route to in_progress")
ok(rstat(r_active)["started_at"] is not None, "backfill fills started_at from created_at")
ok(rstat(r_noact)["status"] == "open", "backfill leaves a no-activity route not-started")
ok(rstat(r_fresh)["status"] == "open", "backfill leaves a fresh route not-started")
conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")
def geturl(rid):
    return cl.get("/driver/route/%d" % rid).get_data(as_text=True)

# 1) Fresh route → pre-flight only, no stop list.
h = geturl(r_fresh)
ok("pf-card" in h and "PRE-FLIGHT" in h and "START ROUTE" in h, "fresh route shows the pre-flight card")
ok("Tap to Navigate" not in h and "cab-sticky-bar" not in h and "2 B St" not in h and "3 C St" not in h,
   "fresh route hides the stop list (no nav, no sticky bar, no later stops)")
ok(">3<" in h and ">60<" in h and ">1<" in h, "stat tiles: 3 stops / 60 yards / 1 dump")
ok("First stop" in h and "1 A St" in h, "first-stop preview present")
ok("pretrip-checklist" not in h and "Coming soon" not in h,
   "no placeholder checklist slot in shipped UI")
ok("min-height:64px" in h, "START ROUTE button is >=64px tall")

# 2) 0-stop route must not crash the tiles.
h0 = geturl(r_zero)
ok("pf-card" in h0 and "START ROUTE" in h0, "0-stop route renders pre-flight without crashing")
ok("No stops on this route yet" in h0, "0-stop route says so in place of a first-stop preview")

# 3) START transition sets started_at once + shows running view.
conn = app.get_db(); before = rstat(r_fresh); conn.close()
ok(before["started_at"] is None, "fresh route has no started_at before start")
rr = cl.post("/route/%d/start" % r_fresh, data={"_csrf_token": "tok"})
ok(rr.status_code in (302, 303), "START posts and redirects")
conn = app.get_db(); after = rstat(r_fresh); conn.close()
ok(after["status"] == "in_progress" and after["started_at"] is not None, "START flips to in_progress + sets started_at")
first_started = after["started_at"]

hr = geturl(r_fresh)
ok("cab-sticky-bar" in hr and "END ROUTE" in hr, "running view has the sticky bar + END ROUTE")
ok("STOP 1 OF 3" in hr, "running view shows STOP 1 OF 3")
ok("pf-card" not in hr and "START ROUTE" not in hr, "running view has no pre-flight card")

# 4) Double-tap START → started_at unchanged (idempotent WHERE status='open').
cl.post("/route/%d/start" % r_fresh, data={"_csrf_token": "tok"})
cl.post("/route/%d/start" % r_fresh, data={"_csrf_token": "tok"})
conn = app.get_db(); dbl = rstat(r_fresh); conn.close()
ok(dbl["started_at"] == first_started, "double-tap START does not reset started_at")

# 5) Hard refresh mid-route → still running, never bounces back to pre-flight.
ok("pf-card" not in geturl(r_fresh), "hard refresh mid-route stays in the running view")

# 6) A pre-existing (backfilled) route opens straight into the running view.
ha = geturl(r_active)
ok("pf-card" not in ha, "backfilled route opens straight into running (no pre-flight)")

print("\nALL CAB PRE-FLIGHT TESTS PASSED")
