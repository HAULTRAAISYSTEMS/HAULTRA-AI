import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "rh.db")
os.environ["SECRET_KEY"] = "rh"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

# ── Unit: deliver-step label decision ──────────────────────────────────────
ds = app._chain_deliver_step
ok(ds("none", "X", True, "H", None) is None, "terminal none -> no deliver step")
ok("Empty to Yard" in ds("yard", "X", True, "H", None)[1], "terminal yard -> Empty to Yard")
ok("Deliver Empty to 999 D St" in ds("delivery", "X", True, "H", "999 D St")[1],
   "terminal delivery -> names the delivery stop")
act, lbl, cls = ds("head", "543 Central Dr", True, "543 Central Dr", None)
ok(act == "box_in" and "Return Empty to 543 Central Dr" in lbl, "explicit head -> Return Empty to head")
# The bug: an unterminated tail (NULL/blank terminal) fell through to the
# middle branch and pointed at "the next stop".
act, lbl, cls = ds("", None, True, "543 Central Dr", None)
ok(act == "box_in" and "Return Empty to 543 Central Dr" in lbl,
   "blank terminal on tail defaults to head -> Return Empty to 543 Central Dr")
act, lbl, cls = ds("", "114 Sawyers Creek", False, "543 Central Dr", None)
ok("Deliver Empty to 114 Sawyers Creek" in lbl, "middle keeps Deliver Empty to next stop")
ok(act == "box_in" and cls == "btn-driver btn-driver-complete", "deliver step posts box_in")

# ── Unit: carry-destination resolution (the handoff strip) ─────────────────
cd = app._chain_carry_dest_id
ok(cd(True, 2, False, "", 1) == 2, "head/middle -> onward stop id")
ok(cd(True, None, True, "", 1) == 1, "unterminated tail -> head id (default head)")
ok(cd(True, 1, True, "head", 1) == 1, "explicit head terminal -> head id via gives_to")
ok(cd(True, None, True, "yard", 1) is None, "yard terminal -> nowhere to navigate")
ok(cd(True, None, True, "none", 1) is None, "none terminal -> nowhere to navigate")
ok(cd(True, None, True, "delivery", 1) is None, "delivery terminal w/o gives link -> None")
ok(cd(False, 2, False, "", None) is None, "non-chained -> None (PR plan handles it)")

# ── HTTP: the driver card itself ───────────────────────────────────────────
app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts(); today = app.today_str()
cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at) VALUES (?,?,?,?,?,?)",
            ("RH", "rhco", "pro", "active", 10, ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES (?,?,?,?,?)",
            ("rh_boss", "x", "boss", co, ts))
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("rh_drv", "x", "driver", "Dave", co, ts)); drv = cur.lastrowid
cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at) VALUES (?,?,?,?,?,'in_progress',?,?)",
            (co, today, "R", drv, drv, ts, ts)); rid = cur.lastrowid
# 2-stop chain: stop 1 (head) -> stop 2 (tail). The tail has NO explicit
# terminal in the DB (legacy/unterminated data) — the documented default is head.
cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,city,state,action,container_size,
               status,driver_status,chain_group_id,chain_seq,chain_gives_to_stop_id,chain_takes_from_stop_id,created_at)
               VALUES (?,?,?,'543 Central Dr','Virginia Beach','VA','Pickup and Return','30yd','open','pending','g1',0,2,NULL,?)""",
            (rid, 1, "Priority Pest", ts))
s1 = cur.lastrowid
cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,city,state,action,container_size,
               status,driver_status,chain_group_id,chain_seq,chain_gives_to_stop_id,chain_takes_from_stop_id,chain_terminal,created_at)
               VALUES (?,?,?,'114 Sawyers Creek','Camden','NC','Pickup and Return','30yd','open','pending','g1',1,NULL,?,NULL,?)""",
            (rid, 2, "Camden Site", s1, ts))
s2 = cur.lastrowid
conn.commit(); conn.close()
# fix stop 1's gives_to now that stop 2 exists
conn = app.get_db()
conn.execute("UPDATE stops SET chain_gives_to_stop_id=? WHERE id=?", (s2, s1))
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")
def cab(): return cl.get("/driver/route/%d" % rid).get_data(as_text=True)
def set_stop(sid, **kw):
    c = app.get_db()
    c.execute("UPDATE stops SET %s WHERE id=?" % ", ".join("%s=?" % k for k in kw), (*kw.values(), sid))
    c.commit(); c.close()

# Fix 2: unterminated tail at need_box_in names the head, not "the next stop".
set_stop(s1, status="completed", driver_status="completed")
_TS = app.now_ts()
set_stop(s2, driver_status="need_box_in", arrived_at=_TS)
h = cab()
ok("Return Empty to" in h and "543 Central Dr" in h,
   "unterminated tail card says Return Empty to 543 Central Dr")
ok("Deliver Empty to the next stop" not in h,
   "unterminated tail card never says 'the next stop'")

# Fix 1 (tail return): after the return tap, the handoff points back to the head.
set_stop(s2, driver_status="box_in", arrived_at=_TS)
h = cab()
ok('cab-next-handoff' in h, "handoff strip renders after the deliver tap")
ok("543 Central Dr" in h and "Navigate" in h, "handoff names the head address with Navigate")
ok("openNavStop" in h, "handoff Navigate uses the nav-preference helper")

# Fix 1 (middle): after delivering to the next stop, the handoff names it.
set_stop(s1, status="open", driver_status="box_in", arrived_at=_TS)
set_stop(s2, status="open", driver_status="pending", arrived_at=None)
h = cab()
ok('cab-next-handoff' in h and "114 Sawyers Creek" in h,
   "middle handoff names the next stop after the deliver tap")

print("ALL PASS")
