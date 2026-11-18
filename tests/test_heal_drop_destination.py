"""A stop that already exists picks up its drop-off leg too (fix/heal-drop-can-destination).

Reported from the cab 2026-11-18, looking at a stop whose note plainly says
where the can goes:

    LEG 2 OF 2 · PULL Sussex → DUMP Branscome
    20yd · concrete. After dumping take the container to dominion landfill

    "It's still not showing dropping off at dominion"

PR #151 taught the PARSER to read that sentence into a return leg. It did not
help this stop, because this stop was already in the database before #151
shipped — return_destination is STAMPED when a stop is created, not derived
when the cab draws it. Exactly the trap already hit twice before: once on the
address book ("nothing changed"), and once on the yard can flow, which is why
_heal_yard_can_flow exists two functions away. The lesson did not get applied
the third time.

So the same shape as that heal: read-time, fires only on the signature of an
un-upgraded stop, writes nothing when there is nothing to do.
"""
import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "healdrop.db")
os.environ["SECRET_KEY"] = "healdrop"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

import datetime as _dt
_TODAY = app.now_ts()[:10]
def _day(n):
    return (_dt.date.fromisoformat(_TODAY) + _dt.timedelta(days=n)).isoformat()

app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,
               yard_address,yard_city,created_at) VALUES (?,?,?,?,?,?,?,?)""",
            ("HealCo", "healco", "pro", "active", 10, "2545 Squadron Ct", "Virginia Beach", ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("h_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("h_drv", "x", "driver", "Tim", co, ts)); drv = cur.lastrowid
for _n, _a, _c in (("Dominion", "1 Dominion Way", "Chesapeake"),
                   ("Branscome", "5225 Learning Cir", "Virginia Beach")):
    cur.execute("""INSERT INTO dump_locations (company_id,name,address,city,state,active,created_at)
                   VALUES (?,?,?,?,?,1,?)""", (co, _n, _a, _c, "VA", ts))
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
HJ = {"X-CSRF-Token": "tok"}
def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")
def as_driver():
    with cl.session_transaction() as s:
        s.update(user_id=drv, company_id=co, role="driver", roles=["driver"], _csrf_token="tok")

# A stop as it exists in the database TODAY: dumped at Branscome, the
# instruction in the notes, and return_destination empty because it was
# created before the parser learned to read it.
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": _TODAY, "stops": [
    {"action": "P", "address": "3425 Westminister Ave, Norfolk", "customer": "Sussex",
     "container_size": "20yd", "dump_leg": "Branscome",
     "notes": "concrete. After dumping take the container to dominion landfill"},
    {"action": "P", "address": "401 Clearfield Ave, Chesapeake", "customer": "Balicore",
     "container_size": "30yd", "dump_leg": "Branscome",
     "notes": "regular trash, nothing special"},
]}, headers=HJ)
ok(r.status_code == 200, "the day dispatches — status %s" % r.status_code)
c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=?", (co,)).fetchone()["id"]
sid = c.execute("SELECT id FROM stops WHERE route_id=? AND customer_name='Sussex'",
                (rid,)).fetchone()["id"]
# Force the pre-#151 state, whatever the dispatch path did.
c.execute("UPDATE stops SET return_destination='', return_site_id=NULL WHERE route_id=?", (rid,))
c.commit()
ok(not (app._row_get(c.execute("SELECT * FROM stops WHERE id=?", (sid,)).fetchone(),
                     "return_destination") or ""),
   "fixture really is in the un-upgraded state: no return destination")


# ── 1. the heal ────────────────────────────────────────────────────────────
ok(app._heal_drop_can_destination(c, rid) == 1,
   "the heal recognises ONE stop whose note names a destination it never got")
c.commit()
_row = c.execute("SELECT * FROM stops WHERE id=?", (sid,)).fetchone()
ok((app._row_get(_row, "return_destination") or "") == "Dominion",
   "Sussex now drops the can at Dominion — the reported bug")
_other = c.execute("SELECT * FROM stops WHERE route_id=? AND customer_name='Balicore'",
                   (rid,)).fetchone()
ok(not (app._row_get(_other, "return_destination") or ""),
   "the stop whose note says nothing of the kind is untouched")

# Idempotent — a read-time heal must not write on every page load.
ok(app._heal_drop_can_destination(c, rid) == 0,
   "running it again writes nothing — it fires only on the un-upgraded "
   "signature, so a healthy route costs one SELECT")
c.close()


# ── 2. the cab really draws the third leg ─────────────────────────────────
as_driver()
cl.post("/driver/clock/in", data={"_csrf_token": "tok", "next": "/driver/route/%d" % rid})
cl.post("/route/%d/start" % rid, data={"_csrf_token": "tok"})
_h = cl.get("/driver/route/%d?show_stop=%d" % (rid, sid)).get_data(as_text=True)
ok('class="cab-card' in _h and "PRE-FLIGHT" not in _h, "the cab card renders")
ok("LEG 1 OF 3" in _h or "OF 3" in _h,
   "the card counts THREE legs now, not two — Sussex, Branscome, Dominion")
ok("Dominion" in _h, "and Dominion is on it by name")


# ── 3. and it heals from a cold page load, with no explicit call ──────────
# The whole point: the driver opens the cab and the leg is simply there.
c = app.get_db()
c.execute("UPDATE stops SET return_destination='', return_site_id=NULL WHERE id=?", (sid,))
c.commit(); c.close()
_h2 = cl.get("/driver/route/%d?show_stop=%d" % (rid, sid)).get_data(as_text=True)
ok("Dominion" in _h2,
   "opening the cab on an un-upgraded stop heals it in passing — no "
   "re-dispatch, no re-paste, nothing for the driver to do")

c = app.get_db()
_row2 = c.execute("SELECT * FROM stops WHERE id=?", (sid,)).fetchone()
c.close()
ok((app._row_get(_row2, "return_destination") or "") == "Dominion",
   "and the destination is persisted, so the board and the fleet see it too")

print("ALL HEAL-DROP-DESTINATION TESTS PASSED")
