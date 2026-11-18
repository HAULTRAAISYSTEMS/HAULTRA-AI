""""After dumping take the container to dominion" is a RETURN leg (feat/drop-can-at-site).

Reported from the cab 2026-11-18, with the instruction sitting in the stop's
notes as prose:

    concrete. After dumping take the container to dominion landfill

and on the driver's own paper log, in his handwriting: "leave @ dom after
dumping it".

    "And how can we do this ? After I dump he wants me to take the container
     to dominion"

The can comes off Sussex, gets emptied at Branscome (the concrete yard), and
is then STAGED at Dominion — neither the customer nor the yard. That is an
ordinary roll-off move: cans get left where tomorrow's work is.

The cab has handled this shape since it was built. _cab_stop_legs assembles a
RETURN leg from return_destination, and its own comment says it fires "when
the stop simply has no dump leg -- 'after the dump' on a plain Pull means
after the work here". Nothing ever read the instruction out of the sentence,
so return_destination stayed empty, no third leg appeared, and the driver got
no Navigate for the place he actually had to drive to.

This file pins the new rule AND the one it could collide with: 2026-11-16
taught the parser that "head to yard once returned" moves the TRUCK and must
leave the return leg empty. The difference is the object — take THE CONTAINER
somewhere moves the can.
"""
import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "dropcan.db")
os.environ["SECRET_KEY"] = "dropcan"
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
            ("StageCo", "stageco", "pro", "active", 10, "2545 Squadron Ct", "Virginia Beach", ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("s_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("s_drv", "x", "driver", "Tim", co, ts)); drv = cur.lastrowid
for _n, _a, _c in (("Dominion", "1 Dominion Way", "Chesapeake"),
                   ("Branscome", "5225 Learning Cir", "Virginia Beach")):
    cur.execute("""INSERT INTO dump_locations (company_id,name,address,city,state,active,created_at)
                   VALUES (?,?,?,?,?,1,?)""", (co, _n, _a, _c, "VA", ts))
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,
               norm_key,hidden,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,0,1,?,?)""",
            (co, "Yard", "2545 Squadron Ct", "2545 Squadron Ct, Virginia Beach", "yard",
             app._address_book_key("Yard", "2545 Squadron Ct", "yard"), ts, ts))
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
HJ = {"X-CSRF-Token": "tok"}
def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")

c = app.get_db()
_known = app._known_site_names(c, co)
c.close()
ok("dominion" in _known and "branscome" in _known,
   "the company's own sites are what a destination is resolved against")


# ── 1. the phrasings a boss actually writes ────────────────────────────────
for _t in ["concrete. After dumping take the container to dominion landfill",
           "leave the can at dominion after you dump",
           "drop the box at dominion when it's empty",
           "dump at branscome then stage it at dominion",
           "after dumping take the container to dominion",
           "leave @ dominion after dumping it",
           "take can 2036 to dominion"]:
    ok(app._find_drop_destination(_t, _known) == "Dominion",
       "destination found in: %r" % _t)

ok(app._find_drop_destination(
    "concrete. After dumping take the container to dominion landfill", _known) == "Dominion",
   "'dominion landfill' resolves to the site named Dominion — the boss's "
   "spelling does not have to match the record exactly")
ok(app._find_drop_destination("pull it and dump at branscome", _known) == "",
   "a plain dump instruction names no destination for the empty")
ok(app._find_drop_destination("ask onsite for placement", _known) == "",
   "and ordinary site notes are not mistaken for one")
ok(app._find_drop_destination("take it to mars", _known) == "",
   "a place the company has never heard of is NOT used — a leg with a dead "
   "Navigate button is worse than no leg")


# ── 2. the guard on the parsed stop ────────────────────────────────────────
_stops = [{
    "action": "P", "address": "5225 Learning Cir, Virginia Beach", "customer": "Sussex",
    "container_size": "20yd", "dump_leg": "Branscome", "return_leg": "",
    "notes": "concrete. After dumping take the container to dominion landfill",
    "raw": "P 5225 learning cir sussex 20yd dump branscome, after dumping take the container to dominion landfill",
}]
_out = app._ensure_drop_can_at_site(_stops, co)
ok(_out[0]["return_leg"] == "Dominion",
   "the empty's destination becomes the RETURN leg — the driver gets a third "
   "leg with its own Navigate instead of prose in the notes (the report)")
ok(_out[0]["dump_leg"] == "Branscome",
   "the dump leg is untouched — the concrete still goes to Branscome")
ok(_out[0]["action"] == "P",
   "and it stays a Pull: a Pull WITH a return leg means haul it, empty it, "
   "and leave the can at that site")
ok("concrete" in (_out[0].get("notes") or ""),
   "the boss's other words survive in the notes")

# Never overwrite an explicit instruction.
_explicit = [{"action": "PR", "address": "x", "return_leg": "Branscome",
              "notes": "after dumping take the container to dominion", "raw": ""}]
ok(app._ensure_drop_can_at_site(_explicit, co)[0]["return_leg"] == "Branscome",
   "a return leg the boss already set is never overwritten")

# A stop with nothing to say is left alone.
_plain = [{"action": "PR", "address": "x", "return_leg": "",
           "notes": "ask onsite for placement", "raw": "del 806 curtis saunders"}]
ok((app._ensure_drop_can_at_site(_plain, co)[0].get("return_leg") or "") == "",
   "a stop that names no destination gets no return leg invented for it")


# ── 3. it does not fight the 2026-11-16 yard rule ──────────────────────────
# "head to yard once returned" moves the TRUCK and must leave the return leg
# empty. If this guard put the yard back, that fix would be undone.
_yard = [{"action": "PR", "address": "520 Kingsborough Sq", "customer": "Velocity",
          "dump_leg": "Dominion", "return_leg": "",
          "notes": "", "raw": "pr 520 kings borough sq velocity 30yd dump dominion and head to yard once returned"}]
_yout = app._ensure_drop_can_at_site(_yard, co)
ok((_yout[0].get("return_leg") or "") != "Yard",
   "'head to yard once returned' still gets NO yard return leg — the truck "
   "goes to the yard, the can went back to Velocity")

# And the two guards in the real order, on the real sentence.
_chain = [{"action": "PR", "address": "520 Kingsborough Sq", "customer": "Velocity",
           "dump_leg": "Dominion", "return_leg": "2545 Squadron Ct, Virginia Beach",
           "notes": "", "raw": "pr 520 kings borough sq velocity 30yd dump dominion and head to yard once returned"}]
_chain = app._ensure_head_to_yard_not_return(_chain, co)
_chain = app._ensure_drop_can_at_site(_chain, co)
ok((_chain[0].get("return_leg") or "") == "",
   "run in the order the parser runs them, the yard rule clears the leg and "
   "this guard does not put it back")


# ── 4. it survives the insert and becomes a real leg ──────────────────────
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": _day(1), "stops": [
    {"action": "P", "address": "5225 Learning Cir, Virginia Beach", "customer": "Sussex",
     "container_size": "20yd", "dump_leg": "Branscome", "return_leg": "Dominion",
     "notes": "concrete. After dumping take the container to dominion landfill"},
]}, headers=HJ)
ok(r.status_code == 200, "the stop dispatches — status %s" % r.status_code)
c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=?", (co,)).fetchone()["id"]
_row = c.execute("SELECT * FROM stops WHERE route_id=?", (rid,)).fetchone()
ok((app._row_get(_row, "return_destination") or "") == "Dominion",
   "the destination persists on the stop as return_destination")

_site_addr = {}
_dump_by_name = {}
for d in c.execute("SELECT name, address, city, state, zip_code FROM dump_locations WHERE company_id=?", (co,)):
    _dump_by_name[(d["name"] or "").lower()] = dict(d)
# _cab_stop_legs expects a dict (it calls .get); the cab passes one too.
_legs, _active = app._cab_stop_legs(dict(_row), "5225 Learning Cir, Virginia Beach",
                                    _site_addr, _dump_by_name)
c.close()
_keys = [l["key"] for l in _legs]
ok(_keys == ["primary", "dump", "return"],
   "the cab builds THREE legs — Sussex, Branscome, Dominion (got %s)" % _keys)
_ret = [l for l in _legs if l["key"] == "return"][0]
ok(_ret["name"] == "Dominion", "the third leg is named Dominion")
ok("Dominion Way" in (_ret["address"] or ""),
   "and carries a real address, so Navigate works: %r" % _ret["address"])

print("ALL DROP-CAN-AT-SITE TESTS PASSED")
