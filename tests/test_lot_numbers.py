"""A lot number is a lot number, not a customer.

2026-10-31. The boss writes the lot into the customer field, because until
now that was the only field that would hold one. Every lot then became its
own customer record: three stops at 11496 Shiloh Dr arrived as "Lot 35",
"Ashdon" and "EW" -- one builder, three "customers". Separately, a clipped
builder name with the lot glued on ("bish0090", "BISH2643") multiplied the
same builder once per lot.

The rule for the glued form is the boss's own, and it is the only test
applied: if two names sit at the SAME street address and differ only by
trailing digits, those digits are a lot number. Everything else is left
strictly alone -- which is what protects "A1 Demolition", "757 Restoration",
and two unrelated customers who happen to share a building.

The dangerous failure here is not a missed merge. It is a WRONG merge: two
real customers folded into one would misbill, silently. So most of this file
is about what must NOT collapse.

Run:  python3 tests/test_lot_numbers.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-lots-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "lots.db")
os.environ["SECRET_KEY"] = "lots"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


# ── 1. Reading an explicit lot out of free text ────────────────────
print("\n-- split_explicit_lot --")
for raw, want_rest, want_lot in [
    ("Ashdon lot 35", "Ashdon", "35"),
    ("Ashdon Lot#35", "Ashdon", "35"),
    ("Ashdon LT 41", "Ashdon", "41"),
    ("lot 7a", "", "7a"),
    ("Ashdon", "Ashdon", ""),
]:
    rest, lot = app.split_explicit_lot(raw)
    ok(rest == want_rest and lot == want_lot,
       "%r -> name %r lot %r (got %r / %r)" % (raw, want_rest, want_lot, rest, lot))

# The can number is the trap: it is a bare 4-digit run, exactly like a lot.
# Only a run introduced by lot/lt/# may be read as a lot.
print("\n-- a can number is never a lot --")
rest, lot = app.split_explicit_lot("lot 41 can 3104")
ok(lot == "41", "'lot 41 can 3104' reads lot 41, not 3104 (got %r)" % lot)
ok("3104" in rest, "the can number survives in the remaining text (got %r)" % rest)
for raw in ["can 3124", "container #3117 dropped", "bin 3080", "3117 at yard",
            "30yd", "can #3104", "dropped #3080 here"]:
    rest, lot = app.split_explicit_lot(raw)
    ok(lot == "", "%r yields no lot (got %r)" % (raw, lot))
    ok(rest == raw.strip(),
       "%r is returned untouched, so the can reference survives (got %r)" % (raw, rest))

# A bare '#36' IS a lot, but only in the customer field, where a can number
# has no business being. Notes must never take that reading.
print("\n-- bare '#' is opt-in, per field --")
ok(app.split_explicit_lot("Ashdon #36", allow_bare_hash=True) == ("Ashdon", "36"),
   "customer field: 'Ashdon #36' reads lot 36")
ok(app.split_explicit_lot("Ashdon #36")[1] == "",
   "notes: the same text yields no lot without opting in")
ok(app.split_explicit_lot("can #3104", allow_bare_hash=True)[1] == "3104",
   "the opt-in really is permissive -- which is why notes never get it")
# A street number must never be read as a lot either.
_, lot = app.split_explicit_lot("11496 Shiloh Dr")
ok(lot == "", "a street number is not a lot (got %r)" % lot)

# ── 2. A name that is ONLY a lot ───────────────────────────────────
print("\n-- is_lot_only_name --")
for raw, want in [("Lot 35", True), ("#41", True), ("lot 7a", True), ("35", True),
                  ("Ashdon", False), ("757 Rest", False), ("EW", False),
                  ("A1 Demolition", False)]:
    ok(app.is_lot_only_name(raw) is want,
       "%r is%s a lot-only name" % (raw, "" if want else " not"))

# ── 3. Lot numbers compare by value, not by spelling ───────────────
print("\n-- _norm_lot --")
ok(app._norm_lot("0090") == app._norm_lot("90") == "90",
   "'0090' and '90' are the same lot")
ok(app._norm_lot("7a") == "7a", "a letter suffix is kept")
ok(app._norm_lot("") == "" and app._norm_lot(None) == "", "empty stays empty")
ok(app._fmt_lot("0090") == "Lot 90", "display form drops the leading zeros")
ok(app._fmt_lot("") == "", "no lot renders as nothing")

# ── 4. The glued split is a PROPOSAL, never a decision ─────────────
print("\n-- propose_glued_lot --")
ok(app.propose_glued_lot("bish0090") == ("bish", "90"), "bish0090 proposes bish + 90")
ok(app.propose_glued_lot("BISH2643") == ("BISH", "2643"), "BISH2643 proposes BISH + 2643")
ok(app.propose_glued_lot("BISHARD")[1] == "", "BISHARD has no trailing digits")
ok(app.propose_glued_lot("757 Rest")[1] == "",
   "leading digits are part of the name, not a lot")
ok(app.propose_glued_lot("757 Restoration")[1] == "", "same for the full spelling")
ok(app.propose_glued_lot("A1")[1] == "",
   "a single-letter base proposes nothing -- too little to go on")

# ── 5. THE RULE: same address + trailing digits = one customer ─────
print("\n-- _resolve_lot_names: the merge that should happen --")
r = app._resolve_lot_names([
    ("bish0090", "123 Builder Way"),
    ("BISH2643", "123 Builder Way"),
    ("BISHARD",  "123 Builder Way"),
])
ok(set(r) == {"bish0090", "bish2643", "bishard"},
   "all three spellings are claimed by the rule (got %r)" % sorted(r))
ok(all(v[0] == "BISHARD" for v in r.values()),
   "the digit-free spelling becomes the customer name on the invoice")
ok(r.get("bish0090", ("", ""))[1] == "90", "bish0090 carries lot 90")
ok(r.get("bish2643", ("", ""))[1] == "2643", "BISH2643 carries lot 2643")
ok(r.get("bishard", ("", "x"))[1] == "", "BISHARD itself has no lot")

# With no digit-free spelling present, the shared base is the best name there is.
r2 = app._resolve_lot_names([("bish0090", "1 A St"), ("BISH2643", "1 A St")])
ok(set(r2) == {"bish0090", "bish2643"} and all(v[0] == "BISH" for v in r2.values()),
   "with no full spelling on file, the shared base is used")

# ── 6. THE MERGES THAT MUST NOT HAPPEN ─────────────────────────────
# This is the half that matters. A wrong merge misbills one customer for
# another's cans and does it quietly.
print("\n-- what must never collapse --")
must_not = {
    "two unrelated customers in one building":
        [("Dentist Office", "500 Plaza Blvd"), ("Nail Salon", "500 Plaza Blvd")],
    "a lone name with digits proves nothing":
        [("ACME1234", "9 Lone Rd"), ("Hampton Roads Co", "9 Lone Rd")],
    "name variants at DIFFERENT addresses (that is the merge tool's job)":
        [("757 Rest", "1 A St"), ("757 Restoration", "2 B St")],
    "a real name ending in a digit beside its own prefix":
        [("A1 Demolition", "7 Yard Rd"), ("A1", "7 Yard Rd")],
    "a short prefix must not sweep in unrelated builders":
        [("EW1", "5 X St"), ("EWING CONSTRUCTION", "5 X St"), ("Everett Homes", "5 X St")],
    "Shiloh Dr: different names, no digits -- nothing to key on":
        [("Lot 35", "11496 Shiloh Dr"), ("Ashdon", "11496 Shiloh Dr"),
         ("EW", "11496 Shiloh Dr")],
    "one name at one address":
        [("Ashdon", "11496 Shiloh Dr")],
    "no address at all -- never guess":
        [("bish0090", ""), ("BISHARD", "")],
}
for label, pairs in must_not.items():
    res = app._resolve_lot_names(pairs)
    ok(res == {}, "left alone: %s (got %r)" % (label, res))

# A genuinely different builder at the same address is not dragged in.
r3 = app._resolve_lot_names([
    ("bish0090", "123 Builder Way"),
    ("BISHARD", "123 Builder Way"),
    ("Tidewater Framing", "123 Builder Way"),
])
ok("tidewater framing" not in r3,
   "an unrelated builder sharing the address is not folded in")
ok(r3.get("bish0090", ("", ""))[0] == "BISHARD",
   "while the real lot variants still resolve")

# ── 7. End to end through /api/dispatch ────────────────────────────
print("\n-- dispatch: the lot lands in its own column --")
app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
            " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
            ("Lot Co", "lotco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("lot_boss", "x", "boss", "Lot Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("lot_drv", "x", "driver", "Lot Driver", co, ts))
drv = cur.lastrowid
conn.commit()

cols = {r["name"] for r in conn.execute("PRAGMA table_info(stops)").fetchall()}
ok("lot" in cols, "stops.lot column exists")
scols = {r["name"] for r in conn.execute("PRAGMA table_info(sites)").fetchall()}
ok("lot" in scols, "sites.lot column exists")

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss",
             roles=["boss", "owner", "dispatcher", "customer_manager"],
             _csrf_token="tok")
HJ = {"X-CSRF-Token": "tok"}

r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-11-02", "stops": [
    {"action": "D",  "address": "11496 Shiloh Dr", "customer": "Lot 35",
     "container_size": "20yd", "notes": "place on lot 35"},
    {"action": "PR", "address": "11496 Shiloh Dr", "customer": "Ashdon lot 36",
     "container_size": "30yd", "notes": "can 3124"},
    {"action": "P",  "address": "11496 Shiloh Dr", "customer": "EW",
     "container_size": "30yd", "notes": "lot 41 can 3104"},
]}, headers=HJ)
ok(r.status_code == 200, "dispatch accepted (got %d)" % r.status_code)

conn2 = app.get_db()
rid = conn2.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1",
                    (co,)).fetchone()["id"]
rows = [dict(x) for x in conn2.execute(
    "SELECT customer_name, lot, notes, action FROM stops WHERE route_id=? ORDER BY stop_order",
    (rid,)).fetchall()]
conn2.close()
ok(len(rows) == 3, "all three stops persisted (got %d)" % len(rows))

# Stop 1: the customer field held nothing but a lot.
ok(app._norm_lot(rows[0]["lot"]) == "35", "stop 1 lot is 35 (got %r)" % rows[0]["lot"])
ok((rows[0]["customer_name"] or "") == "",
   "stop 1 has NO customer name -- 'Lot 35' was never a customer (got %r)"
   % rows[0]["customer_name"])

# Stop 2: builder and lot together in one field.
ok(rows[1]["customer_name"].strip().lower() == "ashdon",
   "stop 2 customer is Ashdon, lot stripped off (got %r)" % rows[1]["customer_name"])
ok(app._norm_lot(rows[1]["lot"]) == "36", "stop 2 lot is 36 (got %r)" % rows[1]["lot"])

# Stop 3: lot read from the note, note left intact for the driver.
ok(app._norm_lot(rows[2]["lot"]) == "41",
   "stop 3 lot 41 read out of the note (got %r)" % rows[2]["lot"])
ok(rows[2]["customer_name"].strip() == "EW", "stop 3 keeps its customer EW")
ok("3104" in (rows[2]["notes"] or ""),
   "the note keeps the can number (got %r)" % rows[2]["notes"])
ok("lot 41" in (rows[2]["notes"] or "").lower(),
   "and keeps the placement instruction the driver needs (got %r)" % rows[2]["notes"])

# ── 8. "Lot 35" never becomes a customer record ────────────────────
print("\n-- the customer list --")
conn3 = app.get_db()
app._sync_customer_records(conn3, co)
names = [(_r["business_name"] or "") for _r in conn3.execute(
    "SELECT business_name FROM customers WHERE company_id=? AND is_active=1", (co,)).fetchall()]
conn3.close()
lowered = [n.strip().lower() for n in names]
ok(not any(app.is_lot_only_name(n) for n in names),
   "no customer record is a bare lot number (got %r)" % names)
ok("lot 35" not in lowered, "'Lot 35' is not on the customer list")
ok("ashdon" in lowered, "Ashdon IS on the customer list (got %r)" % names)

# The history case: a year of old stops already carry lots in customer_name.
# The parse path stops creating them going forward, but the sync re-mints a
# customer from every historical name on every run, so it has to skip them
# too -- otherwise "Lot 12" comes back on the next page load.
print("\n-- history already full of lots in the name --")
conn4 = app.get_db()
c4 = conn4.cursor()
c4.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
           " assigned_to, status, created_at) VALUES (?,?,?,?,?,'completed',?)",
           (co, "2026-06-01", "Old Route", boss, drv, ts))
_old = c4.lastrowid
for _n, _cn in ((1, "Lot 12"), (2, "#77"), (3, "Marlyn")):
    c4.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                  state, action, container_size, status, created_at)
                  VALUES (?,?,?,?,'Norfolk','VA','Pull','20yd','completed',?)""",
               (_old, _n, _cn, "900 Old Rd", ts))
conn4.commit()
app._sync_customer_records(conn4, co)
names2 = [(_r["business_name"] or "") for _r in conn4.execute(
    "SELECT business_name FROM customers WHERE company_id=? AND is_active=1", (co,)).fetchall()]
conn4.close()
low2 = [n.strip().lower() for n in names2]
ok("lot 12" not in low2, "a lot in old history does not become a customer (got %r)" % names2)
ok("#77" not in low2, "nor does a bare '#77' from old history")
ok(not any(app.is_lot_only_name(n) for n in names2),
   "no lot-only name survives the sync at all (got %r)" % names2)
ok("marlyn" in low2, "a real customer in the same old route is still created")

# ── 9. The display label ───────────────────────────────────────────
print("\n-- stop_customer_label --")
ok(app.stop_customer_label("Ashdon", "35") == "Ashdon — Lot 35",
   "builder first, then the lot")
ok(app.stop_customer_label("Ashdon", "") == "Ashdon", "no lot, just the builder")
ok(app.stop_customer_label("", "35") == "Lot 35", "no builder, just the lot")
ok(app.stop_customer_label("", "", "Stop 4") == "Stop 4", "neither, fall back")
ok(app.stop_customer_label("Ashdon", "0090") == "Ashdon — Lot 90",
   "leading zeros do not reach the driver")

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
