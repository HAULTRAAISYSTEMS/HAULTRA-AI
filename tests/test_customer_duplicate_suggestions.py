"""Find the duplicate customer records already on the books, and let the
boss collapse them in one click.

2026-10-31. Two PRs this week stopped NEW duplicates being created, and the
Customers list did not change by a single row -- because
_sync_customer_records only ever CREATES a record. It never deactivates or
merges one:

    for _k, _spell in _votes.items():
        if _k in _existing or _k in _aliases:
            continue

So 'bish0090', 'BISH2643', 'BISHARD' and 'Bushard 30/20' all sit there as
four separate customers, and the page lists every active record.

This finds them and offers the merge. It never performs one on its own.
A missed suggestion is a row the boss scrolls past; a WRONG merge moves a
can and a bill onto someone else's account silently, so the split between
what is offered and what is auto-applied matters more than the matching.

Confidence has two levels:
  high   -- the boss's own stated rule: names at the SAME address differing
            only by trailing digits are one builder with several lots.
  review -- everything else. Offered, never pre-selected, never applied
            without a click.

Run:  python3 tests/test_customer_duplicate_suggestions.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-dupes-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "d.db")
os.environ["SECRET_KEY"] = "d"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


# ── 1. Size fragments in a name ────────────────────────────────────
# "Bushard 30/20" is a swap instruction -- put a 30 in, take the 20 -- that
# leaked into the customer field, the same way lot numbers did.
print("\n-- _strip_size_fragment --")
for raw, want in [
    ("Bushard 30/20", "Bushard"),
    ("Bushard 30 / 20", "Bushard"),
    ("Marlyn 20yd", "Marlyn"),
    ("Marlyn 30 yd", "Marlyn"),
    ("Napo 10/20/30", "Napo"),
    ("Ashdon", "Ashdon"),
    ("757 Restoration", "757 Restoration"),
    ("", ""),
]:
    got = app._strip_size_fragment(raw)
    ok(got == want, "%r -> %r (got %r)" % (raw, want, got))

ok(app._strip_size_fragment("30/20") == "30/20",
   "a name that is ONLY a size fragment is left alone, never emptied")

# ── 2. Near-name matching ──────────────────────────────────────────
print("\n-- _name_near --")
NEAR = [
    ("757 Rest", "757 Restoration", "one is a prefix of the other"),
    ("Bushard", "Bishard", "single-letter typo"),
    ("BISHARD", "bishard", "case only"),
    ("Marlyn 20yd", "Marlyn", "size fragment stripped"),
    ("Heartland", "HEARTLAND", "case only"),
]
for a, b, why in NEAR:
    ok(app._name_near(a, b), "%r ~ %r (%s)" % (a, b, why))

FAR = [
    ("Napo", "Marlyn", "unrelated"),
    ("Beck", "Bees", "two short names, two letters apart"),
    ("EW", "EWING", "too short a stem to claim a prefix"),
    ("Bishard Homes", "Bishard Plumbing", "could be two real companies"),
    ("Baylor", "Taylor", "one letter apart but both common names"),
    ("burg", "Bees", "unrelated short names"),
]
for a, b, why in FAR:
    ok(not app._name_near(a, b), "%r is NOT near %r (%s)" % (a, b, why))

ok(not app._name_near("Ashdon", "Ashdon"),
   "a name is never 'near' itself -- that would suggest merging a record into itself")

# ── 3. The groups, against the real customer list ──────────────────
print("\n-- customer_duplicate_groups --")
app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
            " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
            ("Dupe Co", "dupeco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("d_boss", "x", "boss", "Dupe Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("d_drv", "x", "driver", "Dupe Driver", co, ts))
drv = cur.lastrowid

# The real list, trimmed: four Bishard spellings, two 757s, and a handful
# of genuinely separate customers that must be left alone.
NAMES = ["bish0090", "BISH2643", "BISHARD", "Bushard 30/20",
         "757 Rest", "757 Restoration",
         "Baylor", "BECK", "Bees", "BRICKNER", "burg", "Caleb", "Marlyn"]
ids = {}
for nm in NAMES:
    cur.execute("INSERT INTO customers (company_id, business_name, portal_token,"
                " is_active, created_at) VALUES (?,?,?,1,?)",
                (co, nm, "tok-" + nm.replace(" ", "-").replace("/", "-"), ts))
    ids[nm] = cur.lastrowid

# Route history: the three bish spellings share one address (the boss's own
# rule for a lot number); Bushard 30/20 is at a different one.
cur.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
            " assigned_to, status, created_at) VALUES (?,?,?,?,?,'completed',?)",
            (co, "2026-10-01", "Hist", boss, drv, ts))
rid = cur.lastrowid
HIST = [("bish0090", "123 Builder Way"), ("BISH2643", "123 Builder Way"),
        ("BISHARD", "123 Builder Way"), ("Bushard 30/20", "77 Other Rd"),
        ("757 Rest", "1 A St"), ("757 Restoration", "2 B St")]
for i, (cn, ad) in enumerate(HIST, start=1):
    cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                   state, action, container_size, status, created_at)
                   VALUES (?,?,?,?,'Norfolk','VA','Pull','20yd','completed',?)""",
                (rid, i, cn, ad, ts))
conn.commit()

groups = app.customer_duplicate_groups(conn, co)
ok(isinstance(groups, list) and groups, "some duplicate groups are found (got %d)" % len(groups))


def group_with(name):
    for g in groups:
        if any(m["name"] == name for m in g["members"]) or g["survivor"]["name"] == name:
            return g
    return None


g_bish = group_with("BISHARD")
ok(g_bish is not None, "the Bishard spellings are grouped")
if g_bish:
    _all = {g_bish["survivor"]["name"]} | {m["name"] for m in g_bish["members"]}
    ok("bish0090" in _all and "BISH2643" in _all,
       "the two lot spellings are in it (got %r)" % (_all,))
    ok(g_bish["survivor"]["name"] == "BISHARD",
       "the digit-free spelling is the survivor (got %r)" % g_bish["survivor"]["name"])
    ok(g_bish["confidence"] == "high",
       "same address + trailing digits is high confidence (got %r)" % g_bish["confidence"])
    ok(ids["BISHARD"] not in [m["id"] for m in g_bish["members"]],
       "the survivor is never also listed as one of its own members")

g_757 = group_with("757 Rest")
ok(g_757 is not None, "the two 757 spellings are grouped")
if g_757:
    ok(g_757["survivor"]["name"] == "757 Restoration",
       "the fuller spelling survives (got %r)" % g_757["survivor"]["name"])
    ok(g_757["confidence"] == "review",
       "different addresses means it needs a human (got %r)" % g_757["confidence"])

print("\n-- what must NOT be suggested --")
_suggested = set()
for g in groups:
    _suggested.add(g["survivor"]["name"])
    for m in g["members"]:
        _suggested.add(m["name"])
for lone in ("Baylor", "BECK", "Bees", "BRICKNER", "burg", "Caleb", "Marlyn"):
    ok(lone not in _suggested,
       "%r is not dragged into any group" % lone)

# ── 4. Merging a whole group ───────────────────────────────────────
print("\n-- the merge --")
app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss",
             roles=["boss", "owner", "customer_manager"], _csrf_token="tok")

_surv = ids["BISHARD"]
_aliases = [ids["bish0090"], ids["BISH2643"]]
r = cl.post("/customers/%d/merge-group" % _surv,
            data={"alias_ids": ",".join(str(i) for i in _aliases), "_csrf_token": "tok"},
            follow_redirects=True)
ok(r.status_code == 200, "merge-group posts (got %d)" % r.status_code)

c2 = app.get_db()
_active = [r2["business_name"] for r2 in c2.execute(
    "SELECT business_name FROM customers WHERE company_id=? AND is_active=1", (co,)).fetchall()]
ok("BISHARD" in _active, "the survivor is still active")
ok("bish0090" not in _active and "BISH2643" not in _active,
   "both aliases are gone from the list (got %r)" % (_active,))
_al = {r2["alias_key"]: r2["survivor_id"] for r2 in c2.execute(
    "SELECT alias_key, survivor_id FROM customer_aliases WHERE company_id=?", (co,)).fetchall()}
ok(_al.get("bish0090") == _surv and _al.get("bish2643") == _surv,
   "both spellings are recorded as aliases of the survivor, so the sync does "
   "not recreate them (got %r)" % (_al,))

# The sync must now leave them merged rather than minting them again.
app._sync_customer_records(c2, co)
_active2 = [r2["business_name"] for r2 in c2.execute(
    "SELECT business_name FROM customers WHERE company_id=? AND is_active=1", (co,)).fetchall()]
c2.close()
ok("bish0090" not in _active2 and "BISH2643" not in _active2,
   "and a later sync does NOT bring them back (got %r)" % (_active2,))

# ── 5. The page offers it ──────────────────────────────────────────
print("\n-- the Customers page --")
r = cl.get("/customers")
html = r.get_data(as_text=True)
ok(r.status_code == 200, "customers page renders (got %d)" % r.status_code)
ok("757 Restoration" in html, "the remaining duplicate pair is offered on the page")
ok("merge-group" in html, "with a merge control wired to the group endpoint")

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
