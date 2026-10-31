"""A customer's job sites come from the routes he actually runs.

2026-10-31. The `sites` table, the customer detail page that lists sites, and
merge_customer's re-pointing of sites all existed -- but the only writers were
the manual "+ Add Customer" form, manual bin-add, and the demo seeder. Dispatch
never created one. So every customer that arrived through a route text had an
empty job-site list, and a builder working six addresses was six unrelated
strings on six stops.

The underlying cause: a dispatched stop carried a customer NAME and never a
customer_id, so the customer had to be reverse-engineered afterwards by voting
on spellings. This wires the stop to the record and records the site.

The risk this file exists to pin down: attaching a stop to the WRONG customer.
That is worse than attaching to none, because it silently moves a can and a
bill onto someone else's account. So the cases below care as much about stops
that must get NO customer as about the ones that must get the right one.

Run:  python3 tests/test_dispatch_job_sites.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-jobsites-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "sites.db")
os.environ["SECRET_KEY"] = "sites"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
            " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
            ("Site Co", "siteco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("site_boss", "x", "boss", "Site Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("site_drv", "x", "driver", "Site Driver", co, ts))
drv = cur.lastrowid
conn.commit()

ccols = {r["name"] for r in conn.execute("PRAGMA table_info(sites)").fetchall()}
ok("lot" in ccols, "sites.lot exists (from the lot-number work)")
conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss",
             roles=["boss", "owner", "dispatcher", "customer_manager"],
             _csrf_token="tok")
HJ = {"X-CSRF-Token": "tok"}


def dispatch(date, stops):
    r = cl.post("/api/dispatch",
                json={"driver_id": drv, "route_date": date, "stops": stops},
                headers=HJ)
    return r


def sites_for(name):
    """(address, lot) pairs recorded against the customer with this name."""
    c = app.get_db()
    row = c.execute(
        "SELECT id FROM customers WHERE company_id=? AND is_active=1 "
        "AND LOWER(COALESCE(business_name, contact_name,''))=LOWER(?)",
        (co, name)).fetchone()
    if not row:
        c.close()
        return None
    out = [(r["address"], app._norm_lot(app._row_get(r, "lot")))
           for r in c.execute("SELECT address, lot FROM sites WHERE customer_id=? ORDER BY id",
                              (row["id"],)).fetchall()]
    c.close()
    return out


def stop_rows(n=None):
    c = app.get_db()
    rid = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1",
                    (co,)).fetchone()["id"]
    rows = [dict(x) for x in c.execute(
        "SELECT customer_name, customer_id, lot, address FROM stops "
        "WHERE route_id=? ORDER BY stop_order", (rid,)).fetchall()]
    c.close()
    return rows


# ── 1. The reported case: one builder, six different job sites ─────
print("\n-- one customer, six addresses --")
SIX = ["101 Oak St", "205 Pine Ave", "310 Maple Dr", "412 Birch Ln",
       "518 Cedar Ct", "620 Elm Rd"]
r = dispatch("2026-11-03", [
    {"action": "D", "address": a, "customer": "757 Restoration",
     "container_size": "20yd", "notes": ""} for a in SIX
])
ok(r.status_code == 200, "dispatch accepted (got %d)" % r.status_code)

c = app.get_db()
n_cust = c.execute(
    "SELECT COUNT(*) n FROM customers WHERE company_id=? AND is_active=1 "
    "AND LOWER(COALESCE(business_name, contact_name,''))='757 restoration'",
    (co,)).fetchone()["n"]
c.close()
ok(n_cust == 1, "exactly ONE customer record for the builder (got %d)" % n_cust)

got = sites_for("757 Restoration")
ok(got is not None, "the customer record exists")
ok(got is not None and len(got) == 6,
   "all six addresses are recorded as job sites (got %r)" % (got,))
if got:
    norm_got = {app._normalize_addr(a) for a, _l in got}
    ok(norm_got == {app._normalize_addr(a) for a in SIX},
       "and they are the six addresses dispatched, not approximations")

rows = stop_rows()
ok(all(x["customer_id"] for x in rows),
   "every stop is linked to the customer RECORD, not just a name string")
_ids = {x["customer_id"] for x in rows}
ok(len(_ids) == 1 and all(_ids),
   "and all six point at the SAME non-null record (got %r)" % (_ids,))

# ── 2. Dispatching the same address again adds no second site ──────
print("\n-- repeat visits --")
r = dispatch("2026-11-04", [
    {"action": "P", "address": "101 Oak St", "customer": "757 Restoration",
     "container_size": "20yd", "notes": ""},
    {"action": "D", "address": "101 Oak St", "customer": "757 Restoration",
     "container_size": "30yd", "notes": ""},
])
ok(r.status_code == 200, "second route accepted (got %d)" % r.status_code)
got2 = sites_for("757 Restoration")
ok(got2 is not None and len(got2) == 6,
   "pulling and re-dropping at a known address creates NO new site (got %d)"
   % (len(got2) if got2 else -1))

# Address spelled a little differently is the same place.
r = dispatch("2026-11-05", [
    {"action": "P", "address": "101 Oak Street", "customer": "757 Restoration",
     "container_size": "20yd", "notes": ""},
])
got3 = sites_for("757 Restoration")
ok(got3 is not None and len(got3) == 6,
   "'101 Oak Street' is not a seventh site next to '101 Oak St' (got %d)"
   % (len(got3) if got3 else -1))

# ── 3. Two lots at one address are two places a can sits ───────────
print("\n-- lots make distinct sites --")
r = dispatch("2026-11-06", [
    {"action": "D", "address": "900 Shiloh Dr", "customer": "Ashdon lot 35",
     "container_size": "20yd", "notes": ""},
    {"action": "D", "address": "900 Shiloh Dr", "customer": "Ashdon lot 41",
     "container_size": "20yd", "notes": ""},
])
ok(r.status_code == 200, "lot route accepted (got %d)" % r.status_code)
ash = sites_for("Ashdon")
ok(ash is not None and len(ash) == 2,
   "one address, two lots -> two job sites (got %r)" % (ash,))
ok(ash is not None and {l for _a, l in ash} == {"35", "41"},
   "and each carries its own lot number (got %r)" % (ash,))

# Re-dispatching lot 35 does not add a third.
dispatch("2026-11-07", [
    {"action": "P", "address": "900 Shiloh Dr", "customer": "Ashdon lot 35",
     "container_size": "20yd", "notes": ""},
])
ash2 = sites_for("Ashdon")
ok(ash2 is not None and len(ash2) == 2,
   "revisiting lot 35 adds no site (got %d)" % (len(ash2) if ash2 else -1))

# ── 4. A lot-only stop attaches to whoever owns the address ────────
print("\n-- a bare lot inherits the address's customer --")
r = dispatch("2026-11-08", [
    {"action": "PR", "address": "900 Shiloh Dr", "customer": "Lot 35",
     "container_size": "20yd", "notes": ""},
])
ok(r.status_code == 200, "lot-only stop accepted (got %d)" % r.status_code)
rows = stop_rows()
c = app.get_db()
ash_id = c.execute(
    "SELECT id FROM customers WHERE company_id=? AND is_active=1 "
    "AND LOWER(COALESCE(business_name, contact_name,''))='ashdon'", (co,)).fetchone()
c.close()
ok(ash_id is not None, "Ashdon is on the books")
ok(rows and rows[0]["customer_id"] == (ash_id["id"] if ash_id else -1),
   "a stop whose only 'customer' was 'Lot 35' is attached to Ashdon, "
   "because Ashdon owns that address (got %r)" % (rows[0]["customer_id"] if rows else None))
ok(rows and app._norm_lot(rows[0]["lot"]) == "35", "and it keeps lot 35")

# ── 5. WHAT MUST NOT GET A CUSTOMER ────────────────────────────────
# Attaching a stop to the wrong customer moves a can and a bill onto
# someone else's account, quietly. These are the guards.
print("\n-- stops that must stay unattached --")

# The yard is not a customer.
dispatch("2026-11-09", [
    {"action": "D", "address": "1 Yard Rd", "customer": "The Yard",
     "container_size": "20yd", "notes": ""},
])
rows = stop_rows()
ok(rows and not rows[0]["customer_id"],
   "'The Yard' does not become a customer (got %r)" % (rows[0]["customer_id"] if rows else None))

# A vendor stop is a repair shop, not a job site.
dispatch("2026-11-10", [
    {"action": "SHOP", "address": "55 Repair Way", "customer": "Maypaw Diesel",
     "container_size": "", "notes": "hydraulic line"},
])
rows = stop_rows()
c = app.get_db()
vend_as_cust = c.execute(
    "SELECT COUNT(*) n FROM customers WHERE company_id=? AND is_active=1 "
    "AND LOWER(COALESCE(business_name, contact_name,''))='maypaw diesel'",
    (co,)).fetchone()["n"]
c.close()
ok(vend_as_cust == 0,
   "a vendor does not become a customer (got %d records)" % vend_as_cust)
ok(rows and not rows[0]["customer_id"], "and its stop gets no customer_id")

# An unknown bare lot, at an address nobody owns, attaches to nobody
# rather than guessing.
dispatch("2026-11-11", [
    {"action": "D", "address": "777 Nobody Knows Rd", "customer": "Lot 9",
     "container_size": "20yd", "notes": ""},
])
rows = stop_rows()
ok(rows and not rows[0]["customer_id"],
   "a bare lot at an unowned address is left unattached, not guessed "
   "(got %r)" % (rows[0]["customer_id"] if rows else None))

# Two different builders at one address stay on their own records.
dispatch("2026-11-12", [
    {"action": "D", "address": "500 Plaza Blvd", "customer": "Dentist Office",
     "container_size": "20yd", "notes": ""},
    {"action": "D", "address": "500 Plaza Blvd", "customer": "Nail Salon",
     "container_size": "20yd", "notes": ""},
])
rows = stop_rows()
ok(len({x["customer_id"] for x in rows}) == 2,
   "two customers sharing a building keep separate records (got %r)"
   % [x["customer_id"] for x in rows])
d_sites = sites_for("Dentist Office")
n_sites = sites_for("Nail Salon")
ok(d_sites is not None and len(d_sites) == 1 and n_sites is not None and len(n_sites) == 1,
   "each gets that address as its OWN job site (got %r / %r)" % (d_sites, n_sites))

# ── 6. Merging moves the job sites, loses none ──────────────────────
print("\n-- merge gathers the sites --")
dispatch("2026-11-13", [
    {"action": "D", "address": "11 Short St", "customer": "757 Rest",
     "container_size": "20yd", "notes": ""},
    {"action": "D", "address": "12 Short St", "customer": "757 Rest",
     "container_size": "20yd", "notes": ""},
])
short = sites_for("757 Rest")
full = sites_for("757 Restoration")
ok(short is not None and len(short) == 2,
   "the clipped name has its own 2 sites before the merge (got %r)" % (short,))
ok(full is not None and len(full) == 6,
   "and the full name still has 6 (got %d)" % (len(full) if full else -1))

c = app.get_db()
surv = c.execute("SELECT id FROM customers WHERE company_id=? AND is_active=1 AND "
                 "LOWER(COALESCE(business_name, contact_name,''))='757 restoration'",
                 (co,)).fetchone()["id"]
alias = c.execute("SELECT id FROM customers WHERE company_id=? AND is_active=1 AND "
                  "LOWER(COALESCE(business_name, contact_name,''))='757 rest'",
                  (co,)).fetchone()["id"]
c.close()
r = cl.post("/customers/%d/merge" % surv,
            data={"alias_id": str(alias), "_csrf_token": "tok"},
            headers=HJ, follow_redirects=True)
ok(r.status_code == 200, "merge posted (got %d)" % r.status_code)
# Historical route stops must follow the surviving customer after a merge.
# Otherwise Daily Routes still points at a deactivated customer record.
c = app.get_db()
_orphaned = c.execute(
    "SELECT COUNT(*) n FROM stops s JOIN routes r ON r.id=s.route_id "
    "WHERE r.company_id=? AND s.customer_id=?", (co, alias)
).fetchone()["n"]
_relinked = c.execute(
    "SELECT COUNT(*) n FROM stops s JOIN routes r ON r.id=s.route_id "
    "WHERE r.company_id=? AND s.customer_id=? AND s.address IN (?,?)",
    (co, surv, "11 Short St", "12 Short St")
).fetchone()["n"]
c.close()
ok(_orphaned == 0, "merged alias has no historical route stop references")
ok(_relinked == 2, "historical route stops now point to surviving customer")

after = sites_for("757 Restoration")
ok(after is not None and len(after) == 8,
   "after the merge the survivor holds all 8 job sites, none lost (got %d)"
   % (len(after) if after else -1))


# ── 7. History that predates all of this ───────────────────────────
# A year of routes went out before dispatch recorded sites. Without a
# backfill a long-standing customer shows an empty job-site list until he
# happens to be dispatched again.
print("\n-- backfill from existing history --")
c = app.get_db()
c2 = c.cursor()
c2.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
           " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
           ("Old Co", "oldco", "pro", "active", 10, ts))
oco = c2.lastrowid
c2.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
           " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
           ("old_drv", "x", "driver", "Old Driver", oco, ts))
odrv = c2.lastrowid
c2.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
           " assigned_to, status, created_at) VALUES (?,?,?,?,?,'completed',?)",
           (oco, "2026-03-02", "Legacy", odrv, odrv, ts))
orid = c2.lastrowid
# Three addresses for one builder, plus a lot-only stop at one of them, plus
# a vendor visit that must not become a customer -- written the pre-change
# way: a name string, no customer_id, no site.
LEGACY = [(1, "Marlyn Builders", "40 Legacy Way", None, "Delivery"),
          (2, "Marlyn Builders", "41 Legacy Way", None, "Pull"),
          (3, "Marlyn Builders", "42 Legacy Way", None, "Delivery"),
          (4, "Lot 8", "40 Legacy Way", "8", "Pull"),
          (5, "Maypaw Diesel", "55 Repair Way", None, "Vendor")]
for _o, _cn, _ad, _lot, _act in LEGACY:
    c2.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                  state, action, container_size, lot, status, created_at)
                  VALUES (?,?,?,?,'Norfolk','VA',?,'20yd',?,'completed',?)""",
               (orid, _o, _cn, _ad, _act, _lot, ts))
c.commit()
_pre = c.execute("SELECT COUNT(*) n FROM sites s JOIN customers cu ON cu.id=s.customer_id "
                 "WHERE cu.company_id=?", (oco,)).fetchone()["n"]
ok(_pre == 0, "legacy company starts with no job sites at all (got %d)" % _pre)

app._sync_customer_records(c, oco)
mar = c.execute("SELECT id FROM customers WHERE company_id=? AND is_active=1 AND "
                "LOWER(COALESCE(business_name, contact_name,''))='marlyn builders'",
                (oco,)).fetchone()
ok(mar is not None, "the legacy builder has a customer record")
_sites = [(r["address"], app._norm_lot(app._row_get(r, "lot"))) for r in c.execute(
    "SELECT address, lot FROM sites WHERE customer_id=? ORDER BY id",
    (mar["id"] if mar else -1,)).fetchall()] if mar else []
ok(len(_sites) == 4,
   "backfill recovers 3 addresses plus lot 8 as a 4th site (got %r)" % (_sites,))
ok ("8" in {l for _a, l in _sites}, "the lot-only legacy stop became its own site")
_vend = c.execute("SELECT COUNT(*) n FROM customers WHERE company_id=? AND is_active=1 AND "
                  "LOWER(COALESCE(business_name, contact_name,''))='maypaw diesel'",
                  (oco,)).fetchone()["n"]
ok(_vend == 0, "the legacy vendor visit did NOT become a customer (got %d)" % _vend)
_linked = c.execute("SELECT COUNT(*) n FROM stops s JOIN routes r ON r.id=s.route_id "
                    "WHERE r.company_id=? AND s.customer_id IS NOT NULL", (oco,)).fetchone()["n"]
ok(_linked == 4, "the four customer stops are now linked to the record (got %d)" % _linked)
_flag = c.execute("SELECT job_sites_seeded FROM companies WHERE id=?", (oco,)).fetchone()[0]
ok(_flag == 1, "the company is flagged as seeded so this does not re-run")

# Idempotence: running the sync again must not duplicate a single site.
app._sync_customer_records(c, oco)
app._sync_customer_records(c, oco)
_again = c.execute("SELECT COUNT(*) n FROM sites WHERE customer_id=?",
                   (mar["id"] if mar else -1,)).fetchone()["n"]
c.close()
ok(_again == 4, "two further syncs add no duplicate sites (got %d)" % _again)

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
