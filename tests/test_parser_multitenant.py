#!/usr/bin/env python3
"""Deterministic multi-tenant parser checks (no API key needed).

Verifies the company-scoping guarantees for the parser vocabulary and the
self-calibrating onboarding seed:
  1. dump_locations is per-company — one company's parse context never sees
     another's dump sites (the leak this PR fixes).
  2. parse_vocab and the address-book top-50 in the parse context are scoped.
  3. The onboarding seed endpoint learns locations + dump sites for the calling
     company only.
Runs entirely offline against the DB + endpoints — no LLM involved.
"""
import os, sys, tempfile, importlib

TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "mt.db")
os.environ["SECRET_KEY"] = "mt"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")


def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)


conn = app.get_db()
cur = conn.cursor()

# The bootstrap company (id 1) exists with the seeded VA dump sites after init.
boot_id = conn.execute("SELECT id FROM companies ORDER BY id LIMIT 1").fetchone()["id"]
boot_dumps = conn.execute(
    "SELECT COUNT(*) n FROM dump_locations WHERE company_id=?", (boot_id,)).fetchone()["n"]
ok(boot_dumps > 0, "bootstrap company owns the seeded dump sites (backfilled to a company_id)")
unscoped = conn.execute(
    "SELECT COUNT(*) n FROM dump_locations WHERE company_id IS NULL").fetchone()["n"]
ok(unscoped == 0, "no dump_locations left global/unscoped after migration")

# Two fresh tenants A and B.
def mk_company(name):
    cur.execute("""INSERT INTO companies (name, slug, subscription_plan, subscription_status,
                   max_drivers, trial_ends_at, created_at) VALUES (?,?,?,?,?,?,?)""",
                (name, name.lower(), "pro", "active", 10, None, app.now_ts()))
    company_id = cur.lastrowid
    cur.execute("""INSERT INTO users (username, password_hash, role, full_name, phone,
                   company_id, created_at) VALUES (?,?,?,?,?,?,?)""",
                (name + "boss", "x", "boss", "B", "", company_id, app.now_ts()))
    return company_id, cur.lastrowid

A_co, A_boss = mk_company("Alpha")
B_co, B_boss = mk_company("Bravo")
# A has its own dump site; B has a different one.
cur.execute("INSERT INTO dump_locations (company_id, name, active, created_at) VALUES (?,?,1,?)",
            (A_co, "Alpha Transfer Station", app.now_ts()))
cur.execute("INSERT INTO dump_locations (company_id, name, active, created_at) VALUES (?,?,1,?)",
            (B_co, "Bravo Landfill", app.now_ts()))
# A has company shorthand; B does not.
cur.execute("INSERT INTO parse_vocab (company_id, term, expansion, kind, created_at) VALUES (?,?,?,'shorthand',?)",
            (A_co, "atx", "Alpha City", app.now_ts()))
conn.commit()

# 1. Parse context is company-scoped: A sees Alpha's dump, not Bravo's; vice versa.
ctxA = app._parse_vocab_context(conn, A_co)
ctxB = app._parse_vocab_context(conn, B_co)
ok("Alpha Transfer Station" in ctxA and "Bravo Landfill" not in ctxA,
   "company A parse context has A's dump site, NOT B's")
ok("Bravo Landfill" in ctxB and "Alpha Transfer Station" not in ctxB,
   "company B parse context has B's dump site, NOT A's")
ok("Alpha City" in ctxA and "Alpha City" not in ctxB,
   "company A shorthand does not leak into company B's parse context")
# Neither new tenant inherits the bootstrap company's seeded VA dumps.
ok("Holland" not in ctxA and "Holland" not in ctxB,
   "new tenants do NOT inherit the bootstrap company's seeded dump sites")
conn.close()

# 2. Onboarding seed endpoint — scoped to the calling company.
app.app.config["TESTING"] = True
client = app.app.test_client()
with client.session_transaction() as s:
    s["user_id"] = A_boss; s["role"] = "boss"; s["roles"] = ["owner", "dispatcher"]
    s["company_id"] = A_co; s["_csrf_token"] = "tok"

r = client.post("/onboarding/parser/seed", json={"_csrf_token": "tok", "stops": [
    {"action": "PR", "address": "500 Alpha Way, Alpha City", "customer": "Acme",
     "container_size": "30yd", "dump_leg": "Nansemond Dump"},
    {"action": "P", "address": "12 Beta Rd", "customer": "Beta Co", "container_size": "20yd"},
]})
ok(r.status_code == 200, "onboarding seed endpoint accepted confirmed stops")
d = r.get_json()
ok(d.get("seeded") == 2 and d.get("dump_sites_added") == 1,
   "seed learned 2 locations and added 1 new dump site")

conn = app.get_db()
# The new dump site belongs to A only.
inA = conn.execute("SELECT COUNT(*) n FROM dump_locations WHERE company_id=? AND name='Nansemond Dump'",
                   (A_co,)).fetchone()["n"]
inB = conn.execute("SELECT COUNT(*) n FROM dump_locations WHERE company_id=? AND name='Nansemond Dump'",
                   (B_co,)).fetchone()["n"]
ok(inA == 1 and inB == 0, "seeded dump site is owned by company A only")
# Learned customers landed in A's address book, not B's.
aLoc = conn.execute("SELECT COUNT(*) n FROM saved_addresses WHERE company_id=? AND customer_name='Acme'",
                    (A_co,)).fetchone()["n"]
bLoc = conn.execute("SELECT COUNT(*) n FROM saved_addresses WHERE company_id=? AND customer_name='Acme'",
                    (B_co,)).fetchone()["n"]
ok(aLoc == 1 and bLoc == 0, "learned customer is in company A's address book only")
# Re-seeding the same dump site does not duplicate it.
conn.close()
r2 = client.post("/onboarding/parser/seed", json={"_csrf_token": "tok", "stops": [
    {"action": "PR", "address": "500 Alpha Way, Alpha City", "dump_leg": "Nansemond Dump"}]})
ok(r2.get_json().get("dump_sites_added") == 0, "re-seeding an existing dump site adds no duplicate")

# 3. A boss cannot edit another company's dump site (id-scoped mutation).
conn = app.get_db()
b_dump_id = conn.execute("SELECT id FROM dump_locations WHERE company_id=? AND name='Bravo Landfill'",
                         (B_co,)).fetchone()["id"]
conn.close()
r3 = client.post(f"/dump-locations/{b_dump_id}/delete", data={"_csrf_token": "tok"})
conn = app.get_db()
still = conn.execute("SELECT COUNT(*) n FROM dump_locations WHERE id=?", (b_dump_id,)).fetchone()["n"]
conn.close()
ok(still == 1, "company A cannot delete company B's dump site (company_id-scoped)")

print("\nALL MULTITENANT TESTS PASSED")
