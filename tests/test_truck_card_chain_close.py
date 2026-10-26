# Trucks on the Road chain-close rule (2026-10-26, user's call):
# once a head-terminal chain's HEAD completes, the final empty is back at
# the head — the truck card must stop reporting it as on the truck
# (Marlyn kept showing 3063 after the driver had dropped it and reached
# Katchmark). While the head is still open, the driver really is carrying
# the bin back to it, so the card keeps showing it.
import os, sqlite3, sys

sys.path.insert(0, os.path.expanduser("~/workspace/haultra"))
os.environ.setdefault("SECRET_KEY", "test")
DB = "/tmp/test_truck_card_chain.db"
if os.path.exists(DB):
    os.remove(DB)
os.environ["DATABASE_PATH"] = DB
import app as A

FAILURES = []


def ok(c, m):
    print(("PASS - " if c else "FAIL - ") + m)
    if not c:
        FAILURES.append(m)


A.app.testing = True
conn = sqlite3.connect(DB)
conn.row_factory = sqlite3.Row
TS = "2026-10-26"
conn.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status, max_drivers, created_at) VALUES ('Truck Co', 'truckco', 'pro', 'active', 10, ?)", (TS,))
co = conn.execute("SELECT id FROM companies WHERE slug='truckco'").fetchone()["id"]
conn.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at) VALUES ('truckdrv', 'x', 'driver', 'Dave', ?, ?)", (co, TS))
drv = conn.execute("SELECT id FROM users WHERE username='truckdrv'").fetchone()["id"]


def mkroute(name):
    conn.execute("INSERT INTO routes (company_id, route_name, route_date, status, assigned_to, created_by, created_at, started_at) VALUES (?, ?, '2026-10-26', 'in_progress', ?, ?, ?, '2026-10-26 07:00:00')", (co, name, drv, drv, TS))
    return conn.execute("SELECT id FROM routes WHERE route_name=?", (name,)).fetchone()["id"]


def mkstop(r, order, cust, addr, status, dstatus, group=None, seq=None, gives=None, takes=None, term=None, act='Pickup and Return'):
    conn.execute("INSERT INTO stops (route_id, stop_order, action, customer_name, address, city, container_size, status, driver_status, notes, created_at, chain_group_id, chain_seq, chain_gives_to_stop_id, chain_takes_from_stop_id, chain_terminal) VALUES (?, ?, ?, ?, ?, 'X', '30yd', ?, ?, '', ?, ?, ?, ?, ?, ?)", (r, order, act, cust, addr, status, dstatus, TS, group, seq, gives, takes, term))
    return conn.execute("SELECT id FROM stops WHERE route_id=? AND stop_order=?", (r, order)).fetchone()["id"]


def mkticket(r, sid, can):
    conn.execute("INSERT INTO dump_tickets (route_id, stop_id, dump_site, can_number, created_at) VALUES (?, ?, 'Dominion', ?, ?)", (r, sid, can, TS))


# State 1 — CLOSED chain: head + tail completed, driver at Katchmark.
r1 = mkroute("CLOSED")
h1 = mkstop(r1, 1, "Marlyn", "5366 Virginia Beach Blvd", "completed", "completed", "cg", 0, None, None, None)
t1 = mkstop(r1, 2, "HEARTLAND", "114 Sawyers Creek", "completed", "completed", "cg", 1, None, h1, "head")
k1 = mkstop(r1, 3, "Katchmark", "800 Independence Blvd", "open", "arrived")
conn.execute("UPDATE stops SET chain_gives_to_stop_id=? WHERE id=?", (t1, h1))
mkticket(r1, h1, "3016")
mkticket(r1, t1, "3063")
conn.commit()
res = A._route_on_truck(conn, r1)
ok(res is not None, "closed chain: truck card renders")
if res:
    ok(res.get("can") in ("", None) and not res.get("has_can"), "closed chain: truck empty (no 3063), got %r" % res.get("can"))
    ok("Katchmark" in res.get("step", ""), "closed chain: step names Katchmark, got %r" % res.get("step"))

# State 2 — OPEN chain: tail completed, head still open (returning).
r2 = mkroute("OPEN")
h2 = mkstop(r2, 1, "Marlyn", "5366 Virginia Beach Blvd", "open", "box_in", "cg", 0, None, None, None)
t2 = mkstop(r2, 2, "HEARTLAND", "114 Sawyers Creek", "completed", "completed", "cg", 1, None, h2, "head")
k2 = mkstop(r2, 3, "Katchmark", "800 Independence Blvd", "open", "pending")
conn.execute("UPDATE stops SET chain_gives_to_stop_id=? WHERE id=?", (t2, h2))
mkticket(r2, h2, "3016")
mkticket(r2, t2, "3063")
conn.commit()
res = A._route_on_truck(conn, r2)
ok(res is not None, "open chain: truck card renders")
if res:
    ok(res.get("can") == "3063" and res.get("has_can"), "open chain: still carrying 3063 back, got %r" % res.get("can"))
    ok("Marlyn" in res.get("step", ""), "open chain: heading back to Marlyn, got %r" % res.get("step"))

# State 3 — BASELINE: plain completed pull, next stop pending (unchanged).
r3 = mkroute("PLAIN")
p3 = mkstop(r3, 1, "Solo", "1 Solo Way", "completed", "completed", act='Pull')
n3 = mkstop(r3, 2, "Next", "2 Next Way", "open", "pending")
mkticket(r3, p3, "3100")
conn.commit()
res = A._route_on_truck(conn, r3)
ok(res is not None, "plain pull: truck card renders")
if res:
    ok(res.get("can") == "3100", "plain pull: still carrying 3100, got %r" % res.get("can"))

print()
if FAILURES:
    print("FAILURES (%d):" % len(FAILURES))
    for f in FAILURES:
        print("  - " + f)
    sys.exit(1)
print("ALL PASS")
