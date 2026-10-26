# Daily Log chain Finish rule (2026-10-26, user's call):
# a finished chain RECEIVER's Finish is its landfill depart — the dump work
# ended when the truck left the landfill, not when the Return tap landed
# later. The head keeps its rule (blank while open); non-chain stops keep
# their completion time; a receiver with no ticket falls back to its
# completion time.
import os, re, sqlite3, sys

sys.path.insert(0, os.path.expanduser("~/workspace/haultra"))
os.environ.setdefault("SECRET_KEY", "test")
DB = "/tmp/test_chain_log_finish.db"
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
conn.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status, max_drivers, created_at) VALUES ('Log Co', 'logco', 'pro', 'active', 10, ?)", (TS,))
co = conn.execute("SELECT id FROM companies WHERE slug='logco'").fetchone()["id"]
conn.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at) VALUES ('logboss', 'x', 'boss', 'Boss', ?, ?)", (co, TS))
boss = conn.execute("SELECT id FROM users WHERE username='logboss'").fetchone()["id"]
conn.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at) VALUES ('logdrv', 'x', 'driver', 'Dave', ?, ?)", (co, TS))
drv = conn.execute("SELECT id FROM users WHERE username='logdrv'").fetchone()["id"]
conn.execute("INSERT INTO routes (company_id, route_name, route_date, status, assigned_to, created_by, created_at, started_at) VALUES (?, 'TIM', '2026-10-26', 'in_progress', ?, ?, ?, '2026-10-26 07:01:00')", (co, drv, boss, TS))
r = conn.execute("SELECT id FROM routes WHERE route_name='TIM'").fetchone()["id"]


def mkstop(order, cust, addr, status, dstatus, completed_at=None, arrived=None):
    conn.execute("INSERT INTO stops (route_id, stop_order, action, customer_name, address, city, container_size, status, driver_status, notes, created_at, completed_at, arrived_at) VALUES (?, ?, 'Pickup and Return', ?, ?, 'X', '30yd', ?, ?, '', ?, ?, ?)", (r, order, cust, addr, status, dstatus, TS, completed_at, arrived))
    return conn.execute("SELECT id FROM stops WHERE route_id=? AND stop_order=?", (r, order)).fetchone()["id"]


ah = mkstop(1, "Marlyn", "5366 Virginia Beach Blvd", "open", "box_in", None, "2026-10-26 07:30:00")
mid = mkstop(2, "Midway", "100 Midway Rd", "completed", "completed", "2026-10-26 11:00:00", "2026-10-26 10:00:00")
bt = mkstop(3, "HEARTLAND", "114 Sawyers Creek", "completed", "completed", "2026-10-26 12:07:00", "2026-10-26 11:30:00")
plain = mkstop(4, "Katchmark", "800 Independence Blvd", "completed", "completed", "2026-10-26 13:00:00", "2026-10-26 12:30:00")
conn.execute("UPDATE stops SET chain_group_id='cg', chain_seq=0, chain_gives_to_stop_id=? WHERE id=?", (mid, ah))
conn.execute("UPDATE stops SET chain_group_id='cg', chain_seq=1, chain_takes_from_stop_id=?, chain_gives_to_stop_id=? WHERE id=?", (ah, bt, mid))
conn.execute("UPDATE stops SET chain_group_id='cg', chain_seq=2, chain_takes_from_stop_id=?, chain_terminal='head' WHERE id=?", (mid, bt))
conn.execute("INSERT INTO dump_tickets (route_id, stop_id, dump_site, arrival_time, departure_time, can_number, net_tons, ticket_number, created_at) VALUES (?, ?, 'Dominion', '2026-10-26 08:55:00', '2026-10-26 09:10:00', '3016', 1.67, 'T1', ?)", (r, ah, TS))
conn.execute("INSERT INTO dump_tickets (route_id, stop_id, dump_site, arrival_time, departure_time, can_number, net_tons, ticket_number, created_at) VALUES (?, ?, 'Dominion', '2026-10-26 11:50:00', '2026-10-26 12:04:00', '3063', 3.53, 'T2', ?)", (r, bt, TS))
conn.commit()
conn.close()

cl = A.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["boss"], _csrf_token="testtoken")
resp = cl.get("/route/%d/daily-log" % r)
html = resp.get_data(as_text=True)
ok(resp.status_code == 200, "daily log renders (200)")


def row_cells(addr):
    m = re.search(r"<tr[^>]*>(?:(?!</tr>).)*?" + re.escape(addr) + r".*?</tr>", html, re.S)
    if not m:
        return None
    return re.findall(r"<td[^>]*>(.*?)</td>", m.group(0), re.S)


def cell_text(c):
    return re.sub(r"<[^>]+>", "", c or "").strip()


# Columns: 0 # 1 work 2 customer 3 address 4 city 5 size 6 start 7 arrive
# 8 depart 9 FINISH 10 box-in 11 box-out 12 tons 13 site 14 ticket
tail = row_cells("114 Sawyers Creek")
ok(tail is not None, "tail row found")
if tail:
    ok(cell_text(tail[9]) == "12:04 pm", "tail Finish is its landfill depart (12:04 pm), got %r" % cell_text(tail[9]))
    ok(cell_text(tail[8]) == "12:04 pm", "tail Depart still 12:04 pm")
head = row_cells("5366 Virginia Beach Blvd")
ok(head is not None, "head row found")
if head:
    ok(cell_text(head[9]) == "", "open head Finish stays blank, got %r" % cell_text(head[9]))
midrow = row_cells("100 Midway Rd")
ok(midrow is not None, "middle row found")
if midrow:
    ok(cell_text(midrow[9]) == "11:00 am", "receiver with no ticket falls back to completion time, got %r" % cell_text(midrow[9]))
plainrow = row_cells("800 Independence Blvd")
ok(plainrow is not None, "plain row found")
if plainrow:
    ok(cell_text(plainrow[9]) == "1:00 pm", "non-chain stop keeps its completion time, got %r" % cell_text(plainrow[9]))

print()
if FAILURES:
    print("FAILURES (%d):" % len(FAILURES))
    for f in FAILURES:
        print("  - " + f)
    sys.exit(1)
print("ALL PASS")
