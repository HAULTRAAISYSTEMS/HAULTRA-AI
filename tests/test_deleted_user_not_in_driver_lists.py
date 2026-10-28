"""A deleted user's tombstone must never appear in a list of people.

2026-10-28: deleting a driver left "deleted-24-<hex>" in the Driver Pay
Week card on the owner dashboard, at 0.0h, permanently.

Deleting a user does not remove the row -- it is overwritten as a
non-identifying tombstone (username "deleted-<id>-<hex>", full_name NULL,
is_active=0) so historical routes keep a valid foreign key. But `role`
deliberately stays 'driver', and several queries selected drivers by role
alone. The codebase's own convention is `role='driver' AND is_active=1`
(the reassign-dropdown query in the same function as one of the offenders
already had it), so these were oversights, not choices.

Covers all four call sites plus the team page's Hours link.

Run:  python3 tests/test_deleted_user_not_in_driver_lists.py
"""
import os
import re
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-tombstone-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "tomb.db")
os.environ["SECRET_KEY"] = "tomb"
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
            ("Tomb Co", "tombco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("tomb_boss", "x", "boss", "Tomb Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("keeper", "x", "driver", "Keep Me", co, ts))
keeper = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("goner", "x", "driver", "Delete Me", co, ts))
goner = cur.lastrowid
conn.commit()

# Give the doomed driver real history, so the tombstone has routes hanging
# off it -- the reason the row is kept rather than deleted.
cur.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
            " assigned_to, status, created_at) VALUES (?,?,?,?,?,'completed',?)",
            (co, "2026-10-20", "Goner Route", boss, goner, ts))
gone_route = cur.lastrowid
cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city, state,
               action, container_size, status, completed_at, created_at)
               VALUES (?,1,'c','1 St','Norfolk','VA','Pull','20yd','completed',?,?)""",
            (gone_route, ts, ts))
conn.commit()

# Tombstone the driver exactly as the delete path does.
TOMB_NAME = "deleted-%d-abc123def456" % goner
cur.execute("""UPDATE users SET username=?, full_name=NULL, phone=NULL, email=NULL,
               avatar_path=NULL, is_active=0 WHERE id=?""", (TOMB_NAME, goner))
conn.commit()

row = dict(conn.execute("SELECT role, is_active FROM users WHERE id=?", (goner,)).fetchone())
ok(row["role"] == "driver" and row["is_active"] == 0,
   "tombstone keeps role='driver' with is_active=0 (the trap this guards)")

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["boss", "owner"],
             _csrf_token="tok")


def body(path):
    r = cl.get(path)
    return r.status_code, r.get_data(as_text=True)


# ── 1. Driver Pay Week (the reported bug) ──────────────────────────
print("\n-- owner dashboard: Driver Pay Week --")
code, html = body("/boss")
ok(code == 200, "owner dashboard renders (got %d)" % code)
ok("Keep Me" in html, "the live driver is still listed")
# Scope to the pay-week card: the tombstone legitimately appears elsewhere on
# this page as a past route's assignee, where it must now read "Former driver"
# rather than vanish (dropping it would disagree with Pulls Today).
_pay = html.split("Driver Pay Week", 1)[1] if "Driver Pay Week" in html else ""
ok(TOMB_NAME not in _pay, "tombstone is absent from the Driver Pay Week card")
ok(TOMB_NAME not in html.split("Driver Pay Week", 1)[0],
   "raw tombstone username appears nowhere above it either")
ok("Former driver" in html, "past attribution reads 'Former driver' instead")

# ── 2. Analytics driver breakdown ──────────────────────────────────
print("\n-- analytics --")
code, html = body("/analytics")
ok(code == 200, "analytics renders (got %d)" % code)
ok(TOMB_NAME not in html, "tombstone is absent from analytics")

# ── 3. Dashboard top-drivers leaderboard ───────────────────────────
print("\n-- dashboard leaderboard --")
code, html = body("/dashboard")
ok(code == 200, "dashboard renders (got %d)" % code)
ok(TOMB_NAME not in html, "raw tombstone username is absent from the dashboard")

# ── 4. Direct-message thread ───────────────────────────────────────
print("\n-- direct messages --")
r = cl.get("/dm/%d/messages" % goner)
ok(r.status_code == 404, "DM thread to a tombstone is 404 (got %d)" % r.status_code)
r = cl.get("/dm/%d/messages" % keeper)
ok(r.status_code == 200, "DM thread to a live driver still works (got %d)" % r.status_code)

# ── 5. Team page: row stays, Hours link does not ───────────────────
print("\n-- team page --")
code, html = body("/team")
ok(code == 200, "team page renders (got %d)" % code)
ok(TOMB_NAME in html,
   "tombstone row IS still shown on the team page (audit trail, by design)")
_tomb_seg = html.split(TOMB_NAME, 1)[1][:1400] if TOMB_NAME in html else ""
ok("driver_id=%d" % goner not in _tomb_seg,
   "no Hours link on the tombstone row")
ok(("driver_id=%d" % keeper) in html, "live driver keeps an Hours link")

# ── 6. The history itself is untouched ─────────────────────────────
print("\n-- history preserved --")
n = conn.execute("SELECT COUNT(*) c FROM routes WHERE assigned_to=?", (goner,)).fetchone()["c"]
ok(n == 1, "the tombstone's historical route still exists (got %d)" % n)

# ── 7. The label helper itself ─────────────────────────────────────
print("\n-- display_user_name --")
ok(app.display_user_name("deleted-24-39e4f669cd58") == "Former driver",
   "maps deleted-<id>-<hex> to a readable label")
ok(app.display_user_name("deleted-driver-24-39e4f669cd58ab") == "Former driver",
   "maps the deleted-<role>-<id>-<hex> form too")
ok(app.display_user_name("tim") == "tim", "leaves a real username alone")
ok(app.display_user_name("deleted_items_report") == "deleted_items_report",
   "does not match a username that merely starts with 'deleted'")
ok(app.display_user_name("") == "", "empty stays empty for the or-Unassigned callers")

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
