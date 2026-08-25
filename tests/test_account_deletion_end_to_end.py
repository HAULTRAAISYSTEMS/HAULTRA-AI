"""End-to-end coverage for Apple 5.1.1(v) account deletion and demo repair."""

import os
import re
import sys
import tempfile
from pathlib import Path

from werkzeug.security import check_password_hash, generate_password_hash


ROOT = Path(__file__).resolve().parents[1]
TMP = tempfile.TemporaryDirectory()
os.environ["DATABASE_PATH"] = str(Path(TMP.name) / "deletion.db")
os.environ["UPLOAD_FOLDER"] = str(Path(TMP.name) / "uploads")
os.environ["SECRET_KEY"] = "account-deletion-end-to-end-test"
os.environ["FLASK_ENV"] = "testing"
os.environ["APP_REVIEW_BOSS_USERNAME"] = "review-boss"
os.environ["APP_REVIEW_BOSS_PASSWORD"] = "ReviewBossPassword!1"
os.environ["APP_REVIEW_DRIVER_USERNAME"] = "review-driver"
os.environ["APP_REVIEW_DRIVER_PASSWORD"] = "ReviewDriverPassword!1"
os.environ["APP_REVIEW_DELETE_USERNAME"] = "review-delete"
os.environ["APP_REVIEW_DELETE_PASSWORD"] = "ReviewDeletePassword!1"
sys.path.insert(0, str(ROOT))

import app as haultra  # noqa: E402


haultra.app.config["TESTING"] = True


def check(condition, label):
    if not condition:
        raise AssertionError(label)
    print("PASS -", label)


def csrf_from(response):
    match = re.search(rb'<meta name="csrf-token" content="([^"]+)"', response.data)
    if not match:
        raise AssertionError("CSRF token missing")
    return match.group(1).decode()


def set_user_session(client, user):
    with client.session_transaction() as sess:
        sess.clear()
        sess["user_id"] = user["id"]
        sess["username"] = user["username"]
        sess["role"] = user["role"]
        sess["roles"] = sorted(haultra.user_role_set(user))
        sess["company_id"] = user["company_id"]
        sess["is_superadmin"] = bool(user["is_superadmin"])


def create_company(conn, slug):
    cur = conn.execute(
        """INSERT INTO companies
           (name,slug,subscription_plan,subscription_status,max_drivers,created_at)
           VALUES (?,?,'pro','active',30,?)""",
        (slug.replace("-", " ").title(), slug, haultra.now_ts()),
    )
    return cur.lastrowid


def create_user(conn, company_id, username, role="driver", full_name=None):
    cur = conn.execute(
        """INSERT INTO users
           (username,password_hash,role,role_owner,full_name,phone,email,
            company_id,created_at,is_active)
           VALUES (?,?,?,?,?,?,?,?,?,1)""",
        (
            username,
            generate_password_hash("ValidDeletionPassword!1"),
            role,
            1 if role == "boss" else 0,
            full_name or username.title(),
            "757-555-0199",
            f"{username}@example.invalid",
            company_id,
            haultra.now_ts(),
        ),
    )
    return cur.lastrowid


def add_route(conn, company_id, boss_id, driver_id, status, name):
    cur = conn.execute(
        """INSERT INTO routes
           (route_date,route_name,assigned_to,created_by,status,created_at,company_id)
           VALUES ('2026-08-24',?,?,?,?,?,?)""",
        (name, driver_id, boss_id, status, haultra.now_ts(), company_id),
    )
    route_id = cur.lastrowid
    cur = conn.execute(
        """INSERT INTO stops
           (route_id,stop_order,customer_name,address,action,status,
            driver_signature,created_at)
           VALUES (?,1,'Fictional Customer','1 Test Way','Delivery',?,?,?)""",
        (
            route_id,
            "completed" if status == "completed" else "open",
            "Original Driver Name",
            haultra.now_ts(),
        ),
    )
    return route_id, cur.lastrowid


# Driver deletion preserves completed company records and unresolved exceptions.
conn = haultra.get_db()
company_id = create_company(conn, "driver-delete-company")
boss_id = create_user(conn, company_id, "driver-delete-boss", "boss")
driver_id = create_user(conn, company_id, "driver-delete-user", full_name="Original Driver Name")
conn.execute("UPDATE companies SET owner_id=? WHERE id=?", (boss_id, company_id))
completed_route_id, completed_stop_id = add_route(
    conn, company_id, boss_id, driver_id, "completed", "Completed Driver Route"
)
open_route_id, _ = add_route(conn, company_id, boss_id, driver_id, "open", "Open Driver Route")
conn.execute(
    """INSERT INTO route_exceptions
       (company_id,client_uuid,stop_id,driver_id,type,occurred_at,created_at)
       VALUES (?,?,?,?,?,?,?)""",
    (company_id, "delete-exception", completed_stop_id, driver_id, "GATE_CLOSED", haultra.now_ts(), haultra.now_ts()),
)
cur = conn.execute(
    """INSERT INTO trucks(company_id,name,is_active,created_at)
       VALUES (?,'Deletion Test Truck',1,?)""",
    (company_id, haultra.now_ts()),
)
truck_id = cur.lastrowid
conn.execute(
    """INSERT INTO inspections
       (company_id,truck_id,driver_id,type,overall,signature_name,created_at)
       VALUES (?,?,?,'pre_trip','safe','Original Driver Name',?)""",
    (company_id, truck_id, driver_id, haultra.now_ts()),
)
conn.commit()
driver = conn.execute("SELECT * FROM users WHERE id=?", (driver_id,)).fetchone()
conn.close()

client = haultra.app.test_client()
set_user_session(client, driver)
second_driver_session = haultra.app.test_client()
set_user_session(second_driver_session, driver)
page = client.get("/account/delete")
response = client.post(
    "/account/delete",
    data={
        "_csrf_token": csrf_from(page),
        "password": "ValidDeletionPassword!1",
        "confirm_delete": "DELETE",
    },
    follow_redirects=True,
)
check(response.status_code == 200, "eligible driver completes deletion")
conn = haultra.get_db()
tombstone = conn.execute("SELECT * FROM users WHERE id=?", (driver_id,)).fetchone()
check(not tombstone["is_active"] and tombstone["full_name"] == "Deleted driver",
      "driver roster row becomes inactive tombstone")
check(tombstone["phone"] is None and tombstone["email"] is None,
      "driver contact identifiers are erased")
check(conn.execute("SELECT assigned_to FROM routes WHERE id=?", (completed_route_id,)).fetchone()["assigned_to"] == driver_id,
      "completed route retains tombstone assignment")
check(conn.execute("SELECT assigned_to FROM routes WHERE id=?", (open_route_id,)).fetchone()["assigned_to"] is None,
      "unstarted route returns to dispatch")
inspection = conn.execute("SELECT driver_id,signature_name FROM inspections WHERE driver_id=?", (driver_id,)).fetchone()
check(inspection and inspection["signature_name"] == "Deleted user",
      "historical DVIR resolves through tombstone without driver name")
exception = conn.execute("SELECT * FROM route_exceptions WHERE driver_id=?", (driver_id,)).fetchone()
check(exception and exception["resolution"] is None and exception["client_uuid"].startswith("deleted-exception-"),
      "unresolved exception remains open with anonymized attribution")
conn.close()
other_session_response = second_driver_session.get("/driver", follow_redirects=False)
check(other_session_response.status_code == 302 and "/login" in other_session_response.headers["Location"],
      "all pre-existing workforce sessions lose access after deletion")

boss_client = haultra.app.test_client()
conn = haultra.get_db()
boss = conn.execute("SELECT * FROM users WHERE id=?", (boss_id,)).fetchone()
conn.close()
set_user_session(boss_client, boss)
team = boss_client.get("/team")
check(b"Inactive tombstone" in team.data and b"Original Driver Name" not in team.data,
      "boss roster shows inactive tombstone without former name")


# In-progress route blocks deletion with zero database changes.
conn = haultra.get_db()
blocked_driver_id = create_user(conn, company_id, "blocked-driver", full_name="Blocked Driver")
blocked_route_id, _ = add_route(conn, company_id, boss_id, blocked_driver_id, "in_progress", "Active Route")
conn.commit()
before_user = dict(conn.execute("SELECT * FROM users WHERE id=?", (blocked_driver_id,)).fetchone())
before_audit = conn.execute("SELECT COUNT(*) n FROM account_deletion_audit").fetchone()["n"]
blocked_driver = conn.execute("SELECT * FROM users WHERE id=?", (blocked_driver_id,)).fetchone()
conn.close()
blocked_client = haultra.app.test_client()
set_user_session(blocked_client, blocked_driver)
page = blocked_client.get("/account/delete")
blocked = blocked_client.post(
    "/account/delete",
    data={"_csrf_token": csrf_from(page), "password": "ValidDeletionPassword!1", "confirm_delete": "DELETE"},
    follow_redirects=True,
)
check(b"in-progress route" in blocked.data, "in-progress driver receives the correct blocker")
conn = haultra.get_db()
check(dict(conn.execute("SELECT * FROM users WHERE id=?", (blocked_driver_id,)).fetchone()) == before_user,
      "in-progress blocker leaves user unchanged")
check(conn.execute("SELECT assigned_to FROM routes WHERE id=?", (blocked_route_id,)).fetchone()["assigned_to"] == blocked_driver_id,
      "in-progress blocker leaves route unchanged")
check(conn.execute("SELECT COUNT(*) n FROM account_deletion_audit").fetchone()["n"] == before_audit,
      "in-progress blocker writes no audit or deletion data")
conn.close()


# Last active boss blocks deletion with zero database changes.
conn = haultra.get_db()
solo_company_id = create_company(conn, "solo-boss-company")
solo_boss_id = create_user(conn, solo_company_id, "solo-boss", "boss", "Solo Boss")
conn.execute("UPDATE companies SET owner_id=? WHERE id=?", (solo_boss_id, solo_company_id))
conn.commit()
solo_before = dict(conn.execute("SELECT * FROM users WHERE id=?", (solo_boss_id,)).fetchone())
audit_before = conn.execute("SELECT COUNT(*) n FROM account_deletion_audit").fetchone()["n"]
solo_boss = conn.execute("SELECT * FROM users WHERE id=?", (solo_boss_id,)).fetchone()
conn.close()
solo_client = haultra.app.test_client()
set_user_session(solo_client, solo_boss)
page = solo_client.get("/account/delete")
blocked = solo_client.post(
    "/account/delete",
    data={"_csrf_token": csrf_from(page), "password": "ValidDeletionPassword!1", "confirm_delete": "DELETE"},
    follow_redirects=True,
)
check(b"last active boss" in blocked.data, "last boss receives the correct blocker")
conn = haultra.get_db()
check(dict(conn.execute("SELECT * FROM users WHERE id=?", (solo_boss_id,)).fetchone()) == solo_before,
      "last-boss blocker leaves account unchanged")
check(conn.execute("SELECT COUNT(*) n FROM account_deletion_audit").fetchone()["n"] == audit_before,
      "last-boss blocker writes zero deletion data")
conn.close()


# Customer deletion revokes auth while preserving hauler-owned sites and bins.
conn = haultra.get_db()
customer_company_id = create_company(conn, "portal-delete-company")
customer_boss_id = create_user(conn, customer_company_id, "portal-boss", "boss")
customer_driver_id = create_user(conn, customer_company_id, "portal-driver")
conn.execute("UPDATE companies SET owner_id=? WHERE id=?", (customer_boss_id, customer_company_id))
portal_token = "customer-portal-token-for-deletion"
cur = conn.execute(
    """INSERT INTO customers
       (company_id,business_name,contact_name,phone,email,portal_token,is_active,created_at)
       VALUES (?,'Preserved Business LLC','Personal Contact','(757) 555-0123',
               'contact@example.invalid',?,1,?)""",
    (customer_company_id, portal_token, haultra.now_ts()),
)
customer_id = cur.lastrowid
cur = conn.execute(
    """INSERT INTO sites(customer_id,address,lat,lng,notes,created_at)
       VALUES (?,'500 Preserved Service Road',36.91,-76.11,'Hauler gate instructions',?)""",
    (customer_id, haultra.now_ts()),
)
site_id = cur.lastrowid
route_id, stop_id = add_route(conn, customer_company_id, customer_boss_id, customer_driver_id, "completed", "Portal History")
conn.execute("UPDATE stops SET customer_id=?,address='500 Preserved Service Road' WHERE id=?", (customer_id, stop_id))
cur = conn.execute(
    """INSERT INTO bins(customer_id,site_id,size,dropped_at,label,drop_stop_id)
       VALUES (?,?,'20yd','2026-08-20','Hauler Bin Label',?)""",
    (customer_id, site_id, stop_id),
)
bin_id = cur.lastrowid
cur = conn.execute(
    """INSERT INTO containers(company_id,size,label,status,created_at)
       VALUES (?,'20yd','PORTAL-CAN','deployed',?)""",
    (customer_company_id, haultra.now_ts()),
)
container_id = cur.lastrowid
conn.execute(
    """INSERT INTO customer_containers
       (company_id,address,size,container_id,delivered_stop_id,delivered_at,status,created_at)
       VALUES (?,'500 Preserved Service Road','20yd',?,?,?,'on_site',?)""",
    (customer_company_id, container_id, stop_id, haultra.now_ts(), haultra.now_ts()),
)
conn.execute(
    """INSERT INTO orders
       (customer_name,phone,email,address,city,state,zip_code,service_type,status,company_id,created_at)
       VALUES ('Personal Contact','7575550123','contact@example.invalid','500 Preserved Service Road',
               'Review City','VA','00000','Delivery','closed',?,?)""",
    (customer_company_id, haultra.now_ts()),
)
conn.execute(
    """INSERT INTO orders
       (customer_name,phone,email,address,service_type,status,company_id,created_at)
       VALUES ('Unrelated Person','7575559999','other@example.invalid','Other Road','Delivery','closed',?,?)""",
    (customer_company_id, haultra.now_ts()),
)
conn.commit()
site_before = dict(conn.execute("SELECT * FROM sites WHERE id=?", (site_id,)).fetchone())
bin_before = dict(conn.execute("SELECT * FROM bins WHERE id=?", (bin_id,)).fetchone())
conn.close()
portal_client = haultra.app.test_client()
page = portal_client.get(f"/c/{portal_token}/delete")
deleted = portal_client.post(
    f"/c/{portal_token}/delete",
    data={"_csrf_token": csrf_from(page), "portal_credential": portal_token, "confirm_delete": "DELETE"},
)
check(deleted.status_code == 200, "customer completes token-confirmed portal deletion")
check(portal_client.get(f"/c/{portal_token}").status_code == 404,
      "old customer portal token is revoked")
conn = haultra.get_db()
customer = conn.execute("SELECT * FROM customers WHERE id=?", (customer_id,)).fetchone()
check(not customer["is_active"] and customer["contact_name"] is None
      and customer["phone"] is None and customer["email"] is None
      and customer["portal_token"] != portal_token,
      "customer contact data is anonymized and token replaced")
check(dict(conn.execute("SELECT * FROM sites WHERE id=?", (site_id,)).fetchone()) == site_before,
      "site address coordinates and hauler notes remain intact")
check(dict(conn.execute("SELECT * FROM bins WHERE id=?", (bin_id,)).fetchone()) == bin_before,
      "bin facts and hauler label remain intact")
notification = conn.execute(
    "SELECT * FROM boss_notifications WHERE company_id=? AND site_id=?",
    (customer_company_id, site_id),
).fetchone()
check(notification and notification["deployment_state"] == "deployed",
      "boss notification fires and flags deployed bin")
orders = conn.execute("SELECT * FROM orders WHERE company_id=? ORDER BY id", (customer_company_id,)).fetchall()
check(orders[0]["email"] is None and orders[0]["address"] == "[redacted]",
      "exact-match order PII is scrubbed")
check(orders[1]["email"] == "other@example.invalid",
      "unmatched tenant order is not guessed or modified")
conn.close()


# Disposable App Review user is genuinely deleted, then repaired by the seed.
conn = haultra.get_db()
demo_user = conn.execute(
    "SELECT * FROM users WHERE username=?",
    (os.environ["APP_REVIEW_DELETE_USERNAME"],),
).fetchone()
check(demo_user is not None, "disposable demo user is initially seeded")
old_demo_id = demo_user["id"]
conn.close()
demo_client = haultra.app.test_client()
set_user_session(demo_client, demo_user)
page = demo_client.get("/account/delete")
deleted = demo_client.post(
    "/account/delete",
    data={"_csrf_token": csrf_from(page), "password": os.environ["APP_REVIEW_DELETE_PASSWORD"], "confirm_delete": "DELETE"},
)
check(deleted.status_code == 302, "disposable demo user completes genuine deletion")
conn = haultra.get_db()
check(not conn.execute("SELECT is_active FROM users WHERE id=?", (old_demo_id,)).fetchone()["is_active"],
      "deleted demo user remains an inactive tombstone before repair")
conn.close()
repair = haultra.verify_app_review_demo(repair=True)
check(repair["ready"] and repair["repaired"], "demo verifier repairs deleted disposable user")
conn = haultra.get_db()
restored = conn.execute(
    "SELECT * FROM users WHERE username=? AND is_active=1",
    (os.environ["APP_REVIEW_DELETE_USERNAME"],),
).fetchone()
check(restored and restored["id"] != old_demo_id
      and check_password_hash(restored["password_hash"], os.environ["APP_REVIEW_DELETE_PASSWORD"]),
      "next startup repair restores working disposable credentials")
conn.close()


print("\nALL ACCOUNT-DELETION END-TO-END TESTS PASSED")
