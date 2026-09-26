"""Deleting a route or a stop that has a logged issue must not 500.

route_exceptions holds a foreign key onto stops(id) and PRAGMA foreign_keys is
ON, but _detach_stop_references() never cleared it. Deleting anything whose
stops carried an exception — that is, anything where a driver tapped Track
Issue — failed with "FOREIGN KEY constraint failed", which reaches the user as
a 500 with the row still on the page.

The App Review demo seed plants an exception on the first stop of its route, so
a reviewer (or the developer) clearing demo data hit this immediately.

Both delete paths are covered: delete_stop() and delete_route() share
_detach_stop_references() and both delete stops straight after it, so a fix
applied to one alone would leave the other broken.

Exceptions are deleted rather than detached because route_exceptions CHECKs that
exactly one of stop_id / disposal_site_id is set — nulling stop_id would trade
the FK failure for a CHECK failure. Exceptions logged against a disposal site
carry no stop_id and must survive, which is asserted here too.
"""

import os
import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TMP = tempfile.TemporaryDirectory()
os.environ["DATABASE_PATH"] = str(Path(TMP.name) / "route-delete.db")
os.environ["UPLOAD_FOLDER"] = str(Path(TMP.name) / "uploads")
os.environ["SECRET_KEY"] = "route-delete-fk-test"
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

failures = []


def ok(condition, message):
    print(("PASS" if condition else "FAIL") + " - " + message)
    if not condition:
        failures.append(message)


def csrf_from(response):
    match = re.search(rb'<meta name="csrf-token" content="([^"]+)"', response.data)
    if not match:
        raise AssertionError("CSRF token missing")
    return match.group(1).decode()


def demo_company():
    with haultra.app.app_context():
        return haultra.get_db().execute(
            "SELECT id FROM companies WHERE slug=?", (haultra.APP_REVIEW_DEMO_SLUG,)
        ).fetchone()["id"]


def open_routes(company_id):
    with haultra.app.app_context():
        return [
            (r["id"], r["route_name"]) for r in haultra.get_db().execute(
                "SELECT id, route_name FROM routes WHERE company_id=? AND status='open'"
                " ORDER BY id", (company_id,)
            ).fetchall()
        ]


def stops_of(route_id):
    with haultra.app.app_context():
        return [
            r["id"] for r in haultra.get_db().execute(
                "SELECT id FROM stops WHERE route_id=? ORDER BY stop_order, id",
                (route_id,),
            ).fetchall()
        ]


def exceptions_on(stop_ids):
    if not stop_ids:
        return 0
    with haultra.app.app_context():
        marks = ",".join("?" * len(stop_ids))
        return haultra.get_db().execute(
            f"SELECT COUNT(*) n FROM route_exceptions WHERE stop_id IN ({marks})",
            list(stop_ids),
        ).fetchone()["n"]


def log_exception(company_id, stop_id, uuid):
    with haultra.app.app_context():
        conn = haultra.get_db()
        driver = conn.execute(
            "SELECT id FROM users WHERE company_id=? AND role='driver' AND is_active=1"
            " ORDER BY id LIMIT 1", (company_id,)
        ).fetchone()
        conn.execute(
            """INSERT INTO route_exceptions
               (company_id,client_uuid,stop_id,driver_id,type,note,occurred_at,created_at)
               VALUES (?,?,?,?,'GATE_CLOSED',?,?,?)""",
            (company_id, uuid, stop_id, driver["id"], "fk regression fixture",
             haultra.now_ts(), haultra.now_ts()),
        )
        conn.commit()


with haultra.app.app_context():
    status = haultra.verify_app_review_demo(repair=True)
ok(status["ready"], "App Review demo tenant seeded and ready")

company_id = demo_company()

client = haultra.app.test_client()
page = client.get("/login")
login = client.post(
    "/login",
    data={
        "_csrf_token": csrf_from(page),
        "username": os.environ["APP_REVIEW_BOSS_USERNAME"],
        "password": os.environ["APP_REVIEW_BOSS_PASSWORD"],
    },
    follow_redirects=True,
)
ok(login.status_code == 200, "signed in as the demo boss")

routes = open_routes(company_id)
ok(len(routes) >= 1, f"demo tenant has an open route ({len(routes)} found)")

# A site exception carries no stop_id and must survive both deletes below.
with haultra.app.app_context():
    conn = haultra.get_db()
    site = conn.execute("SELECT id FROM disposal_sites LIMIT 1").fetchone()
    driver = conn.execute(
        "SELECT id FROM users WHERE company_id=? AND role='driver' AND is_active=1"
        " ORDER BY id LIMIT 1", (company_id,)
    ).fetchone()
    site_exception = bool(site and driver)
    if site_exception:
        conn.execute(
            """INSERT INTO route_exceptions
               (company_id,client_uuid,stop_id,disposal_site_id,driver_id,type,
                note,occurred_at,created_at)
               VALUES (?,?,NULL,?,?,'GATE_CLOSED',?,?,?)""",
            (company_id, "fk-test-site-exception", site["id"], driver["id"],
             "site exception, no stop", haultra.now_ts(), haultra.now_ts()),
        )
        conn.commit()

# ── Stop deletion ─────────────────────────────────────────────────────────
route_id, route_name = routes[0]
stop_ids = stops_of(route_id)
ok(len(stop_ids) >= 2, f"{route_name} has stops to work with ({len(stop_ids)})")

victim = stop_ids[0]
log_exception(company_id, victim, "fk-test-stop-exception")
ok(exceptions_on([victim]) > 0, "the stop carries a logged exception")

page = client.get(f"/route/{route_id}")
removed = client.post(
    f"/stop/{victim}/delete",
    data={"_csrf_token": csrf_from(page)},
    follow_redirects=True,
)
ok(removed.status_code == 200, "deleting a stop with an exception returns 200, not a 500")
with haultra.app.app_context():
    ok(
        haultra.get_db().execute(
            "SELECT id FROM stops WHERE id=?", (victim,)
        ).fetchone() is None,
        "the stop row is actually gone",
    )
ok(exceptions_on([victim]) == 0, "its exception went with it")

# ── Route deletion ────────────────────────────────────────────────────────
remaining = stops_of(route_id)
ok(bool(remaining), "the route still has stops after the single-stop delete")
if remaining:
    log_exception(company_id, remaining[0], "fk-test-route-exception")
    ok(exceptions_on(remaining) > 0, "a remaining stop carries a logged exception")

page = client.get("/routes")
deleted = client.post(
    f"/route/{route_id}/delete",
    data={"_csrf_token": csrf_from(page)},
    follow_redirects=True,
)
ok(deleted.status_code == 200, f"deleting {route_name} returns 200, not a 500")

with haultra.app.app_context():
    conn = haultra.get_db()
    ok(
        conn.execute("SELECT id FROM routes WHERE id=?", (route_id,)).fetchone() is None,
        "the route row is actually gone",
    )
    ok(
        conn.execute(
            "SELECT COUNT(*) n FROM stops WHERE route_id=?", (route_id,)
        ).fetchone()["n"] == 0,
        "its stops went with it",
    )
ok(exceptions_on(remaining) == 0, "its exceptions went with it")

if site_exception:
    with haultra.app.app_context():
        kept = haultra.get_db().execute(
            "SELECT COUNT(*) n FROM route_exceptions "
            "WHERE client_uuid='fk-test-site-exception'"
        ).fetchone()["n"]
    ok(kept == 1, "a disposal-site exception with no stop_id is left alone")

# The repair pass must rebuild what the deletes removed.
with haultra.app.app_context():
    restored = haultra.verify_app_review_demo(repair=True)
ok(restored["ready"], "repair pass rebuilds the demo tenant after deletion")

rebuilt = open_routes(company_id)
ok(len(rebuilt) == 1, f"rebuilt as a single lane, not one route per stop ({len(rebuilt)})")
if rebuilt:
    ok(len(stops_of(rebuilt[0][0])) == 3, "the rebuilt lane carries its three stops")

if failures:
    raise SystemExit("FAILED: " + "; ".join(failures))

print("\nALL ROUTE/STOP DELETE TESTS PASSED")
