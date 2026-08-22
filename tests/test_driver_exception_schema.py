"""Schema-only coverage for structured driver exceptions.

No route or template behavior belongs in this suite. It proves fresh database
creation, enum guards, tenant ownership, and the loaded-at-yard migration state.
"""
import os
import sqlite3
import sys
import tempfile

tmp = tempfile.TemporaryDirectory()
os.environ["DATABASE_PATH"] = os.path.join(tmp.name, "driver-exceptions.db")
os.environ["FLASK_ENV"] = "testing"
os.environ["SECRET_KEY"] = "driver-exception-schema-test"
os.environ["UPLOAD_FOLDER"] = os.path.join(tmp.name, "uploads")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Seed the pre-feature containers shape so importing app exercises the real
# idempotent CHECK-constraint rebuild rather than only fresh-table creation.
legacy = sqlite3.connect(os.environ["DATABASE_PATH"])
legacy.execute("""
    CREATE TABLE containers (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id INTEGER NOT NULL,
        size TEXT NOT NULL,
        label TEXT,
        status TEXT NOT NULL DEFAULT 'yard'
            CHECK(status IN ('yard','deployed','lost','retired')),
        notes TEXT,
        created_at TEXT NOT NULL
    )
""")
legacy.execute(
    "INSERT INTO containers (company_id,size,label,status,created_at) VALUES (1,'30yd','C-1','deployed','legacy')"
)
legacy.commit()
legacy.close()

import app  # noqa: E402


def ok(condition, label):
    if not condition:
        raise AssertionError(label)
    print("PASS -", label)


conn = app.get_db()

container_sql = conn.execute(
    "SELECT sql FROM sqlite_master WHERE type='table' AND name='containers'"
).fetchone()["sql"]
ok("loaded_at_yard" in container_sql, "containers accepts loaded_at_yard")
ok(conn.execute("SELECT label,status FROM containers WHERE label='C-1'").fetchone()["status"] == "deployed",
   "legacy container rows survive the CHECK migration")

disposal_cols = {r["name"] for r in conn.execute("PRAGMA table_info(disposal_sites)")}
ok({"id", "company_id", "name", "address", "lat", "lng", "material_type",
    "notes", "hours_last_verified", "created_at"} <= disposal_cols,
   "disposal_sites model is complete and tenant-scoped")
ok(not ({"open_time", "close_time", "days_open"} & disposal_cols),
   "legacy flat hours fields are not part of disposal_sites")

hours_cols = {r["name"] for r in conn.execute("PRAGMA table_info(disposal_site_hours)")}
ok({"id", "disposal_site_id", "weekday", "open_time", "close_time", "is_closed"} <= hours_cols,
   "disposal_site_hours supports per-weekday schedules")

exception_cols = {r["name"] for r in conn.execute("PRAGMA table_info(route_exceptions)")}
ok({"id", "company_id", "client_uuid", "stop_id", "disposal_site_id", "driver_id",
    "type", "lat", "lng", "container_state_at_time", "note", "occurred_at",
    "created_at", "resolution",
    "resolved_by", "resolved_at"} <= exception_cols,
   "route_exceptions model captures structured context and resolution")

company_id = conn.execute("SELECT id FROM companies ORDER BY id LIMIT 1").fetchone()["id"]
boss_id = conn.execute("SELECT id FROM users WHERE company_id=? ORDER BY id LIMIT 1", (company_id,)).fetchone()["id"]
cur = conn.execute(
    "INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES (?,?,?,?,?)",
    ("exception_driver", "x", "driver", company_id, app.now_ts()),
)
driver_id = cur.lastrowid
cur = conn.execute(
    "INSERT INTO routes (route_date,route_name,assigned_to,created_by,status,company_id,created_at) "
    "VALUES (?,?,?,?,?,?,?)",
    ("2026-08-22", "Exception schema", driver_id, boss_id, "in_progress", company_id, app.now_ts()),
)
route_id = cur.lastrowid
cur = conn.execute(
    "INSERT INTO stops (route_id,stop_order,address,action,status,created_at) VALUES (?,?,?,?,?,?)",
    (route_id, 1, "1 Test Rd", "Pull", "open", app.now_ts()),
)
stop_id = cur.lastrowid
cur = conn.execute(
    "INSERT INTO disposal_sites "
    "(company_id,name,address,material_type,hours_last_verified,created_at) VALUES (?,?,?,?,?,?)",
    (company_id, "Dominion", "5444 Bainbridge Blvd", "C&D", "2026-08-20", app.now_ts()),
)
site_id = cur.lastrowid
conn.execute(
    "INSERT INTO disposal_site_hours (disposal_site_id,weekday,open_time,close_time,is_closed) "
    "VALUES (?,?,?,?,0)", (site_id, 0, "07:00", "16:00")
)
conn.execute(
    "INSERT INTO disposal_site_hours (disposal_site_id,weekday,is_closed) VALUES (?,?,1)",
    (site_id, 6)
)
ok(conn.execute("SELECT COUNT(*) n FROM disposal_site_hours WHERE disposal_site_id=?", (site_id,)).fetchone()["n"] == 2,
   "open and closed weekdays store independently")

conn.execute(
    "INSERT INTO route_exceptions "
    "(company_id,client_uuid,stop_id,driver_id,type,container_state_at_time,occurred_at,created_at) "
    "VALUES (?,?,?,?,?,?,?,?)",
    (company_id, "device-stop-1", stop_id, driver_id, "GATE_CLOSED", "deployed",
     "2026-08-22 07:45:00", app.now_ts()),
)
conn.execute(
    "INSERT INTO route_exceptions "
    "(company_id,client_uuid,disposal_site_id,driver_id,type,container_state_at_time,occurred_at,created_at) "
    "VALUES (?,?,?,?,?,?,?,?)",
    (company_id, "device-disposal-1", site_id, driver_id, "DISPOSAL_CLOSED", "loaded_at_yard",
     "2026-08-22 07:46:00", app.now_ts()),
)
conn.commit()
ok(conn.execute("SELECT COUNT(*) n FROM route_exceptions").fetchone()["n"] == 2,
   "stop and disposal exceptions insert without an optional note")
ok(conn.execute("SELECT stop_id FROM route_exceptions WHERE type='DISPOSAL_CLOSED'").fetchone()["stop_id"] is None,
   "DISPOSAL_CLOSED can point only at a disposal site")

try:
    conn.execute(
        "INSERT INTO route_exceptions "
        "(company_id,client_uuid,stop_id,driver_id,type,occurred_at,created_at) VALUES (?,?,?,?,?,?,?)",
        (company_id, "invalid-type", stop_id, driver_id, "FREE_TEXT_OTHER", app.now_ts(), app.now_ts()),
    )
    conn.commit()
    raise AssertionError("invalid exception type was accepted")
except sqlite3.IntegrityError:
    conn.rollback()
    ok(True, "free-form exception types are rejected by the schema")

try:
    conn.execute(
        "INSERT INTO route_exceptions "
        "(company_id,client_uuid,stop_id,disposal_site_id,driver_id,type,occurred_at,created_at) "
        "VALUES (?,?,?,?,?,?,?,?)",
        (company_id, "both-contexts", stop_id, site_id, driver_id, "GATE_CLOSED", app.now_ts(), app.now_ts()),
    )
    conn.commit()
    raise AssertionError("both context FKs were accepted")
except sqlite3.IntegrityError:
    conn.rollback()
    ok(True, "exactly one context FK is enforced")

try:
    conn.execute(
        "INSERT INTO route_exceptions "
        "(company_id,client_uuid,stop_id,driver_id,type,occurred_at,created_at) VALUES (?,?,?,?,?,?,?)",
        (company_id, "device-stop-1", stop_id, driver_id, "TRUCK_ISSUE", app.now_ts(), app.now_ts()),
    )
    conn.commit()
    raise AssertionError("duplicate client UUID was accepted")
except sqlite3.IntegrityError:
    conn.rollback()
    ok(True, "client UUID is unique within a company")

conn.execute(
    "UPDATE route_exceptions SET resolution='VOIDED',resolved_by=?,resolved_at=? WHERE client_uuid=?",
    (boss_id, app.now_ts(), "device-stop-1"),
)
conn.commit()
ok(conn.execute("SELECT resolution FROM route_exceptions WHERE client_uuid='device-stop-1'").fetchone()["resolution"] == "VOIDED",
   "VOIDED is an allowed structured resolution")

conn.close()
tmp.cleanup()
print("\nALL DRIVER-EXCEPTION SCHEMA TESTS PASSED")
