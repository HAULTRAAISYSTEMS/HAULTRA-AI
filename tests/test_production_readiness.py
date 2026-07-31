#!/usr/bin/env python3
"""Regression coverage for production security and retention controls."""

import os
import re
import sys
import tempfile
import io
import logging
from datetime import datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

os.environ.setdefault("SECRET_KEY", "production-readiness-test-secret")
os.environ["SESSION_COOKIE_SECURE"] = "1"
_tmp = tempfile.TemporaryDirectory()
os.environ["DATABASE_PATH"] = os.path.join(_tmp.name, "production.db")
os.environ["UPLOAD_FOLDER"] = os.path.join(_tmp.name, "uploads")
os.environ["PUBLIC_BASE_URL"] = "https://haultra-systems.com"

from werkzeug.security import generate_password_hash

import app as haultra


def check(condition, label):
    if not condition:
        raise AssertionError(label)
    print(f"PASS - {label}")


haultra.init_db()

check(
    haultra.password_policy_error("short") is not None,
    "short passwords are rejected",
)
check(
    haultra.password_policy_error("a-long-production-password") is None,
    "long passwords are accepted",
)

conn = haultra.get_db()
check(
    conn.execute("PRAGMA foreign_keys").fetchone()[0] == 1,
    "SQLite foreign keys are enabled",
)
check(
    conn.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name='auth_rate_limits'"
    ).fetchone()
    is not None,
    "shared authentication rate-limit table exists",
)
check(
    conn.execute(
        "SELECT 1 FROM sqlite_master "
        "WHERE type='table' AND name='account_deletion_requests'"
    ).fetchone()
    is not None,
    "public deletion requests have durable storage",
)
conn.close()

client = haultra.app.test_client()
with haultra.app.test_request_context("/forgot-password", base_url="https://evil.example"):
    check(
        haultra.public_url("reset_password", token="safe-token")
        == "https://haultra-systems.com/reset-password/safe-token",
        "absolute security links ignore an untrusted Host header",
    )

os.environ.pop("RESEND_API_KEY", None)
log_stream = io.StringIO()
log_handler = logging.StreamHandler(log_stream)
haultra.app.logger.addHandler(log_handler)
try:
    check(
        haultra.send_email(
            "private@example.com",
            "private subject",
            "reset token TOP-SECRET-TOKEN",
        ) is False,
        "missing email provider fails closed",
    )
finally:
    haultra.app.logger.removeHandler(log_handler)
email_log = log_stream.getvalue()
check(
    "TOP-SECRET-TOKEN" not in email_log and "private@example.com" not in email_log,
    "email failures never log message bodies, tokens, or recipients",
)

response = client.get("/privacy", base_url="https://haultra-systems.com")
check(response.status_code == 200, "privacy page renders")
check(
    response.headers.get("Strict-Transport-Security", "").startswith("max-age="),
    "HSTS header is present",
)
check(response.headers.get("X-Frame-Options") == "DENY", "framing is denied")
cookie = response.headers.get("Set-Cookie", "")
check("Secure" in cookie and "HttpOnly" in cookie, "session cookie is secure and HttpOnly")
check("SameSite=Lax" in cookie, "session cookie has SameSite protection")
login_page = client.get("/login", base_url="https://haultra-systems.com")
check(
    b"__haultraClearDeviceData" in login_page.data,
    "login clears prior-account offline data before account switching",
)
check(
    login_page.headers.get("Cache-Control") == "private, no-store",
    "authentication pages are not stored in the browser HTTP cache",
)
check(client.get("/init").status_code == 405, "database initialization cannot run through GET")
check(client.get("/dispatch").status_code == 404, "unused legacy Firebase dispatch UI is closed")
check(client.get("/route").status_code == 404, "unused legacy Firebase driver UI is closed")

page = client.get("/delete-account", base_url="https://haultra-systems.com")
csrf_match = re.search(
    rb'<meta name="csrf-token" content="([^"]+)"',
    page.data,
)
check(csrf_match is not None, "public deletion page includes CSRF protection")
response = client.post(
    "/delete-account",
    data={
        "_csrf_token": csrf_match.group(1).decode(),
        "company_name": "Deletion Test Company",
        "account_email": "owner@deletion-test.example",
        "confirm": "yes",
    },
    base_url="https://haultra-systems.com",
)
check(response.status_code == 200, "public deletion request is accepted")
conn = haultra.get_db()
stored_request = conn.execute(
    """SELECT status FROM account_deletion_requests
       WHERE company_name=? AND account_email=?""",
    ("Deletion Test Company", "owner@deletion-test.example"),
).fetchone()
conn.close()
check(
    stored_request is not None and stored_request["status"] == "pending",
    "public deletion request survives email-provider failure",
)

response = client.patch(
    "/api/customers/1",
    json={"business_name": "Blocked"},
    base_url="https://haultra-systems.com",
)
check(response.status_code == 403, "PATCH requests require CSRF")

conn = haultra.get_db()
default_company = conn.execute("SELECT id FROM companies ORDER BY id LIMIT 1").fetchone()["id"]
due_date = (datetime.now() - timedelta(days=1)).strftime("%Y-%m-%d")
cursor = conn.execute(
    """INSERT INTO users
       (username, password_hash, role, full_name, phone, email, company_id,
        created_at, is_active, pending_deletion_at)
       VALUES (?, ?, 'driver', ?, ?, ?, ?, ?, 0, ?)""",
    (
        "delete-me",
        generate_password_hash("a-long-production-password"),
        "Personal Name",
        "555-0100",
        "person@example.com",
        default_company,
        haultra.now_ts(),
        due_date,
    ),
)
due_user_id = cursor.lastrowid

closed_at = (datetime.now() - timedelta(days=31)).strftime("%Y-%m-%d %H:%M:%S")
cursor = conn.execute(
    """INSERT INTO companies
       (name, slug, subscription_plan, subscription_status, max_drivers,
        created_at, closed_at)
       VALUES ('Due Company', 'due-company', 'trial', 'cancelled', 5, ?, ?)""",
    (haultra.now_ts(), closed_at),
)
due_company_id = cursor.lastrowid
cursor = conn.execute(
    """INSERT INTO users
       (username, password_hash, role, full_name, company_id, created_at, is_active)
       VALUES ('due-owner', ?, 'boss', 'Due Owner', ?, ?, 0)""",
    (
        generate_password_hash("another-production-password"),
        due_company_id,
        haultra.now_ts(),
    ),
)
conn.execute(
    "UPDATE companies SET owner_id=? WHERE id=?",
    (cursor.lastrowid, due_company_id),
)
conn.commit()
conn.close()

result = haultra.purge_due_deletions()
check(result["anonymized_users"] == 1, "due individual account is anonymized")
check(result["purged_companies"] == 1, "due closed company is purged")

conn = haultra.get_db()
user = conn.execute("SELECT * FROM users WHERE id=?", (due_user_id,)).fetchone()
check(
    user is not None
    and user["email"] is None
    and user["phone"] is None
    and user["full_name"] is None,
    "individual personal fields are erased",
)
check(
    conn.execute("SELECT 1 FROM companies WHERE id=?", (due_company_id,)).fetchone()
    is None,
    "closed company row is removed",
)
check(
    conn.execute("PRAGMA foreign_key_check").fetchone() is None,
    "deletion maintenance leaves no foreign-key violations",
)
conn.close()

print("\nALL PRODUCTION-READINESS TESTS PASSED")
