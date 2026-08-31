#!/usr/bin/env python3
"""Fail-fast production configuration and persistent-data release gate.

Run this from the production shell before submitting either native app:

    python3 scripts/release_check.py

The script never prints secret values and never modifies the database.
"""

import os
import re
import shutil
import sqlite3
import sys
from pathlib import Path
from urllib.parse import urlparse


errors = []
warnings = []


def passed(message):
    print(f"PASS - {message}")


def failed(message):
    errors.append(message)
    print(f"FAIL - {message}")


def warned(message):
    warnings.append(message)
    print(f"WARN - {message}")


def require_secret(name, minimum=1):
    value = os.environ.get(name, "").strip()
    if len(value) < minimum:
        failed(f"{name} is configured")
        return ""
    passed(f"{name} is configured")
    return value


secret_key = require_secret("SECRET_KEY", 32)
if secret_key and secret_key.lower() in {"secret", "changeme", "change-me"}:
    failed("SECRET_KEY is not a placeholder")
elif secret_key:
    passed("SECRET_KEY is not an obvious placeholder")

if os.environ.get("FLASK_DEBUG", "0") != "0":
    failed("FLASK_DEBUG is disabled")
else:
    passed("FLASK_DEBUG is disabled")

public_base = os.environ.get("PUBLIC_BASE_URL", "").strip().rstrip("/")
parsed = urlparse(public_base)
if parsed.scheme == "https" and parsed.netloc and not parsed.path:
    passed("PUBLIC_BASE_URL is a canonical HTTPS origin")
else:
    failed("PUBLIC_BASE_URL is a canonical HTTPS origin")

require_secret("RESEND_API_KEY")
from_email = os.environ.get("RESEND_FROM_EMAIL", "").strip()
if from_email and "onboarding@resend.dev" not in from_email:
    passed("RESEND_FROM_EMAIL is set to a non-default sender")
else:
    failed("RESEND_FROM_EMAIL is set to a verified production sender")

for stripe_name in (
    "STRIPE_SECRET_KEY",
    "STRIPE_PRICE_STARTER",
    "STRIPE_PRICE_PRO",
    "STRIPE_WEBHOOK_SECRET",
):
    require_secret(stripe_name)

apple_team = os.environ.get("APPLE_TEAM_ID", "").strip()
if re.fullmatch(r"[A-Z0-9]{10}", apple_team):
    passed("APPLE_TEAM_ID has the expected format")
else:
    failed("APPLE_TEAM_ID has the expected 10-character format")

android_fp = os.environ.get("ANDROID_SHA256_FINGERPRINT", "").strip().upper()
if re.fullmatch(r"(?:[0-9A-F]{2}:){31}[0-9A-F]{2}", android_fp):
    passed("ANDROID_SHA256_FINGERPRINT has the expected SHA-256 format")
else:
    failed("ANDROID_SHA256_FINGERPRINT uses the Play app-signing SHA-256 format")

require_secret("BACKUP_S3_BUCKET")
require_secret("AWS_ACCESS_KEY_ID")
require_secret("AWS_SECRET_ACCESS_KEY")

database_value = os.environ.get("DATABASE_PATH", "").strip()
database_path = Path(database_value).expanduser().resolve() if database_value else None
if not database_path or not database_path.is_file():
    failed("DATABASE_PATH points to the existing persistent production database")
else:
    passed("DATABASE_PATH points to the existing persistent production database")
    try:
        uri = f"file:{database_path}?mode=ro"
        conn = sqlite3.connect(uri, uri=True, timeout=10)
        quick = conn.execute("PRAGMA quick_check(1)").fetchone()
        fk_error = conn.execute("PRAGMA foreign_key_check").fetchone()
        boss = conn.execute(
            "SELECT id FROM users WHERE role='boss' AND is_active=1 LIMIT 1"
        ).fetchone()
        conn.close()
        passed("SQLite quick_check passes") if quick and quick[0] == "ok" else failed("SQLite quick_check passes")
        passed("SQLite has no foreign-key violations") if fk_error is None else failed("SQLite has no foreign-key violations")
        passed("An active boss account exists") if boss else failed("An active boss account exists")
        if boss and os.environ.get("BOOTSTRAP_ADMIN_PASSWORD", "").strip():
            failed("BOOTSTRAP_ADMIN_PASSWORD was removed after first-account creation")
        elif boss:
            passed("BOOTSTRAP_ADMIN_PASSWORD was removed after first-account creation")
    except (OSError, sqlite3.Error) as exc:
        failed(f"Production database can be inspected safely ({type(exc).__name__})")

upload_value = os.environ.get("UPLOAD_FOLDER", "").strip()
upload_path = Path(upload_value).expanduser().resolve() if upload_value else None
if not upload_path or not upload_path.is_dir() or not os.access(upload_path, os.W_OK):
    failed("UPLOAD_FOLDER exists on writable persistent storage")
else:
    passed("UPLOAD_FOLDER exists on writable persistent storage")
    free = shutil.disk_usage(upload_path).free
    if free >= 128 * 1024 * 1024:
        passed("Upload storage has at least 128 MB free")
    else:
        failed("Upload storage has at least 128 MB free")

if warnings:
    print(f"\n{len(warnings)} warning(s).")
if errors:
    print(f"\nRELEASE BLOCKED: {len(errors)} required check(s) failed.")
    sys.exit(1)

print("\nALL PRODUCTION RELEASE CHECKS PASSED")
