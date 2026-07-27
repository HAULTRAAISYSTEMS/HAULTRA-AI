#!/usr/bin/env python3
"""Create or refresh the isolated account used by Apple and Google review.

Run this from the deployed service shell with APP_REVIEW_USERNAME and
APP_REVIEW_PASSWORD set. The command is idempotent and never prints the
password. Put the resulting credentials only in the stores' private review
fields, never in source control or public release notes.
"""

import os
import sys
from datetime import date
from pathlib import Path

from werkzeug.security import generate_password_hash

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from app import get_db, init_db, now_ts


def required_env(name):
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"{name} must be set")
    return value


def main():
    username = required_env("APP_REVIEW_USERNAME")
    password = required_env("APP_REVIEW_PASSWORD")
    company_name = os.environ.get(
        "APP_REVIEW_COMPANY", "HAULTRA App Review Fleet"
    ).strip()
    slug = "haultra-app-review"
    driver_username = f"{username}-driver"

    init_db()
    conn = get_db()
    try:
        company = conn.execute(
            "SELECT id FROM companies WHERE slug=?", (slug,)
        ).fetchone()
        if company:
            company_id = company["id"]
            conn.execute(
                """UPDATE companies
                   SET name=?, subscription_plan='pro',
                       subscription_status='active', max_drivers=30,
                       trial_ends_at=NULL, closed_at=NULL
                   WHERE id=?""",
                (company_name, company_id),
            )
        else:
            cur = conn.execute(
                """INSERT INTO companies
                   (name, slug, subscription_plan, subscription_status,
                    max_drivers, trial_ends_at, created_at)
                   VALUES (?, ?, 'pro', 'active', 30, NULL, ?)""",
                (company_name, slug, now_ts()),
            )
            company_id = cur.lastrowid

        reviewer = conn.execute(
            "SELECT id FROM users WHERE username=? COLLATE NOCASE", (username,)
        ).fetchone()
        password_hash = generate_password_hash(password)
        if reviewer:
            reviewer_id = reviewer["id"]
            conn.execute(
                """UPDATE users
                   SET password_hash=?, role='boss', full_name='App Review',
                       company_id=?, is_active=1, pending_deletion_at=NULL,
                       role_owner=1
                   WHERE id=?""",
                (password_hash, company_id, reviewer_id),
            )
        else:
            cur = conn.execute(
                """INSERT INTO users
                   (username, password_hash, role, role_owner, full_name,
                    phone, email, company_id, created_at, is_active)
                   VALUES (?, ?, 'boss', 1, 'App Review', '', NULL, ?, ?, 1)""",
                (username, password_hash, company_id, now_ts()),
            )
            reviewer_id = cur.lastrowid

        conn.execute(
            "UPDATE companies SET owner_id=? WHERE id=?",
            (reviewer_id, company_id),
        )

        driver = conn.execute(
            "SELECT id FROM users WHERE username=? COLLATE NOCASE",
            (driver_username,),
        ).fetchone()
        if driver:
            driver_id = driver["id"]
            conn.execute(
                """UPDATE users
                   SET password_hash=?, company_id=?, is_active=1,
                       pending_deletion_at=NULL, full_name='Demo Driver'
                   WHERE id=?""",
                (password_hash, company_id, driver_id),
            )
        else:
            cur = conn.execute(
                """INSERT INTO users
                   (username, password_hash, role, full_name, phone,
                    company_id, created_at, is_active)
                   VALUES (?, ?, 'driver', 'Demo Driver', '555-0100', ?, ?, 1)""",
                (driver_username, password_hash, company_id, now_ts()),
            )
            driver_id = cur.lastrowid

        has_subscription = conn.execute(
            "SELECT id FROM subscriptions WHERE company_id=? LIMIT 1",
            (company_id,),
        ).fetchone()
        if not has_subscription:
            conn.execute(
                """INSERT INTO subscriptions
                   (company_id, plan, status, started_at, notes, created_at)
                   VALUES (?, 'pro', 'active', ?, 'Store review access', ?)""",
                (company_id, now_ts(), now_ts()),
            )

        route = conn.execute(
            """SELECT id FROM routes
               WHERE company_id=? AND route_name='App Review Route'
               ORDER BY id DESC LIMIT 1""",
            (company_id,),
        ).fetchone()
        if not route:
            cur = conn.execute(
                """INSERT INTO routes
                   (route_date, route_name, raw_text, assigned_to, created_by,
                    status, notes, created_at, company_id)
                   VALUES (?, 'App Review Route', ?, ?, ?, 'open', ?, ?, ?)""",
                (
                    date.today().isoformat(),
                    "D - 100 Demo Yard Way - 20YD\n"
                    "PR - 200 Review Ave - 30YD",
                    driver_id,
                    reviewer_id,
                    "Sample data for store review. No real customer information.",
                    now_ts(),
                    company_id,
                ),
            )
            route_id = cur.lastrowid
            conn.executemany(
                """INSERT INTO stops
                   (route_id, stop_order, customer_name, address, city, state,
                    zip_code, action, container_size, status, notes, created_at)
                   VALUES (?, ?, ?, ?, 'Virginia Beach', 'VA', '23451',
                           ?, ?, 'open', ?, ?)""",
                [
                    (
                        route_id,
                        1,
                        "Demo Customer One",
                        "100 Demo Yard Way",
                        "Delivery",
                        "20YD",
                        "Sample stop for App Review.",
                        now_ts(),
                    ),
                    (
                        route_id,
                        2,
                        "Demo Customer Two",
                        "200 Review Ave",
                        "Pickup and Return",
                        "30YD",
                        "Sample stop for App Review.",
                        now_ts(),
                    ),
                ],
            )

        conn.commit()
    finally:
        conn.close()

    print(f"App Review account ready: {username}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
