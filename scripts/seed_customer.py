#!/usr/bin/env python3
"""
Dev-only seed for the Customer Request System.

Creates one test customer (with a fresh URL-safe portal token printed to the
console), two job sites, and two active bins — enough to exercise the
customer API with curl immediately. This is a script you run by hand; it is
NOT wired up as a route, so it never runs in production request handling.

Usage:
    python3 scripts/seed_customer.py                # attach to first company
    python3 scripts/seed_customer.py <company_id>   # attach to a specific company

DATABASE_PATH (and SECRET_KEY) must be set in the environment, same as the
web service — importing app relies on them.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import secrets

from app import get_db, now_ts, today_str


def seed(company_id=None):
    conn = get_db()

    if company_id is None:
        row = conn.execute("SELECT id FROM companies ORDER BY id LIMIT 1").fetchone()
        if not row:
            print("No companies found — run the app once to bootstrap the default company.")
            conn.close()
            return
        company_id = row["id"]

    token = secrets.token_urlsafe(32)
    ts = now_ts()

    cur = conn.cursor()
    cur.execute(
        """INSERT INTO customers (company_id, business_name, contact_name, phone,
                                  portal_token, created_at)
           VALUES (?, ?, ?, ?, ?, ?)""",
        (company_id, "Acme Demolition", "Sam Rivera", "757-555-0142", token, ts),
    )
    customer_id = cur.lastrowid

    site_ids = []
    for addr, notes in [
        ("1200 Industrial Blvd, Norfolk, VA", "Gate code 4417; drop by the loading dock"),
        ("58 Harbor View Dr, Virginia Beach, VA", "Tight driveway — back in from the north"),
    ]:
        cur.execute(
            """INSERT INTO sites (customer_id, address, lat, lng, notes, created_at)
               VALUES (?, ?, NULL, NULL, ?, ?)""",
            (customer_id, addr, notes, ts),
        )
        site_ids.append(cur.lastrowid)

    bin_ids = []
    for site_id, size in [(site_ids[0], "20yd"), (site_ids[1], "30yd")]:
        cur.execute(
            """INSERT INTO bins (customer_id, site_id, size, dropped_at)
               VALUES (?, ?, ?, ?)""",
            (customer_id, site_id, size, today_str()),
        )
        bin_ids.append(cur.lastrowid)

    conn.commit()
    conn.close()

    print("Seeded Customer Request System test data:")
    print(f"  company_id  : {company_id}")
    print(f"  customer_id : {customer_id}  (Acme Demolition)")
    print(f"  site_ids    : {site_ids}")
    print(f"  bin_ids     : {bin_ids}")
    print()
    print("  PORTAL TOKEN (use in the customer API URLs):")
    print(f"  {token}")
    print()
    print("  Try it:")
    print(f"    curl http://localhost:5000/api/c/{token}/dashboard")


if __name__ == "__main__":
    cid_arg = int(sys.argv[1]) if len(sys.argv) > 1 else None
    seed(cid_arg)
