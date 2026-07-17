#!/usr/bin/env python3
"""
One-time backfill: geocode every container currently out that doesn't have
map coordinates yet.

Run this directly on the server (e.g. the Render Shell) once after
deploying the Bin Tracker map, so existing containers-out show up on the
map immediately instead of waiting for their next completion event (new
drops/relocates get geocoded automatically going forward).

Usage:
    python3 scripts/backfill_geocode.py            # every company
    python3 scripts/backfill_geocode.py <company_id>

Respects Nominatim's 1 request/second usage policy via the same rate
limiter and address cache the app uses everywhere else
(geocode_address_cached / _geocode_server) — an address already geocoded
on some other stop is reused for free, no network call.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from app import get_db, compute_containers_out, geocode_address_cached


def backfill_company(company_id):
    conn = get_db()
    out = compute_containers_out(conn, company_id)
    to_geocode = [c for c in out if c["lat"] is None or c["lng"] is None]

    print(f"Company {company_id}: {len(out)} containers out, {len(to_geocode)} need geocoding.")

    succeeded = 0
    failed = 0
    for c in to_geocode:
        coords = geocode_address_cached(conn, company_id, c["address"], c["city"], c["state"])
        if coords:
            conn.execute(
                "UPDATE stops SET lat=?, lng=? WHERE id=?",
                (coords[0], coords[1], c["stop_id"])
            )
            conn.commit()
            succeeded += 1
            print(f"  OK   {c['address']}, {c['city']} -> {coords[0]:.5f}, {coords[1]:.5f}")
        else:
            failed += 1
            print(f"  FAIL {c['address']}, {c['city']}  (no geocode result)")

    conn.close()
    return succeeded, failed


def main():
    conn = get_db()
    if len(sys.argv) > 1:
        company_ids = [int(sys.argv[1])]
    else:
        company_ids = [r["id"] for r in conn.execute("SELECT id FROM companies").fetchall()]
    conn.close()

    if not company_ids:
        print("No companies found.")
        return

    total_ok, total_fail = 0, 0
    for company_id in company_ids:
        ok, fail = backfill_company(company_id)
        total_ok += ok
        total_fail += fail

    print(f"\nDone. {total_ok} succeeded, {total_fail} failed.")


if __name__ == "__main__":
    main()
