#!/usr/bin/env python3
"""
Back up the SQLite database to a timestamped copy.

Uses sqlite3's online backup API (not a plain file copy) so a backup taken
while the app is live and writing doesn't produce a corrupt snapshot.

Usage:
    python3 scripts/backup_db.py                  # backs up $DATABASE_PATH
    python3 scripts/backup_db.py --keep 14         # also prune, keep last 14

Scheduling on Render: the persistent disk (see render.yaml) is NOT backed
up by Render itself, and a dyno restart / disk replacement loses everything
on it. Add a Render Cron Job running this script daily, with the same
DATABASE_PATH env var as the web service, writing into a subdirectory of
the same persistent disk (e.g. DATABASE_PATH's directory + "/backups") --
that only protects against accidental deletion/corruption, not disk loss,
since it's still the same disk. For real disaster recovery the backups/
directory should also be synced off-disk (e.g. to S3) after each run;
that requires storage credentials this script does not have.
"""
import os
import sqlite3
import sys
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def backup(db_path, backup_dir):
    os.makedirs(backup_dir, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    dest_path = os.path.join(backup_dir, f"haultra-{stamp}.db")

    src = sqlite3.connect(db_path)
    dest = sqlite3.connect(dest_path)
    with dest:
        src.backup(dest)
    dest.close()
    src.close()

    size_kb = os.path.getsize(dest_path) / 1024
    print(f"Backed up {db_path} -> {dest_path} ({size_kb:.1f} KB)")
    return dest_path


def prune(backup_dir, keep):
    backups = sorted(
        f for f in os.listdir(backup_dir)
        if f.startswith("haultra-") and f.endswith(".db")
    )
    stale = backups[:-keep] if keep > 0 else []
    for f in stale:
        os.remove(os.path.join(backup_dir, f))
        print(f"Pruned old backup: {f}")


if __name__ == "__main__":
    db_path = os.environ.get("DATABASE_PATH", "").strip()
    if not db_path:
        raise RuntimeError("DATABASE_PATH is not set. Add it as an environment variable.")

    backup_dir = os.path.join(os.path.dirname(os.path.abspath(db_path)) or ".", "backups")

    dest = backup(db_path, backup_dir)

    if "--keep" in sys.argv:
        keep_n = int(sys.argv[sys.argv.index("--keep") + 1])
        prune(backup_dir, keep_n)
