# HAULTRA AI

Roll-off dispatch and fleet management system. Flask app (`app.py`), SQLite database, deployed on Render (`Procfile`, `render.yaml`).

## Operations

### Password reset (transactional email)

Password reset emails are sent via [Resend](https://resend.com). Set these environment variables:

- `RESEND_API_KEY` — required. Without it, reset/username-recovery requests still succeed from the user's point of view (the app never reveals whether an email is on file or a send failed), but no email actually goes out — check the server logs for `send_email: RESEND_API_KEY not configured`.
- `RESEND_FROM_EMAIL` — optional, defaults to `HAULTRA AI <onboarding@resend.dev>`. Set this to a verified sending domain in Resend for production.

The mail-sending logic lives entirely in the `send_email()` helper in `app.py` — swap providers by editing that one function.

### Push alerts to the boss's phone

Everything a driver sends — running late, messages, breakdowns, cancels, time
off — lands in one feed at `/boss/notifications`, and the nav badge counts what
still needs a decision. That much works with no configuration.

To also push those alerts to a phone, set three environment variables from the
[Firebase console](https://console.firebase.google.com) for the
`haultra-dispatch` project:

- `FCM_PROJECT_ID` — Project settings → General → Project ID
- `FCM_SERVICE_ACCOUNT_JSON` — Project settings → Service accounts → *Generate
  new private key*. Paste the whole JSON blob as one variable.
- `FCM_VAPID_PUBLIC_KEY` — Project settings → Cloud Messaging → Web Push
  certificates → *Generate key pair*. This is what lets a browser request a token.

With none of them set the app runs exactly as before: alerts still appear in the
feed, and the send is skipped with a log line — same graceful degradation as
`RESEND_API_KEY`. The "Get these on your phone" row stays hidden until the
server reports push is configured, so nobody is offered a button that can't work.

Each boss device registers itself once from that row. `push_tokens` holds one
row per browser or app install; a boss with a phone and a laptop has two. Dead
tokens are retired automatically when FCM reports them unregistered.

Only `critical` and `warning` alerts push. A time-off request is recorded but
never buzzes a phone.

### Production backups and retention

The web workers create a consistent SQLite snapshot once per day. Configure
`BACKUP_S3_BUCKET`, `BACKUP_S3_REGION`, and AWS-compatible credentials so each
snapshot is copied to independent encrypted object storage. Set
`BACKUP_S3_ENDPOINT` when using a non-AWS S3 provider. Configure a 90-day
lifecycle policy on the bucket and test restoration before launch.

The service checks for due account deletions every six hours. Individual user
accounts are anonymized after their 30-day window; closed companies and their
operational uploads are purged. Maintenance can also be run manually:

```bash
python3 scripts/purge_deleted_accounts.py
python3 scripts/backup_db.py --keep 3
```

Production readiness is reported by `/health`, which checks SQLite integrity,
database access, writable persistent storage, and at least 128 MB free space.

### Break-glass password reset

If email is down, `RESEND_API_KEY` isn't set, or it's the boss's own account and they're locked out, reset a password directly from the server shell (e.g. the Render Shell) without needing email at all:

```bash
python3 scripts/reset_password.py <username> <new_password>
```

Username matching is case-insensitive and whitespace-trimmed, same as the login page. The script writes straight to the database using the app's normal password hashing — no token, no email.

If you'd rather do it by hand (e.g. in a `flask shell` / Python REPL with `app.py`'s directory on `sys.path`):

```python
from app import get_db
from werkzeug.security import generate_password_hash

conn = get_db()
conn.execute(
    "UPDATE users SET password_hash = ? WHERE username = ? COLLATE NOCASE",
    (generate_password_hash("new-password-here"), "the-username")
)
conn.commit()
conn.close()
```
