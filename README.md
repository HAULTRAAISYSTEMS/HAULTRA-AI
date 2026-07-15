# HAULTRA AI

Roll-off dispatch and fleet management system. Flask app (`app.py`), SQLite database, deployed on Render (`Procfile`, `render.yaml`).

## Operations

### Password reset (transactional email)

Password reset emails are sent via [Resend](https://resend.com). Set these environment variables:

- `RESEND_API_KEY` — required. Without it, reset/username-recovery requests still succeed from the user's point of view (the app never reveals whether an email is on file or a send failed), but no email actually goes out — check the server logs for `send_email: RESEND_API_KEY not configured`.
- `RESEND_FROM_EMAIL` — optional, defaults to `HAULTRA AI <onboarding@resend.dev>`. Set this to a verified sending domain in Resend for production.

The mail-sending logic lives entirely in the `send_email()` helper in `app.py` — swap providers by editing that one function.

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
