"""
Mingl VIP Hub — a Telegram Mini App.

One Railway service does two jobs:
  1. Serves the Mini App web page (the "app inside the bot").
  2. Runs the Telegram bot that launches the app + handles admin commands.

Data is stored in Postgres (same pattern as the Mingl bot). Everything the
members see — updates, channel links, content — is editable by you via admin
commands, so you never have to touch code to post a new update.
"""

import os
import re
import json
import time
import hmac
import base64
import hashlib
import logging
import mimetypes
import threading
import urllib.request
import urllib.parse
from urllib.parse import parse_qsl

try:
    from Crypto.Cipher import AES
    MEGA_LOOKUP_AVAILABLE = True
except ImportError:
    MEGA_LOOKUP_AVAILABLE = False

import psycopg
from psycopg.rows import dict_row
from flask import Flask, request, jsonify, send_from_directory, Response
import requests

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("vip-hub")

BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()

# Self-hosted local Bot API server (removes the 20MB download cap the cloud
# API enforces). Off by default — existing deployments keep working exactly
# as before unless this is explicitly turned on after the Dockerfile/start.sh
# setup is actually in place. Set USE_LOCAL_BOT_API=1 once that's deployed
# and verified working.
USE_LOCAL_BOT_API = os.environ.get("USE_LOCAL_BOT_API", "").strip() == "1"
LOCAL_BOT_API_URL = os.environ.get("LOCAL_BOT_API_URL", "http://localhost:8081").rstrip("/")


def _bot_api_base():
    """Base URL for Bot API calls — local server if enabled, else Telegram's cloud API."""
    if USE_LOCAL_BOT_API:
        return f"{LOCAL_BOT_API_URL}/bot{BOT_TOKEN}"
    return f"https://api.telegram.org/bot{BOT_TOKEN}"
DATABASE_URL = os.environ.get("DATABASE_URL", "").strip()
STRIPE_SECRET_KEY = os.environ.get("STRIPE_SECRET_KEY", "").strip()
BOT_USERNAME = os.environ.get("BOT_USERNAME", "").strip().lstrip("@")
VIP_GROUP_ID = os.environ.get("VIP_GROUP_ID", "").strip()
ADMIN_IDS = {
    int(x) for x in os.environ.get("ADMIN_IDS", "").replace(" ", "").split(",") if x
}

app = Flask(__name__)


@app.errorhandler(400)
def handle_bad_request(e):
    # Without this, Werkzeug's default 400 page is HTML — the frontend's
    # fetch(...).then(r=>r.json()) call then fails to even parse the error
    # response, so admins saw a vague fallback message instead of anything
    # useful. This is most commonly hit when an upload gets interrupted
    # mid-transfer (phone locked, app backgrounded, connection dropped) —
    # the multipart body arrives incomplete/malformed.
    log.error("400 Bad Request: %s", getattr(e, "description", e))
    return jsonify({
        "ok": False,
        "error": "The upload was interrupted or malformed — this usually means the "
                 "connection dropped mid-upload (e.g. the app was backgrounded or the "
                 "phone locked during a large video). Try again and keep the app open "
                 "and active until it finishes.",
    }), 400


@app.errorhandler(413)
def handle_too_large(e):
    log.error("413 Request Entity Too Large: %s", getattr(e, "description", e))
    return jsonify({
        "ok": False,
        "error": "That upload was too large for the server to accept in one request.",
    }), 413


# ---------------------------------------------------------------- database ---
def get_conn():
    return psycopg.connect(DATABASE_URL, row_factory=dict_row, autocommit=True)


def init_db():
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS access_codes (
                code TEXT PRIMARY KEY,
                label TEXT,
                created_at BIGINT,
                active INTEGER DEFAULT 1,
                single_use INTEGER DEFAULT 0,
                used_by BIGINT,
                used_at BIGINT
            );
            CREATE TABLE IF NOT EXISTS members (
                telegram_id BIGINT PRIMARY KEY,
                name TEXT,
                unlocked INTEGER DEFAULT 0,
                code_used TEXT,
                joined_at BIGINT,
                welcomed INTEGER DEFAULT 0,
                source TEXT
            );
            CREATE TABLE IF NOT EXISTS updates (
                id BIGSERIAL PRIMARY KEY,
                title TEXT,
                body TEXT,
                created_at BIGINT
            );
            CREATE TABLE IF NOT EXISTS links (
                id BIGSERIAL PRIMARY KEY,
                category TEXT,          -- 'channel' or 'content'
                title TEXT,
                url TEXT,
                created_at BIGINT
            );
            CREATE TABLE IF NOT EXISTS reviews (
                id BIGSERIAL PRIMARY KEY,
                telegram_id BIGINT,
                name TEXT,
                body TEXT,
                created_at BIGINT
            );
            CREATE TABLE IF NOT EXISTS stripe_orders (
                session_id TEXT PRIMARY KEY,
                code TEXT,
                created_at BIGINT
            );
            CREATE TABLE IF NOT EXISTS support_messages (
                id BIGSERIAL PRIMARY KEY,
                telegram_id BIGINT,
                name TEXT,
                body TEXT,
                created_at BIGINT
            );
            CREATE TABLE IF NOT EXISTS gallery_posts (
                id BIGSERIAL PRIMARY KEY,
                caption TEXT,
                created_at BIGINT
            );
            CREATE TABLE IF NOT EXISTS gallery_media (
                id BIGSERIAL PRIMARY KEY,
                post_id BIGINT REFERENCES gallery_posts(id) ON DELETE CASCADE,
                file_id TEXT NOT NULL,
                media_type TEXT NOT NULL,
                duration TEXT,
                sort_order INTEGER DEFAULT 0
            );
            """
        )
        # Safe migrations for tables that may already exist from an earlier deploy.
        for col_def in (
            "ALTER TABLE access_codes ADD COLUMN IF NOT EXISTS single_use INTEGER DEFAULT 0",
            "ALTER TABLE access_codes ADD COLUMN IF NOT EXISTS used_by BIGINT",
            "ALTER TABLE access_codes ADD COLUMN IF NOT EXISTS used_at BIGINT",
            "ALTER TABLE members ADD COLUMN IF NOT EXISTS welcomed INTEGER DEFAULT 0",
            "ALTER TABLE members ADD COLUMN IF NOT EXISTS source TEXT",
            "ALTER TABLE members ADD COLUMN IF NOT EXISTS terms_accepted_at BIGINT",
        ):
            try:
                cur.execute(col_def)
            except Exception as e:
                log.error("migration skipped: %s", e)
    log.info("DB ready")


# ------------------------------------------------------------- data helpers ---
def code_is_valid(code: str) -> bool:
    """A code is valid if it's active AND (reusable OR not yet used)."""
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "SELECT single_use, used_by FROM access_codes "
            "WHERE code = %s AND active = 1", (code,)
        )
        row = cur.fetchone()
        if not row:
            return False
        if row["single_use"] and row["used_by"]:
            return False
        return True


def burn_code(code: str, telegram_id: int):
    """Mark a single-use code as consumed by this member."""
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "UPDATE access_codes SET used_by = %s, used_at = %s "
            "WHERE code = %s AND single_use = 1 AND used_by IS NULL",
            (telegram_id, int(time.time()), code),
        )


def gen_codes(count: int, label: str):
    """Generate `count` random single-use codes. Returns the list of codes."""
    import secrets
    import string
    alphabet = string.ascii_uppercase + string.digits
    alphabet = alphabet.replace("O", "").replace("0", "").replace("I", "").replace("1", "")
    codes = []
    with get_conn() as conn, conn.cursor() as cur:
        for _ in range(count):
            code = "".join(secrets.choice(alphabet) for _ in range(8))
            try:
                cur.execute(
                    "INSERT INTO access_codes (code, label, created_at, active, single_use) "
                    "VALUES (%s, %s, %s, 1, 1)",
                    (code, label, int(time.time())),
                )
                codes.append(code)
            except Exception:
                continue
    return codes


def add_code(code: str, label: str):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "INSERT INTO access_codes (code, label, created_at, active) "
            "VALUES (%s, %s, %s, 1) ON CONFLICT (code) DO UPDATE SET active = 1",
            (code, label, int(time.time())),
        )


def revoke_code(code: str):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("UPDATE access_codes SET active = 0 WHERE code = %s", (code,))


def list_codes():
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("SELECT * FROM access_codes ORDER BY created_at DESC")
        return cur.fetchall()


def unlock_member(tid: int, name: str, code: str, source: str = "code"):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "INSERT INTO members (telegram_id, name, unlocked, code_used, joined_at, source) "
            "VALUES (%s, %s, 1, %s, %s, %s) "
            "ON CONFLICT (telegram_id) DO UPDATE SET unlocked = 1, code_used = %s",
            (tid, name, code, int(time.time()), source, code),
        )


def needs_welcome(tid: int) -> bool:
    """True if this member hasn't seen the welcome yet."""
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("SELECT welcomed FROM members WHERE telegram_id = %s", (tid,))
        row = cur.fetchone()
        return bool(row and not row["welcomed"])


def mark_welcomed(tid: int):
    """Marks the member as having seen the welcome AND accepted the disclaimer."""
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "UPDATE members SET welcomed = 1, terms_accepted_at = %s WHERE telegram_id = %s",
            (int(time.time()), tid),
        )


def all_member_ids():
    """All unlocked members' telegram IDs (for broadcasts)."""
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("SELECT telegram_id FROM members WHERE unlocked = 1")
        return [r["telegram_id"] for r in cur.fetchall()]


def member_stats():
    """Analytics for the admin /stats command."""
    now = int(time.time())
    day_ago = now - 86400
    week_ago = now - 7 * 86400
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("SELECT COUNT(*) AS c FROM members WHERE unlocked = 1")
        total = cur.fetchone()["c"]
        cur.execute("SELECT COUNT(*) AS c FROM members WHERE unlocked = 1 AND joined_at > %s", (day_ago,))
        today = cur.fetchone()["c"]
        cur.execute("SELECT COUNT(*) AS c FROM members WHERE unlocked = 1 AND joined_at > %s", (week_ago,))
        week = cur.fetchone()["c"]
        cur.execute("SELECT source, COUNT(*) AS c FROM members WHERE unlocked = 1 GROUP BY source")
        by_source = {r["source"] or "unknown": r["c"] for r in cur.fetchall()}
        cur.execute("SELECT COUNT(*) AS c FROM reviews")
        reviews = cur.fetchone()["c"]
    return {"total": total, "today": today, "week": week, "by_source": by_source, "reviews": reviews}


def member_unlocked(tid: int) -> bool:
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("SELECT unlocked FROM members WHERE telegram_id = %s", (tid,))
        row = cur.fetchone()
        return bool(row and row["unlocked"])


def get_member(tid: int):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("SELECT * FROM members WHERE telegram_id = %s", (tid,))
        return cur.fetchone()


def count_members() -> int:
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("SELECT COUNT(*) AS c FROM members WHERE unlocked = 1")
        return cur.fetchone()["c"]


def add_update(title: str, body: str):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "INSERT INTO updates (title, body, created_at) VALUES (%s, %s, %s)",
            (title, body, int(time.time())),
        )


def get_updates(limit: int = 30):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "SELECT * FROM updates ORDER BY created_at DESC LIMIT %s", (limit,)
        )
        return cur.fetchall()


def delete_update(uid: int):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("DELETE FROM updates WHERE id = %s", (uid,))


# ------------------------------------------------------ Mega name lookup ---
def _b64_url_decode(s: str) -> bytes:
    s = s.replace('-', '+').replace('_', '/')
    s += '=' * (-len(s) % 4)
    return base64.b64decode(s)


def _mega_decrypt_attr(attr_b64: str, key_bytes: bytes):
    """Decrypt a Mega node's name/attribute blob given its raw AES key."""
    raw = _b64_url_decode(attr_b64)
    cipher = AES.new(key_bytes, AES.MODE_CBC, iv=b'\0' * 16)
    decrypted = cipher.decrypt(raw).rstrip(b'\0')
    if decrypted.startswith(b'MEGA'):
        decrypted = decrypted[4:]
    return json.loads(decrypted.decode('utf-8', errors='ignore'))


def _mega_api_call(url_with_params, body_obj):
    """POST to Mega's public API and return the parsed JSON. Raises a
    descriptive error (not a bare crash) if the response is empty or isn't
    JSON — Mega is known to silently return nothing for requests that look
    automated, and a browser-like User-Agent header often fixes that."""
    body = json.dumps(body_obj).encode()
    req = urllib.request.Request(
        url_with_params,
        data=body,
        headers={
            "Content-Type": "application/json",
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
            ),
        },
    )
    with urllib.request.urlopen(req, timeout=10) as resp:
        raw = resp.read()
        status = resp.status
    if not raw.strip():
        raise ValueError(
            f"Mega returned an empty response (HTTP {status}). This usually means Mega "
            "is silently blocking the request — often because it's coming from a cloud/"
            "datacenter server IP (like Railway's) rather than a normal home connection."
        )
    try:
        return json.loads(raw.decode("utf-8", errors="replace"))
    except json.JSONDecodeError:
        preview = raw[:200].decode("utf-8", errors="replace")
        raise ValueError(f"Mega returned non-JSON (HTTP {status}): {preview!r}")


def _mega_unwrap_key_candidates(k_field: str, wrapping_key: bytes):
    """A node's 'k' field holds its REAL key, encrypted (wrapped) with a
    different key and cipher mode (AES-ECB) than the attribute encryption
    (AES-CBC). Skipping this unwrap step was the actual bug — decrypting
    attributes directly with the share key only works if a node's real key
    happens to equal the share key, which isn't guaranteed even for root.
    Returns a list of candidate unwrapped 16-byte keys to try."""
    if not k_field:
        return []
    candidates = []
    for part in k_field.split('/'):
        enc_key_b64 = part.split(':', 1)[1] if ':' in part else part
        try:
            raw = _b64_url_decode(enc_key_b64)
            cipher = AES.new(wrapping_key, AES.MODE_ECB)
            candidates.append(cipher.decrypt(raw)[:16])
        except Exception:
            continue
    return candidates


def fetch_mega_name_debug(url: str):
    """Same lookup as fetch_mega_name, but returns (name, reason) so the
    single-link /addmega command can show admins exactly what went wrong —
    no server logs or local scripts needed, the failure reason shows up
    right in the Telegram reply."""
    if not MEGA_LOOKUP_AVAILABLE:
        return None, "pycryptodome isn't installed on the server — check requirements.txt was updated and redeployed."
    try:
        m = re.search(r'mega\.nz/(folder|file)/([^#]+)#([^/?\s]+)', url)
        if m:
            kind, handle, key_str = m.group(1), m.group(2), m.group(3)
        else:
            m2 = re.search(r'mega\.nz/#(F?)!([^!]+)!([^/?\s]+)', url)
            if not m2:
                return None, "Couldn't parse that as a Mega link at all — check the URL format."
            kind = 'folder' if m2.group(1) == 'F' else 'file'
            handle, key_str = m2.group(2), m2.group(3)

        key_bytes_full = _b64_url_decode(key_str)

        if kind == 'file':
            data = _mega_api_call("https://g.api.mega.co.nz/cs?id=0", [{"a": "g", "p": handle}])
            if not data:
                return None, "Empty response from Mega's API."
            if isinstance(data[0], int):
                return None, f"Mega API returned error code {data[0]} for this file link."
            if "at" not in data[0]:
                return None, f"Unexpected response shape: {str(data)[:300]}"
            attr_key = key_bytes_full[:16]
            if len(key_bytes_full) >= 32:
                k1, k2 = key_bytes_full[:16], key_bytes_full[16:32]
                attr_key = bytes(a ^ b for a, b in zip(k1, k2))
            info = _mega_decrypt_attr(data[0]["at"], attr_key)
            name = info.get("n")
            return (name, None) if name else (None, f"Decrypted OK but found no name field: {info}")

        else:  # folder
            data = _mega_api_call(
                f"https://g.api.mega.co.nz/cs?id=0&n={handle}",
                [{"a": "f", "c": 1, "r": 1}],
            )
            if not data:
                return None, "Empty response from Mega's API."
            if isinstance(data[0], int):
                # Mega returns a bare negative error code (e.g. -2, -9) instead
                # of a listing when something's wrong.
                return None, f"Mega API returned error code {data[0]} for this folder link."
            if "f" not in data[0]:
                return None, f"Unexpected response shape: {str(data)[:300]}"
            nodes = data[0]["f"]
            if not nodes:
                return None, "Folder listing came back empty."

            # Don't guess which node is "root" from parent/handle heuristics —
            # that guess was wrong and caused decryption to run against the
            # wrong node, producing garbage bytes that happened to fail JSON
            # parsing with this exact same error every time. Instead, try the
            # share key directly against every node: only the true root's key
            # IS the raw share key, every child's key is separately wrapped,
            # so children will fail cleanly here rather than silently succeed
            # with wrong data.
            name = None
            for n in nodes:
                try:
                    info = _mega_decrypt_attr(n.get("a", ""), key_bytes_full[:16])
                    if info.get("n"):
                        name = info["n"]
                        break
                except Exception:
                    continue

            if name:
                return name, None

            sample = [{"h": n.get("h"), "p": n.get("p"), "t": n.get("t")} for n in nodes[:5]]
            return None, (
                f"Got {len(nodes)} node(s) back from Mega but couldn't decrypt any of them "
                f"with the share key. First few nodes' structure: {sample}"
            )
    except Exception as e:
        return None, f"Crashed: {type(e).__name__}: {e}"


def fetch_mega_name(url: str):
    """Thin wrapper for batch imports — per-line debug output would be way
    too noisy across hundreds of lines. See fetch_mega_name_debug for the
    diagnostic version used by the single-link /addmega command."""
    name, _ = fetch_mega_name_debug(url)
    return name


def add_link(category: str, title: str, url: str):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "INSERT INTO links (category, title, url, created_at) VALUES (%s, %s, %s, %s)",
            (category, title, url, int(time.time())),
        )


def get_links(category: str):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "SELECT * FROM links WHERE category = %s ORDER BY created_at ASC",
            (category,),
        )
        return cur.fetchall()


def delete_link(lid: int):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("DELETE FROM links WHERE id = %s", (lid,))


def add_review(telegram_id, name: str, body: str):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "INSERT INTO reviews (telegram_id, name, body, created_at) "
            "VALUES (%s, %s, %s, %s)",
            (telegram_id, name, body, int(time.time())),
        )


def get_reviews(limit: int = 100):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "SELECT * FROM reviews ORDER BY created_at DESC LIMIT %s", (limit,)
        )
        return cur.fetchall()


def delete_review(rid: int):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("DELETE FROM reviews WHERE id = %s", (rid,))


def member_has_reviewed(telegram_id) -> bool:
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "SELECT 1 FROM reviews WHERE telegram_id = %s LIMIT 1", (telegram_id,)
        )
        return cur.fetchone() is not None


# ------------------------------------------------------------------ Gallery ---
def add_gallery_post(caption: str, media_items: list):
    """media_items: list of {'file_id': str, 'media_type': 'photo'|'video'}."""
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "INSERT INTO gallery_posts (caption, created_at) VALUES (%s, %s) RETURNING id",
            (caption, int(time.time())),
        )
        post_id = cur.fetchone()["id"]
        for i, item in enumerate(media_items):
            cur.execute(
                "INSERT INTO gallery_media (post_id, file_id, media_type, duration, sort_order) "
                "VALUES (%s, %s, %s, %s, %s)",
                (post_id, item["file_id"], item["media_type"], item.get("duration"), i),
            )
    return post_id


def get_gallery_posts(limit: int = 50):
    """Newest first. Each post carries its own ordered list of media items."""
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "SELECT * FROM gallery_posts ORDER BY created_at DESC LIMIT %s", (limit,)
        )
        posts = cur.fetchall()
        result = []
        for p in posts:
            cur.execute(
                "SELECT * FROM gallery_media WHERE post_id = %s ORDER BY sort_order ASC",
                (p["id"],),
            )
            media = cur.fetchall()
            result.append({
                "id": p["id"],
                "caption": p["caption"],
                "created_at": p["created_at"],
                "media": [
                    {"id": m["id"], "type": m["media_type"], "duration": m["duration"]}
                    for m in media
                ],
            })
        return result


def get_gallery_media_file_id(media_id: int):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("SELECT file_id FROM gallery_media WHERE id = %s", (media_id,))
        row = cur.fetchone()
        return row["file_id"] if row else None


def delete_gallery_post(post_id: int):
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("DELETE FROM gallery_posts WHERE id = %s", (post_id,))  # cascades to media


def relay_file_to_telegram(file_storage, chat_id):
    """Send an admin-uploaded file to Telegram (the admin's own chat with the
    bot) via the Bot API, and return the file_id Telegram hands back. Telegram
    becomes the actual file host — this app never stores the raw bytes itself,
    same pattern as any content posted through the bot directly."""
    content_type = file_storage.content_type or ""
    is_video = content_type.startswith("video/")
    method = "sendVideo" if is_video else "sendPhoto"
    field = "video" if is_video else "photo"
    url = f"{_bot_api_base()}/{method}"
    # Local mode allows uploads up to 2000MB vs. the cloud API's 50MB, so a
    # big video can genuinely take a while to relay — give it more room.
    timeout = 300 if USE_LOCAL_BOT_API else 60
    try:
        resp = requests.post(
            url,
            data={"chat_id": chat_id},
            files={field: (file_storage.filename, file_storage.stream, content_type)},
            timeout=timeout,
        )
        data = resp.json()
        if not data.get("ok"):
            return None, None, data.get("description", "Telegram rejected the upload.")
        result = data["result"]
        if is_video:
            file_id = result["video"]["file_id"]
        else:
            file_id = result["photo"][-1]["file_id"]  # largest size Telegram generated
        return file_id, ("video" if is_video else "photo"), None
    except Exception as e:
        return None, None, str(e)


# ------------------------------------------- Telegram initData verification ---
def verify_init_data(init_data: str):
    """Validate the Telegram WebApp initData signature and return the user dict.
    Returns None if the signature is invalid (someone faking a request)."""
    try:
        parsed = dict(parse_qsl(init_data, keep_blank_values=True))
        received_hash = parsed.pop("hash", None)
        if not received_hash:
            return None
        data_check = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
        secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, data_check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, received_hash):
            return None
        return json.loads(parsed.get("user", "{}"))
    except Exception as e:
        log.error("verify_init_data failed: %s", e)
        return None


def _user_from_request():
    init_data = request.headers.get("X-Init-Data", "")
    user = verify_init_data(init_data)
    return user


def is_group_member(telegram_id: int) -> bool:
    """Check if the user is in the VIP group (so existing members auto-unlock).
    Requires the bot to be an admin in that group. Uses a direct Telegram API
    call. Returns False on any error so it never wrongly grants access."""
    if not VIP_GROUP_ID or not BOT_TOKEN:
        return False
    try:
        import urllib.request
        import urllib.parse
        params = urllib.parse.urlencode({"chat_id": VIP_GROUP_ID, "user_id": telegram_id})
        url = f"https://api.telegram.org/bot{BOT_TOKEN}/getChatMember?{params}"
        with urllib.request.urlopen(url, timeout=6) as resp:
            data = json.loads(resp.read().decode())
        if not data.get("ok"):
            return False
        status = data.get("result", {}).get("status", "")
        # These statuses mean they're currently in the group.
        return status in ("creator", "administrator", "member", "restricted")
    except Exception as e:
        log.error("group member check failed: %s", e)
        return False


# ------------------------------------------------------------- web routes ---
@app.route("/")
def index():
    return send_from_directory("static", "index.html")


@app.route("/static/<path:filename>")
def static_files(filename):
    return send_from_directory("static", filename)


@app.route("/api/state")
def api_state():
    """Everything the app needs on load: whether the user is unlocked + all data."""
    user = _user_from_request()
    if not user:
        return jsonify({"error": "invalid"}), 403
    tid = user["id"]
    unlocked = member_unlocked(tid)
    # Existing members: if they're in the VIP group, unlock them automatically
    # (no code needed) and remember it so future opens are instant.
    if not unlocked and is_group_member(tid):
        unlock_member(tid, user.get("first_name", "Member"), "group", source="group")
        unlocked = True
    payload = {
        "unlocked": unlocked,
        "name": user.get("first_name", "Member"),
        "is_admin": tid in ADMIN_IDS,
    }
    if unlocked:
        # First-time welcome flag (shows the in-app welcome once).
        payload["show_welcome"] = needs_welcome(tid)
    if unlocked:
        payload["channels"] = [
            {"title": l["title"], "url": l["url"], "ts": l["created_at"]} for l in get_links("channel")
        ]
        payload["content"] = [
            {"title": l["title"], "url": l["url"], "ts": l["created_at"]} for l in get_links("content")
        ]
        payload["megas"] = [
            {"title": l["title"], "url": l["url"], "ts": l["created_at"]} for l in get_links("mega")
        ]
        m = get_member(tid)
        payload["membership"] = {
            "joined": m["joined_at"] if m else None,
            "member_no": tid,
        }
        payload["reviews"] = [
            {"id": r["id"], "name": r["name"], "body": r["body"], "ts": r["created_at"]}
            for r in get_reviews()
        ]
        payload["has_reviewed"] = member_has_reviewed(tid)
    return jsonify(payload)


@app.route("/api/gallery")
def api_gallery():
    """Newest-first feed for the Gallery tab. Members only."""
    user = _user_from_request()
    if not user:
        return jsonify({"error": "invalid"}), 403
    if not member_unlocked(user["id"]):
        return jsonify({"error": "locked"}), 403
    return jsonify({"posts": get_gallery_posts()})


@app.route("/api/gallery/file/<int:media_id>")
def api_gallery_file(media_id):
    """Streams a single photo/video on demand. The app never stores media
    itself — every request here fetches fresh using the saved file_id, so
    there's no separate storage to manage, and no bot token ever reaches the
    frontend. Uses the self-hosted local Bot API server when USE_LOCAL_BOT_API
    is on (no size limit); otherwise falls back to Telegram's cloud API,
    which caps downloads at 20MB regardless of upload size."""
    user = _user_from_request()
    if not user:
        return jsonify({"error": "invalid"}), 403
    if not member_unlocked(user["id"]):
        return jsonify({"error": "locked"}), 403
    file_id = get_gallery_media_file_id(media_id)
    if not file_id:
        return jsonify({"error": "not found"}), 404
    try:
        info = requests.get(
            f"{_bot_api_base()}/getFile",
            params={"file_id": file_id}, timeout=10,
        ).json()
        if not info.get("ok"):
            desc = (info.get("description") or "").lower()
            if "too big" in desc:
                # Only reachable in cloud mode — local mode has no size cap.
                return jsonify({"error": "file_too_big", "detail": info.get("description")}), 413
            return jsonify({"error": "telegram lookup failed", "detail": info.get("description")}), 502

        file_path = info["result"]["file_path"]

        if USE_LOCAL_BOT_API:
            # Local mode hands back an absolute path on this same container's
            # disk instead of a URL — no separate download step, no size cap.
            if not os.path.isfile(file_path):
                log.error("local bot api reported file_path %s but it doesn't exist", file_path)
                return jsonify({"error": "file not found on local server"}), 502
            with open(file_path, "rb") as f:
                content = f.read()
            content_type = mimetypes.guess_type(file_path)[0] or "application/octet-stream"
            return Response(content, content_type=content_type)

        tg_resp = requests.get(
            f"https://api.telegram.org/file/bot{BOT_TOKEN}/{file_path}",
            timeout=30,
        )
        return Response(
            tg_resp.content,
            content_type=tg_resp.headers.get("Content-Type", "application/octet-stream"),
        )
    except Exception as e:
        log.error("gallery file proxy failed for media %s: %s", media_id, e)
        return jsonify({"error": "failed to fetch file"}), 502


@app.route("/api/admin/gallery/upload", methods=["POST"])
def api_admin_gallery_upload():
    """Admin-only: upload one or more photos/videos plus a caption directly
    from the Mini App. Every file gets relayed to Telegram (see
    relay_file_to_telegram) so Telegram hosts it, same as bot-posted content.
    This check is independent of whatever the frontend shows — a hidden
    button is not security, this server-side check is."""
    user = _user_from_request()
    if not user or user["id"] not in ADMIN_IDS:
        return jsonify({"ok": False, "error": "Admins only."}), 403

    caption = (request.form.get("caption") or "").strip()
    files = request.files.getlist("files")
    if not files:
        return jsonify({"ok": False, "error": "No files provided."})
    if len(files) > 200:
        return jsonify({"ok": False, "error": "Max 200 files per post — split anything larger into two posts."})

    media_items = []
    errors = []
    for f in files:
        file_id, media_type, err = relay_file_to_telegram(f, user["id"])
        if file_id:
            media_items.append({"file_id": file_id, "media_type": media_type})
        else:
            errors.append(f"{f.filename}: {err}")
            log.error("gallery upload relay failed for %s: %s", f.filename, err)

    if not media_items:
        # Show the real reason instead of sending the admin to check server
        # logs — the first failure is almost always representative of the
        # rest (e.g. every video rejected the same way).
        detail = errors[0] if errors else "Unknown error."
        return jsonify({"ok": False, "error": f"Upload failed — {detail}"})

    post_id = add_gallery_post(caption, media_items)
    return jsonify({
        "ok": True, "post_id": post_id,
        "uploaded": len(media_items), "failed": len(errors),
        "errors": errors[:5],  # cap so a huge batch doesn't blow up the response
    })


@app.route("/api/admin/gallery/delete/<int:post_id>", methods=["POST"])
def api_admin_gallery_delete(post_id):
    """Admin-only: remove a post and all its media from the Gallery. Same
    server-side admin check as everywhere else — never trust the frontend."""
    user = _user_from_request()
    if not user or user["id"] not in ADMIN_IDS:
        return jsonify({"ok": False, "error": "Admins only."}), 403
    delete_gallery_post(post_id)
    return jsonify({"ok": True})


@app.route("/api/review", methods=["POST"])
def api_review():
    user = _user_from_request()
    if not user:
        return jsonify({"error": "invalid"}), 403
    tid = user["id"]
    if not member_unlocked(tid):
        return jsonify({"ok": False, "error": "Unlock the hub first."})
    body = (request.json or {}).get("body", "").strip()
    if len(body) < 3:
        return jsonify({"ok": False, "error": "Please write a little more."})
    if len(body) > 600:
        body = body[:600]
    # Light profanity guard — blocks the most obvious stuff.
    lowered = body.lower()
    banned = ["fuck", "shit", "cunt", "nigger", "faggot", "bitch", "porn"]
    if any(w in lowered for w in banned):
        return jsonify({"ok": False, "error": "Let's keep reviews clean, please."})
    add_review(tid, user.get("first_name", "Member"), body)
    return jsonify({"ok": True})


@app.route("/api/unlock", methods=["POST"])
def api_unlock():
    user = _user_from_request()
    if not user:
        return jsonify({"error": "invalid"}), 403
    code = (request.json or {}).get("code", "").strip()
    if code_is_valid(code):
        unlock_member(user["id"], user.get("first_name", "Member"), code, source="code")
        burn_code(code, user["id"])  # consume it if it's single-use
        return jsonify({"ok": True})
    return jsonify({"ok": False, "error": "That code isn't valid or has already been used."})


@app.route("/api/welcomed", methods=["POST"])
def api_welcomed():
    user = _user_from_request()
    if not user:
        return jsonify({"error": "invalid"}), 403
    mark_welcomed(user["id"])
    return jsonify({"ok": True})


@app.route("/api/support", methods=["POST"])
def api_support():
    user = _user_from_request()
    if not user:
        return jsonify({"error": "invalid"}), 403
    tid = user["id"]
    unlocked = member_unlocked(tid)
    body = (request.json or {}).get("body", "").strip()
    if len(body) < 3:
        return jsonify({"ok": False, "error": "Please write your message."})
    if len(body) > 1000:
        body = body[:1000]
    name = user.get("first_name", "Member")
    # Store it.
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "INSERT INTO support_messages (telegram_id, name, body, created_at) "
            "VALUES (%s, %s, %s, %s)",
            (tid, name, body, int(time.time())),
        )
    # Tag lock-screen (not-yet-unlocked) messages so you know it's a code problem.
    tag = "💬 *Support message*" if unlocked else "🔑 *Code help needed* (locked)"
    note = (
        f"{tag}\n"
        f"From: {name} (`{tid}`)\n\n"
        f"{body}\n\n"
        f"_Or use:_ `/reply {tid} your message`"
    )
    support_kb = {
        "inline_keyboard": [[
            {"text": "💬 Reply to Customer", "callback_data": f"replysupport|{tid}"},
            {"text": "🔑 Submit New Code", "callback_data": f"submitcode|{tid}"},
        ]]
    }
    for admin_id in ADMIN_IDS:
        _send_via_api(admin_id, note, reply_markup=support_kb)
    return jsonify({"ok": True})


def _send_via_api(chat_id, text, markdown=True, reply_markup=None):
    """Send a Telegram message via direct API (usable from the Flask thread)."""
    try:
        import urllib.request
        import urllib.parse
        data = {"chat_id": chat_id, "text": text}
        if markdown:
            data["parse_mode"] = "Markdown"
        if reply_markup:
            data["reply_markup"] = json.dumps(reply_markup)
        body = urllib.parse.urlencode(data).encode()
        url = f"https://api.telegram.org/bot{BOT_TOKEN}/sendMessage"
        urllib.request.urlopen(urllib.request.Request(url, data=body), timeout=6)
        return True
    except Exception as e:
        log.error("send_via_api failed: %s", e)
        return False


@app.route("/api/logout", methods=["POST"])
def api_logout():
    user = _user_from_request()
    if not user:
        return jsonify({"error": "invalid"}), 403
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "UPDATE members SET unlocked = 0 WHERE telegram_id = %s", (user["id"],)
        )
    return jsonify({"ok": True})


@app.route("/health")
def health():
    return "ok"


@app.route("/success")
def stripe_success():
    """Stripe redirects paid customers here. We verify the session was actually
    paid, then show them a single-use code. Revisiting shows the SAME code."""
    session_id = request.args.get("session_id", "").strip()
    if not session_id or not STRIPE_SECRET_KEY:
        return _success_page(error="Missing payment details. Please contact support.")

    # Did we already issue a code for this session? If so, show the same one.
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute("SELECT code FROM stripe_orders WHERE session_id = %s", (session_id,))
        existing = cur.fetchone()
    if existing:
        return _success_page(code=existing["code"])

    # Verify the session with Stripe and confirm it's paid.
    try:
        import stripe
        stripe.api_key = STRIPE_SECRET_KEY
        session = stripe.checkout.Session.retrieve(session_id)
        # session may be a StripeObject or dict-like; handle both.
        payment_status = None
        try:
            payment_status = session["payment_status"]
        except Exception:
            payment_status = getattr(session, "payment_status", None)
        if payment_status != "paid":
            log.error("stripe payment_status=%r for %s", payment_status, session_id)
            return _success_page(error="Payment not confirmed yet. If you've paid, refresh in a moment.")
    except Exception as e:
        import traceback
        log.error("stripe verify failed: %s\n%s", repr(e), traceback.format_exc())
        return _success_page(error="Couldn't verify your payment. Please contact support.")

    # Generate a fresh single-use code and remember it for this session.
    codes = gen_codes(1, "stripe")
    if not codes:
        return _success_page(error="Something went wrong issuing your code. Please contact support.")
    code = codes[0]
    with get_conn() as conn, conn.cursor() as cur:
        cur.execute(
            "INSERT INTO stripe_orders (session_id, code, created_at) VALUES (%s, %s, %s) "
            "ON CONFLICT (session_id) DO NOTHING",
            (session_id, code, int(time.time())),
        )
    return _success_page(code=code)


def _success_page(code: str = "", error: str = ""):
    bot_user = BOT_USERNAME or "BritishOnTopBot"
    if error:
        inner = f'<div class="err">{error}</div>'
        confetti = ""
    else:
        inner = (
            f'<div class="lbl">Your access code</div>'
            f'<div class="code" id="code" onclick="copyCode()">{code}</div>'
            f'<div class="copied" id="copied">Tap code to copy</div>'
            f'<a class="gobtn" href="https://t.me/{bot_user}">Open British On Top →</a>'
            f'<p class="hint">Tap the button, then <b>Open British On Top</b> in the bot and enter your code. '
            f'It works once and is yours alone.</p>'
        )
        confetti = '<div class="confetti" id="confetti"></div>'
    return f"""<!DOCTYPE html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Payment Successful</title>
<link href="https://fonts.googleapis.com/css2?family=Rajdhani:wght@500;600;700&family=Manrope:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
  :root{{--violet:#8b6fd4;--violet-deep:#6847b0;--violet-soft:#b8a6e8;--ink:#f3eeff;--muted:#9d8ec4;--line:rgba(139,111,212,0.2);--ok:#7ee0a0;}}
  *{{margin:0;padding:0;box-sizing:border-box;}}
  body{{font-family:'Manrope',sans-serif;background:radial-gradient(130% 90% at 50% 0%,#1a1430,#0d0a18 58%);
    color:var(--ink);min-height:100vh;display:grid;place-items:center;padding:24px;overflow:hidden;position:relative;}}
  .aurora{{position:fixed;inset:0;overflow:hidden;pointer-events:none;z-index:0;opacity:.5;}}
  .aurora span{{position:absolute;border-radius:50%;filter:blur(60px);}}
  .aurora .a1{{width:260px;height:260px;background:#7d4fd6;top:-70px;left:-50px;animation:flt1 10s ease-in-out infinite;}}
  .aurora .a2{{width:210px;height:210px;background:#b06fd4;bottom:-50px;right:-40px;animation:flt2 12s ease-in-out infinite;}}
  @keyframes flt1{{0%,100%{{transform:translate(0,0);}}50%{{transform:translate(46px,34px);}}}}
  @keyframes flt2{{0%,100%{{transform:translate(0,0);}}50%{{transform:translate(-34px,-46px);}}}}
  .confetti{{position:fixed;inset:0;pointer-events:none;z-index:5;overflow:hidden;}}
  .confetti i{{position:absolute;top:-14px;width:9px;height:14px;opacity:0;animation:fall 2.8s linear forwards;}}
  @keyframes fall{{0%{{transform:translateY(-20px) rotate(0);opacity:1;}}100%{{transform:translateY(105vh) rotate(540deg);opacity:.9;}}}}
  .card{{position:relative;z-index:2;max-width:420px;width:100%;text-align:center;
    background:linear-gradient(150deg,rgba(42,30,80,0.6),rgba(22,15,42,0.6));backdrop-filter:blur(10px);
    border:1px solid var(--line);border-radius:24px;padding:44px 26px;animation:pop .5s ease;overflow:hidden;}}
  .card::before{{content:"";position:absolute;inset:0;padding:1px;border-radius:24px;
    background:linear-gradient(130deg,var(--violet),transparent 40%,transparent 60%,var(--violet-soft));
    -webkit-mask:linear-gradient(#000 0 0) content-box,linear-gradient(#000 0 0);
    -webkit-mask-composite:xor;mask-composite:exclude;opacity:.4;animation:spin 14s linear infinite;pointer-events:none;}}
  @keyframes spin{{to{{transform:rotate(360deg);}}}}
  @keyframes pop{{from{{opacity:0;transform:scale(.94) translateY(16px);}}to{{opacity:1;transform:scale(1) translateY(0);}}}}
  .crest{{width:76px;height:76px;margin:0 auto 22px;border-radius:22px;display:grid;place-items:center;font-size:38px;position:relative;
    background:linear-gradient(140deg,var(--violet),var(--violet-deep));box-shadow:0 12px 40px rgba(139,111,212,.55);animation:pulse 3s ease-in-out infinite;}}
  @keyframes pulse{{0%,100%{{transform:scale(1);}}50%{{transform:scale(1.03);}}}}
  h1{{font-family:'Rajdhani',sans-serif;font-size:30px;font-weight:700;text-transform:uppercase;letter-spacing:.06em;margin:0 0 4px;position:relative;}}
  .tick{{color:var(--ok);font-size:13.5px;font-weight:600;margin-bottom:30px;position:relative;letter-spacing:.02em;}}
  .tick .dot{{width:8px;height:8px;border-radius:50%;background:var(--ok);display:inline-block;margin-right:5px;box-shadow:0 0 8px var(--ok);animation:blink 1.6s infinite;}}
  @keyframes blink{{0%,100%{{opacity:1;}}50%{{opacity:.4;}}}}
  .lbl{{font-size:10.5px;letter-spacing:.26em;text-transform:uppercase;color:var(--violet-soft);font-weight:700;margin-bottom:12px;position:relative;}}
  .code{{font-family:'Rajdhani',sans-serif;font-size:38px;font-weight:700;letter-spacing:.22em;color:#fff;background:#0d0a18;
    border:1px dashed rgba(139,111,212,.45);border-radius:16px;padding:20px;user-select:all;cursor:pointer;position:relative;
    transition:transform .12s,border-color .2s;animation:codeReveal .6s ease .25s both;}}
  .code:active{{transform:scale(.98);}}
  @keyframes codeReveal{{from{{opacity:0;transform:translateY(6px);}}to{{opacity:1;transform:translateY(0);}}}}
  .copied{{color:var(--muted);font-size:11.5px;margin-top:10px;position:relative;}}
  .copied.show{{color:var(--ok);}}
  .gobtn{{display:block;margin-top:24px;padding:17px;background:linear-gradient(135deg,var(--violet),var(--violet-deep));
    color:#fff;font-weight:700;font-size:16px;text-decoration:none;border-radius:14px;position:relative;overflow:hidden;box-shadow:0 8px 24px rgba(104,71,176,.4);}}
  .gobtn::before{{content:"";position:absolute;top:0;left:-80%;width:55%;height:100%;
    background:linear-gradient(90deg,transparent,rgba(255,255,255,0.22),transparent);animation:sheen 5s ease-in-out infinite;}}
  @keyframes sheen{{0%{{left:-80%;}}45%,100%{{left:135%;}}}}
  .hint{{color:var(--muted);font-size:13px;line-height:1.6;margin-top:20px;position:relative;}}
  .err{{color:#e06b7a;font-size:15px;line-height:1.6;position:relative;z-index:2;}}
</style></head>
<body>
<div class="aurora"><span class="a1"></span><span class="a2"></span></div>
{confetti}
<div class="card">
  <div class="crest">👑</div>
  <h1>Payment Successful</h1>
  <div class="tick"><span class="dot"></span>Welcome to British On Top</div>
  {inner}
</div>
<script>
function copyCode(){{
  var t=document.getElementById('code').innerText.trim();
  navigator.clipboard && navigator.clipboard.writeText(t);
  var c=document.getElementById('copied'); if(c){{c.classList.add('show');c.textContent='Copied \u2713';}}
}}
(function party(){{
  var box=document.getElementById('confetti'); if(!box) return;
  var colors=['#8b6fd4','#b8a6e8','#7ee0a0','#ffd76a','#fff'];
  for(var i=0;i<28;i++){{
    var s=document.createElement('i');
    s.style.left=Math.random()*100+'%';
    s.style.background=colors[Math.floor(Math.random()*colors.length)];
    s.style.animationDelay=(Math.random()*0.6)+'s';
    s.style.transform='rotate('+(Math.random()*360)+'deg)';
    if(Math.random()>0.5) s.style.borderRadius='50%';
    box.appendChild(s);
  }}
}})();
</script>
</body></html>"""


# ------------------------------------------------------------------- bot ---
def run_bot():
    """Runs the Telegram bot in a background thread (long polling)."""
    import asyncio
    # A background thread has no event loop by default; create one for this
    # thread so python-telegram-bot's async polling can run here.
    asyncio.set_event_loop(asyncio.new_event_loop())

    from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, WebAppInfo, ForceReply
    from telegram.ext import (
        Application, CommandHandler, ContextTypes, MessageHandler, filters,
        CallbackQueryHandler,
    )

    WEBAPP_URL = os.environ.get("WEBAPP_URL", "").strip()

    def is_admin(uid):
        return uid in ADMIN_IDS

    async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("🚪 Open British On Top", web_app=WebAppInfo(url=WEBAPP_URL))
        ]])
        caption = (
            "👑 *Welcome to British On Top*\n\n"
            "Tap below to open the app. You'll need your access code the first time."
        )
        # Try to show the animated banner (static/banner.gif served from our own
        # Railway URL). If anything goes wrong, fall back to a plain text welcome
        # so /start never breaks.
        banner_url = f"{WEBAPP_URL.rstrip('/')}/static/vip.gif.gif.mp4" if WEBAPP_URL else ""
        if banner_url:
            try:
                await update.message.reply_animation(
                    animation=banner_url,
                    caption=caption,
                    parse_mode="Markdown",
                    reply_markup=kb,
                )
                return
            except Exception as e:
                log.error("banner send failed, falling back to text: %s", e)
        await update.message.reply_text(caption, parse_mode="Markdown", reply_markup=kb)

    async def newcode(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        if not context.args:
            await update.message.reply_text("Usage: /newcode CODE [label]")
            return
        code = context.args[0]
        label = " ".join(context.args[1:]) or "—"
        add_code(code, label)
        await update.message.reply_text(f"✅ Code `{code}` is now active.", parse_mode="Markdown")

    async def gencodes(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        count = 20
        if context.args and context.args[0].isdigit():
            count = min(int(context.args[0]), 200)  # cap per batch
        label = " ".join(context.args[1:]) if len(context.args) > 1 else "batch"
        codes = gen_codes(count, label)
        if not codes:
            await update.message.reply_text("Couldn't generate codes, try again.")
            return
        # Send as a copy-friendly block. Chunk if long.
        header = f"🔑 *{len(codes)} single-use codes generated*\nEach works ONCE then dies.\n\n"
        body = "\n".join(f"`{c}`" for c in codes)
        text = header + body
        for i in range(0, len(text), 3500):
            await update.message.reply_text(text[i:i+3500], parse_mode="Markdown")

    async def revokecode(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        if not context.args:
            await update.message.reply_text("Usage: /revokecode CODE")
            return
        revoke_code(context.args[0])
        await update.message.reply_text(f"🚫 Code `{context.args[0]}` revoked.", parse_mode="Markdown")

    async def codes(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        rows = list_codes()
        if not rows:
            await update.message.reply_text("No codes yet. /gencodes 50 to make a batch.")
            return
        used = sum(1 for r in rows if r.get("used_by"))
        available = sum(1 for r in rows if r.get("single_use") and not r.get("used_by") and r["active"])
        reusable = sum(1 for r in rows if not r.get("single_use") and r["active"])
        summary = (
            f"🔑 *Codes overview*\n"
            f"Total: {len(rows)}\n"
            f"🟢 Unused single-use: {available}\n"
            f"⚫ Used: {used}\n"
            f"♾️ Reusable: {reusable}\n\n"
            f"_Use /listunused to see codes you can still hand out._"
        )
        await update.message.reply_text(summary, parse_mode="Markdown")

    async def listunused(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        rows = list_codes()
        avail = [r for r in rows if r.get("single_use") and not r.get("used_by") and r["active"]]
        if not avail:
            await update.message.reply_text("No unused single-use codes left. /gencodes 50 to make more.")
            return
        text = f"🟢 *{len(avail)} unused codes* (hand these out):\n\n" + "\n".join(f"`{r['code']}`" for r in avail)
        for i in range(0, len(text), 3500):
            await update.message.reply_text(text[i:i+3500], parse_mode="Markdown")

    def _open_app_kb():
        """Inline 'Open App Now' button that launches the Mini App directly."""
        if not WEBAPP_URL:
            return None
        return InlineKeyboardMarkup([[
            InlineKeyboardButton("🚀 Open App Now", web_app=WebAppInfo(url=WEBAPP_URL))
        ]])

    async def _notify_members(context, text, reply_markup=None):
        """Push a notification to every unlocked member, rate-limited."""
        import asyncio
        ids = all_member_ids()
        sent = 0
        for i, mid in enumerate(ids):
            try:
                await context.bot.send_message(mid, text, parse_mode="Markdown", reply_markup=reply_markup)
                sent += 1
            except Exception:
                pass  # blocked the bot / deleted account — skip
            if (i + 1) % 25 == 0:
                await asyncio.sleep(1)
        return sent

    async def post(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        text = update.message.text.partition(" ")[2]
        if "|" not in text:
            await update.message.reply_text("Usage: /post Title | Body of the update")
            return
        title, _, body = text.partition("|")
        add_update(title.strip(), body.strip())
        await update.message.reply_text("📢 Update posted. Notifying members…")
        notify_text = (
            "👑 *STRICTLY VIP*\n"
            "━━━━━━━━━━━━━━━━━━\n\n"
            "📢 *NEW UPDATE*\n\n"
            f"*{title.strip()}*\n"
            f"{body.strip()}\n\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "_Tap below to Open App_"
        )
        sent = await _notify_members(context, notify_text, reply_markup=_open_app_kb())
        await update.message.reply_text(f"✅ Posted + notified {sent} members.")

    async def addchannel(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        text = update.message.text.partition(" ")[2]
        if "|" not in text:
            await update.message.reply_text("Usage: /addchannel Name | https://t.me/link")
            return
        title, _, url = text.partition("|")
        add_link("channel", title.strip(), url.strip())
        await update.message.reply_text("🔗 Channel added. Notifying members…")
        notify_text = (
            "👑 *STRICTLY VIP*\n"
            "━━━━━━━━━━━━━━━━━━\n\n"
            "🔗 *NEW CHANNEL UNLOCKED*\n\n"
            f"*{title.strip()}*\n\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "_Tap below to Open App_"
        )
        sent = await _notify_members(context, notify_text, reply_markup=_open_app_kb())
        await update.message.reply_text(f"✅ Added + notified {sent} members.")

    async def addcontent(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        text = update.message.text.partition(" ")[2]
        if "|" not in text:
            await update.message.reply_text("Usage: /addcontent Name | https://link")
            return
        title, _, url = text.partition("|")
        add_link("content", title.strip(), url.strip())
        await update.message.reply_text("🎁 Content added. Notifying members…")
        notify_text = (
            "👑 *STRICTLY VIP*\n"
            "━━━━━━━━━━━━━━━━━━\n\n"
            "🎁 *NEW EXCLUSIVE CONTENT*\n\n"
            f"*{title.strip()}*\n\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "_Tap below to Open App_"
        )
        sent = await _notify_members(context, notify_text, reply_markup=_open_app_kb())
        await update.message.reply_text(f"✅ Added + notified {sent} members.")

    async def addmega(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        text = update.message.text.partition(" ")[2].strip()
        if not text:
            await update.message.reply_text(
                "Usage: /addmega https://mega.nz/folder/...\n"
                "(name is fetched automatically) or /addmega Name | link to set it yourself"
            )
            return

        if "|" in text:
            title, _, url = text.partition("|")
            title, url = title.strip(), url.strip()
        else:
            url = text
            await update.message.reply_text("🔎 Looking up the name on Mega…")
            title, reason = await asyncio.to_thread(fetch_mega_name_debug, url)
            if not title:
                # No Markdown here — the reason string can contain characters
                # (underscores, brackets from JSON) that would break Markdown
                # parsing and silently swallow this exact message again.
                await update.message.reply_text(
                    "⚠️ [lookup-v5] Couldn't fetch a name automatically for that link.\n\n"
                    f"Reason: {reason}\n\n"
                    "Send me that reason and I'll fix it, or add it manually with:\n"
                    "/addmega Name | " + url
                )
                return

        add_link("mega", title, url)
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("📲 Notify members", callback_data=f"notify_mega|{title[:40]}"),
            InlineKeyboardButton("🔕 Don't notify", callback_data="notify_no"),
        ]])
        await update.message.reply_text(
            f"📦 *{title}* added to the Megas tab.\n\nNotify members?",
            parse_mode="Markdown", reply_markup=kb,
        )

    async def megas_file_import(update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Send the bot a .txt or .csv file — one Mega per line. Lines can be
        'Name | link', 'Name,link', OR just a bare link with no name at all —
        bare links get their real name looked up from Mega automatically, so
        a file of 500 plain links imports itself with correct titles, no
        typing required. Prepare the list in Notes/Excel/Sheets, export as
        .txt or .csv, and just send the file directly — no command needed."""
        if not is_admin(update.effective_user.id):
            return
        doc = update.message.document
        if not doc:
            return
        if doc.file_size and doc.file_size > 3_000_000:
            await update.message.reply_text(
                "That file's larger than expected for a link list — keep it under 3MB "
                "(that's comfortably tens of thousands of lines) and try again."
            )
            return
        await update.message.reply_text("📥 Reading file…")
        try:
            tg_file = await context.bot.get_file(doc.file_id)
            raw = await tg_file.download_as_bytearray()
            text = bytes(raw).decode("utf-8", errors="ignore")
        except Exception as e:
            await update.message.reply_text(f"Couldn't read that file: {e}")
            return

        lines = [l.strip() for l in text.splitlines() if l.strip()]
        auto_lookup = [l for l in lines if "|" not in l and "," not in l]
        if auto_lookup:
            await update.message.reply_text(
                f"🔎 {len(lines)} line(s) found, {len(auto_lookup)} with no name — "
                f"fetching those from Mega automatically. This can take a few minutes for a big batch, hang tight…"
            )

        added = []
        skipped = []
        for line in lines:
            sep = "|" if "|" in line else ("," if "," in line else None)
            if sep:
                title, _, url = line.partition(sep)
                title, url = title.strip(), url.strip()
                if title and url:
                    add_link("mega", title, url)
                    added.append(title)
                else:
                    skipped.append(line)
            else:
                url = line
                title = await asyncio.to_thread(fetch_mega_name, url)
                if title:
                    add_link("mega", title, url)
                    added.append(title)
                else:
                    skipped.append(line)

        if not added:
            await update.message.reply_text(
                "No valid lines found. Each line needs: Name | link  (or Name,link — or a bare link if you want the name auto-fetched)"
            )
            return

        # With hundreds of lines, listing every title would itself blow past
        # Telegram's message limit — so just preview a handful and give a total.
        preview = "\n".join(f"• {t}" for t in added[:15])
        more = f"\n…and {len(added) - 15} more" if len(added) > 15 else ""
        msg = f"📦 Imported *{len(added)}* Megas from the file:\n{preview}{more}"
        if skipped:
            skip_list = "\n".join(f"• {s}" for s in skipped[:10])
            skip_more = f"\n…and {len(skipped) - 10} more" if len(skipped) > 10 else ""
            msg += (
                f"\n\n⚠️ Skipped {len(skipped)} line(s) — either the name lookup failed "
                f"or the line was malformed:\n{skip_list}{skip_more}"
            )
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("📲 Notify members", callback_data="notify_megabatch"),
            InlineKeyboardButton("🔕 Don't notify", callback_data="notify_no"),
        ]])
        context.chat_data["megabatch"] = added
        await update.message.reply_text(msg, parse_mode="Markdown", reply_markup=kb)

    async def addmegas(update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Batch add: paste 'Name | link' one per line, or just bare links —
        any line with no 'Name |' part gets its name looked up automatically."""
        if not is_admin(update.effective_user.id):
            return
        text = update.message.text or ""
        parts = text.split(None, 1)
        body = parts[1] if len(parts) > 1 else ""
        lines = [l.strip() for l in body.splitlines() if l.strip()]
        if not lines:
            await update.message.reply_text(
                "Paste one per line after the command — names are optional, "
                "we'll fetch them from Mega automatically:\n\n"
                "/addmegas\nhttps://mega.nz/folder/...\nhttps://mega.nz/folder/...\n"
                "Custom Name | https://mega.nz/folder/... (to override)"
            )
            return

        auto_lookup = [l for l in lines if "|" not in l]
        if auto_lookup:
            await update.message.reply_text(
                f"🔎 Looking up names for {len(auto_lookup)} link(s) on Mega… this can take a bit for a large batch."
            )

        added = []
        skipped = []
        for line in lines:
            if "|" in line:
                title, _, url = line.partition("|")
                title, url = title.strip(), url.strip()
                if title and url:
                    add_link("mega", title, url)
                    added.append(title)
                else:
                    skipped.append(line)
            else:
                url = line
                title = await asyncio.to_thread(fetch_mega_name, url)
                if title:
                    add_link("mega", title, url)
                    added.append(title)
                else:
                    skipped.append(line)
        if not added:
            await update.message.reply_text(
                "No valid lines found. Use: Name | link  (one per line, each needs a name AND a link)"
            )
            return
        preview = "\n".join(f"• {t}" for t in added[:15])
        more = f"\n…and {len(added) - 15} more" if len(added) > 15 else ""
        msg = f"📦 Added *{len(added)}* Megas:\n{preview}{more}"
        if skipped:
            skip_list = "\n".join(f"• {s}" for s in skipped[:10])
            skip_more = f"\n…and {len(skipped) - 10} more" if len(skipped) > 10 else ""
            msg += (
                f"\n\n⚠️ Skipped {len(skipped)} line(s) — either the name lookup failed "
                f"or the line was malformed. Add these manually with Name | link:\n{skip_list}{skip_more}"
            )
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("📲 Notify members", callback_data="notify_megabatch"),
            InlineKeyboardButton("🔕 Don't notify", callback_data="notify_no"),
        ]])
        context.chat_data["megabatch"] = added
        await update.message.reply_text(msg, parse_mode="Markdown", reply_markup=kb)

    async def on_notify_choice(update: Update, context: ContextTypes.DEFAULT_TYPE):
        q = update.callback_query
        if not is_admin(q.from_user.id):
            await q.answer()
            return
        await q.answer()
        data = q.data or ""
        if data == "notify_no":
            await q.edit_message_text("✅ Added quietly — members were not notified.")
            return
        if data == "notify_megabatch":
            added = context.chat_data.get("megabatch", [])
            n = len(added)
            await q.edit_message_text(f"📲 Notifying members about {n} new Megas…")
            names = "\n".join(f"• {t}" for t in added)
            notify_text = (
                "👑 *STRICTLY VIP*\n"
                "━━━━━━━━━━━━━━━━━━\n\n"
                f"📦 *{n} NEW MEGAS ADDED*\n\n"
                f"{names}\n\n"
                "━━━━━━━━━━━━━━━━━━\n"
                "_Tap below to Open App_"
            )
            sent = await _notify_members(context, notify_text, reply_markup=_open_app_kb())
            context.chat_data.pop("megabatch", None)
            await q.edit_message_text(f"✅ Added + notified {sent} members about {n} Megas.")
            return
        if data.startswith("notify_mega|"):
            title = data.split("|", 1)[1]
            await q.edit_message_text(f"📲 Notifying members about *{title}*…", parse_mode="Markdown")
            notify_text = (
                "👑 *STRICTLY VIP*\n"
                "━━━━━━━━━━━━━━━━━━\n\n"
                "📦 *NEW MEGA ADDED*\n\n"
                f"*{title}*\n\n"
                "━━━━━━━━━━━━━━━━━━\n"
                "_Tap below to Open App_"
            )
            sent = await _notify_members(context, notify_text, reply_markup=_open_app_kb())
            await q.edit_message_text(f"✅ Added + notified {sent} members about *{title}*.", parse_mode="Markdown")

    async def addreview(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        text = update.message.text.partition(" ")[2]
        if "|" not in text:
            await update.message.reply_text("Usage: /addreview Name | Their review text")
            return
        name, _, body = text.partition("|")
        add_review(None, name.strip(), body.strip())
        await update.message.reply_text("⭐ Review added to the hub.")

    async def listitems(update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Show everything with IDs so admin can delete by id."""
        if not is_admin(update.effective_user.id):
            return
        lines = ["MANAGE HUB ITEMS", ""]
        chans = get_links("channel")
        conts = get_links("content")
        megas = get_links("mega")
        revs = get_reviews()
        ups = get_updates()
        lines.append("Channels (/delchannel ID)")
        for l in chans:
            lines.append(f"  [{l['id']}] {l['title']}")
        lines.append("")
        lines.append("Content (/delcontent ID)")
        for l in conts:
            lines.append(f"  [{l['id']}] {l['title']}")
        lines.append("")
        lines.append("Megas (/delmega ID)")
        for l in megas:
            lines.append(f"  [{l['id']}] {l['title']}")
        lines.append("")
        lines.append("Updates (/delupdate ID)")
        for u in ups:
            lines.append(f"  [{u['id']}] {u['title']}")
        lines.append("")
        lines.append("Reviews (/delreview ID)")
        for r in revs:
            snippet = (r['body'][:30] + "…") if len(r['body']) > 30 else r['body']
            lines.append(f"  [{r['id']}] {r['name']}: {snippet}")
        # Plain text, not Markdown — titles/reviews are member- or admin-typed
        # free text and can contain _ * ` characters that break Markdown
        # parsing and cause the whole message to silently fail to send.
        text = "\n".join(lines)
        if not text.strip():
            await update.message.reply_text("Nothing added yet.")
            return
        for i in range(0, len(text), 3500):
            await update.message.reply_text(text[i:i+3500])

    async def _del_generic(update, context, kind):
        if not is_admin(update.effective_user.id):
            return
        if not context.args or not context.args[0].isdigit():
            await update.message.reply_text(f"Usage: /del{kind} ID  (see /list)")
            return
        rid = int(context.args[0])
        if kind == "review":
            delete_review(rid)
        elif kind == "update":
            delete_update(rid)
        else:
            delete_link(rid)
        await update.message.reply_text(f"🗑️ Deleted {kind} #{rid}.")

    async def delchannel(update, context): await _del_generic(update, context, "channel")
    async def delcontent(update, context): await _del_generic(update, context, "content")
    async def delmega(update, context): await _del_generic(update, context, "mega")
    async def delupdate(update, context): await _del_generic(update, context, "update")
    async def delreview(update, context): await _del_generic(update, context, "review")

    async def stats(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        s = member_stats()
        src_lines = "\n".join(f"  • {k}: {v}" for k, v in s["by_source"].items()) or "  • —"
        await update.message.reply_text(
            f"👑 *British On Top stats*\n\n"
            f"Total members: *{s['total']}*\n"
            f"Joined today: *{s['today']}*\n"
            f"Joined this week: *{s['week']}*\n\n"
            f"*By source:*\n{src_lines}\n\n"
            f"Reviews: *{s['reviews']}*",
            parse_mode="Markdown",
        )

    # Broadcast with a confirm step. The pending message is held per-admin.
    _pending_broadcast = {}

    async def _customer_name(context, tid):
        """Real first name + username straight from Telegram, not our DB — this
        works even for people who were never successfully unlocked (e.g. their
        code never worked, so they have no row in `members` at all)."""
        try:
            chat = await context.bot.get_chat(tid)
            first = chat.first_name or "there"
            username = chat.username
        except Exception:
            m = get_member(tid)
            first = (m["name"] if m else None) or "there"
            username = None
        return first, username

    def _member_reply_kb():
        """Attach this to any message sent TO a member so they have an obvious
        button to tap instead of having to know they can just type a reply."""
        return InlineKeyboardMarkup([[
            InlineKeyboardButton("💬 Reply", callback_data="memberreply")
        ]])

    async def reply(update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Admin replies to a member's support message: /reply USER_ID message"""
        if not is_admin(update.effective_user.id):
            return
        args = update.message.text.partition(" ")[2].strip()
        parts = args.split(" ", 1)
        if len(parts) < 2 or not parts[0].isdigit():
            await update.message.reply_text("Usage: /reply USER_ID your message")
            return
        target = int(parts[0])
        msg = parts[1]
        try:
            await context.bot.send_message(
                target,
                f"💬 *Support reply*\n\n{msg}",
                parse_mode="Markdown",
                reply_markup=_member_reply_kb(),
            )
            await update.message.reply_text("✅ Reply sent.")
        except Exception as e:
            await update.message.reply_text(f"Couldn't send: {e}")

    async def broadcast(update: Update, context: ContextTypes.DEFAULT_TYPE):
        uid = update.effective_user.id
        if not is_admin(uid):
            return
        msg = update.message.text.partition(" ")[2].strip()
        if not msg:
            await update.message.reply_text("Usage: /broadcast Your message to all members")
            return
        _pending_broadcast[uid] = msg
        count = len(all_member_ids())
        await update.message.reply_text(
            f"📢 *Ready to broadcast to {count} members:*\n\n{msg}\n\n"
            f"Send /confirmbroadcast to send it, or /cancelbroadcast to abort.",
            parse_mode="Markdown",
        )

    async def confirmbroadcast(update: Update, context: ContextTypes.DEFAULT_TYPE):
        uid = update.effective_user.id
        if not is_admin(uid):
            return
        msg = _pending_broadcast.pop(uid, None)
        if not msg:
            await update.message.reply_text("Nothing queued. Use /broadcast first.")
            return
        ids = all_member_ids()
        await update.message.reply_text(f"📤 Sending to {len(ids)} members…")
        sent = 0
        failed = 0
        for i, mid in enumerate(ids):
            try:
                await context.bot.send_message(mid, msg, reply_markup=_open_app_kb())
                sent += 1
            except Exception:
                failed += 1
            # Respect Telegram rate limits: pause briefly every ~25 sends.
            if (i + 1) % 25 == 0:
                import asyncio
                await asyncio.sleep(1)
        await update.message.reply_text(f"✅ Broadcast done. Sent: {sent}, failed: {failed}.")

    async def cancelbroadcast(update: Update, context: ContextTypes.DEFAULT_TYPE):
        uid = update.effective_user.id
        if not is_admin(uid):
            return
        _pending_broadcast.pop(uid, None)
        await update.message.reply_text("Broadcast cancelled.")

    async def resetwelcome(update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Admin: force EVERYONE to see + accept the disclaimer on next open."""
        if not is_admin(update.effective_user.id):
            return
        with get_conn() as conn, conn.cursor() as cur:
            cur.execute("UPDATE members SET welcomed = 0")
        await update.message.reply_text(
            "✅ Done — every member will see and must accept the disclaimer "
            "next time they open the app."
        )

    async def helpcmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            return
        await update.message.reply_text(
            "*Admin commands*\n\n"
            "*Codes*\n"
            "/gencodes N [label] — make N single-use codes\n"
            "/newcode CODE [label] — one specific code\n"
            "/codes — codes overview\n"
            "/listunused — unused codes to hand out\n"
            "/revokecode CODE — turn a code off\n\n"
            "*Content*\n"
            "/post Title | Body — post an update\n"
            "/addchannel Name | url — add a channel\n"
            "/addcontent Name | url — add content\n"
            "/addreview Name | text — add a review\n"
            "/list — see items with IDs\n"
            "/delchannel /delcontent /delupdate /delreview ID\n\n"
            "*Members*\n"
            "/stats — member analytics\n"
            "/broadcast msg — message all members (asks to confirm)\n",
            parse_mode="Markdown",
        )

    async def on_support_action(update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handles taps on the two support buttons: Submit New Code / Reply to Customer."""
        q = update.callback_query
        if not is_admin(q.from_user.id):
            await q.answer()
            return
        data = q.data or ""
        kind, _, tid_str = data.partition("|")
        if not tid_str.isdigit():
            await q.answer()
            return
        tid = int(tid_str)
        name, username = await _customer_name(context, tid)
        handle = f" (@{username})" if username else ""

        if kind == "submitcode":
            await q.answer("Generating code…")
            codes = gen_codes(1, f"support-{tid}")
            if not codes:
                await q.message.reply_text("⚠️ Couldn't generate a code — try again.")
                return
            code = codes[0]
            customer_msg = (
                "👑 *British On Top Support*\n\n"
                f"Hi {name}, here's a replacement access code:\n\n"
                f"`{code}`\n\n"
                "Open the app and enter it to get back in.\n\n"
                "If you run into any issues, simply reply to this message and we'll sort it out."
            )
            try:
                await context.bot.send_message(
                    tid, customer_msg, parse_mode="Markdown", reply_markup=_member_reply_kb()
                )
                await q.message.reply_text(
                    f"✅ New code sent to {name}{handle} (`{tid}`): `{code}`", parse_mode="Markdown"
                )
            except Exception as e:
                await q.message.reply_text(
                    f"⚠️ Generated `{code}` but couldn't message {name}{handle}: {e}", parse_mode="Markdown"
                )
            return

        if kind == "replysupport":
            await q.answer()
            prompt = await context.bot.send_message(
                q.message.chat_id,
                f"💬 Type your reply to {name}{handle} (`{tid}`) — reply to THIS message with your answer:",
                parse_mode="Markdown",
                reply_markup=ForceReply(selective=True),
            )
            context.bot_data.setdefault("reply_targets", {})[prompt.message_id] = tid
            return

    async def on_admin_reply_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Captures the admin's reply to a 'Reply to Customer' prompt and forwards it."""
        msg = update.message
        if not msg or not msg.reply_to_message or not msg.text:
            return
        if not is_admin(update.effective_user.id):
            return
        targets = context.bot_data.get("reply_targets", {})
        tid = targets.get(msg.reply_to_message.message_id)
        if not tid:
            return
        try:
            await context.bot.send_message(
                tid, f"💬 *Support reply*\n\n{msg.text}",
                parse_mode="Markdown", reply_markup=_member_reply_kb(),
            )
            await msg.reply_text("✅ Reply sent.")
            targets.pop(msg.reply_to_message.message_id, None)
        except Exception as e:
            await msg.reply_text(f"Couldn't send: {e}")

    async def on_member_reply_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Customer taps 'Reply' on a message we sent them — prompt them to type,
        same ForceReply trick we use for admins. Whatever they send next is
        picked up automatically by member_dm_to_support below."""
        q = update.callback_query
        await q.answer()
        await context.bot.send_message(
            q.message.chat_id,
            "💬 Type your message below and we'll get back to you:",
            reply_markup=ForceReply(selective=True),
        )

    async def member_dm_to_support(update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Any plain-text DM a member sends the bot becomes a support message to
        admins — this is what makes 'just reply to this message' a real promise
        rather than a line with nothing behind it."""
        msg = update.message
        if not msg or not msg.text:
            return
        uid = update.effective_user.id
        if is_admin(uid):
            return
        body = msg.text.strip()
        if not body:
            return
        name = update.effective_user.first_name or "Member"
        with get_conn() as conn, conn.cursor() as cur:
            cur.execute(
                "INSERT INTO support_messages (telegram_id, name, body, created_at) "
                "VALUES (%s, %s, %s, %s)",
                (uid, name, body, int(time.time())),
            )
        note = f"💬 *Support message* (via chat)\nFrom: {name} (`{uid}`)\n\n{body}"
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("💬 Reply to Customer", callback_data=f"replysupport|{uid}"),
            InlineKeyboardButton("🔑 Submit New Code", callback_data=f"submitcode|{uid}"),
        ]])
        for admin_id in ADMIN_IDS:
            try:
                await context.bot.send_message(admin_id, note, parse_mode="Markdown", reply_markup=kb)
            except Exception as e:
                log.error("member DM forward failed: %s", e)
        await msg.reply_text("✅ Got it — we'll get back to you here shortly.")

    application = Application.builder().token(BOT_TOKEN).build()
    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("newcode", newcode))
    application.add_handler(CommandHandler("gencodes", gencodes))
    application.add_handler(CommandHandler("revokecode", revokecode))
    application.add_handler(CommandHandler("codes", codes))
    application.add_handler(CommandHandler("listunused", listunused))
    # /post retired — Gallery (photos/videos with captions) replaces the old
    # text-only update feature. The post() function is left defined above,
    # unused, in case you ever want it back.
    # application.add_handler(CommandHandler("post", post))
    application.add_handler(CommandHandler("addchannel", addchannel))
    application.add_handler(CommandHandler("addcontent", addcontent))
    application.add_handler(CommandHandler("addmega", addmega))
    application.add_handler(CommandHandler("addmegas", addmegas))
    application.add_handler(CallbackQueryHandler(on_notify_choice, pattern=r"^notify_"))
    application.add_handler(CommandHandler("addreview", addreview))
    application.add_handler(CommandHandler("list", listitems))
    application.add_handler(CommandHandler("delchannel", delchannel))
    application.add_handler(CommandHandler("delcontent", delcontent))
    application.add_handler(CommandHandler("delmega", delmega))
    application.add_handler(CommandHandler("delupdate", delupdate))
    application.add_handler(CommandHandler("delreview", delreview))
    application.add_handler(CommandHandler("stats", stats))
    application.add_handler(CommandHandler("broadcast", broadcast))
    application.add_handler(CommandHandler("reply", reply))
    application.add_handler(CommandHandler("resetwelcome", resetwelcome))
    application.add_handler(CommandHandler("confirmbroadcast", confirmbroadcast))
    application.add_handler(CommandHandler("cancelbroadcast", cancelbroadcast))
    application.add_handler(CommandHandler("help", helpcmd))
    application.add_handler(CallbackQueryHandler(on_support_action, pattern=r"^(replysupport|submitcode)\|"))
    application.add_handler(CallbackQueryHandler(on_member_reply_button, pattern=r"^memberreply$"))
    application.add_handler(MessageHandler(filters.REPLY & filters.TEXT & ~filters.COMMAND, on_admin_reply_text))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE, member_dm_to_support))

    log.info("Bot starting (polling)...")
    # stop_signals=None because signal handlers can only be set in the main
    # thread — this bot runs in a background thread.
    application.run_polling(close_loop=False, stop_signals=None)


if __name__ == "__main__":
    log.info("=== BUILD MARKER: lookup-v5 ===")
    init_db()
    # Bot runs in a background thread; Flask serves the web app on the main thread.
    if BOT_TOKEN:
        threading.Thread(target=run_bot, daemon=True).start()
    port = int(os.environ.get("PORT", "8080"))
    app.run(host="0.0.0.0", port=port)
