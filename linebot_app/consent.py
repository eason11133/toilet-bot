import os
import logging
import threading
import time
from collections import OrderedDict, deque
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit

import requests
from flask import has_request_context, request
from linebot.models import TextSendMessage

POSTGRES_ENABLED = False
_pg_connect = None
T = None
CONSENT_PAGE_URL = ""
CONSENT_FLOW_VERSION = os.getenv("CONSENT_FLOW_VERSION", "20261121-5")
CONSENT_STAGING_URL = (os.getenv("CONSENT_STAGING_URL") or "").strip()
CONSENT_STAGING_SECRET = (os.getenv("CONSENT_STAGING_SECRET") or "").strip()


def _staging_post(action, payload=None, include_secret=True):
    if not CONSENT_STAGING_URL:
        return None
    headers = {"Content-Type": "application/json"}
    if include_secret:
        if not CONSENT_STAGING_SECRET:
            return None
        headers["x-consent-backend-secret"] = CONSENT_STAGING_SECRET
    try:
        response = requests.post(
            CONSENT_STAGING_URL,
            json={"action": action, **(payload or {})},
            headers=headers,
            timeout=float(os.getenv("CONSENT_STAGING_TIMEOUT_SEC", "6")),
        )
        data = response.json() if response.content else {}
        return data if response.ok and isinstance(data, dict) else None
    except (requests.RequestException, ValueError) as exc:
        logging.warning("consent staging request failed: %s", type(exc).__name__)
        return None


def _staging_has_consented(user_id):
    result = _staging_post("check", {"userId": user_id})
    return bool(result and result.get("ok") and result.get("agreed"))


def _staging_upsert(access_token, agreed, source_type, ua):
    if not access_token:
        return False
    result = _staging_post(
        "upsert",
        {
            "accessToken": access_token,
            "agreed": bool(agreed),
            "sourceType": source_type or "",
            "userAgent": ua or "",
        },
        include_secret=False,
    )
    return bool(result and result.get("ok"))


def sync_staged_consents(batch_limit=500, max_batches=10):
    """Idempotently copy staged consents back to Neon when it is available."""
    if not POSTGRES_ENABLED or not CONSENT_STAGING_URL or not CONSENT_STAGING_SECRET:
        return 0
    total = 0
    for _ in range(max_batches):
        result = _staging_post("list_unsynced", {"limit": int(batch_limit)})
        rows = result.get("rows") if isinstance(result, dict) else None
        if not rows:
            break
        conn = None
        try:
            conn = _pg_connect()
            cur = conn.cursor()
            values = []
            ids = []
            for row in rows:
                user_id = str(row.get("user_id") or "").strip()
                if not user_id:
                    continue
                ids.append(user_id)
                values.append((
                    user_id,
                    bool(row.get("agreed")),
                    str(row.get("display_name") or "")[:200],
                    str(row.get("source_type") or "")[:50],
                    str(row.get("user_agent") or "")[:500],
                    row.get("consented_at"),
                    row.get("updated_at"),
                ))
            if not values:
                break
            cur.executemany("""
                INSERT INTO user_consent
                    (user_id, agreed, display_name, source_type, user_agent, created_at, updated_at)
                VALUES (%s, %s, %s, %s, %s, COALESCE(%s::timestamptz, NOW()), COALESCE(%s::timestamptz, NOW()))
                ON CONFLICT (user_id) DO UPDATE SET
                    agreed = EXCLUDED.agreed,
                    display_name = EXCLUDED.display_name,
                    source_type = EXCLUDED.source_type,
                    user_agent = EXCLUDED.user_agent,
                    updated_at = EXCLUDED.updated_at
            """, values)
            conn.commit()
        except Exception:
            if conn is not None:
                try:
                    conn.rollback()
                except Exception:
                    pass
            break
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
        marked = _staging_post("mark_synced", {"userIds": ids})
        if not marked or not marked.get("ok"):
            break
        total += len(ids)
        if len(rows) < batch_limit:
            break
    return total


def configure_consent(postgres_enabled=False, pg_connect=None, T_func=None, consent_page_url=""):
    global POSTGRES_ENABLED, _pg_connect, T, CONSENT_PAGE_URL
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    T = T_func
    CONSENT_PAGE_URL = consent_page_url or ""


# === consent 背景排隊（429 時不回 500） ===
_consent_q = deque(maxlen=max(10, int(os.getenv("CONSENT_QUEUE_MAX", "200"))))
_consent_lock = threading.Lock()    

def _start_consent_worker():
    def loop():
        next_sync_at = time.time() + 60
        while True:
            job = None
            try:
                # 取出一個工作
                with _consent_lock:
                    if _consent_q:
                        job = _consent_q.popleft()
            except Exception as e:
                logging.error(f"Consent worker dequeue error: {e}")

            if not job:
                if time.time() >= next_sync_at:
                    try:
                        synced = sync_staged_consents()
                        if synced:
                            logging.info("consent staging sync complete rows=%s", synced)
                    except Exception as exc:
                        logging.warning("consent staging sync skipped: %s", type(exc).__name__)
                    next_sync_at = time.time() + max(
                        300, int(os.getenv("CONSENT_STAGING_SYNC_INTERVAL_SEC", "21600"))
                    )
                time.sleep(0.2)
                continue

            try:
                job()  # 執行補寫
            except Exception as e:
                logging.error(f"Consent worker error: {e}")

    t = threading.Thread(target=loop, name="consent-worker", daemon=True)
    t.start()


# === 同意工具 ===
def _booly(v):
    s = str(v).strip().lower()
    return s in ["1", "true", "yes", "y", "同意"]

# （可選微優化）本機同意快取，TTL 預設 10 分鐘；失敗時當未同意（不影響功能）
_consent_cache = OrderedDict()   # bounded user_id -> (ts, bool)
_consent_cache_lock = threading.Lock()
# Consent is correctness/privacy state, not ordinary content cache. Keep the
# default disabled so every webhook observes the durable database value. A
# short positive-only TTL can still be opted into explicitly if traffic grows.
_CONSENT_TTL = max(0, int(os.getenv("CONSENT_TTL_SEC", "0")))
_CONSENT_CACHE_MAX = max(100, int(os.getenv("CONSENT_CACHE_MAX", "2000")))

def _consent_cache_set(user_id, value):
    with _consent_cache_lock:
        # Never cache a negative answer. A consent write may be handled by a
        # different Gunicorn process, and a cached False would keep blocking
        # that user until the old 10-minute TTL expired.
        if not value:
            _consent_cache.pop(user_id, None)
            return
        _consent_cache[user_id] = (time.time(), True)
        _consent_cache.move_to_end(user_id)
        while len(_consent_cache) > _CONSENT_CACHE_MAX:
            _consent_cache.popitem(last=False)

def has_consented(user_id: str) -> bool:
    """Read consent from Neon user_consent."""
    if not user_id:
        return False
    if not POSTGRES_ENABLED:
        logging.warning("Postgres not enabled for consent")
        return _staging_has_consented(user_id)
    conn = None
    try:
        now = time.time()
        with _consent_cache_lock:
            hit = _consent_cache.get(user_id)
            if _CONSENT_TTL > 0 and hit and bool(hit[1]) and (now - hit[0] < _CONSENT_TTL):
                _consent_cache.move_to_end(user_id)
                return True
            if hit:
                _consent_cache.pop(user_id, None)

        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("SELECT agreed FROM user_consent WHERE user_id = %s", (user_id,))
        row = cur.fetchone()
        conn.close()
        conn = None

        ok = bool(row and row[0])
        _consent_cache_set(user_id, ok)
        return ok
    except Exception as e:
        logging.warning("Neon consent read failed; trying staging: %s", type(e).__name__)
        return _staging_has_consented(user_id)
    finally:
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass


def upsert_consent(
    user_id: str,
    agreed: bool,
    display_name: str,
    source_type: str,
    ua: str,
    ts_iso: str,
    access_token: str = "",
):
    """Write consent to Neon user_consent."""
    if not user_id:
        return False
    if not POSTGRES_ENABLED:
        logging.warning("Postgres not enabled for consent")
        ok = _staging_upsert(access_token, agreed, source_type, ua)
        if ok:
            _consent_cache_set(user_id, agreed)
        return ok
    conn = None
    try:
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO user_consent (user_id, agreed, display_name, source_type, user_agent, created_at, updated_at)
            VALUES (%s, %s, %s, %s, %s, NOW(), NOW())
            ON CONFLICT (user_id)
            DO UPDATE SET
                agreed = EXCLUDED.agreed,
                display_name = EXCLUDED.display_name,
                source_type = EXCLUDED.source_type,
                user_agent = EXCLUDED.user_agent,
                updated_at = NOW()
        """, (user_id, bool(agreed), display_name or "", source_type or "", ua or ""))
        conn.commit()
        conn.close()
        conn = None
        _consent_cache_set(user_id, agreed)
        return True
    except Exception as e:
        logging.warning("Neon consent write failed; trying staging: %s", type(e).__name__)
        ok = _staging_upsert(access_token, agreed, source_type, ua)
        if ok:
            _consent_cache_set(user_id, agreed)
        return ok
    finally:
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass

def ensure_consent_or_prompt(user_id: str):
    if has_consented(user_id):
        return None
    consent_url = CONSENT_PAGE_URL
    if not consent_url and has_request_context():
        consent_url = request.url_root.rstrip("/") + "/consent"
    if consent_url:
        parts = urlsplit(consent_url)
        query = dict(parse_qsl(parts.query, keep_blank_values=True))
        query["cv"] = CONSENT_FLOW_VERSION
        consent_url = urlunsplit(
            (parts.scheme, parts.netloc, parts.path, urlencode(query), parts.fragment)
        )
    tip = T("consent_required", uid=user_id, url=consent_url)
    return TextSendMessage(text=tip)


def _database_error_category(exc):
    """Return a non-sensitive connection error category for diagnostics."""
    message = str(exc).lower()
    if "exceeded the quota" in message or "quota exceeded" in message:
        return "quota_exceeded"
    if "password authentication failed" in message or "authentication failed" in message:
        return "invalid_credentials"
    if "could not translate host name" in message or "name or service not known" in message:
        return "dns_failure"
    if "timeout" in message or "timed out" in message:
        return "timeout"
    if "too many connections" in message or "remaining connection slots" in message:
        return "connection_limit"
    if "max client connections" in message:
        return "connection_limit"
    if "connection refused" in message:
        return "connection_refused"
    if "server closed the connection unexpectedly" in message:
        return "server_closed"
    if "connection reset" in message:
        return "connection_reset"
    if "network is unreachable" in message or "no route to host" in message:
        return "network_unreachable"
    if "endpoint" in message and ("disabled" in message or "suspended" in message):
        return "endpoint_inactive"
    if "database" in message and "does not exist" in message:
        return "missing_database"
    if "role" in message and "does not exist" in message:
        return "missing_role"
    if "invalid dsn" in message or "invalid connection option" in message:
        return "invalid_dsn"
    if "ssl" in message or "tls" in message or "certificate" in message:
        return "tls_failure"
    return "other"


def consent_storage_health():
    """Check consent persistence without reading any user record."""
    if not POSTGRES_ENABLED:
        staging = _staging_post("health")
        return (True, "staging_ok") if staging and staging.get("ok") else (False, "postgres_disabled")
    conn = None
    try:
        conn = _pg_connect()
    except Exception as exc:
        error_type = type(exc).__name__
        category = _database_error_category(exc)
        logging.warning("consent storage connection failed: %s/%s", error_type, category)
        staging = _staging_post("health")
        if staging and staging.get("ok"):
            return True, f"staging_ok:neon_{category}"
        return False, f"connection_failed:{error_type}:{category}"
    try:
        cur = conn.cursor()
        cur.execute("SELECT to_regclass('public.user_consent') IS NOT NULL")
        row = cur.fetchone()
        return bool(row and row[0]), "ok" if row and row[0] else "table_missing"
    except Exception as exc:
        error_type = type(exc).__name__
        logging.warning("consent storage query failed: %s", error_type)
        staging = _staging_post("health")
        if staging and staging.get("ok"):
            return True, f"staging_ok:neon_query_{error_type}"
        return False, f"query_failed:{error_type}"
    finally:
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass


# === LIFF 同意 API：微節流；只有資料庫確實寫入才回成功 ===
_last_consent_ts = OrderedDict()
_CONSENT_RATE_LIMIT_MAX = max(100, int(os.getenv("CONSENT_RATE_LIMIT_MAX", "5000")))

def record_consent_attempt(user_id, now):
    _last_consent_ts[user_id] = now
    _last_consent_ts.move_to_end(user_id)
    while len(_last_consent_ts) > _CONSENT_RATE_LIMIT_MAX:
        _last_consent_ts.popitem(last=False)

CONSENT_MIN_INTERVAL = float(os.getenv("CONSENT_MIN_INTERVAL", "1.0"))
