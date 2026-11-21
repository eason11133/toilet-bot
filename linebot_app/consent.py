import os
import logging
import threading
import time
from collections import OrderedDict, deque
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit

from flask import has_request_context, request
from linebot.models import TextSendMessage

POSTGRES_ENABLED = False
_pg_connect = None
T = None
CONSENT_PAGE_URL = ""
CONSENT_FLOW_VERSION = os.getenv("CONSENT_FLOW_VERSION", "20261121-4")


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
        return False
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
        logging.warning(f"查詢 Neon 同意資料失敗: {e}")
        return False
    finally:
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass


def upsert_consent(user_id: str, agreed: bool, display_name: str, source_type: str, ua: str, ts_iso: str):
    """Write consent to Neon user_consent."""
    if not user_id:
        return False
    if not POSTGRES_ENABLED:
        logging.warning("Postgres not enabled for consent")
        return False
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
        logging.error(f"寫入/更新 Neon 同意資料失敗: {e}", exc_info=True)
        return False
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
    if "password authentication failed" in message or "authentication failed" in message:
        return "invalid_credentials"
    if "could not translate host name" in message or "name or service not known" in message:
        return "dns_failure"
    if "timeout" in message or "timed out" in message:
        return "timeout"
    if "too many connections" in message or "remaining connection slots" in message:
        return "connection_limit"
    if "connection refused" in message:
        return "connection_refused"
    if "ssl" in message or "tls" in message or "certificate" in message:
        return "tls_failure"
    return "other"


def consent_storage_health():
    """Check consent persistence without reading any user record."""
    if not POSTGRES_ENABLED:
        return False, "postgres_disabled"
    conn = None
    try:
        conn = _pg_connect()
    except Exception as exc:
        error_type = type(exc).__name__
        category = _database_error_category(exc)
        logging.warning("consent storage connection failed: %s/%s", error_type, category)
        return False, f"connection_failed:{error_type}:{category}"
    try:
        cur = conn.cursor()
        cur.execute("SELECT to_regclass('public.user_consent') IS NOT NULL")
        row = cur.fetchone()
        return bool(row and row[0]), "ok" if row and row[0] else "table_missing"
    except Exception as exc:
        error_type = type(exc).__name__
        logging.warning("consent storage query failed: %s", error_type)
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
