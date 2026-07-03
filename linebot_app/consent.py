import os
import logging
import threading
import time

from linebot.models import TextSendMessage

POSTGRES_ENABLED = False
_pg_connect = None
T = None
CONSENT_PAGE_URL = ""


def configure_consent(postgres_enabled=False, pg_connect=None, T_func=None, consent_page_url=""):
    global POSTGRES_ENABLED, _pg_connect, T, CONSENT_PAGE_URL
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    T = T_func
    CONSENT_PAGE_URL = consent_page_url or ""


# === consent 背景排隊（429 時不回 500） ===
_consent_q = []                    
_consent_lock = threading.Lock()    

def _start_consent_worker():
    def loop():
        while True:
            job = None
            try:
                # 取出一個工作
                with _consent_lock:
                    if _consent_q:
                        job = _consent_q.pop(0)
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
_consent_cache = {}   # user_id -> (ts, bool)
_CONSENT_TTL = int(os.getenv("CONSENT_TTL_SEC", "600"))

def has_consented(user_id: str) -> bool:
    """Read consent from Neon user_consent."""
    if not user_id:
        return False
    if not POSTGRES_ENABLED:
        logging.warning("Postgres not enabled for consent")
        return False
    try:
        now = time.time()
        hit = _consent_cache.get(user_id)
        if hit and (now - hit[0] < _CONSENT_TTL):
            return bool(hit[1])

        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("SELECT agreed FROM user_consent WHERE user_id = %s", (user_id,))
        row = cur.fetchone()
        conn.close()

        ok = bool(row and row[0])
        _consent_cache[user_id] = (now, ok)
        return ok
    except Exception as e:
        logging.warning(f"查詢 Neon 同意資料失敗: {e}")
        return False


def upsert_consent(user_id: str, agreed: bool, display_name: str, source_type: str, ua: str, ts_iso: str):
    """Write consent to Neon user_consent."""
    if not user_id:
        return False
    if not POSTGRES_ENABLED:
        logging.warning("Postgres not enabled for consent")
        return False
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
        _consent_cache[user_id] = (time.time(), bool(agreed))
        return True
    except Exception as e:
        logging.error(f"寫入/更新 Neon 同意資料失敗: {e}", exc_info=True)
        return False

def ensure_consent_or_prompt(user_id: str):
    if has_consented(user_id):
        return None
    tip = T("consent_required", uid=user_id, url=CONSENT_PAGE_URL)
    return TextSendMessage(text=tip)


# === LIFF 同意 API（新增：微節流＋失敗入背景佇列，回 200） ===
_last_consent_ts = {}
CONSENT_MIN_INTERVAL = float(os.getenv("CONSENT_MIN_INTERVAL", "1.0"))
