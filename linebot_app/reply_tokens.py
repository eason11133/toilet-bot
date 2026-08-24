import os
import logging
import threading
import hashlib

import requests
from core.database import POSTGRES_ENABLED, _pg_connect

# === reply_token 使用記錄（新增） ===
_USED_REPLY_TOKENS = set()
_USED_REPLY_LOCK = threading.Lock()
_MAX_USED_TOKENS = 50000  # 防止集合無限成長
CHANNEL_ACCESS_TOKEN = os.getenv("LINE_CHANNEL_ACCESS_TOKEN")

def show_loading(uid, seconds=10):
    url = "https://api.line.me/v2/bot/chat/loading/start"
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {CHANNEL_ACCESS_TOKEN}"
    }
    payload = {
        "chatId": uid,
        "loadingSeconds": max(5, min(seconds, 60))
    }

    try:
        timeout = float(os.getenv("LINE_LOADING_TIMEOUT_SEC", "3"))
        resp = requests.post(url, headers=headers, json=payload, timeout=timeout)
        logging.info(f"[loading] {resp.status_code} {resp.text}")
        return resp.ok
    except requests.RequestException as e:
        # Loading animation is best-effort and must never delay the actual
        # reply long enough for its one-minute token window to expire.
        logging.warning(f"[loading] request failed; continue without animation: {e}")
        return False

def _mark_token_used(tok: str):
    try:
        if not tok:
            return
        with _USED_REPLY_LOCK:
            _USED_REPLY_TOKENS.add(tok)
            if len(_USED_REPLY_TOKENS) > _MAX_USED_TOKENS:
                _USED_REPLY_TOKENS.clear()  # 簡單清理
    except Exception:
        pass


def _is_token_used(tok: str) -> bool:
    if not tok:
        return False
    try:
        with _USED_REPLY_LOCK:
            return tok in _USED_REPLY_TOKENS
    except Exception:
        return False


def claim_reply_token(tok: str) -> bool:
    """Atomically reserve a reply token before sending it to LINE."""
    if not tok:
        return False

    token_hash = hashlib.sha256(tok.encode("utf-8")).hexdigest()
    if POSTGRES_ENABLED:
        conn = None
        cur = None
        try:
            conn = _pg_connect()
            cur = conn.cursor()
            cur.execute(
                "INSERT INTO line_reply_tokens (token_hash) VALUES (%s) "
                "ON CONFLICT (token_hash) DO NOTHING RETURNING token_hash",
                (token_hash,),
            )
            inserted = cur.fetchone() is not None
            if inserted and int(token_hash[:4], 16) % 100 == 0:
                cur.execute(
                    "DELETE FROM line_reply_tokens "
                    "WHERE created_at < NOW() - INTERVAL '24 hours'"
                )
            conn.commit()
            return inserted
        except Exception as e:
            if conn is not None:
                try:
                    conn.rollback()
                except Exception:
                    pass
            logging.warning(f"persistent reply-token claim failed; using local fallback: {e}")
        finally:
            if cur is not None:
                try:
                    cur.close()
                except Exception:
                    pass
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass

    with _USED_REPLY_LOCK:
        if tok in _USED_REPLY_TOKENS:
            return False
        _USED_REPLY_TOKENS.add(tok)
        if len(_USED_REPLY_TOKENS) > _MAX_USED_TOKENS:
            _USED_REPLY_TOKENS.clear()
            _USED_REPLY_TOKENS.add(tok)
        return True


# ------ 統一設定（已抽到 config.py；這裡只保留 runtime state）------
