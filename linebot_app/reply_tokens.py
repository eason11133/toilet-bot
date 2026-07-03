import os
import logging
import threading

import requests

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

    resp = requests.post(url, headers=headers, json=payload)
    logging.info(f"[loading] {resp.status_code} {resp.text}")

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


# ------ 統一設定（已抽到 config.py；這裡只保留 runtime state）------
