import os
import json
import logging
import threading
import time

from linebot.models import MessageEvent, TextMessage, LocationMessage, PostbackEvent

# === 防重複（簡單版：避免同一 webhook 在短時間內重複處理）===
DEDUPE_WINDOW = int(os.getenv("DEDUPE_WINDOW", "10"))
_DEDUPE_SIMPLE_LOCK = threading.Lock()
_RECENT_EVENTS_SIMPLE = {}

def is_duplicate_and_mark(key: str, window: int = DEDUPE_WINDOW) -> bool:
    """簡單防重：同一 key 在 window 秒內視為重複。

    這段邏輯保留給舊流程使用；下方另有更精準的事件去重（_event_type_and_key）。
    """
    now = time.time()
    if not key:
        return False
    try:
        with _DEDUPE_SIMPLE_LOCK:
            ts = _RECENT_EVENTS_SIMPLE.get(key)
            if ts is not None and (now - ts) < window:
                logging.info(f"🔁 skip duplicate: {key}")
                return True
            _RECENT_EVENTS_SIMPLE[key] = now
            # 輕量清理，避免 dict 無限成長
            if len(_RECENT_EVENTS_SIMPLE) > 5000:
                cutoff = now - window
                for k, tstamp in list(_RECENT_EVENTS_SIMPLE.items()):
                    if tstamp < cutoff:
                        _RECENT_EVENTS_SIMPLE.pop(k, None)
        return False
    except Exception:
        return False


def _event_type_and_key(event):
    """回傳 (event_type, dedupe_key)。盡量使用 LINE event 的穩定欄位組 key。"""
    try:
        source = getattr(event, "source", None)
        uid = getattr(source, "user_id", "") or ""
        ts = str(getattr(event, "timestamp", "") or "")

        if isinstance(event, PostbackEvent):
            data = getattr(getattr(event, "postback", None), "data", "") or ""
            params = getattr(getattr(event, "postback", None), "params", None)
            params_str = json.dumps(params, ensure_ascii=False, sort_keys=True) if params else ""
            return "postback", f"{uid}|postback|{data}|{params_str}|{ts}"

        if isinstance(event, MessageEvent):
            msg = getattr(event, "message", None)
            msg_id = getattr(msg, "id", None)
            if msg_id:
                return "message", f"{uid}|message_id|{msg_id}"

            if isinstance(msg, LocationMessage):
                lat = getattr(msg, "latitude", "")
                lon = getattr(msg, "longitude", "")
                title = getattr(msg, "title", "") or ""
                address = getattr(msg, "address", "") or ""
                return "location", f"{uid}|location|{lat}|{lon}|{title}|{address}|{ts}"

            if isinstance(msg, TextMessage):
                txt = getattr(msg, "text", "") or ""
                return "text", f"{uid}|text|{txt}|{ts}"

            return "message", f"{uid}|message|{ts}"

        return "event", f"{uid}|event|{ts}"
    except Exception:
        return "event", f"fallback|{time.time()}"


def is_duplicate_and_mark_event(event, window: int = DEDUPE_WINDOW) -> bool:
    """事件級防重複：
    - 若 LINE 標記為 redelivery，直接略過
    - 其餘事件用穩定 key 在短時間內去重
    """
    try:
        if is_redelivery(event):
            logging.info("🔁 skip redelivery event")
            return True

        event_type, key = _event_type_and_key(event)
        duplicated = is_duplicate_and_mark(key, window=window)
        if duplicated:
            logging.info(f"🔁 skip duplicate {event_type}: {key}")
        return duplicated
    except Exception as e:
        logging.error(f"is_duplicate_and_mark_event failed: {e}", exc_info=True)
        return False


def is_redelivery(event) -> bool:
    try:
        dc = getattr(event, "delivery_context", None)
        return bool(getattr(dc, "is_redelivery", False))
    except Exception:
        return False

