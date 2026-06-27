import os
import csv
import json
import logging
import sqlite3
import requests
import traceback
import heapq
import math
import uuid
from collections import OrderedDict
from math import radians, cos, sin, asin, sqrt
from flask_cors import CORS
from flask import Flask, request, abort, render_template, redirect, url_for, Response, jsonify
from dotenv import load_dotenv
from urllib.parse import quote, unquote, parse_qs
import urllib.parse
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError, LineBotApiError
from linebot.models import (
    MessageEvent, TextMessage, LocationMessage,
    TextSendMessage, FlexSendMessage,
    QuickReply, QuickReplyButton, LocationAction, MessageAction,
    PostbackEvent, PostbackAction   
)
from linebot.models import QuickReply, QuickReplyButton
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeoutError
from datetime import datetime, timezone, timedelta
from openai import OpenAI
import hashlib
import html
import joblib
import threading
import time
import statistics
from difflib import SequenceMatcher
import random
import re

try:
    import psycopg2
    import psycopg2.extras
except Exception:
    psycopg2 = None

load_dotenv()
try:
    import pandas as pd
except Exception:
    pd = None

# === 全域設定 ===
def _try_acquire_loc_slot() -> bool:
    try:
        return _LOC_SEM.acquire(blocking=False)
    except Exception:
        return False

def _release_loc_slot():
    try:
        _LOC_SEM.release()
    except Exception:
        pass

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

def grid_coord(v, g=0.0005):
    """
    座標格點化：
    g=0.0005 ≈ 50 公尺
    """
    try:
        return round(float(v) / g) * g
    except Exception:
        return v

class SimpleLRU(OrderedDict):
    def __init__(self, maxsize=500):
        super().__init__()
        self.maxsize = maxsize
    def get(self, key, default=None):
        if key in self:
            self.move_to_end(key)
            return super().get(key)
        return default
    def set(self, key, value):
        super().__setitem__(key, value)
        self.move_to_end(key)
        while len(self) > self.maxsize:
            self.popitem(last=False)

def _in_bbox(lat, lon, clat, clon, radius_m):
    """
    粗略矩形篩選，先擋掉不可能在半徑內的點
    """
    try:
        lat = float(lat); lon = float(lon)
        clat = float(clat); clon = float(clon)
    except Exception:
        return False

    dlat = radius_m / 111000.0
    dlon = radius_m / (111000.0 * math.cos(math.radians(clat)))
    return (
        clat - dlat <= lat <= clat + dlat and
        clon - dlon <= lon <= clon + dlon
    )

CMD_NEARBY = "nearby"
CMD_HELP   = "help"

def infer_cmd_from_text(text: str):
    if not text:
        return None
    t = text.lower().strip()

    # nearby toilets intent (fuzzy)
    if (("nearby" in t and ("toilet" in t or "restroom" in t)) or
        ("toilet" in t and "near" in t)):
        return CMD_NEARBY

    if t in ["help", "usage", "instructions"]:
        return CMD_HELP

    return None

# ------ 統一設定（可用環境變數覆寫；若你已在別處定義，請以這裡為準）------

TW_TZ = timezone(timedelta(hours=8))
LOC_MAX_CONCURRENCY = int(os.getenv("LOC_MAX_CONCURRENCY", "3"))      # 同時最多幾個使用者在跑附近查詢
LOC_QUERY_TIMEOUT_SEC = float(os.getenv("LOC_QUERY_TIMEOUT_SEC", "3.0"))  # 各資料源逾時（秒）
LOC_MAX_RESULTS = int(os.getenv("LOC_MAX_RESULTS", "4"))             # 最多回幾個

SHOW_SEARCHING_BUBBLE = False
_LOC_SEM = threading.Semaphore(LOC_MAX_CONCURRENCY)
ENRICH_MAX_ITEMS    = int(os.getenv("ENRICH_MAX_ITEMS", "60"))
OVERPASS_MAX_ITEMS  = int(os.getenv("OVERPASS_MAX_ITEMS", "60"))
ENRICH_LRU_SIZE     = int(os.getenv("ENRICH_LRU_SIZE", "300"))
NEARBY_LRU_SIZE     = int(os.getenv("NEARBY_LRU_SIZE", "300"))

FEEDBACK_INDEX_TTL  = int(os.getenv("FEEDBACK_INDEX_TTL", "180"))  # 由 60 → 180
STATUS_INDEX_TTL    = int(os.getenv("STATUS_INDEX_TTL", "180"))    # 由 60 → 180
FEEDBACK_LOOKBACK_LIMIT = int(os.getenv("FEEDBACK_LOOKBACK_LIMIT", "4000"))

# === internal TTL aliases (single source of truth) ===
_FEEDBACK_INDEX_TTL = int(os.getenv("FEEDBACK_INDEX_TTL_SEC", str(FEEDBACK_INDEX_TTL)))
_STATUS_INDEX_TTL   = int(os.getenv("STATUS_INDEX_TTL_SEC",   str(STATUS_INDEX_TTL)))

# ------ 將原本的 dict 換成 LRU（⚠️ 別在檔案其他地方再賦值覆蓋它們）------
_ENRICH_CACHE = SimpleLRU(maxsize=ENRICH_LRU_SIZE)
_CACHE        = SimpleLRU(maxsize=NEARBY_LRU_SIZE)

# （可選）啟動時印出快取型別，方便檢查沒有被覆蓋回 dict
try:
    logging.info(f"🔍 ENRICH_CACHE={_ENRICH_CACHE.__class__.__name__} NEARBY_CACHE={_CACHE.__class__.__name__}")
except Exception:
    pass

# 使用者語言（記憶體版，之後可換 DB）
user_lang = {}

def set_user_lang(uid: str, lang: str):
    try:
        if not uid:
            return
        lang = "en" if (lang or "").lower() == "en" else "zh"
        conn = _get_db()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO user_lang (user_id, lang)
            VALUES (?, ?)
            ON CONFLICT(user_id) DO UPDATE SET lang=excluded.lang
        """, (uid, lang))
        conn.commit()
        conn.close()
    except Exception as e:
        logging.warning(f"set_user_lang failed: {e}")

def mask_user_id(uid):
    if not uid:
        return None
    return hashlib.sha256(str(uid).encode()).hexdigest()[:10]

def get_user_lang(uid: str) -> str:
    try:
        if not uid:
            return "zh"
        conn = _get_db()
        cur = conn.cursor()
        cur.execute("SELECT lang FROM user_lang WHERE user_id=?", (uid,))
        row = cur.fetchone()
        conn.close()
        if row and row[0] == "en":
            return "en"
        return "zh"
    except Exception as e:
        logging.warning(f"get_user_lang failed: {e}")
        return "zh"


TEXTS = {
    "nearby_toilet": {
        "zh": "附近廁所",
        "en": "Nearby toilets"
    },
    "ask_location": {
        "zh": "請傳送你的位置",
        "en": "Please share your location"
    },
    "no_result": {
        "zh": "附近沒有找到廁所",
        "en": "No toilets found nearby"
    },
    "loading": {
        "zh": "查詢中，請稍候…",
        "en": "Searching, please wait…"
    },
    "added_favorite": {
        "zh": "已加入最愛 ⭐",
        "en": "Added to favorites ⭐"
    },
    "removed_favorite": {
        "zh": "已移除最愛",
        "en": "Removed from favorites"
    },
}

TEXTS.update({
    "ask_location_normal": {
        "zh": "📍 請點『傳送我的位置』，我立刻幫你找廁所",
        "en": "📍 Please share your location and I’ll find nearby toilets for you"
    },
    "ask_location_ai": {
        "zh": "📍 請點『傳送我的位置』，我會用 AI 幫你挑附近的廁所",
        "en": "📍 Please share your location and I’ll use AI to recommend nearby toilets"
    },
    "added_fav_ok": {
        "zh": "✅ 已收藏 {name}",
        "en": "✅ Added {name} to favorites"
    },
    "removed_fav_ok": {
        "zh": "✅ 已移除最愛",
        "en": "✅ Removed from favorites"
    },
    "removed_fav_fail": {
        "zh": "❌ 移除失敗",
        "en": "❌ Failed to remove"
    },
    "confirm_delete": {
        "zh": "⚠️ 確定要刪除 {name} 嗎？（目前刪除為移除最愛）",
        "en": "⚠️ Are you sure you want to remove {name} from favorites?"
    },
    "confirm_hint": {
        "zh": "請輸入『確認刪除』或『取消』",
        "en": "Please type “Confirm delete” or “Cancel”"
    }

    ,
    "busy_try_later": {
        "zh": "系統忙線中，請稍後再試 🙏",
        "en": "System is busy. Please try again later 🙏"
    },
    "lang_switch_fail": {
        "zh": "❌ 切換語言失敗，請稍後再試",
        "en": "❌ Failed to switch language. Please try again later."
    },
    # Used by ensure_consent_or_prompt() — must include {url} placeholder.
    # Previously missing after Google Sheets removal, causing the bot to
    # send the literal string "consent_required" instead of real text.
    "consent_required": {
        "zh": "📋 使用「智慧廁所助手」前，請先閱讀並同意個資使用條款：\n{url}",
        "en": "📋 Before using the Smart Toilet Assistant, please read and agree to our privacy policy:\n{url}"
    }
})

# === 外部語言包（lang/zh.json, lang/en.json）===
LANG_DIR = os.path.join(os.path.dirname(__file__), "lang")

def _load_lang_pack(lang_code: str):
    try:
        path = os.path.join(LANG_DIR, f"{lang_code}.json")
        if not os.path.exists(path):
            return {"texts": {}, "literals": {}}
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return {"texts": {}, "literals": {}}
        return {
            "texts": data.get("texts", {}) or {},
            "literals": data.get("literals", {}) or {}
        }
    except Exception as e:
        logging.warning(f"load lang pack failed ({lang_code}): {e}")
        return {"texts": {}, "literals": {}}

_LANG_PACKS = {
    "zh": _load_lang_pack("zh"),
    "en": _load_lang_pack("en"),
}

def _lang_text(key: str, lang: str):
    pack = _LANG_PACKS.get(lang, {})
    texts = pack.get("texts", {}) if isinstance(pack, dict) else {}
    if key in texts:
        return texts.get(key)
    return None

def _translate_literal_runtime(text: str, lang: str):
    if not isinstance(text, str) or not text:
        return text
    pack = _LANG_PACKS.get(lang, {})
    literals = pack.get("literals", {}) if isinstance(pack, dict) else {}
    if not literals:
        return text

    # 先 exact match，再做長字串優先的子字串替換
    if text in literals:
        return literals[text]

    out = text
    try:
        for src, dst in sorted(literals.items(), key=lambda kv: len(kv[0]), reverse=True):
            if src and src in out:
                out = out.replace(src, dst)
    except Exception:
        return text
    return out

def _localize_line_message_object(obj, lang: str):
    """
    針對 LINE message object 做遞迴在地化。
    - 會翻譯 TextSendMessage / FlexSendMessage / QuickReply label 等顯示文字
    - 不翻譯 postback data / URI / MessageAction.text，避免功能被翻壞
    """
    if obj is None:
        return obj

    def walk(node):
        if node is None:
            return
        if isinstance(node, list):
            for item in node:
                walk(item)
            return
        if isinstance(node, tuple):
            for item in node:
                walk(item)
            return
        if isinstance(node, dict):
            for k, v in list(node.items()):
                if isinstance(v, str):
                    # 避免翻掉功能欄位
                    if k in ("data", "uri"):
                        continue
                    node[k] = _translate_literal_runtime(v, lang)
                else:
                    walk(v)
            return

        if hasattr(node, "__dict__"):
            cls_name = node.__class__.__name__
            for attr, value in vars(node).items():
                if attr.startswith("_"):
                    continue

                if isinstance(value, str):
                    # 避免翻壞功能用文字
                    if attr in ("data", "uri"):
                        continue
                    if cls_name == "MessageAction" and attr == "text":
                        continue
                    # 顯示文字可翻
                    if attr in ("text", "alt_text", "label", "title", "placeholder", "display_text"):
                        try:
                            setattr(node, attr, _translate_literal_runtime(value, lang))
                        except Exception:
                            pass
                else:
                    walk(value)

    walk(obj)
    return obj

def _localize_outgoing_messages(messages, uid=None, lang=None):
    target_lang = resolve_lang(uid=uid, lang=lang)
    if target_lang == "zh":
        return messages

    if messages is None:
        return messages
    if not isinstance(messages, list):
        messages = [messages]

    out = []
    for msg in messages:
        try:
            out.append(_localize_line_message_object(msg, target_lang))
        except Exception:
            out.append(msg)
    return out


# =========================
# ✅ 統一語言/翻譯入口（唯一入口）
# - LINE：用 uid 決定語言（get_user_lang）
# - API：用 ?lang=en 決定語言（request.args）
# - 舊函式 t/L/_api_L/_api_T 仍保留，但全部改走這裡
# =========================

def _api_lang():
    # API 沒有 LINE uid 時，用 querystring 控制語言：?lang=en
    lang = (request.args.get("lang") or "").strip().lower()
    return "en" if lang == "en" else "zh"

def resolve_lang(uid=None, lang=None):
    # 1) 明確指定 lang（最優先）
    if (lang or "").lower() == "en":
        return "en"
    if (lang or "").lower() == "zh":
        return "zh"

    # 2) 有 uid → 走使用者語言
    if uid:
        try:
            return "en" if get_user_lang(uid) == "en" else "zh"
        except Exception:
            return "zh"

    # 3) 無 uid → 視為 API → 走 querystring
    return _api_lang()

def T(key_or_zh, uid=None, en=None, lang=None, **fmt):
    """
    ✅ 統一翻譯函式（全案唯一入口）
    用法：
    1) key 模式（推薦）：T("no_result", uid=uid)  → 從外部語言包 / TEXTS 抓 zh/en
    2) zh/en 模式（相容舊碼）：T("附近沒有廁所", uid=uid, en="No toilets nearby")
    3) API 模式：T("missing_params", lang=_api_lang())
    4) 支援 format：T("added_fav_ok", uid=uid, name="xxx")
    """
    l = resolve_lang(uid=uid, lang=lang)

    # key 模式：先查外部語言包，再 fallback 到內建 TEXTS
    if en is None and isinstance(key_or_zh, str):
        from_pack = _lang_text(key_or_zh, l)
        if from_pack is not None:
            s = from_pack
        elif key_or_zh in TEXTS:
            s = TEXTS[key_or_zh].get(l, TEXTS[key_or_zh].get("zh", "")) or ""
        else:
            s = key_or_zh or ""
    else:
        # zh/en 模式（相容）
        s = (en if l == "en" else key_or_zh) if en is not None else (key_or_zh or "")

    # 最後做一次 literal runtime 替換，補齊未完全 key 化的字串
    s = _translate_literal_runtime(s, l)

    try:
        return s.format(**fmt)
    except Exception:
        return s

def t(key, uid):

    return T(key, uid=uid)

def L(uid, zh_or_key, en=None):
    # 舊 L(uid, "key") 或 L(uid, "中文", "English") 都能用
    return T(zh_or_key, uid=uid, en=en)

def _api_L(zh, en):
    # 舊 API 翻譯（相容）
    return T(zh, lang=_api_lang(), en=en)

# ✅ 把 API_TEXTS 併入 TEXTS（避免再多一套字典）
API_TEXTS = {
    "missing_params": ("缺少參數", "Missing parameters"),
    "invalid_params": ("參數錯誤", "Invalid parameters"),
    "not_found": ("找不到資料", "Data not found"),
    "write_failed": ("寫入失敗", "Write failed"),
    "server_error": ("伺服器錯誤", "Server error"),
}
for k, (zh, en) in API_TEXTS.items():
    if k not in TEXTS:
        TEXTS[k] = {"zh": zh, "en": en}

def _api_T(key: str):
    # 舊 _api_T（相容）
    return T(key, lang=_api_lang())


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

_start_consent_worker()

def make_location_quick_reply(prompt_text, mode="normal", uid=None):
    """
    prompt_text: 主訊息文字（建議呼叫前就用 L(uid, zh, en) 產好）
    mode: "normal" or "ai"
    uid: LINE user id（用來判斷語言）
    """

    # 防呆：如果沒傳 uid，就用中文
    def _L(zh, en):
        return L(uid, zh, en) if uid else zh

    items = [
        QuickReplyButton(
            action=LocationAction(
                label=_L("傳送我的位置", "Share location")
            )
        )
    ]

    if mode == "normal":
        # 👉 切換到 AI 模式（走 postback，不再送文字）
        items.append(
            QuickReplyButton(
                action=PostbackAction(
                    label=_L("AI 推薦附近廁所", "AI nearby"),
                    data="ask_ai_location",
                    display_text=_L("切換成 AI 推薦模式", "Switch to AI mode")
                )
            )
        )
    else:  # mode == "ai"
        # 👉 切回一般模式
        items.append(
            QuickReplyButton(
                action=PostbackAction(
                    label=_L("切換回一般模式", "Normal mode"),
                    data="ask_location",
                    display_text=_L("切換回一般模式", "Switch to normal mode")
                )
            )
        )

    return TextSendMessage(
        text=prompt_text,
        quick_reply=QuickReply(items=items)
    )

def make_retry_location_text(uid=None):
    return TextSendMessage(
        text=L(uid,
               "現在查詢人數有點多，我排一下隊；你可再傳一次位置或稍候幾秒～",
               "Too many requests now. Please send your location again or try in a few seconds."),
        quick_reply=QuickReply(items=[
            QuickReplyButton(action=LocationAction(label=L(uid, "傳送我的位置", "Share location")))
        ])
    )

def make_no_toilet_quick_reply(uid, lat=None, lon=None):
    return TextSendMessage(
        text=L(uid, "附近沒有廁所 😥 要不要補上一間？",
                  "No toilets nearby 😥 Want to add one?"),
        quick_reply=QuickReply(items=[
            QuickReplyButton(action=LocationAction(label=L(uid, "傳送我的位置", "Share location"))),
            QuickReplyButton(action=MessageAction(label=L(uid, "新增廁所", "Add toilet"),
                                                  text=L(uid, "新增廁所", "Add toilet")))
        ])
    )

# === 初始化 ===
logging.basicConfig(level=logging.INFO)
app = Flask(__name__)
CORS(app)

class _NoHealthzFilter(logging.Filter):
    def filter(self, record):
        try:
            msg = record.getMessage()
        except Exception:
            return True
        return "/healthz" not in msg

# === 安全標頭與快取策略（新增） ===
@app.after_request
def add_security_headers(resp):
    """安全標頭與快取策略
    - 一般頁面：禁止被 iframe（XFO=DENY + frame-ancestors 'none'）
    - LIFF/同意/回饋等頁面：需要在 LINE/LIFF WebView 裡開啟，必須放寬 frame-ancestors 與 script/connect 白名單
    """
    try:
        resp.headers.setdefault("Cache-Control", "no-store")
        resp.headers.setdefault("Pragma", "no-cache")
        resp.headers.setdefault("X-Content-Type-Options", "nosniff")
        resp.headers.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")

        path = (request.path or "").lower()

        # 需要在 LIFF WebView / LINE 內嵌開啟的頁面（請依你的實際路由再增減）
        is_liff_page = (
            path.startswith("/status_liff")
            or path.startswith("/toilet_feedback_by_coord")
            or path.startswith("/feedback_form")
            or path.startswith("/add")
            or path.startswith("/consent")
        )

        if is_liff_page:
            # ✅ LIFF 需要允許被 LINE/LIFF 內嵌
            # X-Frame-Options 建議不要用 DENY（會擋 iframe / webview），改成 SAMEORIGIN（或乾脆不設）
            resp.headers["X-Frame-Options"] = "SAMEORIGIN"

            # ✅ CSP：允許 LIFF SDK、Chart.js、以及 LIFF 可能用到的 API/連線
            csp = [
                "default-src 'self'",
                "img-src 'self' data: https:",
                "script-src 'self' 'unsafe-inline' 'unsafe-eval' https://static.line-scdn.net https://cdn.jsdelivr.net https://cdnjs.cloudflare.com https://unpkg.com",
                "style-src 'self' 'unsafe-inline'",
                "connect-src 'self' https: https://api.line.me https://access.line.me",
                "font-src 'self' data: https:",
                # 允許 LINE/LIFF 內嵌（如需也可加上特定 domain）
                "frame-ancestors 'self' https://access.line.me https://liff.line.me",
            ]
            resp.headers["Content-Security-Policy"] = "; ".join(csp) + ";"
        else:
            # ✅ 非 LIFF 頁面：更嚴格
            resp.headers.setdefault("X-Frame-Options", "DENY")
            csp = [
                "default-src 'self'",
                "img-src 'self' data: https:",
                "script-src 'self' 'unsafe-inline' https://cdn.jsdelivr.net https://cdnjs.cloudflare.com https://unpkg.com",
                "style-src 'self' 'unsafe-inline'",
                "connect-src 'self' https:",
                "font-src 'self' data: https:",
                "frame-ancestors 'none'",
            ]
            resp.headers["Content-Security-Policy"] = "; ".join(csp) + ";"
    except Exception as e:
        logging.debug(f"add_security_headers skipped: {e}")
    return resp

# === 就緒檢查端點（新增） ===
@app.route("/readyz", methods=["GET", "HEAD"])
def readyz():
    """Readiness check: Neon/Postgres is the primary store now."""
    ok = POSTGRES_ENABLED
    status = 200 if ok else 503
    msg = "ready" if ok else "not-ready: postgres disabled"
    headers = {"Content-Type": "text/plain; charset=utf-8", "Cache-Control": "no-store", "X-Robots-Tag": "noindex"}
    if request.method == "HEAD":
        return Response(status=204 if ok else 503, headers=headers)
    return Response(msg, status=status, headers=headers)

logging.getLogger("werkzeug").addFilter(_NoHealthzFilter())

# === 健康檢查端點 ===
@app.route("/healthz", methods=["GET", "HEAD"])
def healthz():
    headers = {
        "Content-Type": "text/plain; charset=utf-8",
        "Cache-Control": "no-store",
        "X-Robots-Tag": "noindex",
    }
    if request.method == "HEAD":
        return Response(status=204, headers=headers)
    return Response("ok", status=200, headers=headers)

@app.route("/go_to_toilet")
def go_to_toilet():
    query_id = request.args.get("qid", "")
    uid = request.args.get("uid", "")
    toilet_id = request.args.get("tid", "")
    lat = request.args.get("lat", "")
    lon = request.args.get("lon", "")
    name = request.args.get("name", "")

    try:
        log_user_action(
            query_id=query_id,
            uid=uid,
            toilet_id=toilet_id,
            action_type="click_navigation",
            extra_info=json.dumps({
                "lat": lat,
                "lon": lon,
                "name": name
            }, ensure_ascii=False)
        )
    except Exception as e:
        logging.warning(f"go_to_toilet log failed: {e}")

    return redirect(f"https://www.google.com/maps/search/?api=1&query={lat},{lon}")

# === 自我激活設定 ===
KEEPALIVE_URL = (
    os.getenv("KEEPALIVE_URL")
    or (os.getenv("PUBLIC_URL") and os.getenv("PUBLIC_URL").rstrip("/") + "/healthz")
    or (os.getenv("RENDER_EXTERNAL_URL") and os.getenv("RENDER_EXTERNAL_URL").rstrip("/") + "/healthz")
)
KEEPALIVE_ENABLE = os.getenv("KEEPALIVE_ENABLE", "1") == "1"
KEEPALIVE_INTERVAL_SECONDS = int(os.getenv("KEEPALIVE_INTERVAL_SECONDS", "600"))
KEEPALIVE_JITTER_SECONDS   = int(os.getenv("KEEPALIVE_JITTER_SECONDS", "60"))

def _self_keepalive_background():
    if not KEEPALIVE_ENABLE or not KEEPALIVE_URL:
        logging.info("⏭️ keepalive disabled (no URL or disabled by env).")
        return
    headers = {"User-Agent": f"SelfKeepalive/1.0 (+{os.getenv('CONTACT_EMAIL','you@example.com')})"}
    while True:
        try:
            requests.head(KEEPALIVE_URL, timeout=8, headers=headers)
            logging.debug("✅ keepalive ok")
        except Exception as e:
            logging.debug(f"⚠️ keepalive failed: {e}")
        sleep_for = KEEPALIVE_INTERVAL_SECONDS + random.randint(0, KEEPALIVE_JITTER_SECONDS)
        time.sleep(sleep_for)

line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

# === 共用 base url（避免硬寫 domain）===
def _base_url():
    # PUBLIC_URL 優先，沒設定就用 request.url_root
    try:
        if PUBLIC_URL:
            return PUBLIC_URL.rstrip("/")
        return request.url_root.rstrip("/")
    except Exception:
        # 保底：至少不要噴錯
        return (PUBLIC_URL or "").rstrip("/")


def _append_uid_lang(url: str, uid: str, lang: str = None, extra: dict = None) -> str:
    """把 uid/lang 安全地加到 URL querystring（避免 LIFF 頁面拿不到語言）"""
    try:
        if not uid and not lang and not extra:
            return url
        parsed = urllib.parse.urlparse(url)
        qs = dict(urllib.parse.parse_qsl(parsed.query, keep_blank_values=True))
        if uid:
            qs.setdefault("uid", uid)
        if lang:
            qs.setdefault("lang", "en" if (lang or '').lower().startswith('en') else "zh")
        if extra:
            for k, v in extra.items():
                if v is None:
                    continue
                qs.setdefault(str(k), str(v))
        new_q = urllib.parse.urlencode(qs)
        return urllib.parse.urlunparse(parsed._replace(query=new_q))
    except Exception:
        return url

def _user_lang_q(uid: str) -> str:
    try:
        return "en" if get_user_lang(uid) == "en" else "zh"
    except Exception:
        return "zh"

def get_nearby_toilets(uid, lat, lon):
    key = f"{lat},{lon}"
    cached = _CACHE.get(key)
    if cached is not None:
        return cached
    toilets = _merge_and_dedupe_lists(query_public_csv_toilets(lat, lon), query_saved_toilets(lat, lon))
    _CACHE.set(key, toilets)
    return toilets

# === 檔案 ===
DATA_DIR = os.path.join(os.getcwd(), "data")
TOILETS_FILE_PATH = os.path.join(DATA_DIR, "public_toilets.csv")
FAVORITES_FILE_PATH = os.path.join(DATA_DIR, "favorites.txt")
_FAV_LOCK = threading.Lock()

# public_toilets.csv is in the hot path for every location query.
# Cache it in memory and reload only when the file mtime changes.
_PUBLIC_CSV_CACHE = {"mtime": None, "rows": []}
_PUBLIC_CSV_CACHE_LOCK = threading.Lock()

os.makedirs(DATA_DIR, exist_ok=True)

if not os.path.exists(FAVORITES_FILE_PATH):
    open(FAVORITES_FILE_PATH, "a", encoding="utf-8").close()

# === Persistent DB (Postgres) ===
DATABASE_URL = (os.getenv("DATABASE_URL") or "").strip()
POSTGRES_ENABLED = bool(DATABASE_URL and psycopg2 is not None)

def _pg_connect():
    if not POSTGRES_ENABLED:
        raise RuntimeError("Postgres not enabled")
    conn = psycopg2.connect(DATABASE_URL, sslmode="require")
    conn.autocommit = False
    return conn

def _persistent_store_ready() -> bool:
    return POSTGRES_ENABLED

def init_persistent_store():
    if not POSTGRES_ENABLED:
        if DATABASE_URL and psycopg2 is None:
            logging.warning("DATABASE_URL 已設定，但缺少 psycopg2；請安裝 psycopg2-binary")
        return

    try:
        conn = _pg_connect()
        cur = conn.cursor()

        # === Dashboard / analytics events ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS analytics_events (
            id BIGSERIAL PRIMARY KEY,
            user_id TEXT,
            event_type TEXT,
            result_count INTEGER DEFAULT 0,
            success INTEGER DEFAULT 1,
            response_time_ms INTEGER,
            lat DOUBLE PRECISION,
            lon DOUBLE PRECISION,
            area_name TEXT,
            query_text TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_created_at ON analytics_events(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_user_id ON analytics_events(user_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_event_type ON analytics_events(event_type)")

        # === User-added toilets ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS user_toilets (
            id BIGSERIAL PRIMARY KEY,
            user_id TEXT,
            name TEXT NOT NULL,
            address TEXT,
            lat DOUBLE PRECISION NOT NULL,
            lon DOUBLE PRECISION NOT NULL,
            level TEXT,
            floor_hint TEXT,
            entrance_hint TEXT,
            access_note TEXT,
            open_hours TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            updated_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)

        # 補齊已存在資料表的欄位（Neon 主儲存）
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS source TEXT DEFAULT 'neon'")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS verification_status TEXT DEFAULT 'pending'")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS verification_score INTEGER DEFAULT 0")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS verification_reason TEXT")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS verified_at TIMESTAMPTZ")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS verified_by TEXT")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS reject_reason TEXT")
        # === Auto Verification 1.0：使用者新增資料自動驗證 ===
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS auto_verification_score INTEGER DEFAULT 0")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS auto_verification_result TEXT DEFAULT 'pending'")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS auto_verification_reason TEXT")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS risk_flags TEXT")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS similar_toilets_json TEXT")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_toilets_auto_result ON user_toilets(auto_verification_result)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_toilets_lat_lon ON user_toilets(lat, lon)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_toilets_created_at ON user_toilets(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_toilets_verification ON user_toilets(verification_status)")

        # === Maintenance Action 1.1：人工審核紀錄 / audit log ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS user_toilet_review_logs (
            id BIGSERIAL PRIMARY KEY,
            toilet_id BIGINT,
            toilet_name TEXT,
            old_status TEXT,
            new_status TEXT,
            old_score INTEGER,
            new_score INTEGER,
            auto_verification_score INTEGER,
            reviewer TEXT,
            action_reason TEXT,
            reject_reason TEXT,
            risk_flags TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_review_logs_toilet_id ON user_toilet_review_logs(toilet_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_review_logs_created_at ON user_toilet_review_logs(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_review_logs_new_status ON user_toilet_review_logs(new_status)")

        # === User consent ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS user_consent (
            user_id TEXT PRIMARY KEY,
            agreed BOOLEAN NOT NULL DEFAULT FALSE,
            display_name TEXT,
            source_type TEXT,
            user_agent TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            updated_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)

        # === Toilet status reports ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS toilet_status_reports (
            id BIGSERIAL PRIMARY KEY,
            user_id TEXT,
            display_name TEXT,
            lat DOUBLE PRECISION,
            lon DOUBLE PRECISION,
            status TEXT,
            note TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_status_reports_lat_lon ON toilet_status_reports(lat, lon)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_status_reports_created_at ON toilet_status_reports(created_at)")

        # === Toilet feedbacks ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS toilet_feedbacks (
            id BIGSERIAL PRIMARY KEY,
            name TEXT,
            address TEXT,
            rating INTEGER,
            toilet_paper TEXT,
            accessibility TEXT,
            time_of_use TEXT,
            comment TEXT,
            cleanliness_score DOUBLE PRECISION,
            lat DOUBLE PRECISION NOT NULL,
            lon DOUBLE PRECISION NOT NULL,
            floor_hint TEXT,
            user_id_hash TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_toilet_feedbacks_lat_lon ON toilet_feedbacks(lat, lon)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_toilet_feedbacks_created_at ON toilet_feedbacks(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_toilet_feedbacks_name ON toilet_feedbacks(name)")

        # === Favorites ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS favorites (
            id BIGSERIAL PRIMARY KEY,
            user_id TEXT NOT NULL,
            name TEXT NOT NULL,
            lat DOUBLE PRECISION NOT NULL,
            lon DOUBLE PRECISION NOT NULL,
            address TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            UNIQUE(user_id, name, lat, lon)
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_favorites_user_id ON favorites(user_id)")

        # === NTS 2.0：推薦結果紀錄 ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS recommendation_logs (
            id BIGSERIAL PRIMARY KEY,
            query_id TEXT NOT NULL,
            user_id_hash TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            user_lat DOUBLE PRECISION,
            user_lon DOUBLE PRECISION,
            rank INTEGER,
            toilet_id TEXT,
            toilet_name TEXT,
            distance_m DOUBLE PRECISION,
            distance_score DOUBLE PRECISION,
            trust_score DOUBLE PRECISION,
            info_score DOUBLE PRECISION,
            status_score DOUBLE PRECISION,
            nts_score DOUBLE PRECISION,
            source TEXT,
            verification_status TEXT
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_recommendation_logs_query_id ON recommendation_logs(query_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_recommendation_logs_user_id_hash ON recommendation_logs(user_id_hash)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_recommendation_logs_created_at ON recommendation_logs(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_recommendation_logs_toilet_id ON recommendation_logs(toilet_id)")
        cur.execute("ALTER TABLE recommendation_logs ADD COLUMN IF NOT EXISTS model_version TEXT DEFAULT 'nts_1_0'")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_recommendation_logs_model_version ON recommendation_logs(model_version)")

        # === NTS 2.0：使用者後續行為紀錄 ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS user_actions (
            id BIGSERIAL PRIMARY KEY,
            query_id TEXT,
            user_id_hash TEXT,
            toilet_id TEXT,
            action_type TEXT NOT NULL,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            extra_info TEXT
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_actions_query_id ON user_actions(query_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_actions_user_id_hash ON user_actions(user_id_hash)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_actions_created_at ON user_actions(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_actions_action_type ON user_actions(action_type)")

        # === NTS 2.0 Shadow Ranking：使用者看 2.0，後台同步記錄 1.0 排序 ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS recommendation_shadow_logs (
            id BIGSERIAL PRIMARY KEY,
            query_id TEXT NOT NULL,
            user_id_hash TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            user_lat DOUBLE PRECISION,
            user_lon DOUBLE PRECISION,
            production_model_version TEXT,
            shadow_model_version TEXT,
            rank INTEGER,
            toilet_id TEXT,
            toilet_name TEXT,
            distance_m DOUBLE PRECISION,
            distance_score DOUBLE PRECISION,
            trust_score DOUBLE PRECISION,
            info_score DOUBLE PRECISION,
            status_score DOUBLE PRECISION,
            nts_score DOUBLE PRECISION,
            source TEXT,
            verification_status TEXT
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_shadow_logs_query_id ON recommendation_shadow_logs(query_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_shadow_logs_toilet_id ON recommendation_shadow_logs(toilet_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_shadow_logs_created_at ON recommendation_shadow_logs(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_shadow_logs_models ON recommendation_shadow_logs(production_model_version, shadow_model_version)")

        # === NTS 2.0：資料來源查詢耗時與 OSM fallback 紀錄 ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS source_query_logs (
            id BIGSERIAL PRIMARY KEY,
            query_id TEXT,
            user_id_hash TEXT,
            model_version TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            source_name TEXT NOT NULL,
            used_osm BOOLEAN DEFAULT FALSE,
            result_count INTEGER DEFAULT 0,
            elapsed_ms INTEGER,
            success BOOLEAN DEFAULT TRUE,
            reason TEXT,
            error_message TEXT
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_source_query_logs_query_id ON source_query_logs(query_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_source_query_logs_model_version ON source_query_logs(model_version)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_source_query_logs_source_name ON source_query_logs(source_name)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_source_query_logs_created_at ON source_query_logs(created_at)")

        conn.commit()
        conn.close()
        logging.info("✅ Postgres persistent store ready")

    except Exception as e:
        logging.error(f"❌ init_persistent_store failed: {e}")

# === 同意書設定 ===
_PUBLIC_URL_FOR_CONSENT = (os.getenv("PUBLIC_URL") or "").rstrip("/")
CONSENT_PAGE_URL = os.getenv("CONSENT_PAGE_URL") or (f"{_PUBLIC_URL_FOR_CONSENT}/consent" if _PUBLIC_URL_FOR_CONSENT else "")

# 近點/快取/有效期
_STATUS_NEAR_M = 35
_STATUS_TTL_HOURS = 6
_status_index_cache = {"ts": 0, "data": {}}
# _STATUS_INDEX_TTL is defined in global config section (see above)

# === 載入模型 ===
BASE_DIR = os.path.abspath(os.path.dirname(__file__))

def load_cleanliness_model():
    try:
        model_path = os.path.join(BASE_DIR, 'models', 'clean_model.pkl')
        model = joblib.load(model_path)
        logging.info("✅ 清潔度模型已載入")
        return model
    except Exception as e:
        logging.error(f"❌ 清潔度模型載入失敗: {e}")
        return None

def load_label_encoder():
    try:
        encoder_path = os.path.join(BASE_DIR, 'models', 'label_encoder.pkl')
        encoder = joblib.load(encoder_path)
        logging.info("✅ LabelEncoder 已載入")
        return encoder
    except Exception as e:
        logging.error(f"❌ LabelEncoder 載入失敗: {e}")
        return None

cleanliness_model = load_cleanliness_model()
label_encoder = load_label_encoder()

# === 參數 ===
LAST_N_HISTORY = 5

# === 工具：座標標準化／解析 ===
def norm_coord(x, ndigits=6):
    try:
        return f"{round(float(x), ndigits):.{ndigits}f}"
    except:
        return str(x)
    
def safe_html(s):
    return html.escape(s or "")

def _parse_lat_lon(lat_s, lon_s):
    try:
        lat = float(str(lat_s).strip())
        lon = float(str(lon_s).strip())
    except Exception:
        return None, None
    if abs(lat) > 90 and abs(lon) <= 90:
        lat, lon = lon, lat
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        return None, None
    return lat, lon

# === LIFF 設定 ===
PUBLIC_URL = (os.getenv("PUBLIC_URL") or "").rstrip("/")
LIFF_STATUS_ID = os.getenv("LIFF_STATUS_ID", "")

def _status_liff_url(lat=None, lon=None, uid=None):
    """回傳狀態回報 LIFF 頁面網址。

    ✅ 重要：LIFF 網頁本身不會自動知道你在 LINE 裡切到哪個語言，所以我們在 URL 上帶：
      - uid：讓後端可以查 get_user_lang(uid)
      - lang：讓前端（或後端 redirect）可以直接用 ?lang=en 切語言
    若沒帶座標，讓 LIFF 自己取定位。
    """
    if not PUBLIC_URL:
        return None

    base = f"{PUBLIC_URL}/status_liff"

    params = {}
    # 讓 LIFF 能知道是誰（也方便後端做預設語言）
    if uid:
        params["uid"] = uid
        try:
            params["lang"] = "en" if get_user_lang(uid) == "en" else "zh"
        except Exception:
            params["lang"] = "zh"

    if lat is not None and lon is not None:
        params["lat"] = norm_coord(lat)
        params["lon"] = norm_coord(lon)

    if not params:
        return base
    return base + "?" + urllib.parse.urlencode(params)


# === 樓層推斷 ===
def _floor_from_tags(tags: dict):
    if not tags:
        return None
    level = tags.get("level") or tags.get("level:ref") or tags.get("addr:floor")
    loc = (tags.get("location") or "").lower()
    try:
        if level is not None and str(level).strip() != "":
            lv_str = str(level).strip().replace("F","").replace("f","")
            lv = int(float(lv_str))
            if lv < 0:
                return f"地下{abs(lv)}F"
            if lv == 0:
                return "地面"
            return f"{lv}F"
    except Exception:
        pass
    if loc == "underground":
        return "地下"
    if loc == "overground":
        return "地面"
    return None

_ZH_DIGIT = {"零":0,"〇":0,"一":1,"二":2,"兩":2,"三":3,"四":4,"五":5,"六":6,"七":7,"八":8,"九":9}

def _zh_to_int_word(word: str):
    if not word:
        return None
    w = word.replace("两","兩")
    if "十" not in w:
        return _ZH_DIGIT.get(w)
    left, _, right = w.partition("十")
    tens = 10 if left == "" else (_ZH_DIGIT.get(left, 0) * 10)
    ones = 0 if right == "" else _ZH_DIGIT.get(right, 0)
    val = tens + ones
    return val if val > 0 else None

def _normalize_floor_label(n: int, underground: bool=False):
    try:
        n = int(n)
    except Exception:
        return None
    if underground:
        return f"地下{abs(n)}F"
    if n == 0:
        return "地面"
    return f"{n}F"

def _floor_from_name(name: str):
    if not name:
        return None
    s = str(name).strip()
    s_lower = s.lower()

    if re.search(r'(?:^|[^a-z])g\s*/?\s*f(?:[^a-z]|$)', s_lower) or re.search(r'ground\s*floor', s_lower):
        return "地面"

    m = re.search(r'(?:^|[^a-z])[bＢ]\s*-?\s*(\d{1,2})\s*(?:f|樓|層)?(?:[^0-9]|$)', s_lower)
    if m:
        n = int(m.group(1))
        if n > 0:
            return _normalize_floor_label(n, underground=True)

    m = re.search(r'地下\s*([一二兩三四五六七八九十〇零\d]{1,3})\s*(?:樓|層|f)?', s_lower)
    if m:
        token = m.group(1)
        n = int(token) if token.isdigit() else _zh_to_int_word(token)
        if n and n > 0:
            return _normalize_floor_label(n, underground=True)

    m = re.search(r'(\d{1,3})\s*(?:f|樓|層)(?:[^a-z0-9]|$)', s_lower)
    if m:
        return _normalize_floor_label(int(m.group(1)))

    m = re.search(r'第?\s*([一二兩三四五六七八九十〇零]{1,3})\s*(?:樓|層)', s_lower)
    if m:
        n = _zh_to_int_word(m.group(1))
        if n:
            return _normalize_floor_label(n)

    m = re.search(r'(?:^|[^a-z])l\s*(\d{1,3})(?:[^0-9]|$)', s_lower)
    if m:
        return _normalize_floor_label(int(m.group(1)))

    return None

# === 依附近場館命名 ===
_ENRICH_TTL = 120

def enrich_nearby_places(lat, lon, radius=500):
    # 🔌 總開關：預設關閉（ENV 可設 ENRICH_ENABLE=1 開啟）
    enabled = globals().get("ENRICH_ENABLE", None)
    if enabled is None:
        try:
            enabled = int(os.getenv("ENRICH_ENABLE", "0"))
        except Exception:
            enabled = 0
    if not enabled:
        return []

    key = f"{round(lat,4)},{round(lon,4)}:{radius}"
    now = time.time()
    cached = _ENRICH_CACHE.get(key)
    if cached and (now - cached[0] < _ENRICH_TTL):
        return cached[1]

    q = f"""
    [out:json][timeout:25];
    (
      node(around:{radius},{lat},{lon})["name"]["building"];
      way(around:{radius},{lat},{lon})["name"]["building"];
      node(around:{radius},{lat},{lon})["name"]["shop"];
      way(around:{radius},{lat},{lon})["name"]["shop"];
      node(around:{radius},{lat},{lon})["name"]["amenity"];
      way(around:{radius},{lat},{lon})["name"]["amenity"];
    );
    out center tags;
    """
    endpoints = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.openstreetmap.ru/api/interpreter",
    ]
    headers = {"User-Agent": f"ToiletBot/1.0 (+{os.getenv('CONTACT_EMAIL','you@example.com')})"}

    for url in endpoints:
        try:
            resp = requests.post(url, data=q, headers=headers, timeout=30)
            if resp.status_code == 200 and "json" in (resp.headers.get("Content-Type","").lower()):
                els = resp.json().get("elements", [])
                out = []
                for e in els:
                    if e.get("type") == "node":
                        clat, clon = e.get("lat"), e.get("lon")
                    else:
                        c = e.get("center") or {}
                        clat, clon = c.get("lat"), c.get("lon")
                    if clat is None or clon is None:
                        continue
                    nm = (e.get("tags", {}) or {}).get("name")
                    if nm:
                        try:
                            d = haversine(float(lat), float(lon), float(clat), float(clon))
                        except Exception:
                            d = 9e9
                        out.append({"name": nm, "lat": float(clat), "lon": float(clon), "_d": d})

                # 距離排序 + 截斷，避免記憶體暴衝
                if out:
                    out.sort(key=lambda x: x["_d"])
                    # 使用全域/ENV 的 ENRICH_MAX_ITEMS（若無則預設 60）
                    max_items = globals().get("ENRICH_MAX_ITEMS", None)
                    if max_items is None:
                        try:
                            max_items = int(os.getenv("ENRICH_MAX_ITEMS", "60"))
                        except Exception:
                            max_items = 60
                    out = out[:max_items]
                    for o in out:
                        o.pop("_d", None)

                _ENRICH_CACHE.set(key, (now, out))
                return out
        except Exception:
            continue

    _ENRICH_CACHE.set(key, (now, []))
    return []

# === 可找性分數 + 排序 ===
def _findability_bonus(t):
    b = 0.0
    if t.get("place_hint"): b += 0.5
    if t.get("floor_hint"): b += 0.3
    return b

def sort_toilets(toilets):
    def _dist_key(x):
        # haversine() now returns float("inf") on error (Batch 3A).
        # int(float("inf")) raises OverflowError in Python, so cap the
        # value at 1e9 before converting.  Any non-numeric value also
        # falls back safely to the maximum sentinel distance.
        try:
            d = float(x.get("distance", 1e9))
            if not math.isfinite(d):
                d = 1e9
            return (int(d), -_findability_bonus(x))
        except (TypeError, ValueError, OverflowError):
            return (int(1e9), 0)
    toilets.sort(key=_dist_key)
    return toilets

def _score_distance(distance_m):
    """
    距離分數：距離越近分數越高。
    0m = 100 分，1000m 以上趨近 0 分。
    """
    try:
        d = float(distance_m or 0)
        return max(0, 100 - d / 10)
    except Exception:
        return 0


def _score_trust(t):
    """
    Trust Score 2.0：資料可信度分數。

    評估重點：
    1. 資料來源
    2. 後台驗證狀態
    3. 後台 verification_score
    4. 資訊完整度輔助
    5. 資料新鮮度
    """
    source = (t.get("source") or t.get("type") or "").lower()
    status = (t.get("verification_status") or "").lower()

    # rejected 直接視為不可信；sort_toilets_nts 也會排除 rejected，這裡再保險一次
    if status == "rejected":
        return 0

    # === 1. 基礎來源分數 ===
    if source in ("public_csv", "government"):
        score = 85
    elif source in ("osm", "overpass"):
        score = 75
    elif source in ("neon", "user_added", "user", "saved"):
        score = 60
    else:
        score = 60

    # === 2. 後台驗證狀態 ===
    if status == "approved":
        score += 20
    elif status == "pending":
        score += 0
    elif status in ("needs_review", "review"):
        score -= 10

    # === 3. 後台 verification_score 輔助 ===
    try:
        v_score = t.get("verification_score")
        if v_score not in (None, ""):
            v_score = float(v_score)
            # verification_score 若是 0~100，轉成最多約 ±10 分影響
            score += (v_score - 50) / 5
    except Exception:
        pass

    # === 4. 資訊完整度輔助 ===
    try:
        completeness_bonus = 0
        if t.get("address"):
            completeness_bonus += 3
        if t.get("floor_hint") or t.get("level"):
            completeness_bonus += 3
        if t.get("entrance_hint"):
            completeness_bonus += 3
        if t.get("open_hours"):
            completeness_bonus += 2
        score += completeness_bonus
    except Exception:
        pass

    # === 5. 資料新鮮度 ===
    try:
        ts = t.get("updated_at") or t.get("created_at")
        if ts:
            if isinstance(ts, str):
                dt = datetime.fromisoformat(ts.replace("Z", "+00:00"))
            else:
                dt = ts

            now = datetime.now(timezone.utc)
            if getattr(dt, "tzinfo", None) is None:
                dt = dt.replace(tzinfo=timezone.utc)

            age_days = (now - dt).days
            if age_days > 730:
                score -= 10
            elif age_days > 365:
                score -= 5
            elif age_days <= 30:
                score += 5
    except Exception:
        pass

    return max(0, min(round(score, 2), 100))

def _score_info(t):
    """
    資訊完整度分數：越容易找到、越完整分數越高。
    """
    score = 0

    if t.get("name"):
        score += 20
    if t.get("address"):
        score += 30
    if t.get("floor_hint") or t.get("level"):
        score += 20
    if t.get("entrance_hint"):
        score += 15
    if t.get("access_note"):
        score += 10
    if t.get("open_hours"):
        score += 5

    return min(score, 100)


def _score_status(t):
    """
    Status Score 2.0：設施目前可用狀態分數。

    評估重點：
    1. 明確停用/故障/維修 → 大幅降分
    2. 明確正常/可使用 → 加分
    3. 沒有狀態 → 中性分數
    4. 使用者文字回報與 note 一併判斷
    """
    texts = []
    for key in ["status", "status_text", "note", "verification_reason", "reject_reason"]:
        val = t.get(key)
        if val:
            texts.append(str(val))

    s = " ".join(texts).strip()
    if not s:
        return 70

    bad_keywords = [
        "暫停", "故障", "維修", "關閉", "不能使用", "無法使用",
        "停用", "封閉", "施工", "撤除", "不存在", "錯誤", "rejected"
    ]
    warning_keywords = [
        "不確定", "待確認", "可能", "髒", "很髒", "沒有衛生紙",
        "位置不清楚", "入口不明", "找不到"
    ]
    good_keywords = [
        "正常", "恢復", "可使用", "開放", "乾淨", "有衛生紙",
        "確認可用", "已確認"
    ]

    if any(k in s for k in bad_keywords):
        return 0
    if any(k in s for k in warning_keywords):
        return 45
    if any(k in s for k in good_keywords):
        return 95
    return 70

def compute_nts_score(t):
    """
    NTS 節點式廁所搜尋演算法總分。
    """
    distance_score = _score_distance(t.get("distance"))
    trust_score = _score_trust(t)
    info_score = _score_info(t)
    status_score = _score_status(t)

    final_score = (
        0.60 * distance_score +
        0.20 * trust_score +
        0.10 * info_score +
        0.10 * status_score
    )

    t["nts_score"] = round(final_score, 2)
    t["distance_score"] = round(distance_score, 2)
    t["trust_score"] = round(trust_score, 2)
    t["info_score"] = round(info_score, 2)
    t["status_score"] = round(status_score, 2)

    return t["nts_score"]


def sort_toilets_nts(toilets):
    """
    使用 NTS 分數排序。
    rejected 資料不顯示，其餘依 NTS 分數由高到低排序。
    """
    clean = []
    for t in toilets:
        status = (t.get("verification_status") or "pending").lower()
        if status == "rejected":
            continue

        compute_nts_score(t)
        clean.append(t)

    clean.sort(key=lambda x: (-x.get("nts_score", 0), x.get("distance", 999999)))
    return clean


def _score_trust_1_0(t):
    """
    NTS 1.0 baseline 的固定可信度分數。
    用於 shadow ranking，不影響實際給使用者看的 Trust Score 2.0。
    """
    source = (t.get("source") or t.get("type") or "").lower()
    status = (t.get("verification_status") or "pending").lower()
    if status == "rejected":
        return 0
    if source in ("public_csv", "government", "osm", "overpass"):
        return 100
    if status == "approved":
        return 90
    if status == "pending":
        return 60
    return 60


def _score_status_1_0(t):
    """NTS 1.0 baseline 的狀態分數。"""
    s = (t.get("status") or t.get("status_text") or "").strip()
    if not s:
        return 70
    bad_keywords = ["暫停", "故障", "維修", "關閉", "不能使用", "無法使用"]
    good_keywords = ["正常", "恢復", "可使用"]
    if any(k in s for k in bad_keywords):
        return 0
    if any(k in s for k in good_keywords):
        return 100
    return 70


def compute_nts_score_1_0(t):
    """
    用 NTS 1.0 baseline 公式計算分數。
    只用於 shadow ranking；會寫入傳入 dict 的分數欄位。
    """
    distance_score = _score_distance(t.get("distance"))
    trust_score = _score_trust_1_0(t)
    info_score = _score_info(t)
    status_score = _score_status_1_0(t)
    final_score = 0.60 * distance_score + 0.20 * trust_score + 0.10 * info_score + 0.10 * status_score
    t["nts_score"] = round(final_score, 2)
    t["distance_score"] = round(distance_score, 2)
    t["trust_score"] = round(trust_score, 2)
    t["info_score"] = round(info_score, 2)
    t["status_score"] = round(status_score, 2)
    return t["nts_score"]


def sort_toilets_nts_1_0(toilets):
    """
    Shadow ranking：同一批已回傳候選資料用 NTS 1.0 baseline 重新排序。
    不重新查 CSV / Neon / OSM，只重算分數與排序。
    """
    clean = []
    for t in toilets or []:
        status = (t.get("verification_status") or "pending").lower()
        if status == "rejected":
            continue
        item = dict(t)
        compute_nts_score_1_0(item)
        clean.append(item)
    clean.sort(key=lambda x: (-x.get("nts_score", 0), x.get("distance", 999999)))
    return clean

def make_query_id():
    return "Q_" + uuid.uuid4().hex[:16]


def _make_toilet_id(t):
    """
    給沒有固定 id 的政府/OSM 資料一個穩定識別碼。
    user_toilets 若本來有 id，就優先用 id。
    """
    raw_id = t.get("id")
    if raw_id not in (None, ""):
        return str(raw_id)

    name = str(t.get("name") or "")
    lat = norm_coord(t.get("lat"))
    lon = norm_coord(t.get("lon"))
    source = str(t.get("source") or t.get("type") or "")
    key = f"{source}|{name}|{lat}|{lon}"
    return hashlib.sha256(key.encode("utf-8")).hexdigest()[:16]


def log_recommendation_results(query_id, uid, user_lat, user_lon, toilets, limit=5):
    """
    記錄這次系統推薦了哪些結果。
    """
    if not POSTGRES_ENABLED:
        return

    try:
        rows = []
        user_id_hash = mask_user_id(uid)
        model_version = os.getenv("NTS_MODEL_VERSION", "nts_1_0").strip() or "nts_1_0"

        for rank, t in enumerate((toilets or [])[:limit], start=1):
            # 確保 NTS 四個節點分數存在
            try:
                if "nts_score" not in t:
                    compute_nts_score(t)
            except Exception:
                pass

            rows.append((
                query_id,
                user_id_hash,
                float(user_lat),
                float(user_lon),
                rank,
                _make_toilet_id(t),
                t.get("name") or "",
                float(t.get("distance", 0) or 0),
                float(t.get("distance_score", 0) or 0),
                float(t.get("trust_score", 0) or 0),
                float(t.get("info_score", 0) or 0),
                float(t.get("status_score", 0) or 0),
                float(t.get("nts_score", 0) or 0),
                t.get("source") or t.get("type") or "",
                t.get("verification_status") or "",
                model_version
            ))

        if not rows:
            return

        conn = _pg_connect()
        cur = conn.cursor()
        cur.executemany("""
            INSERT INTO recommendation_logs (
                query_id, user_id_hash, user_lat, user_lon,
                rank, toilet_id, toilet_name, distance_m,
                distance_score, trust_score, info_score, status_score,
                nts_score, source, verification_status, model_version
            )
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, rows)
        conn.commit()
        conn.close()

    except Exception as e:
        logging.warning(f"log_recommendation_results failed: {e}", exc_info=True)


def log_shadow_recommendation_results(query_id, uid, user_lat, user_lon, toilets, limit=5):
    """
    Shadow mode：實際給使用者看的是 production model（例如 Trust Score 2.0），
    但後台用同一批已取得的回傳候選結果，偷偷以 NTS 1.0 baseline 重新排序並記錄。
    不重新查 CSV / Neon / OSM，只重算分數與排序，因此效率影響很小。
    """
    if not POSTGRES_ENABLED:
        return
    if os.getenv("SHADOW_NTS_ENABLE", "1") != "1":
        return
    production_model_version = os.getenv("NTS_MODEL_VERSION", "nts_1_0").strip() or "nts_1_0"
    shadow_model_version = os.getenv("SHADOW_MODEL_VERSION", "nts_1_0").strip() or "nts_1_0"
    if production_model_version == shadow_model_version:
        return
    try:
        shadow_sorted = sort_toilets_nts_1_0(toilets or [])
        if not shadow_sorted:
            return
        rows = []
        user_id_hash = mask_user_id(uid)
        for rank, t in enumerate(shadow_sorted[:limit], start=1):
            rows.append((
                query_id, user_id_hash, float(user_lat), float(user_lon),
                production_model_version, shadow_model_version, rank,
                _make_toilet_id(t), t.get("name") or "",
                float(t.get("distance", 0) or 0),
                float(t.get("distance_score", 0) or 0),
                float(t.get("trust_score", 0) or 0),
                float(t.get("info_score", 0) or 0),
                float(t.get("status_score", 0) or 0),
                float(t.get("nts_score", 0) or 0),
                t.get("source") or t.get("type") or "",
                t.get("verification_status") or ""
            ))
        conn = _pg_connect()
        cur = conn.cursor()
        cur.executemany("""
            INSERT INTO recommendation_shadow_logs (
                query_id, user_id_hash, user_lat, user_lon,
                production_model_version, shadow_model_version,
                rank, toilet_id, toilet_name, distance_m,
                distance_score, trust_score, info_score, status_score,
                nts_score, source, verification_status
            )
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, rows)
        conn.commit()
        conn.close()
    except Exception as e:
        logging.warning(f"log_shadow_recommendation_results failed: {e}", exc_info=True)


def log_user_action(query_id, uid, toilet_id, action_type, extra_info=""):
    """
    記錄使用者後續行為，例如點導航、回報問題、加入最愛。
    """
    if not POSTGRES_ENABLED:
        return

    try:
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO user_actions (
                query_id, user_id_hash, toilet_id, action_type, extra_info
            )
            VALUES (%s, %s, %s, %s, %s)
        """, (
            query_id or "",
            mask_user_id(uid),
            str(toilet_id or ""),
            action_type,
            extra_info or ""
        ))
        conn.commit()
        conn.close()

    except Exception as e:
        logging.warning(f"log_user_action failed: {e}", exc_info=True)


def log_source_query(query_id, uid, source_name, result_count=0, elapsed_ms=None, success=True, reason="", error_message="", used_osm=False):
    """
    記錄各資料來源查詢耗時與 OSM fallback 使用情形。
    用來比較：不用 OSM / 使用 OSM 的次數與耗時。
    """
    if not POSTGRES_ENABLED:
        return

    try:
        model_version = os.getenv("NTS_MODEL_VERSION", "nts_1_0").strip() or "nts_1_0"
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO source_query_logs (
                query_id, user_id_hash, model_version, source_name,
                used_osm, result_count, elapsed_ms, success, reason, error_message
            )
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, (
            query_id or "",
            mask_user_id(uid),
            model_version,
            source_name,
            bool(used_osm),
            int(result_count or 0),
            int(elapsed_ms) if elapsed_ms is not None else None,
            bool(success),
            reason or "",
            str(error_message or "")[:500]
        ))
        conn.commit()
        conn.close()
    except Exception as e:
        logging.warning(f"log_source_query failed: {e}", exc_info=True)

# === 使用者新增廁所資料欄位 ===
USER_TOILET_ROW_HEADER = [
    "user_id", "name", "address", "lat", "lon",
    "level", "floor_hint", "entrance_hint", "access_note", "open_hours",
    "timestamp"
]

# === 計算距離 ===
def haversine(lat1, lon1, lat2, lon2):
    try:
        lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
        dlat = lat2 - lat1
        dlon = lon2 - lon1
        a = sin(dlat / 2) ** 2 + cos(lat1) * cos(lat2) * sin(dlon / 2) ** 2
        return 2 * asin(sqrt(a)) * 6371000  # m
    except Exception as e:
        logging.error(f"計算距離失敗: {e}")
        return float("inf")

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

LINE_REPLY_MAX = 5

# push fallback 去重（避免重送 / 重試造成重複推播）
_PUSH_DEDUPE = getattr(globals(), "_PUSH_DEDUPE", {})
_PUSH_LOCK = threading.Lock()
PUSH_FALLBACK_DEDUPE_WINDOW = int(os.getenv("PUSH_FALLBACK_DEDUPE_WINDOW", "180"))

def safe_reply(event, messages):
    """
    ✅ 安全回覆（零 push 版本）：
    - 只使用 reply_message 回覆（不做 push fallback），避免額外消耗月額度與避免 429 洗版
    - 若 reply_token 無效/過期/不存在：直接略過（只記錄 log）
    - 保留最多 5 則訊息限制，避免 LINE API 拒絕
    """
    if messages is None:
        return
    if not isinstance(messages, list):
        messages = [messages]
    messages = [m for m in messages if m is not None]
    if not messages:
        return

    # LINE 規則：一次 reply 最多 5 則
    if len(messages) > LINE_REPLY_MAX:
        logging.warning(f"[safe_reply] messages too many ({len(messages)}), truncating to {LINE_REPLY_MAX}.")
        messages = messages[:LINE_REPLY_MAX]

    # 根據使用者語言做最後一層在地化，盡量避免漏網之魚
    uid = getattr(getattr(event, "source", None), "user_id", None)
    messages = _localize_outgoing_messages(messages, uid=uid)

    # 沒有 reply_token（或事件不支援 reply）就不送，避免用 push
    reply_token = getattr(event, "reply_token", None)
    if not reply_token:
        logging.warning("[safe_reply] no reply_token; skip (push disabled).")
        return

    try:
        line_bot_api.reply_message(reply_token, messages)
        return
    except LineBotApiError as e:
        # 解析錯誤訊息
        try:
            msg_txt = getattr(getattr(e, "error", None), "message", "") or str(e)
        except Exception:
            msg_txt = str(e)

        # reply_token 無效/過期：不做 push，直接跳過
        if "Invalid reply token" in msg_txt:
            logging.warning(f"[safe_reply] invalid reply token; skip (push disabled). err={msg_txt}")
            return

        # 月額度/限流/其他：只記錄，不重試、不 fallback
        logging.warning(f"[safe_reply] reply_message failed; skip (push disabled). err={msg_txt}")
        return
    except Exception as ex:
        logging.error(f"[safe_reply] unexpected error: {ex}", exc_info=True)
        return

def _too_old_to_reply(event, limit_seconds=None):
    try:
        if limit_seconds is None:
            limit_seconds = int(os.getenv("MAX_EVENT_AGE_SEC", "1800"))

        evt_ms = int(getattr(event, "timestamp", 0))
        if evt_ms <= 0:
            return False

        now_ms = int(time.time() * 1000)
        return (now_ms - evt_ms) > (limit_seconds * 1000)
    except Exception:
        return False

def reply_only(event, messages):
    try:
        uid = getattr(getattr(event, "source", None), "user_id", None)
        messages = _localize_outgoing_messages(messages, uid=uid)
        line_bot_api.reply_message(event.reply_token, messages)
    except LineBotApiError as e:
        msg_txt = ""
        try:
            msg_txt = getattr(getattr(e, "error", None), "message", "") or str(e)
        except Exception:
            msg_txt = str(e)
        logging.warning(f"reply_message 失敗（不做 push）：{msg_txt}")
    except Exception as ex:
        logging.error(f"reply_only 執行錯誤：{ex}")

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

# === SQLite 本機快取與分析資料 ===
# 設定 SQLite 資料庫位置
CACHE_DB_PATH = os.path.join(os.path.dirname(__file__), "cache.db")

def _get_db():
    """Return a SQLite connection to the app database (CACHE_DB_PATH).

    This is the single entry point for all SQLite access in the app
    (user_lang, search_log, ai_quota, request_cache, analytics_events).
    It was previously provided by a now-deleted initialization block;
    restored here so that set_user_lang / get_user_lang /
    handle_location / _ai_quota_check_and_inc work correctly.
    """
    conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn

# 建立 SQLite 連線
def create_cache_db():
    # Always open (not just when file is missing) so that new tables added
    # here are created on existing deployments that already have cache.db.
    conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
    cursor = conn.cursor()

    # Original request cache table
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS request_cache (
        query_key TEXT PRIMARY KEY,
        data TEXT,
        timestamp REAL
    )
    """)

    # User language preference — read/written by set_user_lang / get_user_lang.
    # Was missing after Google Sheets removal; restored here.
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS user_lang (
        user_id TEXT PRIMARY KEY,
        lang TEXT NOT NULL DEFAULT 'zh'
    )
    """)

    # Per-user location query log — written by handle_location,
    # read by get_search_count for the usage-review / badges pages.
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS search_log (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id TEXT,
        lat TEXT,
        lon TEXT,
        ts TEXT
    )
    """)
    cursor.execute(
        "CREATE INDEX IF NOT EXISTS idx_search_log_user_id ON search_log(user_id)"
    )

    # AI quota tracking — read/written by _ai_quota_check_and_inc.
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS ai_quota (
        key  TEXT NOT NULL,
        date TEXT NOT NULL,
        count INTEGER NOT NULL DEFAULT 0,
        PRIMARY KEY (key, date)
    )
    """)

    conn.commit()
    conn.close()

# === SQLite 參數強化（新增） ===
def tune_sqlite_for_concurrency():
    try:
        conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
        cur = conn.cursor()
        # 啟用 WAL 提高多執行緒讀/寫並行能力
        cur.execute("PRAGMA journal_mode=WAL;")
        # 設定 busy timeout（毫秒），避免短暫鎖衝突直接拋錯
        cur.execute("PRAGMA busy_timeout=3000;")
        conn.commit()
        conn.close()
        logging.info("✅ SQLite tuned: WAL + busy_timeout")
    except Exception as e:
        logging.warning(f"SQLite tuning skipped: {e}")

# 確認快取是否有效
def get_cached_data(query_key, ttl_sec=60*5):
    conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
    cursor = conn.cursor()
    cursor.execute("SELECT data, timestamp FROM request_cache WHERE query_key = ?", (query_key,))
    result = cursor.fetchone()
    conn.close()

    if result:
        data, timestamp = result
        if time.time() - timestamp < ttl_sec:
            return json.loads(data)
    return None

# 儲存快取
def save_cache(query_key, data):
    conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
    cursor = conn.cursor()
    cursor.execute("""
    INSERT OR REPLACE INTO request_cache (query_key, data, timestamp)
    VALUES (?, ?, ?)
    """, (query_key, json.dumps(data), time.time()))
    conn.commit()
    conn.close()

# 快取初始化
create_cache_db()
tune_sqlite_for_concurrency()

# ================= Analytics DB =================
ANALYTICS_DB_PATH = CACHE_DB_PATH

def create_analytics_tables():
    conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
    cur = conn.cursor()

    cur.execute("""
    CREATE TABLE IF NOT EXISTS analytics_events (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id TEXT,
        event_type TEXT,
        result_count INTEGER,
        success INTEGER,
        response_time_ms INTEGER,
        lat REAL,
        lon REAL,
        area_name TEXT,
        query_text TEXT,
        created_at TEXT
    )
    """)

    cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_created_at ON analytics_events(created_at)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_user_id ON analytics_events(user_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_event_type ON analytics_events(event_type)")

    conn.commit()
    conn.close()

create_analytics_tables()
init_persistent_store()

def log_analytics_event(
    user_id=None,
    event_type="query",
    result_count=0,
    success=1,
    response_time_ms=None,
    lat=None,
    lon=None,
    area_name=None,
    query_text=None,
    created_at=None
):
    try:
        rt_ms = int(response_time_ms) if response_time_ms is not None else None
        if event_type == "location_query" and (rt_ms is None or rt_ms <= 0):
            return
        if POSTGRES_ENABLED:
            conn = _pg_connect()
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO analytics_events
                (user_id, event_type, result_count, success, response_time_ms, lat, lon, area_name, query_text, created_at)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            """, (
                user_id,
                event_type,
                int(result_count or 0),
                int(1 if success else 0),
                rt_ms,
                float(lat) if lat is not None else None,
                float(lon) if lon is not None else None,
                area_name,
                query_text,
                created_at or datetime.now(TW_TZ)
            ))
            conn.commit()
            conn.close()
            return

        conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO analytics_events
            (user_id, event_type, result_count, success, response_time_ms, lat, lon, area_name, query_text, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            user_id,
            event_type,
            int(result_count or 0),
            int(1 if success else 0),
            rt_ms,
            float(lat) if lat is not None else None,
            float(lon) if lon is not None else None,
            area_name,
            query_text,
            created_at or datetime.now(TW_TZ).isoformat()
        ))
        conn.commit()
        conn.close()
    except Exception as e:
        logging.warning(f"log_analytics_event failed: {e}")

def get_area_name(lat, lon):
    try:
        lat = float(lat)
        lon = float(lon)
    except Exception:
        return None

    if 25.040 <= lat <= 25.055 and 121.510 <= lon <= 121.525:
        return "台北車站"
    if 25.040 <= lat <= 25.050 and 121.500 <= lon <= 121.510:
        return "西門町"
    if 25.028 <= lat <= 25.040 and 121.530 <= lon <= 121.570:
        return "信義區"
    if 25.010 <= lat <= 25.025 and 121.525 <= lon <= 121.545:
        return "公館"
    if 25.010 <= lat <= 25.020 and 121.455 <= lon <= 121.470:
        return "板橋車站"
    return "其他區域"

# 查詢廁所資料
# === OSM Overpass ===
def query_overpass_toilets(lat, lon, radius=500):
    overall_deadline = time.time() + 8.0

    def _left():
        return max(1.0, overall_deadline - time.time())

    ua_email = os.getenv("CONTACT_EMAIL", "you@example.com")
    headers = {"User-Agent": f"ToiletBot/1.0 (+{ua_email})"}
    endpoints = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.openstreetmap.ru/api/interpreter",
    ]

    # 讀取限制值
    try:
        max_items = int(os.getenv("OVERPASS_MAX_ITEMS", "80"))
    except Exception:
        max_items = 80
    try:
        enrich_on = int(os.getenv("ENRICH_ENABLE", "0")) == 1
    except Exception:
        enrich_on = False

    # 先小半徑再原半徑
    for r in (300, radius):
        if time.time() >= overall_deadline:
            break

        query = f"""
        [out:json][timeout:25];
        (
          node["amenity"="toilets"](around:{r},{lat},{lon});
          way["amenity"="toilets"](around:{r},{lat},{lon});
          relation["amenity"="toilets"](around:{r},{lat},{lon});
        );
        out center tags;
        """

        last_err = None
        for idx, url in enumerate(endpoints):
            if time.time() >= overall_deadline:
                break
            try:
                resp = requests.post(
                    url,
                    data=query,
                    headers=headers,
                    timeout=min(8, _left())
                )
                ctype = (resp.headers.get("Content-Type") or "").lower()
                if resp.status_code != 200 or "json" not in ctype:
                    last_err = RuntimeError(f"overpass non-json {resp.status_code}")
                    continue

                data = resp.json()
                elements = data.get("elements", [])

                toilets = []

                # 最多處理 4 * max_items（避免 elements 太多）
                hard_cap = max(40, max_items * 4)
                processed = 0

                for elem in elements:
                    if processed >= hard_cap:
                        break
                    processed += 1

                    if "center" in elem:
                        t_lat = elem["center"].get("lat")
                        t_lon = elem["center"].get("lon")
                    elif elem.get("type") == "node":
                        t_lat = elem.get("lat")
                        t_lon = elem.get("lon")
                    else:
                        continue

                    if t_lat is None or t_lon is None:
                        continue

                    if not _in_bbox(t_lat, t_lon, lat, lon, r):
                        continue

                    tags = elem.get("tags", {}) or {}
                    name = tags.get("name", "無名稱")
                    address = (
                        tags.get("addr:full")
                        or tags.get("addr:street")
                        or ""
                    )

                    floor_hint = _floor_from_tags(tags) or _floor_from_name(name)

                    try:
                        dist = haversine(
                            float(lat), float(lon),
                            float(t_lat), float(t_lon)
                        )
                    except Exception:
                        continue

                    if dist > r:
                        continue

                    toilets.append({
                        "name": name,
                        "lat": float(norm_coord(t_lat)),
                        "lon": float(norm_coord(t_lon)),
                        "address": address,
                        "distance": dist,
                        "type": "osm",
                        "floor_hint": floor_hint,
                        "level": tags.get("level") or tags.get("addr:floor") or "",
                        "open_hours": tags.get("opening_hours") or "",
                        "entrance_hint": tags.get("entrance") or "",
                    })

                if not toilets:
                    continue

                # enrich（保持你原本邏輯，不動）
                if enrich_on:
                    try:
                        nearby_named = enrich_nearby_places(lat, lon, radius=500)
                        if nearby_named:
                            for t in toilets:
                                if (not t.get("name")) or t["name"] == "無名稱":
                                    best = None
                                    best_d = 61.0
                                    for p in nearby_named:
                                        d = haversine(
                                            t["lat"], t["lon"],
                                            p["lat"], p["lon"]
                                        )
                                        if d < best_d:
                                            best_d = d
                                            best = p
                                    if best:
                                        t["place_hint"] = best["name"]
                    except Exception:
                        pass

                toilets = heapq.nsmallest(
                    max_items,
                    toilets,
                    key=lambda x: x["distance"]
                )
                return toilets

            except Exception as e:
                last_err = e
                logging.warning(f"Overpass API 查詢失敗（endpoint {idx}）: {e}")

        logging.warning(f"Overpass 半徑 {r} 失敗：{last_err}")

    return []

# === 讀取 Postgres 使用者新增廁所 ===
def query_saved_toilets(user_lat, user_lon, radius=500):
    if not POSTGRES_ENABLED:
        return []

    heap = []
    limit = max(LOC_MAX_RESULTS * 8, 60)
    try:
        user_lat = float(user_lat)
        user_lon = float(user_lon)
        dlat = radius / 111000.0
        dlon = radius / (111000.0 * max(0.1, math.cos(math.radians(user_lat))))
        min_lat, max_lat = user_lat - dlat, user_lat + dlat
        min_lon, max_lon = user_lon - dlon, user_lon + dlon

        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT user_id, name, address, lat, lon, level, floor_hint, entrance_hint, access_note, open_hours, created_at
            FROM user_toilets
            WHERE lat BETWEEN %s AND %s
              AND lon BETWEEN %s AND %s
              AND COALESCE(verification_status, 'pending') <> 'rejected'
            ORDER BY created_at DESC
            LIMIT 500
        """, (min_lat, max_lat, min_lon, max_lon))
        rows = cur.fetchall()
        conn.close()

        for row in rows:
            try:
                t_lat = float(row.get("lat"))
                t_lon = float(row.get("lon"))
            except Exception:
                continue
            if not _in_bbox(t_lat, t_lon, user_lat, user_lon, radius):
                continue
            dist = haversine(user_lat, user_lon, t_lat, t_lon)
            if dist > radius:
                continue
            item = {
                "name": (row.get("name") or "無名稱").strip(),
                "lat": float(norm_coord(t_lat)),
                "lon": float(norm_coord(t_lon)),
                "address": (row.get("address") or "").strip(),
                "distance": dist,
                "type": "user_db",
                "grade": "使用者新增",
                "category": "使用者補充",
                "floor_hint": (row.get("floor_hint") or _floor_from_name(row.get("name") or "")),
                "entrance_hint": row.get("entrance_hint") or "",
                "access_note": row.get("access_note") or "",
                "open_hours": row.get("open_hours") or "",
            }
            heapq.heappush(heap, (-dist, id(item), item))
            if len(heap) > limit:
                heapq.heappop(heap)
    except Exception as e:
        logging.warning(f"query_saved_toilets failed: {e}")
        return []

    return [item for _, _, item in sorted(heap, key=lambda x: -x[0])]

# === 讀取 public_toilets.csv ===
def _load_public_csv_rows_cached():
    """Load public_toilets.csv once and refresh only when the file changes."""
    if not os.path.exists(TOILETS_FILE_PATH):
        return []

    try:
        mtime = os.path.getmtime(TOILETS_FILE_PATH)
    except Exception as e:
        logging.error(f"讀 public_toilets.csv mtime 失敗：{e}")
        return []

    cached_rows = _PUBLIC_CSV_CACHE.get("rows") or []
    if _PUBLIC_CSV_CACHE.get("mtime") == mtime:
        return cached_rows

    with _PUBLIC_CSV_CACHE_LOCK:
        cached_rows = _PUBLIC_CSV_CACHE.get("rows") or []
        if _PUBLIC_CSV_CACHE.get("mtime") == mtime:
            return cached_rows

        try:
            with open(TOILETS_FILE_PATH, "r", encoding="utf-8-sig", newline="") as f:
                rows = list(csv.DictReader(f))
            _PUBLIC_CSV_CACHE["mtime"] = mtime
            _PUBLIC_CSV_CACHE["rows"] = rows
            logging.info(f"✅ public_toilets.csv cached: {len(rows)} rows")
            return rows
        except Exception as e:
            logging.error(f"讀 public_toilets.csv 失敗：{e}")
            return cached_rows


def query_public_csv_toilets(user_lat, user_lon, radius=500):
    rows = _load_public_csv_rows_cached()
    if not rows:
        return []

    heap = []
    limit = LOC_MAX_RESULTS

    try:
        for row in rows:
            try:
                t_lat = float(row.get("latitude"))
                t_lon = float(row.get("longitude"))
            except Exception:
                continue

            if not _in_bbox(t_lat, t_lon, user_lat, user_lon, radius):
                continue

            dist = haversine(user_lat, user_lon, t_lat, t_lon)
            if dist > radius:
                continue

            name = (row.get("name") or "無名稱").strip()
            addr = (row.get("address") or "").strip()
            floor_hint = _floor_from_name(name)

            item = {
                "name": name,
                "lat": float(norm_coord(t_lat)),
                "lon": float(norm_coord(t_lon)),
                "address": addr,
                "distance": dist,
                "type": "public_csv",
                "grade": row.get("grade", ""),
                "category": row.get("type2", ""),
                "floor_hint": floor_hint,
            }

            heapq.heappush(heap, (-dist, id(item), item))
            if len(heap) > limit:
                heapq.heappop(heap)

    except Exception as e:
        logging.error(f"查詢 public_toilets.csv 快取資料失敗：{e}")
        return []

    return [item for _, _, item in sorted(heap, key=lambda x: -x[0])]

# === 合併 + 去重 ===
def _merge_and_dedupe_lists(*lists, dist_th=35, name_sim_th=0.55):
    all_pts = []
    for l in lists:
        if l:
            all_pts.extend(l)
    all_pts.sort(key=lambda x: x.get("distance", 1e9))

    merged = []
    buckets = {}
    # 0.0005 degrees is roughly 50m in Taiwan latitude, enough for a 35m duplicate threshold.
    grid_size = 0.0005

    def _bucket_key(lat, lon):
        return (int(float(lat) / grid_size), int(float(lon) / grid_size))

    def _neighbor_keys(key):
        x, y = key
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                yield (x + dx, y + dy)

    for p in all_pts:
        try:
            p_key = _bucket_key(p["lat"], p["lon"])
            candidate_pool = []
            for k in _neighbor_keys(p_key):
                candidate_pool.extend(buckets.get(k, []))
        except Exception:
            p_key = None
            candidate_pool = merged

        dup = False
        p_name = (p.get("name") or "").lower()
        for q in candidate_pool:
            try:
                near = haversine(p["lat"], p["lon"], q["lat"], q["lon"]) <= dist_th
            except Exception:
                near = False
            if not near:
                continue

            q_name = (q.get("name") or "").lower()
            sim = SequenceMatcher(None, p_name, q_name).ratio()
            if sim >= name_sim_th:
                dup = True
                break

        if not dup:
            merged.append(p)
            if p_key is not None:
                buckets.setdefault(p_key, []).append(p)
    return merged

# === 最愛管理 ===
# favorites.txt 是純文字/CSV 檔，於多執行緒環境下需要鎖避免同時讀寫造成破檔
# （例如同一時間多位使用者點收藏/取消收藏）
_FAV_LOCK = threading.Lock()

def add_to_favorites(uid, toilet):
    """Add a toilet to favorites.
    Primary store: Neon/Postgres favorites table.
    Fallback: local favorites.txt, only if Postgres is not enabled.
    """
    try:
        if not uid or not toilet:
            return False

        name = (toilet.get("name") or "").strip()
        lat = toilet.get("lat")
        lon = toilet.get("lon")
        address = toilet.get("address", "") or ""

        if not name or lat is None or lon is None:
            return False

        lat_f = float(lat)
        lon_f = float(lon)

        if POSTGRES_ENABLED:
            conn = _pg_connect()
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO favorites (user_id, name, lat, lon, address)
                VALUES (%s, %s, %s, %s, %s)
                ON CONFLICT (user_id, name, lat, lon)
                DO UPDATE SET address = COALESCE(NULLIF(EXCLUDED.address, ''), favorites.address)
            """, (uid, name, lat_f, lon_f, address))
            conn.commit()
            conn.close()
            return True

        lat_s = norm_coord(lat_f)
        lon_s = norm_coord(lon_f)
        with _FAV_LOCK:
            # avoid duplicate rows in fallback file
            exists = False
            if os.path.exists(FAVORITES_FILE_PATH):
                with open(FAVORITES_FILE_PATH, "r", encoding="utf-8", newline="") as f:
                    reader = csv.reader(f)
                    for row in reader:
                        if len(row) >= 4 and row[0] == uid and row[1] == name and row[2] == lat_s and row[3] == lon_s:
                            exists = True
                            break
            if not exists:
                with open(FAVORITES_FILE_PATH, "a", encoding="utf-8", newline="") as f:
                    writer = csv.writer(f)
                    writer.writerow([uid, name, lat_s, lon_s, address])
        return True

    except Exception as e:
        logging.error(f"加入最愛失敗: {e}", exc_info=True)
        return False


def remove_from_favorites(uid, name, lat, lon):
    """Remove a favorite from Neon/Postgres, with local-file fallback."""
    try:
        if not uid or not name:
            return False

        lat_f = float(lat)
        lon_f = float(lon)

        if POSTGRES_ENABLED:
            conn = _pg_connect()
            cur = conn.cursor()
            cur.execute("""
                DELETE FROM favorites
                WHERE user_id = %s
                  AND name = %s
                  AND lat = %s
                  AND lon = %s
                RETURNING id
            """, (uid, name, lat_f, lon_f))
            row = cur.fetchone()
            conn.commit()
            conn.close()
            return bool(row)

        lat_s = norm_coord(lat_f)
        lon_s = norm_coord(lon_f)
        with _FAV_LOCK:
            rows = []
            changed = False
            if os.path.exists(FAVORITES_FILE_PATH):
                with open(FAVORITES_FILE_PATH, "r", encoding="utf-8", newline="") as f:
                    reader = csv.reader(f)
                    for row in reader:
                        if len(row) < 5:
                            rows.append(row)
                            continue
                        if not (row[0] == uid and row[1] == name and row[2] == lat_s and row[3] == lon_s):
                            rows.append(row)
                        else:
                            changed = True
            if changed:
                with open(FAVORITES_FILE_PATH, "w", encoding="utf-8", newline="") as f:
                    writer = csv.writer(f)
                    writer.writerows(rows)
        return changed

    except Exception as e:
        logging.error(f"移除最愛失敗: {e}", exc_info=True)
        return False


def get_user_favorites(uid):
    """Read user's favorites.
    Returned rows include type='favorite' so the Flex card shows '移除最愛'.
    """
    favs = []
    if not uid:
        return favs

    try:
        if POSTGRES_ENABLED:
            conn = _pg_connect()
            cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
            cur.execute("""
                SELECT name, lat, lon, address, created_at
                FROM favorites
                WHERE user_id = %s
                ORDER BY created_at DESC
                LIMIT 50
            """, (uid,))
            rows = cur.fetchall()
            conn.close()

            for r in rows:
                favs.append({
                    "user_id": uid,
                    "name": r.get("name") or "",
                    "lat": float(r.get("lat")),
                    "lon": float(r.get("lon")),
                    "address": r.get("address") or "",
                    "type": "favorite",
                    "source": "最愛",
                })
            return favs

        with _FAV_LOCK:
            if not os.path.exists(FAVORITES_FILE_PATH):
                return favs
            with open(FAVORITES_FILE_PATH, "r", encoding="utf-8", newline="") as f:
                reader = csv.reader(f)
                for row in reader:
                    if len(row) < 5:
                        continue
                    if row[0] != uid:
                        continue
                    favs.append({
                        "user_id": row[0],
                        "name": row[1],
                        "lat": float(row[2]),
                        "lon": float(row[3]),
                        "address": row[4],
                        "type": "favorite",
                        "source": "最愛",
                    })
        return favs

    except Exception as e:
        logging.error(f"讀取最愛失敗: {e}", exc_info=True)
        return favs

def geocode_address(address):
    try:
        ua_email = os.getenv("CONTACT_EMAIL", "school-toilet-bot@gmail.com")

        url = (
            "https://nominatim.openstreetmap.org/search"
            f"?format=json&q={quote(address)}"
        )

        headers = {
            "User-Agent": f"ToiletBot/1.0 (+{ua_email})"
        }

        resp = requests.get(url, headers=headers, timeout=10)

        # ① HTTP 狀態碼檢查
        if resp.status_code != 200:
            logging.error(
                f"地址轉經緯度失敗: HTTP {resp.status_code}, text={resp.text[:200]}"
            )
            return None, None

        # ② 空回應檢查
        if not resp.text or not resp.text.strip():
            logging.error("地址轉經緯度失敗: 回傳內容為空")
            return None, None

        # ③ JSON 解析保護
        try:
            data = resp.json()
        except Exception:
            logging.error(
                f"地址轉經緯度失敗: 非 JSON 回應, text={resp.text[:200]}"
            )
            return None, None

        # ④ 資料內容檢查
        if not data:
            logging.warning(f"地址轉經緯度失敗: 查無結果 address={address}")
            return None, None

        # ⑤ 正常回傳
        lat = float(data[0].get("lat"))
        lon = float(data[0].get("lon"))
        return lat, lon

    except Exception as e:
        logging.error(f"地址轉經緯度例外錯誤: {e}", exc_info=True)

    return None, None

# === 附近廁所 API ===
@app.route("/nearby_toilets", methods=["GET"])
def nearby_toilets():
    user_lat = request.args.get('lat')
    user_lon = request.args.get('lon')
    if not user_lat or not user_lon:
        return {"error": _api_L("缺少位置參數", "Missing location parameters")}, 400

    user_lat, user_lon = _parse_lat_lon(user_lat, user_lon)
    if user_lat is None or user_lon is None:
        return {"error": _api_L("位置參數錯誤", "Invalid location parameters")}, 400

    public_csv_toilets = query_public_csv_toilets(user_lat, user_lon, radius=500) or []
    saved_toilets = query_saved_toilets(user_lat, user_lon, radius=500) or []
    osm_toilets = query_overpass_toilets(user_lat, user_lon, radius=500) or []

    all_toilets = _merge_and_dedupe_lists(public_csv_toilets, saved_toilets, osm_toilets)
    sort_toilets(all_toilets)

    if not all_toilets:
        return {"message": _api_L("附近找不到廁所", "No nearby toilets found")}, 404
    return {"toilets": all_toilets}, 200

# === 顯示回饋表單 ===
@app.route("/feedback_form/<toilet_name>/", defaults={'address': ''})
@app.route("/feedback_form/<toilet_name>/<path:address>")
def feedback_form(toilet_name, address):
    address = address or request.args.get("address", "")
    return render_template(
        "feedback_form.html",
        toilet_name=toilet_name,
        address=address,
        lat=request.args.get("lat", ""),
        lon=request.args.get("lon", "")
    )

# === 對齊 ===
def _norm_h(s):
    return (s or "").strip().lower()

def _find_idx(header, candidates):
    hmap = {_norm_h(h): i for i, h in enumerate(header)}
    for c in candidates:
        if _norm_h(c) in hmap:
            return hmap[_norm_h(c)]
    return None

def _feedback_indices(header):
    return {
        "name": _find_idx(header, ["名稱", "name", "toilet_name"]),
        "address": _find_idx(header, ["地址", "address"]),
        "rating": _find_idx(header, ["清潔度評分", "清潔評分", "rating", "score"]),
        "paper": _find_idx(header, ["是否有衛生紙", "toilet_paper", "衛生紙", "紙"]),
        "access": _find_idx(header, ["是否有無障礙設施", "accessibility", "無障礙"]),
        "time": _find_idx(header, ["使用時間", "time_of_use", "time"]),
        "comment": _find_idx(header, ["留言", "comment", "備註"]),
        "pred": _find_idx(header, ["預測分數", "預測評分", "cleanliness_score", "predicted_score"]),
        "lat": _find_idx(header, ["lat", "緯度"]),
        "lon": _find_idx(header, ["lon", "經度", "lng", "long"]),
        "created": _find_idx(header, ["created_at", "建立時間", "時間", "timestamp"]),
        "floor": _find_idx(header, ["floor", "樓層", "floor_hint", "level", "位置樓層"]),
    }

def _toilet_sheet_indices(header):
    return {
        "user_id": _find_idx(header, ["user_id", "uid", "使用者"]),
        "name": _find_idx(header, ["name", "名稱"]),
        "address": _find_idx(header, ["address", "地址"]),
        "lat": _find_idx(header, ["lat", "緯度"]),
        "lon": _find_idx(header, ["lon", "經度", "lng", "long"]),
        "created": _find_idx(header, ["timestamp", "created_at", "建立時間"]),
        "level": _find_idx(header, ["level", "樓層"]),
        "floor_hint": _find_idx(header, ["floor_hint", "位置樓層", "樓層說明"]),
        "open_hours": _find_idx(header, ["open_hours", "開放時間", "營業時間"]),
    }

# === 清潔度預測 ===
def expected_from_feats(feats):
    try:
        if not feats or cleanliness_model is None:
            return None
        if pd is not None:
            df = pd.DataFrame(feats, columns=["rating","toilet_paper","accessibility"])
            probs = cleanliness_model.predict_proba(df)
        else:
            probs = cleanliness_model.predict_proba(feats)

        try:
            classes_enc = cleanliness_model.classes_
            labels = label_encoder.inverse_transform(classes_enc)
            labels = [float(x) for x in labels]
        except Exception:
            labels = [float(c) + 1.0 for c in cleanliness_model.classes_]

        exps = [sum(float(p)*float(l) for p, l in zip(p_row, labels)) for p_row in probs]
        return round(sum(exps)/len(exps), 2) if exps else None
    except Exception as e:
        logging.error(f"❌ 清潔度預測錯誤: {e}")
        return None

def _simple_score(rr, paper, acc):
    try:
        base = 1.0 + 4.0 * (int(rr) - 1) / 9.0
    except Exception:
        return None
    bonus = (0.25 if (paper == "有") else 0.0) + (0.25 if (acc == "有") else 0.0)
    score = base + bonus
    if score < 1.0: score = 1.0
    if score > 5.0: score = 5.0
    return round(score, 2)

def _pred_from_row(r, idx):
    paper_map = {"有": 1, "沒有": 0, "沒注意": 0}
    access_map = {"有": 1, "沒有": 0, "沒注意": 0}

    rr = None
    if idx["rating"] is not None and len(r) > idx["rating"]:
        try:
            rr = int((r[idx["rating"]] or "").strip())
        except:
            rr = None
    pp = (r[idx["paper"]] or "").strip() if idx["paper"] is not None and len(r) > idx["paper"] else "沒注意"
    aa = (r[idx["access"]] or "").strip() if idx["access"] is not None and len(r) > idx["access"] else "沒注意"

    score = None
    if rr is not None and cleanliness_model is not None:
        try:
            feat = [rr, paper_map.get(pp, 0), access_map.get(aa, 0)]
            score = expected_from_feats([feat])
        except Exception:
            score = None
    if score is None and idx["pred"] is not None and len(r) > idx["pred"]:
        try:
            score = float((r[idx["pred"]] or "").strip())
        except:
            score = None
    if score is None:
        score = _simple_score(rr, pp, aa)
    return (score, rr, pp, aa)

# === 即時預測 / 95% CI ===
def compute_nowcast_ci(lat, lon, k=LAST_N_HISTORY, tol=1e-6):
    """Compute nowcast from Neon/Postgres feedback."""
    if not POSTGRES_ENABLED:
        return None

    try:
        NOWCAST_MAX_K = int(os.getenv("NOWCAST_MAX_K", "8"))
    except Exception:
        NOWCAST_MAX_K = 8
    if k is None or not isinstance(k, int) or k <= 0:
        k = LAST_N_HISTORY
    k = min(k, NOWCAST_MAX_K)

    lat_f, lon_f = _parse_lat_lon(lat, lon)
    if lat_f is None or lon_f is None:
        return None

    try:
        rows = _fetch_feedback_pg_by_coord(lat_f, lon_f, tol=1e-4, limit=max(k * 3, k))
        if not rows:
            return None

        vals = []
        for row in rows[:k]:
            sc = row.get("cleanliness_score")
            try:
                if sc not in (None, ""):
                    vals.append(float(sc))
                    continue
            except Exception:
                pass
            try:
                if row.get("rating") not in (None, ""):
                    vals.append(float(row.get("rating")))
            except Exception:
                pass

        if not vals:
            return None

        n = len(vals)
        mean = round(sum(vals) / n, 2)
        if n == 1:
            return {"mean": mean, "lower": mean, "upper": mean, "n": 1}

        try:
            s = statistics.stdev(vals)
        except statistics.StatisticsError:
            s = 0.0
        se = s / (n ** 0.5)
        return {
            "mean": mean,
            "lower": max(1.0, round(mean - 1.96 * se, 2)),
            "upper": min(10.0, round(mean + 1.96 * se, 2)),
            "n": n,
        }
    except Exception as e:
        logging.error(f"❌ compute_nowcast_ci failed: {e}", exc_info=True)
        return None

# === Nowcast API ===
@app.route("/get_nowcast_by_coord/<lat>/<lon>")
def get_nowcast_by_coord(lat, lon):
    try:
        res = compute_nowcast_ci(lat, lon)
        if not res:
            return {"success": True, "n": 0}, 200
        res["success"] = True
        return res, 200
    except Exception as e:
        logging.error(f"❌ Nowcast API 錯誤: {e}")
        return {"success": False}, 500

# ==== 狀態：候選三間（靠 build_nearby_toilets）====
@app.route("/api/status_candidates")
def api_status_candidates():
    try:
        lat = float(request.args.get("lat"))
        lon = float(request.args.get("lon"))
    except Exception:
        return {"ok": False, "message": "缺少或錯誤的座標"}, 400

    try:
        # 半徑放寬一點，提高命中率；已內建快取/去重/排序
        items = build_nearby_toilets("status", lat, lon, radius=700) or []
        out = []
        for t in items[:3]:
            out.append({
                "title": t.get("name") or t.get("place_hint") or "（未命名）廁所",
                "address": t.get("address") or "",
                # 用 norm_coord（字串）讓之後比對座標更穩定
                "lat": norm_coord(t["lat"]),
                "lon": norm_coord(t["lon"]),
                "distance": int(t.get("distance", 0))
            })
        return {"ok": True, "candidates": out}, 200
    except Exception as e:
        logging.error(f"/api/status_candidates 失敗: {e}")
        return {"ok": False, "message": "server error"}, 500

# ==== 狀態：回報（靠 submit_status_update 寫入 status 分頁）====
@app.route("/api/status_report", methods=["POST"])
def api_status_report():
    try:
        payload = request.get_json(force=True)
        lat = float(payload["lat"])
        lon = float(payload["lon"])
        status_text = (payload.get("status") or "").strip()
        user_id = (payload.get("user_id") or "").strip()
        display_name = (payload.get("display_name") or "").strip()
        note = (payload.get("note") or "").strip()
    except Exception:
        return {"ok": False, "message": _api_L("參數錯誤", "Invalid parameters")}, 400

    allowed = {"有人排隊", "缺衛生紙", "暫停使用", "恢復正常"}
    if status_text not in allowed:
        return {"ok": False, "message": _api_L("不支援的狀態", "Unsupported status")}, 400

    try:
        ok = submit_status_update(lat, lon, status_text, user_id, display_name, note)
        return ({"ok": True}, 200) if ok else ({"ok": False, "message": _api_L("寫入失敗", "Write failed")}, 500)
    except Exception as e:
        logging.error(f"/api/status_report 寫入失敗: {e}")
        return {"ok": False, "message": "server error"}, 500


# === Neon feedback storage（正式回饋儲存） ===
def _insert_feedback_pg(name, address, rating, toilet_paper, accessibility, time_of_use,
                        comment, cleanliness_score, lat, lon, floor_hint="", uid=""):
    if not POSTGRES_ENABLED:
        return False
    conn = None
    try:
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO toilet_feedbacks
            (name, address, rating, toilet_paper, accessibility, time_of_use,
             comment, cleanliness_score, lat, lon, floor_hint, user_id_hash, created_at)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, NOW())
        """, (
            name or "",
            address or "",
            int(rating) if str(rating).strip() else None,
            toilet_paper or "",
            accessibility or "",
            time_of_use or "",
            comment or "",
            float(cleanliness_score) if isinstance(cleanliness_score, (int, float)) or str(cleanliness_score).replace('.', '', 1).isdigit() else None,
            float(lat),
            float(lon),
            floor_hint or "",
            mask_user_id(uid) if uid else None,
        ))
        conn.commit()
        return True
    except Exception as e:
        if conn:
            try:
                conn.rollback()
            except Exception:
                pass
        logging.error(f"insert toilet_feedbacks failed: {e}", exc_info=True)
        return False
    finally:
        if conn:
            try:
                conn.close()
            except Exception:
                pass


def _fetch_feedback_pg_by_coord(lat, lon, tol=1e-6, limit=None):
    if not POSTGRES_ENABLED:
        return []
    lat_f, lon_f = _parse_lat_lon(lat, lon)
    if lat_f is None or lon_f is None:
        return []
    try:
        limit = int(limit or FEEDBACK_LOOKBACK_LIMIT or 4000)
    except Exception:
        limit = 4000
    conn = None
    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT name, address, rating, toilet_paper, accessibility, time_of_use,
                   comment, cleanliness_score, lat, lon, floor_hint, created_at
            FROM toilet_feedbacks
            WHERE ABS(lat - %s) <= %s AND ABS(lon - %s) <= %s
            ORDER BY created_at DESC
            LIMIT %s
        """, (float(lat_f), float(tol), float(lon_f), float(tol), limit))
        return [dict(r) for r in (cur.fetchall() or [])]
    except Exception as e:
        logging.error(f"fetch toilet_feedbacks by coord failed: {e}", exc_info=True)
        return []
    finally:
        if conn:
            try:
                conn.close()
            except Exception:
                pass


def _feedback_pg_to_public(row):
    def _clean(v):
        return "" if v is None else str(v)
    created = row.get("created_at")
    if hasattr(created, "isoformat"):
        created_s = created.isoformat()
    else:
        created_s = _clean(created)
    score = row.get("cleanliness_score")
    try:
        score_s = str(round(float(score), 2)) if score is not None else ""
    except Exception:
        score_s = _clean(score)
    return {
        "rating": _clean(row.get("rating")),
        "toilet_paper": _clean(row.get("toilet_paper")),
        "accessibility": _clean(row.get("accessibility")),
        "time_of_use": _clean(row.get("time_of_use")),
        "comment": safe_html(_clean(row.get("comment"))),
        "cleanliness_score": score_s,
        "created_at": created_s,
    }


def _feedback_rows_to_summary(rows):
    if not rows:
        return "尚無回饋資料"
    paper_counts = {"有": 0, "沒有": 0}
    access_counts = {"有": 0, "沒有": 0}
    scores = []
    comments = []
    for row in rows:
        if row.get("toilet_paper") in paper_counts:
            paper_counts[row.get("toilet_paper")] += 1
        if row.get("accessibility") in access_counts:
            access_counts[row.get("accessibility")] += 1
        try:
            if row.get("cleanliness_score") is not None:
                scores.append(float(row.get("cleanliness_score")))
            elif row.get("rating") is not None:
                scores.append(float(row.get("rating")))
        except Exception:
            pass
        c = (row.get("comment") or "").strip()
        if c:
            comments.append(c)
    avg_score = round(sum(scores) / len(scores), 2) if scores else "未預測"
    summary = f"🔍 筆數：{len(rows)}\n"
    summary += f"🧼 平均清潔分數：{avg_score}\n"
    summary += f"🧻 衛生紙：{'有' if paper_counts['有'] >= paper_counts['沒有'] else '沒有'}\n"
    summary += f"♿ 無障礙：{'有' if access_counts['有'] >= access_counts['沒有'] else '沒有'}\n"
    if comments:
        summary += f"💬 最新留言：{comments[0]}"
    return summary

# === 回饋 ===
@app.route("/submit_feedback", methods=["POST"])
def submit_feedback():
    logging.info(f"[submit_feedback] content_type={request.content_type}")

    if not POSTGRES_ENABLED:
        logging.error("submit_feedback failed: Postgres storage is not enabled")
        return "提交失敗：回饋儲存尚未設定", 503

    try:
        payload_json = request.get_json(silent=True)
        if payload_json and isinstance(payload_json, dict) and len(payload_json) > 0:
            data = payload_json
            src = "json"
            getv = lambda k, d="": (data.get(k) if data.get(k) is not None else d)
        else:
            data = request.form
            src = "form"
            getv = lambda k, d="": (data.get(k, d) if data.get(k, d) is not None else d)

        name = (getv("name", "") or "").strip()
        address = (getv("address", "") or "").strip()
        lat_raw = ((getv("lat", "") or request.args.get("lat") or "")).strip()
        lon_raw = ((getv("lon", "") or request.args.get("lon") or "")).strip()

        lat_f, lon_f = _parse_lat_lon(lat_raw, lon_raw)
        if lat_f is None or lon_f is None:
            return "座標格式錯誤", 400

        lat = norm_coord(lat_f)
        lon = norm_coord(lon_f)
        rating = ((getv("rating", "") or "")).strip()
        toilet_paper = ((getv("toilet_paper", "") or "")).strip()
        accessibility = ((getv("accessibility", "") or "")).strip()
        time_of_use = ((getv("time_of_use", "") or "")).strip()
        comment = ((getv("comment", "") or "")).strip()
        floor_hint = ((getv("floor_hint", "") or "")).strip()

        logging.info(
            f"[submit_feedback] src={src} name={name[:40]} rating={rating} "
            f"lat={lat} lon={lon} paper={toilet_paper} access={accessibility}"
        )

        missing = []
        if not name: missing.append("name")
        if not rating: missing.append("rating")
        if not lat_raw: missing.append("lat")
        if not lon_raw: missing.append("lon")
        if not toilet_paper: missing.append("toilet_paper")
        if not accessibility: missing.append("accessibility")
        if missing:
            return "缺少必要欄位：" + ", ".join(missing), 400

        try:
            r = int(rating)
            if r < 1 or r > 10:
                return "清潔度評分必須在 1 到 10 之間", 400
        except ValueError:
            return "清潔度評分必須是數字", 400

        if not floor_hint:
            inferred = _floor_from_name(name)
            if inferred:
                floor_hint = inferred

        paper_map = {"有": 1, "沒有": 0, "沒注意": 0}
        access_map = {"有": 1, "沒有": 0, "沒注意": 0}
        cur_feat = [r, paper_map.get(toilet_paper, 0), access_map.get(accessibility, 0)]

        hist_feats = []
        try:
            recent = _fetch_feedback_pg_by_coord(lat, lon, tol=1e-4, limit=LAST_N_HISTORY)
            for row in recent:
                try:
                    rr = int(row.get("rating"))
                except Exception:
                    continue
                pp = (row.get("toilet_paper") or "沒注意").strip()
                aa = (row.get("accessibility") or "沒注意").strip()
                hist_feats.append([rr, paper_map.get(pp, 0), access_map.get(aa, 0)])
        except Exception as e:
            logging.warning(f"讀歷史回饋失敗，僅用單筆特徵預測：{e}")

        pred_with_hist = expected_from_feats([cur_feat] + hist_feats) or expected_from_feats([cur_feat]) or "未預測"
        uid = (request.args.get("uid") or "").strip()

        ok = _insert_feedback_pg(
            name=name, address=address, rating=rating, toilet_paper=toilet_paper,
            accessibility=accessibility, time_of_use=time_of_use, comment=comment,
            cleanliness_score=pred_with_hist, lat=lat, lon=lon, floor_hint=floor_hint, uid=uid
        )
        if not ok:
            return "提交失敗：回饋資料寫入 Neon 失敗", 500

        lang = (request.args.get("lang") or "").strip().lower()
        target = f"/toilet_feedback_by_coord/{lat}/{lon}"
        if uid:
            target = _append_uid_lang(target, uid, (lang if lang in ("en", "zh") else _user_lang_q(uid)))
        return redirect(target)

    except Exception as e:
        logging.error(f"❌ 提交回饋表單錯誤: {e}", exc_info=True)
        return "提交失敗", 500

# === 讀座標的回饋清單 ===
def get_feedbacks_by_coord(lat, lon, tol=1e-6):
    if not POSTGRES_ENABLED:
        return []
    try:
        return [_feedback_pg_to_public(row) for row in _fetch_feedback_pg_by_coord(lat, lon, tol=tol)]
    except Exception as e:
        logging.error(f"❌ 讀取回饋列表（Neon 座標）錯誤: {e}", exc_info=True)
        return []

# === 座標聚合統計 ===
def get_feedback_summary_by_coord(lat, lon, tol=1e-6):
    if not POSTGRES_ENABLED:
        return "尚無回饋資料"
    try:
        return _feedback_rows_to_summary(_fetch_feedback_pg_by_coord(lat, lon, tol=tol))
    except Exception as e:
        logging.error(f"❌ 查詢回饋統計（Neon 座標）錯誤: {e}", exc_info=True)
        return "讀取錯誤"

# === 指示燈索引 ===
_feedback_index_cache = {"ts": 0, "data": {}}
# _FEEDBACK_INDEX_TTL is defined in global config section (see above)
def build_feedback_index():
    """Feedback feature is disabled; keep interface returning empty indicators."""
    return {}

def submit_status_update(lat, lon, status_text, user_id="", display_name="", note=""):
    """Write toilet status reports to Neon."""
    if not POSTGRES_ENABLED:
        return False
    try:
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO toilet_status_reports (user_id, display_name, lat, lon, status, note, created_at)
            VALUES (%s, %s, %s, %s, %s, %s, NOW())
        """, (user_id or "", display_name or "", float(lat), float(lon), (status_text or "").strip(), (note or "").strip()))
        conn.commit()
        conn.close()
        _status_index_cache["ts"] = 0
        return True
    except Exception as e:
        logging.error(f"寫入 Neon 狀態失敗: {e}", exc_info=True)
        return False

def _is_close_m(lat1, lon1, lat2, lon2, th=_STATUS_NEAR_M):
    try:
        return haversine(float(lat1), float(lon1), float(lat2), float(lon2)) <= th
    except:
        return False

def build_status_index():
    """Build recent status index from Neon toilet_status_reports."""
    if not POSTGRES_ENABLED:
        return {}
    now = time.time()
    if (now - _status_index_cache["ts"] < _STATUS_INDEX_TTL) and _status_index_cache["data"]:
        return _status_index_cache["data"]
    try:
        STATUS_INDEX_MAX_KEYS = int(os.getenv("STATUS_INDEX_MAX_KEYS", "800"))
    except Exception:
        STATUS_INDEX_MAX_KEYS = 800
    out = {}
    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT lat, lon, status, created_at
            FROM toilet_status_reports
            WHERE created_at >= NOW() - (%s || ' hours')::interval
            ORDER BY created_at DESC
            LIMIT 4000
        """, (str(_STATUS_TTL_HOURS),))
        rows = cur.fetchall()
        conn.close()
        merged = []
        for r in rows:
            lat_s, lon_s = norm_coord(r.get("lat")), norm_coord(r.get("lon"))
            st = (r.get("status") or "").strip()
            ts = r.get("created_at")
            ts_s = ts.isoformat() if hasattr(ts, "isoformat") else str(ts or "")
            if not st:
                continue
            placed = False
            for m in merged:
                if _is_close_m(lat_s, lon_s, m["lat"], m["lon"]):
                    placed = True
                    break
            if not placed and len(merged) < STATUS_INDEX_MAX_KEYS:
                merged.append({"lat": lat_s, "lon": lon_s, "status": st, "ts": ts_s})
        for m in merged:
            out[(m["lat"], m["lon"])] = {"status": m["status"], "ts": m["ts"]}
        _status_index_cache.update(ts=now, data=out)
        return out
    except Exception as e:
        logging.warning(f"建立 Neon 狀態索引失敗：{e}")
        _status_index_cache.update(ts=now, data={})
        return {}

# ==== 環境變數（統一 LIFF 讀取）====
def _get_liff_status_id() -> str:
    return (
        os.getenv("LIFF_STATUS_ID")      
        or os.getenv("LIFF_ID_STATUS")
        or os.getenv("LIFF_ID")
        or ""
    ).strip()

LIFF_ID_STATUS = _get_liff_status_id()
PUBLIC_URL = os.getenv("PUBLIC_URL", "").rstrip("/")

# ==== 頁面 routes ====
@app.route("/achievements_liff")
def achievements_liff_page():
    uid = (request.args.get("uid") or "").strip()
    lang = (request.args.get("lang") or "").strip().lower()
    if uid and not lang:
        try:
            lang = "en" if get_user_lang(uid) == "en" else "zh"
        except Exception:
            lang = "zh"
        qs = request.args.to_dict(flat=True)
        qs["lang"] = lang
        return redirect(request.path + "?" + urllib.parse.urlencode(qs), code=302)

    return render_template(
        "achievements_liff.html",
        liff_id=LIFF_ID_STATUS,
        public_url=PUBLIC_URL,
        uid=uid,
        lang=(lang if lang in ["en","zh"] else "zh")
    )

@app.route("/badges_liff")
def badges_liff_page():
    uid = (request.args.get("uid") or "").strip()
    lang = (request.args.get("lang") or "").strip().lower()
    if uid and not lang:
        try:
            lang = "en" if get_user_lang(uid) == "en" else "zh"
        except Exception:
            lang = "zh"
        qs = request.args.to_dict(flat=True)
        qs["lang"] = lang
        return redirect(request.path + "?" + urllib.parse.urlencode(qs), code=302)

    return render_template(
        "badges_liff.html",
        liff_id=LIFF_ID_STATUS,
        public_url=PUBLIC_URL,
        uid=uid,
        lang=(lang if lang in ["en","zh"] else "zh")
    )

# ==== 小工具：讀取狀態表並彙總 ====
def _read_status_rows():
    """Read status rows from Neon for achievements/badges pages."""
    if not POSTGRES_ENABLED:
        return []
    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT lat, lon, status, user_id, display_name, created_at
            FROM toilet_status_reports
            ORDER BY created_at DESC
            LIMIT 4000
        """)
        rows = cur.fetchall()
        conn.close()
        out = []
        for r in rows:
            ts = r.get("created_at")
            out.append({
                "lat": norm_coord(r.get("lat")),
                "lon": norm_coord(r.get("lon")),
                "status": r.get("status") or "",
                "user_id": r.get("user_id") or "",
                "display_name": r.get("display_name") or "",
                "timestamp": ts.isoformat() if hasattr(ts, "isoformat") else str(ts or ""),
            })
        return out
    except Exception as e:
        logging.error(f"_read_status_rows Neon error: {e}")
        return []

def _parse_ts(ts: str):
    try:
        s = (ts or "").strip()
        if not s:
            return None

        # ISO Z → +00:00
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"

        try:
            return datetime.fromisoformat(s)
        except Exception:
            pass

        for fmt in (
            "%Y-%m-%d %H:%M:%S",
            "%Y/%m/%d %H:%M:%S",
            "%Y-%m-%d %H:%M",
            "%Y/%m/%d %H:%M",
        ):
            try:
                return datetime.strptime(s, fmt)
            except Exception:
                continue

        return None
    except Exception:
        return None

def _stats_for_user(uid: str):
    rows = _read_status_rows()
    total = 0
    by_status = {}
    last_ts = None

    for r in rows:
        if uid and r.get("user_id") != uid:
            continue

        total += 1
        s = r.get("status") or ""
        by_status[s] = by_status.get(s, 0) + 1

        ts = r.get("timestamp")
        if ts:
            t = _parse_ts(ts)
            if t is not None:
                if last_ts is None or t > last_ts:
                    last_ts = t

    return {
        "total": total,
        "by_status": by_status,
        "last_ts": last_ts.isoformat() if last_ts else None
    }

def get_search_count(uid: str) -> int:
    try:
        conn = _get_db()
        cur = conn.cursor()
        cur.execute("SELECT COUNT(*) FROM search_log WHERE user_id = ?", (uid,))
        row = cur.fetchone()
        conn.close()
        return int(row[0]) if row and row[0] is not None else 0
    except Exception as e:
        logging.warning(f"查詢 search_log 失敗: {e}")
        return 0

# ==== 成就 API ====
ACHIEVEMENT_RULES = {
    "first": {
        "goal": 1,
        "counter": "total",
        "desc": {
            "zh": "完成第一次狀態回報",
            "en": "Complete your first status report"
        }
    },
    "helper10": {
        "goal": 10,
        "counter": "total",
        "desc": {
            "zh": "累積回報 10 次",
            "en": "Report status 10 times"
        }
    },
    "pro_reporter": {
        "goal": 20,
        "counter": "total",
        "desc": {
            "zh": "累積回報 20 次",
            "en": "Report status 20 times"
        }
    },
    "helper50": {
        "goal": 50,
        "counter": "total",
        "desc": {
            "zh": "累積回報 50 次",
            "en": "Report status 50 times"
        }
    },
    "tissue_guard": {
        "goal": 3,
        "counter": "缺衛生紙",
        "desc": {
            "zh": "回報『缺衛生紙』滿 3 次",
            "en": "Report of 'toilet paper' shortage 3 time"
        }
    },
    "tissue_master": {
        "goal": 10,
        "counter": "缺衛生紙",
        "desc": {
            "zh": "回報『缺衛生紙』滿 10 次",
            "en": "Report of 'toilet paper' shortage 10 time"
        }
    },
    "queue_scout": {
    "goal": 3,
    "counter": "有人排隊",
    "desc": {
        "zh": "回報『有人排隊』滿 3 次",
        "en": "Report 'Queue present' status 3 times"
    }
    },
    "queue_commander": {
        "goal": 10,
        "counter": "有人排隊",
        "desc": {
            "zh": "回報『有人排隊』滿 10 次",
            "en": "Report 'Queue present' status 10 times"
        }
    },
    "maintenance_watcher": {
        "goal": 3,
        "counter": "暫停使用",
        "desc": {
            "zh": "回報『暫停使用』滿 3 次",
            "en": "Report 'Out of service' status 3 times"
        }
    },
    "good_news": {
        "goal": 5,
        "counter": "恢復正常",
        "desc": {
            "zh": "回報『恢復正常』滿 5 次",
            "en": "Report 'Back to normal' status 5 times"
        }
    },
}

@app.route("/api/achievements")
def api_achievements():
    uid = request.args.get("user_id", "").strip()
    lang = resolve_lang(uid=uid, lang=request.args.get("lang"))

    stats = _stats_for_user(uid)
    total = int(stats.get("total", 0) or 0)
    by = stats.get("by_status", {}) or {}

    out = []
    for cfg in BADGE_CONFIG:
        key = cfg["key"]
        rule = ACHIEVEMENT_RULES.get(key)
        if not rule:
            # 如果有在 BADGE_CONFIG 增加新 key 但還沒在 ACHIEVEMENT_RULES 定義，就先跳過
            continue

        counter_type = rule["counter"]
        if counter_type == "total":
            progress = total
        else:
            # counter_type 對應到 by_status 裡的中文 key，例如「缺衛生紙」「有人排隊」等
            progress = int(by.get(counter_type, 0) or 0)

        goal = int(rule["goal"] or 0)

        # ✅ title 也做 i18n（避免只有 UI 變、內容還是中文）
        name = cfg.get("name") or {}
        if isinstance(name, dict):
            title = name.get(lang) or name.get("zh") or ""
        else:
            title = str(name)

        out.append({
            "key": key,
            "title": title,
            "desc": (rule["desc"]["en"] if lang == "en" else rule["desc"]["zh"]),
            "goal": goal,
            "progress": progress,
            # ✅ 成就解鎖應該用成就自己的規則（progress >= goal）
            "unlocked": (progress >= goal),
            "icon": cfg.get("icon", ""),
        })

    return {"ok": True, "achievements": out}, 200

def build_usage_review_text(uid: str) -> str:
    # 改成用 DB 裡的 search_log 統計查詢次數
    search_times = get_search_count(uid)

    stats = _stats_for_user(uid)
    total = int(stats.get("total", 0) or 0)
    by = stats.get("by_status", {}) or {}
    last_ts = stats.get("last_ts") or L(uid, "尚無紀錄", "No record")

    try:
        contribs = get_user_contributions(uid) or []
        num_contribs = len(contribs)
    except Exception:
        num_contribs = 0

    try:
        favs = get_user_favorites(uid) or []
        num_favs = len(favs)
    except Exception:
        num_favs = 0

    unlocked_badges = 0
    try:
        rules = _badge_rules(uid)
        unlocked_badges = sum(1 for v in rules.values() if v)
    except Exception:
        pass

    lines = []

    # === 查詢次數 ===
    lines.append(L(
        uid,
        f"・你總共查詢過附近廁所：{search_times} 次",
        f"• You searched nearby toilets {search_times} times"
    ))

    lines.append("")
    lines.append(L(uid, "📊 使用回顧", "📊 Usage Summary"))
    lines.append("")

    # === 狀態回報 ===
    if total > 0:
        lines.append(L(
            uid,
            f"・狀態回報次數：{total} 次",
            f"• Status reports: {total} times"
        ))

        parts = []

        mapping = {
            "恢復正常": ("✅", "Back to normal"),
            "有人排隊": ("🟡", "Queue"),
            "缺衛生紙": ("🧻", "No toilet paper"),
            "暫停使用": ("⛔", "Out of service"),
        }

        for zh_key, (emo, en_label) in mapping.items():
            c = int(by.get(zh_key, 0) or 0)
            if c > 0:
                parts.append(
                    L(
                        uid,
                        f"{emo}{zh_key} {c} 次",
                        f"{emo}{en_label} {c}"
                    )
                )

        if parts:
            lines.append(L(
                uid,
                "  └ 狀態類型：" + "｜".join(parts),
                "  └ Status types: " + " | ".join(parts)
            ))

        lines.append(L(
            uid,
            f"・最近一次回報時間：{last_ts}",
            f"• Last report time: {last_ts}"
        ))
    else:
        lines.append(L(
            uid,
            "・目前還沒有任何狀態回報紀錄",
            "• No status reports yet"
        ))

    lines.append("")

    # === 新增廁所 & 最愛 ===
    lines.append(L(
        uid,
        f"・你新增的廁所：{num_contribs} 間",
        f"• Toilets you added: {num_contribs}"
    ))
    lines.append(L(
        uid,
        f"・你收藏的最愛廁所：{num_favs} 間",
        f"• Favorite toilets: {num_favs}"
    ))

    # === 徽章 ===
    lines.append("")
    if unlocked_badges > 0:
        lines.append(L(
            uid,
            f"🏅 已解鎖徽章數：{unlocked_badges} 個（可輸入「徽章」查看詳細）",
            f"🏅 Badges unlocked: {unlocked_badges} (type 'Badges' to view)"
        ))
    else:
        lines.append(L(
            uid,
            "🏅 還沒解鎖徽章，試著多回報幾次狀態就會慢慢解鎖囉！",
            "🏅 No badges unlocked yet. Try reporting more status updates!"
        ))

    lines.append("")
    lines.append(L(
        uid,
        "🔁 小提醒：可以輸入「附近廁所」或傳送位置，我會幫你找最近的廁所 🚽",
        "🔁 Tip: Type 'Nearby toilets' or share your location to find toilets 🚽"
    ))

    lines.append("")
    lines.append(L(
        uid,
        "🤖 查看 AI 為你生成的個人化使用分析：",
        "🤖 View your AI-generated personal usage summary:"
    ))
    base = _base_url()
    lines.append(f"👉 {base}/ai_usage_summary_page/{uid}")

    return "\n".join(lines)

def build_ai_usage_summary(uid: str) -> str:
    """
    用 AI 幫使用者做『個人使用回顧』總結。
    - 有資料時：呼叫 OpenAI 產生精簡的 Wrapped 風格文字
    - 資料太少時：直接回固定提示，不浪費 AI 流量
    - 沒有 AI client 時：退回原本的文字版使用回顧
    """
    # 先拿你原本的資料來源
    search_times = get_search_count(uid)  # 資料表 search_log
    stats = _stats_for_user(uid)          # 狀態回報統計

    total = int(stats.get("total", 0) or 0)
    by = stats.get("by_status", {}) or {}
    last_ts = stats.get("last_ts") or L(uid, "尚無紀錄", "No record")

    try:
        contribs = get_user_contributions(uid) or []
        num_contribs = len(contribs)
    except Exception:
        num_contribs = 0

    try:
        favs = get_user_favorites(uid) or []
        num_favs = len(favs)
    except Exception:
        num_favs = 0

    # 徽章數
    unlocked_badges = 0
    try:
        rules = _badge_rules(uid)
        unlocked_badges = sum(1 for v in rules.values() if v)
    except Exception:
        pass

    # 🔹 如果幾乎沒有任何紀錄，就不要浪費 AI，直接回固定文字
    if (search_times == 0 and total == 0 and
        num_contribs == 0 and num_favs == 0 and
        unlocked_badges == 0):
        return L(
            uid,
            "目前還沒有足夠的使用紀錄可以產生 AI 使用回顧喔～\n"
            "可以多多使用「附近廁所」「狀態回報」「新增廁所」「收藏最愛」，\n"
            "之後我會幫你做一份專屬的使用報告 🙌",
            "Not enough usage data yet to generate an AI usage summary.\n"
            "Try using Nearby Toilets, Status Report, Add Toilet, and Favorites more often.\n"
            "I’ll prepare a personalized report for you soon 🙌"
        )

    # 🔸 client 防呆（避免 client 尚未初始化就被呼叫）
    _client = globals().get("client", None)
    if _client is None:
        return build_usage_review_text(uid)

    # 🔹 每個使用者「AI 使用回顧」每天最多觸發 AI_DAILY_LIMIT 次
    ok, used = _ai_quota_check_and_inc(f"usage:{uid or 'anonymous'}")
    if not ok:
        base = build_usage_review_text(uid)
        return base + "\n\n（今日 AI 使用回顧次數已達上限，明天再來看看新的分析吧 🙏）"

    # ✅ 依使用者語言決定 AI 回覆語言（加防呆）
    try:
        lang = get_user_lang(uid)
    except Exception:
        lang = "zh"

    payload = {
        "search_times": search_times,
        "status_total": total,
        "status_by_type": by,
        "last_status_time": last_ts,
        "contributions": num_contribs,
        "favorites": num_favs,
        "unlocked_badges": unlocked_badges,
    }

    try:
        import json
        payload_json = json.dumps(payload, ensure_ascii=False)

        # ✅ 中英 prompt 分離（避免模型語言混亂）
        prompt_zh = f"""
你是一個溫暖的生活小助手，要幫使用者總結他使用「智慧廁所助手」的情況。

下面是一位使用者的使用統計資料（JSON）：
{payload_json}

請根據這些數據，幫他產生一段「個人使用回顧」，要求如下：
- 使用繁體中文
- 整體篇幅控制在 4～7 行以內
- 第 1 行：Wrapped 風格的一句開場總結
- 接著列出 3～5 點重點（用條列）
  - 查詢附近廁所次數
  - 狀態回報次數、最常見的狀態類型
  - 新增廁所數
  - 收藏最愛數
  - 解鎖徽章數（若有）
- 最後 1 行：一句鼓勵或小建議

請直接輸出給使用者看的內容，不要再出現 JSON 或技術描述。
        """.strip()

        prompt_en = f"""
You are a warm, friendly assistant summarizing a user's usage of the "Smart Toilet Assistant".

Here is the user's usage stats (JSON):
{payload_json}

Write a short "usage recap" with:
- English only
- 4–7 lines total
- Line 1: a Wrapped-style headline
- Then 3–5 bullet highlights (searches, status reports + most common types, contributions, favorites, badges)
- Final line: a short encouragement or tip

Output user-facing text only. Do NOT include JSON or technical descriptions.
        """.strip()

        prompt = prompt_en if lang == "en" else prompt_zh
        system_msg = (
            "You are a friendly assistant that writes a short usage recap in English."
            if lang == "en"
            else "你是一個幫忙做使用回顧的生活小助手，說話親切、簡潔，用繁體中文。"
        )

        resp = _client.chat.completions.create(
            model=AI_MODEL,
            messages=[
                {"role": "system", "content": system_msg},
                {"role": "user", "content": prompt}
            ],
        )

        summary = (resp.choices[0].message.content or "").strip()
        return summary or build_usage_review_text(uid)

    except Exception as e:
        logging.error(f"AI usage summary error: {e}", exc_info=True)
        return build_usage_review_text(uid)

def build_ai_nearby_recommendation(uid: str, toilets):
    """
    依據附近廁所清單，呼叫 OpenAI 幫忙產生一段推薦說明文字。
    - 如果沒有 AI 金鑰 / 沒有廁所資料，就直接回空字串，不影響原本流程
    - 每位使用者每天 AI 推薦次數有限，超過就回提示文字
    """
    if client is None:
        return ""
    if not toilets:
        return ""

    # 🔹 每個使用者「AI 推薦附近廁所」每天最多觸發 AI_DAILY_LIMIT 次
    try:
        quota_key = uid or "anonymous"
        ok, used = _ai_quota_check_and_inc(f"nearby:{quota_key}")
    except Exception as e:
        logging.warning(f"AI nearby quota check failed: {e}")
        ok = True  # quota 壞掉時當作不限制

    if not ok:
        return L(
            uid,
            "今天 AI 推薦附近廁所的次數已達每日上限喔～\n"
            "如果還需要查詢，建議先切換回一般模式 👍",
            "You have reached today's AI nearby recommendation limit.\n"
            "Please switch back to normal mode to continue 👍"
        )

    # ✅ 3-3：依使用者語言決定 AI 回覆語言
    lang = get_user_lang(uid)
    lang_rule = "請使用繁體中文回答。" if lang != "en" else "Please answer in English."

    try:
        import json

        # 最多拿前 5 間，避免 token 太大
        indicators = build_feedback_index()
        status_map = build_status_index()

        items = []
        for t in toilets[:5]:
            try:
                lat_s = norm_coord(t["lat"])
                lon_s = norm_coord(t["lon"])
            except Exception:
                continue

            key = (lat_s, lon_s)
            ind = indicators.get(key, {})
            st = status_map.get(key, {})

            items.append({
                "name": t.get("name") or t.get("place_hint") or "未命名廁所",
                "distance_m": int(t.get("distance", 0) or 0),
                "paper": ind.get("paper"),          # "有" / "沒有" / "?"
                "access": ind.get("access"),        # "有" / "沒有" / "?"
                "avg_score": ind.get("avg"),        # 清潔分數平均
                "status": (st.get("status") or ""), # 例如：有人排隊、暫停使用、恢復正常
            })

        if not items:
            return ""

        payload = {
            "uid": uid,
            "nearby_toilets": items
        }

        prompt = f"""
你是一個「智慧廁所助手」的推薦小幫手，使用者剛剛傳了他的位置，我們幫他找到幾間附近的廁所。

下面是整理好的附近廁所資料（JSON）：
{json.dumps(payload, ensure_ascii=False)}

請你根據：
- 距離（distance_m，越小越近）
- 清潔分數 avg_score（數字越高代表越乾淨，如果是 null 代表目前沒有評分）
- 衛生紙狀態 paper（"有"/"沒有"/"?"）
- 無障礙設施 access（"有"/"沒有"/"?"）
- 即時狀態 status（例如：有人排隊、暫停使用、恢復正常）

幫使用者做一段簡短的「推薦說明」，要求：
{lang_rule}
- Keep the total length within 3–5 lines.
- First line: a quick overall summary.
- Then recommend 1–2 toilets (up to 3 max) with brief reasons.
- Final line: a short tip.

Please output user-facing text only. Do NOT include JSON or technical descriptions.
        """.strip()

        resp = client.chat.completions.create(
            model=AI_MODEL,
            messages=[
                {
                    "role": "system",
                    "content": f"You are a friendly assistant that recommends nearby toilets. {lang_rule}"
                },
                {"role": "user", "content": prompt}
            ],
        )

        text = (resp.choices[0].message.content or "").strip()
        return text

    except Exception as e:
        logging.error(f"AI nearby recommendation error: {e}", exc_info=True)
        return ""

# --- 依使用者統計計算解鎖 ---
def _badge_rules(uid: str):
    s = _stats_for_user(uid)
    by = s.get("by_status", {}) or {}
    total = int(s.get("total", 0) or 0)

    def c(k):
        return int(by.get(k, 0) or 0)

    return {
        "first": total >= 1,
        "helper10": total >= 10,
        "pro_reporter": total >= 20,
        "helper50": total >= 50,
        "tissue_guard": c("缺衛生紙") >= 3,
        "tissue_master": c("缺衛生紙") >= 10,
        "queue_scout": c("有人排隊") >= 3,
        "queue_commander": c("有人排隊") >= 10,
        "maintenance_watcher": c("暫停使用") >= 3,
        "good_news": c("恢復正常") >= 5,
    }

# --- 圖像/名稱設定（把 icon 檔放進 /static/badges/，檔名可依你實際素材調整）---
# --- 圖像/名稱設定（把 icon 檔放進 /static/badges/，檔名可依你實際素材調整）---
# ✅ name 改為 {zh,en}，讓「徽章/成就」標題也能跟著語言切換（避免只有 UI 變、內容還是中文）
BADGE_CONFIG = [
    {"key":"first",               "name":{"zh":"新手報到",     "en":"First Report"},          "icon":"/static/badges/first.png"},
    {"key":"helper10",            "name":{"zh":"勤勞小幫手",   "en":"Helpful Reporter"},      "icon":"/static/badges/helper10.png"},
    {"key":"pro_reporter",        "name":{"zh":"資深回報員",   "en":"Pro Reporter"},          "icon":"/static/badges/pro_reporter.png"},
    {"key":"helper50",            "name":{"zh":"超級幫手",     "en":"Super Helper"},          "icon":"/static/badges/helper50.png"},
    {"key":"tissue_guard",        "name":{"zh":"紙巾守護者",   "en":"Tissue Guardian"},       "icon":"/static/badges/tissue_guard.png"},
    {"key":"tissue_master",       "name":{"zh":"紙巾總管",     "en":"Tissue Manager"},        "icon":"/static/badges/tissue_master.png"},
    {"key":"queue_scout",         "name":{"zh":"排隊偵查員",   "en":"Queue Scout"},           "icon":"/static/badges/queue_scout.png"},
    {"key":"queue_commander",     "name":{"zh":"排隊指揮官",   "en":"Queue Commander"},       "icon":"/static/badges/queue_commander.png"},
    {"key":"maintenance_watcher", "name":{"zh":"維運守護者",   "en":"Maintenance Watcher"},   "icon":"/static/badges/maintenance_watcher.png"},
    {"key":"good_news",           "name":{"zh":"好消息分享員", "en":"Good News Messenger"},   "icon":"/static/badges/good_news.png"},
]

# --- 取代原本的 /api/badges 路由 ---

# --- 取代原本的 /api/badges 路由 ---
@app.route("/api/badges")
def api_badges():
    uid = request.args.get("user_id", "").strip()
    lang = resolve_lang(uid=uid, lang=request.args.get("lang"))

    unlocked_map = _badge_rules(uid)
    items = []
    for b in BADGE_CONFIG:
        name = b.get("name") or {}
        if isinstance(name, dict):
            display_name = name.get(lang) or name.get("zh") or ""
        else:
            display_name = str(name)

        items.append({
            "key": b["key"],
            "name": display_name,
            "icon": b["icon"],
            "unlocked": bool(unlocked_map.get(b["key"], False)),
        })
    return {"ok": True, "badges": items}, 200

# === 舊路由保留===
@app.route("/toilet_feedback/<toilet_name>")
def toilet_feedback(toilet_name):
    """Legacy name-based feedback page; use coordinate page."""
    liff_id = _get_liff_status_id()
    uid = (request.args.get("uid") or "").strip()
    lang = (request.args.get("lang") or "").strip().lower()
    if uid and not lang:
        try:
            lang = _user_lang_q(uid)
        except Exception:
            lang = "zh"
        qs = request.args.to_dict(flat=True)
        qs["lang"] = lang
        return redirect(request.path + "?" + urllib.parse.urlencode(qs), code=302)
    return render_template(
        "toilet_feedback.html",
        toilet_name=toilet_name,
        summary="請改用座標版入口（卡片上的『查詢回饋（座標）』）。",
        feedbacks=[], address="", avg_pred_score=("N/A" if lang == "en" else "未預測"),
        lat="", lon="", liff_id=liff_id, uid=uid, lang=(lang if lang in ["en", "zh"] else "zh")
    )

# === 新路由 ===
@app.route("/toilet_feedback_by_coord/<lat>/<lon>")
def toilet_feedback_by_coord(lat, lon):
    liff_id = _get_liff_status_id()
    uid = (request.args.get("uid") or "").strip()
    lang = (request.args.get("lang") or "").strip().lower()
    if uid and not lang:
        try:
            lang = _user_lang_q(uid)
        except Exception:
            lang = "zh"
        qs = request.args.to_dict(flat=True)
        qs["lang"] = lang
        return redirect(request.path + "?" + urllib.parse.urlencode(qs), code=302)

    if not POSTGRES_ENABLED:
        return render_template(
            "toilet_feedback.html",
            toilet_name=f"廁所（{lat}, {lon}）",
            summary="（回饋資料庫尚未就緒）",
            feedbacks=[], address=f"{lat},{lon}", avg_pred_score=("N/A" if lang == "en" else "未預測"),
            lat=lat, lon=lon, liff_id=liff_id, uid=uid, lang=(lang if lang in ["en", "zh"] else "zh")
        )

    try:
        name = f"廁所（{lat}, {lon}）"
        summary = get_feedback_summary_by_coord(lat, lon)
        feedbacks = get_feedbacks_by_coord(lat, lon)
        scores = []
        for fb in feedbacks:
            try:
                sc = fb.get("cleanliness_score")
                if sc not in (None, ""):
                    scores.append(float(sc))
            except Exception:
                pass
        avg_pred_score = round(sum(scores) / len(scores), 2) if scores else "未預測"
        return render_template(
            "toilet_feedback.html",
            toilet_name=name, summary=summary, feedbacks=feedbacks, address=f"{lat},{lon}",
            avg_pred_score=avg_pred_score, lat=lat, lon=lon,
            liff_id=liff_id, uid=uid, lang=(lang if lang in ["en", "zh"] else "zh")
        )
    except Exception as e:
        logging.error(f"❌ 渲染回饋頁面（Neon 座標）錯誤: {e}", exc_info=True)
        return "查詢失敗", 500

# === 清潔度趨勢（名稱版別名） ===
@app.route("/get_clean_trend/<path:toilet_name>")
def get_clean_trend_by_name(toilet_name):
    # Name-based lookup is no longer supported. Use coordinate API instead.
    return {"success": True, "data": []}, 200

# === 清潔度趨勢 API ===
@app.route("/get_clean_trend_by_coord/<lat>/<lon>")
def get_clean_trend_by_coord(lat, lon):
    if not POSTGRES_ENABLED:
        return {"success": True, "data": []}, 200
    try:
        rows = _fetch_feedback_pg_by_coord(lat, lon, tol=1e-4)
        data = []
        for row in rows:
            created = row.get("created_at")
            t = created.isoformat() if hasattr(created, "isoformat") else str(created or "")
            score = row.get("cleanliness_score")
            try:
                if score is None and row.get("rating") is not None:
                    score = float(row.get("rating"))
                if score is not None:
                    data.append({"t": t, "score": round(float(score), 2)})
            except Exception:
                continue
        data.sort(key=lambda d: d["t"])
        return {"success": True, "data": data}, 200
    except Exception as e:
        logging.error(f"❌ 趨勢 API（Neon 座標版）錯誤: {e}", exc_info=True)
        return {"success": False, "data": []}, 500

# === AI 回饋摘要頁面 ===
@app.route("/ai_feedback_summary_page/<lat>/<lon>")
def ai_feedback_summary_page(lat, lon):
    """
    顯示某一個廁所（用座標表示）的 AI 回饋摘要頁面。
    前端會在這個頁面裡用 JS 呼叫 /api/ai_feedback_summary/<lat>/<lon>。
    """
    uid = (request.args.get("uid") or "").strip()

    base = PUBLIC_URL.rstrip("/") if PUBLIC_URL else request.url_root.rstrip("/")
    # 給前端 JS 用的 API URL（順便把 uid 帶進去，用來做每日額度控制）
    api_url = f"{base}/api/ai_feedback_summary/{lat}/{lon}"
    if uid:
        api_url += f"?uid={quote(uid)}"

    # 順便做一個「去留下回饋」的連結（就算沒回饋也可以用）
    feedback_url = (
        f"{base}/feedback_form/"
        f"{quote('這間廁所')}/{quote(lat + ',' + lon)}"
        f"?lat={lat}&lon={lon}&address={quote(lat + ',' + lon)}"
    )

    return render_template(
        "ai_feedback_summary.html",
        lat=lat,
        lon=lon,
        api_url=api_url,
        feedback_url=feedback_url,
        uid=uid,
    )

@app.route("/ai_usage_summary_page/<uid>")
def ai_usage_summary_page(uid):
    text = build_ai_usage_summary(uid)
    return render_template(
        "ai_usage_summary.html",
        uid=uid,
        summary=text
    )

# === AI 回饋摘要 API（放在清潔度趨勢 API 的下面） ===
AI_MODEL = os.getenv("AI_MODEL", "gpt-4o-mini")
AI_KEY   = os.getenv("OPENAI_API_KEY", "")
client   = OpenAI(api_key=AI_KEY) if AI_KEY else None

# --- AI 每日額度控制（方案 D：同一使用者每天最多觸發幾次 AI） ---
AI_DAILY_LIMIT = int(os.getenv("AI_DAILY_LIMIT", "3"))  # 預設 3 次/人/天

_ai_quota_lock = threading.Lock()
_ai_quota = {}  # key: (usage_key, date_str) -> count


def _ai_quota_check_and_inc(key: str):
    today = datetime.now(TW_TZ).strftime("%Y-%m-%d")

    conn = _get_db()
    cur = conn.cursor()

    cur.execute("SELECT count FROM ai_quota WHERE key=? AND date=?", (key, today))
    row = cur.fetchone()
    cnt = row[0] if row else 0

    if cnt >= AI_DAILY_LIMIT:
        conn.close()
        return False, cnt

    if row:
        cur.execute("UPDATE ai_quota SET count=? WHERE key=? AND date=?", (cnt+1, key, today))
    else:
        cur.execute("INSERT INTO ai_quota (key, date, count) VALUES (?, ?, ?)", (key, today, 1))

    conn.commit()
    conn.close()

    return True, cnt+1

from flask import jsonify
import json

@app.route("/api/ai_feedback_summary/<lat>/<lon>")
def api_ai_feedback_summary(lat, lon):
    """Read feedback from Neon/Postgres and ask OpenAI for a summary."""
    uid = (request.args.get("uid") or "").strip()

    try:
        if not POSTGRES_ENABLED:
            return jsonify({
                "success": False,
                "message": L(uid, "回饋資料庫尚未就緒，請稍後再試", "Feedback storage not ready, please try again later")
            }), 503

        if client is None:
            return jsonify({
                "success": False,
                "message": L(uid, "AI 金鑰尚未設定", "AI key not configured")
            }), 500

        lang = resolve_lang(uid=uid, lang=request.args.get("lang"))
        lang_rule = "請使用繁體中文回答。" if lang != "en" else "Please answer in English."
        system_msg = (
            f"You analyze restroom feedback and summarize it clearly. {lang_rule}"
            if lang == "en"
            else f"你負責分析廁所回饋並清楚摘要重點。{lang_rule}"
        )

        lat_f, lon_f = _parse_lat_lon(lat, lon)
        if lat_f is None or lon_f is None:
            return jsonify({
                "success": False,
                "message": L(uid, "lat/lon 格式錯誤", "Invalid latitude / longitude")
            }), 400

        matched = []
        rows = _fetch_feedback_pg_by_coord(lat_f, lon_f, tol=1e-4, limit=FEEDBACK_LOOKBACK_LIMIT)
        for row in rows:
            created = row.get("created_at")
            created_s = created.isoformat() if hasattr(created, "isoformat") else str(created or "")
            matched.append({
                "rating": str(row.get("rating") or ""),
                "paper": row.get("toilet_paper") or "",
                "access": row.get("accessibility") or "",
                "comment": row.get("comment") or "",
                "created_at": created_s,
            })

        if not matched:
            return jsonify({
                "success": True,
                "summary": "",  # 讓前端依 lang 顯示自己的 no_data 文案，避免混語
                "data": [],
                "has_data": False
            }), 200

        # 最多送 30 筆給 AI
        matched = matched[:30]

        # 2️⃣ 每日 AI 額度控制（uid → fallback IP）
        xff = (request.headers.get("X-Forwarded-For") or "").split(",")[0].strip()
        ip = xff or (request.remote_addr or "unknown")
        quota_key = uid or f"ip:{ip}"

        ok, used = _ai_quota_check_and_inc(f"fb:{quota_key}")
        if not ok:
            return jsonify({
                "success": True,
                "summary": L(
                    uid,
                    "今天 AI 摘要查詢次數已達上限，明天再來看看最新的分析吧 🙏",
                    "You’ve reached today’s AI summary limit. Please try again tomorrow 🙏"
                ),
                "data": matched,
                "has_data": True,
                "limit_reached": True
            }), 200

        # 3️⃣ 組 AI Prompt（依語言）
        matched_json = json.dumps(matched, ensure_ascii=False)

        if lang == "en":
            prompt = f"""
You are a restroom cleanliness analysis assistant.

Please read the following feedback data (JSON format) and provide:
1. Common recent issues (e.g. lack of toilet paper, slippery floor, odor, broken facilities)
2. Overall user sentiment (positive / neutral / negative) with a brief explanation
3. Cleanliness trend (getting cleaner / getting worse / mostly stable). If data is insufficient, explain why.
4. A concise recommendation in **no more than 3 lines**

Please respond in **English**, using bullet points or short sentences.

Feedback data (JSON):
{matched_json}
            """.strip()
        else:
            prompt = f"""
你是一個廁所清潔度分析助理，請閱讀以下回饋資料（JSON 格式），並輸出：

1. 最近常見的主要問題（例如：衛生紙不足、地板濕滑、異味、設備老舊等）
2. 使用者整體情緒傾向（正面 / 中性 / 負面），簡短說明原因
3. 清潔度狀態的趨勢（變乾淨 / 變髒 / 大致持平），如果資料不足請說明
4. 最後請用三行以內，給出一段總結建議

請使用繁體中文、條列式或短句，讓一般使用者容易閱讀。

以下是回饋資料（JSON）：
{matched_json}
            """.strip()

        ai_resp = client.chat.completions.create(
            model=AI_MODEL,
            messages=[
                {"role": "system", "content": system_msg},
                {"role": "user", "content": prompt}
            ]
        )

        summary = (ai_resp.choices[0].message.content or "").strip()

        return jsonify({
            "success": True,
            "summary": summary,
            "data": matched,
            "has_data": True
        }), 200

    except Exception as e:
        logging.error(f"AI summary error: {e}", exc_info=True)
        return jsonify({
            "success": False,
            "message": L(uid, "AI 發生錯誤，請稍後再試", "AI error, please try again later")
        }), 500

# === 同意頁面 / 隱私頁 ===
def _get_liff_consent_id() -> str:
    return (os.getenv("LIFF_CONSENT_ID") or "").strip()

@app.route("/consent", methods=["GET"])
def render_consent_page():
    liff_id = (os.getenv("LIFF_ID") or "").strip()   # 改成讀 consent 專用 ID

    if not liff_id:
        logging.error("LIFF_CONSENT_ID not set")
        return "LIFF_CONSENT_ID not set on server", 500

    return render_template(
        "consent.html",
        liff_id=liff_id
    )
@app.route("/privacy", methods=["GET"])
def render_privacy_page():
    return render_template("privacy_policy.html")

# 狀態 LIFF 頁面
@app.route("/status_liff")
def status_liff():
    liff_id = _get_liff_status_id()
    public_url = os.getenv("PUBLIC_URL", "").rstrip("/")

    # ✅ 語言：LIFF 沒辦法自動知道你在聊天裡切的語言，所以用 querystring 帶 uid/lang
    uid = (request.args.get("uid") or "").strip()
    lang = (request.args.get("lang") or "").strip().lower()

    # 如果有 uid 但沒帶 lang，就依資料庫記錄自動補上 lang，避免前端還要自己算
    if uid and not lang:
        try:
            lang = "en" if get_user_lang(uid) == "en" else "zh"
        except Exception:
            lang = "zh"
        # 保留原本的其他 querystring（如 lat/lon）
        qs = request.args.to_dict(flat=True)
        qs["lang"] = lang
        return redirect(request.path + "?" + urllib.parse.urlencode(qs), code=302)

    if not liff_id:
        logging.error("LIFF_STATUS_ID / LIFF_ID_STATUS / LIFF_ID not set")
        return "LIFF ID not set", 500

    if not public_url:
        logging.error("PUBLIC_URL not set")
        return "PUBLIC_URL not set", 500

    return render_template(
        "status_liff.html",
        liff_id=liff_id,
        public_url=public_url,
        uid=uid,
        lang=(lang if lang in ["en","zh"] else "zh")
    )

# === LIFF 同意 API（新增：微節流＋失敗入背景佇列，回 200） ===
_last_consent_ts = {}
CONSENT_MIN_INTERVAL = float(os.getenv("CONSENT_MIN_INTERVAL", "1.0"))

@app.route("/api/consent", methods=["POST"])
def api_consent():
    try:
        payload = request.get_json(force=True, silent=False) or {}
        agreed = bool(payload.get("agree"))
        user_id = (payload.get("userId") or "").strip()
        display_name = payload.get("displayName") or ""
        source_type = payload.get("sourceType") or ""
        ua = payload.get("ua") or request.headers.get("User-Agent","")
        ts = payload.get("ts") or datetime.now(TW_TZ).isoformat()

        if not user_id:
            logging.warning(f"/api/consent missing userId. payload={payload}")
            return {"ok": False, "message": "缺少 userId"}, 400

        now = time.time()
        last = _last_consent_ts.get(user_id, 0.0)
        if now - last < CONSENT_MIN_INTERVAL:
            return {"ok": True, "message": "accepted"}, 200
        _last_consent_ts[user_id] = now

        ok = upsert_consent(user_id, agreed, display_name, source_type, ua, ts)
        if not ok:
            def job():
                try:
                    upsert_consent(user_id, agreed, display_name, source_type, ua, ts)
                except Exception:
                    pass
            with _consent_lock:
                if len(_consent_q) < 1000:
                    _consent_q.append(job)
            return {"ok": True, "message": "queued"}, 200

        return {"ok": True}, 200
    except Exception as e:
        logging.error(f"/api/consent 失敗: {e}")
        return {"ok": False}, 500

@app.route("/_debug_predict")
def _debug_predict():
    try:
        r = int(request.args.get("rating"))
        paper = request.args.get("paper", "沒注意")
        acc = request.args.get("access", "沒注意")

        paper_map = {"有": 1, "沒有": 0, "沒注意": 0}
        access_map = {"有": 1, "沒有": 0, "沒注意": 0}
        feat = [r, paper_map.get(paper, 0), access_map.get(acc, 0)]
        exp = expected_from_feats([feat])

        return {
            "ok": True,
            "input": {"rating": r, "paper": paper, "access": acc},
            "expected": exp
        }, 200
    except Exception as e:
        logging.error(e)
        return {"ok": False}, 500

def _short_txt(s, n=60):
    try:
        s = (s or "").strip()
        return s if len(s) <= n else (s[:n-1] + "…")
    except Exception:
        return s

# === 建立 Flex ===
def create_toilet_flex_messages(toilets, uid=None, query_id=None):
    indicators = build_feedback_index()
    status_map = build_status_index()

    # === 資料來源顯示對照（中/英）===
    SOURCE_LABEL = {
        "public_csv": ("政府開放資料", "Government Open Data"),
        "sheet": ("使用者新增", "User Added"),
        "osm": ("OpenStreetMap", "OpenStreetMap"),
        "user": ("使用者新增", "User Added"),
        "favorite": ("我的最愛", "My Favorites"),
    }

    # === 狀態（中/英）===
    STATUS_EN = {
        "恢復正常": "Back to normal",
        "有人排隊": "Queue present",
        "缺衛生紙": "No toilet paper",
        "暫停使用": "Out of service",
    }

    bubbles = []
    for toilet in toilets[:5]:
        actions = []

        lat_s = norm_coord(toilet['lat'])
        lon_s = norm_coord(toilet['lon'])
        addr_text = toilet.get('address') or L(uid, "（無地址，使用座標）", "(No address, using coordinates)")

        toilet_id = _make_toilet_id(toilet)
        # -------------------------
        # ✅ title（修正：不要先拼中文再 L）
        # -------------------------
        title = (toilet.get('name') or "").strip()
        if (not title) or title == "無名稱":
            ph = (toilet.get("place_hint") or "").strip()

            zh_title = f"{ph}（附近）廁所" if ph else "（未命名）廁所"
            en_title = f"Toilet near {ph}" if ph else "(Unnamed) Toilet"
            title = L(uid, zh_title, en_title)

        # === 來源文字（小小顯示）===
        source_type = toilet.get("type", "")
        src_zh_en = SOURCE_LABEL.get(source_type, ("其他來源", "Other source"))
        source_text = L(uid, src_zh_en[0], src_zh_en[1])

        # 只讀三個欄位（可能為空）
        lvl   = (toilet.get("level") or "").strip()
        pos   = (toilet.get("floor_hint") or "").strip()
        hours = (toilet.get("open_hours") or "").strip()

        # 額外顯示行
        extra_lines = []
        st_obj = status_map.get((lat_s, lon_s))
        if st_obj and st_obj.get("status"):
            st = st_obj["status"]
            emoji = "🟡" if st == "有人排隊" else ("🧻" if st == "缺衛生紙" else ("⛔" if st == "暫停使用" else "✅"))
            st_en = STATUS_EN.get(st, st)

            extra_lines.append({
                "type": "text",
                "text": _short_txt(L(uid, f"{emoji} 狀態：{st}", f"{emoji} Status: {st_en}")),
                "size": "sm", "color": "#666666", "wrap": True
            })

        if lvl or pos:
            if lvl and pos and (lvl.strip().lower() != pos.strip().lower()):
                extra_lines.append({
                    "type": "text",
                    "text": _short_txt(L(uid, f"🏷 樓層：{lvl}", f"🏷 Floor: {lvl}")),
                    "size": "sm", "color": "#666666", "wrap": True
                })
                extra_lines.append({
                    "type": "text",
                    "text": _short_txt(L(uid, f"🧭 位置：{pos}", f"🧭 Location: {pos}")),
                    "size": "sm", "color": "#666666", "wrap": True
                })
            else:
                val = pos or lvl
                extra_lines.append({
                    "type": "text",
                    "text": _short_txt(L(uid, f"🧭 位置/樓層：{val}", f"🧭 Location/Floor: {val}")),
                    "size": "sm", "color": "#666666", "wrap": True
                })

        if hours:
            extra_lines.append({
                "type": "text",
                "text": _short_txt(L(uid, f"🕒 開放：{hours}", f"🕒 Hours: {hours}")),
                "size": "sm", "color": "#666666", "wrap": True
            })

        # 指示燈文字（paper/access/avg）
        ind = indicators.get((lat_s, lon_s), {"paper": "?", "access": "?", "avg": None})

        # ⭐ 評分顯示不分語言
        star_text = f"⭐{ind['avg']}" if ind.get("avg") is not None else "⭐—"

        # 🧻 paper 顯示
        if ind.get("paper") == "有":
            paper_text = L(uid, "🧻有", "🧻Yes")
        elif ind.get("paper") == "沒有":
            paper_text = L(uid, "🧻無", "🧻No")
        else:
            paper_text = "🧻—"

        # ♿ access 顯示
        if ind.get("access") == "有":
            access_text = L(uid, "♿有", "♿Yes")
        elif ind.get("access") == "沒有":
            access_text = L(uid, "♿無", "♿No")
        else:
            access_text = "♿—"

        # 按鈕
        base = _base_url()

        nav_url = (
            f"{base}/go_to_toilet"
            f"?qid={quote(query_id or '')}"
            f"&uid={quote(uid or '')}"
            f"&tid={quote(toilet_id)}"
            f"&lat={quote(lat_s)}"
            f"&lon={quote(lon_s)}"
            f"&name={quote(title)}"
        )

        actions.append({
            "type": "uri",
            "label": L(uid, "導航", "Navigate"),
            "uri": nav_url
        })

        actions.append({
            "type": "uri",
            "label": L(uid, "查詢回饋", "View feedback"),
            "uri": _append_uid_lang(f"{base}/toilet_feedback_by_coord/{lat_s}/{lon_s}", uid, _user_lang_q(uid))
        })

        addr_raw = toilet.get('address') or ""
        addr_param = quote(addr_raw or "-")
        actions.append({
            "type": "uri",
            "label": L(uid, "廁所回饋", "Leave feedback"),
            "uri": (
                f"{base}/feedback_form/"
                f"{quote(title)}/{addr_param}"
                f"?lat={lat_s}&lon={lon_s}&address={quote(addr_raw)}"
            )
        })

        ai_uri = f"{base}/ai_feedback_summary_page/{lat_s}/{lon_s}" + (f"?uid={quote(uid)}" if uid else "")
        actions.append({
            "type": "uri",
            "label": L(uid, "AI 回饋摘要", "AI summary"),
            "uri": ai_uri
        })

        if toilet.get("type") == "favorite" and uid:
            actions.append({
                "type": "postback",
                "label": L(uid, "移除最愛", "Remove favorite"),
                "data": f"remove_fav:{quote(title)}:{lat_s}:{lon_s}"
            })
        elif toilet.get("type") not in ["user", "favorite"] and uid:
            actions.append({
                "type": "postback",
                "label": L(uid, "加入最愛", "Add favorite"),
                "data": f"add:{quote(title)}:{lat_s}:{lon_s}"
            })

        # === 主體內容（加上資料來源）===
        dist = int(toilet.get('distance', 0) or 0)
        dist_text = L(uid, f"{dist} 公尺", f"{dist} m")

        body_contents = [
            {"type": "text", "text": title, "weight": "bold", "size": "lg", "wrap": True},
            {"type": "text", "text": f"{paper_text}  {access_text}  {star_text}", "size": "sm", "color": "#555555", "wrap": True},
            {"type": "text", "text": addr_text, "size": "sm", "color": "#666666", "wrap": True},
        ] + extra_lines + [
            {"type": "text", "text": dist_text, "size": "sm", "color": "#999999"},
            {
                "type": "text",
                "text": L(uid, f"資料來源：{source_text}", f"Source: {source_text}"),
                "size": "xs",
                "color": "#AAAAAA",
                "wrap": True
            }
        ]

        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "contents": body_contents
            },
            "footer": {
                "type": "box",
                "layout": "vertical",
                "spacing": "sm",
                "contents": [
                    {"type": "button", "style": "primary", "height": "sm", "action": actions[0]}
                ] + [
                    {"type": "button", "style": "secondary", "height": "sm", "action": a}
                    for a in actions[1:]
                ]
            }
        }

        bubbles.append(bubble)

    return {"type": "carousel", "contents": bubbles}

# === 列出 我的貢獻 & 刪除 ===
def get_user_contributions(uid):
    """List current user's submitted toilets from Neon."""
    items = []
    if not uid or not POSTGRES_ENABLED:
        return items
    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT id, name, address, lat, lon, created_at, verification_status
            FROM user_toilets
            WHERE user_id = %s
            ORDER BY created_at DESC
            LIMIT 20
        """, (uid,))
        rows = cur.fetchall()
        conn.close()
        for r in rows:
            ts = r.get("created_at")
            status = r.get("verification_status") or "pending"
            items.append({
                "id": r.get("id"),
                "name": r.get("name") or "無名稱",
                "address": r.get("address") or "",
                "lat": float(norm_coord(r.get("lat"))),
                "lon": float(norm_coord(r.get("lon"))),
                "created": ts.isoformat() if hasattr(ts, "isoformat") else str(ts or ""),
                "verification_status": status,
            })
        return items
    except Exception as e:
        logging.error(f"讀取 Neon 我的貢獻失敗：{e}", exc_info=True)
        return items


def create_my_contrib_flex(uid):
    contribs = get_user_contributions(uid)
    if not contribs:
        return None
    status_label = {
        "pending": L(uid, "待審核", "Pending"),
        "approved": L(uid, "已通過", "Approved"),
        "rejected": L(uid, "未通過", "Rejected"),
        "likely": L(uid, "待確認", "Likely"),
    }
    bubbles = []
    for it in contribs[:10]:
        lat_s = norm_coord(it["lat"])
        lon_s = norm_coord(it["lon"])
        st = it.get("verification_status") or "pending"
        actions = [
            {"type": "uri", "label": L(uid, "導航", "Navigate"), "uri": f"https://www.google.com/maps/search/?api=1&query={lat_s},{lon_s}"},
            {"type": "postback", "label": L(uid, "刪除此貢獻", "Delete this contribution"), "data": f"confirm_delete_my_toilet:{it['id']}"}
        ]
        bubble = {
            "type": "bubble",
            "body": {"type": "box", "layout": "vertical", "contents": [
                {"type": "text", "text": it["name"], "size": "lg", "weight": "bold", "wrap": True},
                {"type": "text", "text": it.get("address") or L(uid, "（無地址）", "(No address)"), "size": "sm", "color": "#666666", "wrap": True},
                {"type": "text", "text": L(uid, f"狀態：{status_label.get(st, st)}", f"Status: {status_label.get(st, st)}"), "size": "xs", "color": "#999999", "wrap": True},
                {"type": "text", "text": it.get("created", ""), "size": "xs", "color": "#999999", "wrap": True}
            ]},
            "footer": {"type": "box", "layout": "vertical", "spacing": "sm", "contents": [
                {"type": "button", "style": "primary", "height": "sm", "action": actions[0]},
                {"type": "button", "style": "secondary", "height": "sm", "action": actions[1]},
            ]}
        }
        bubbles.append(bubble)
    return {"type": "carousel", "contents": bubbles}


def delete_my_contribution(uid, toilet_id):
    """Delete current user's submitted toilet from Neon."""
    if not uid or not toilet_id or not POSTGRES_ENABLED:
        return False, "missing_or_postgres_disabled"
    try:
        toilet_id = int(toilet_id)
    except Exception:
        return False, "invalid_id"
    try:
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            DELETE FROM user_toilets
            WHERE id = %s AND user_id = %s
            RETURNING id
        """, (toilet_id, uid))
        row = cur.fetchone()
        conn.commit()
        conn.close()
        try: _CACHE.clear()
        except Exception: pass
        if row:
            return True, "deleted"
        return False, "not_found_or_permission_denied"
    except Exception as e:
        logging.error(f"delete_my_contribution failed: {e}", exc_info=True)
        return False, "exception"

# === Dashboard ===
_DASHBOARD_RANGE_SECONDS = {
    "1h": 3600,
    "1d": 86400,
    "7d": 7 * 86400,
    "30d": 30 * 86400,
    "1y": 365 * 86400,
}

def _dashboard_range_to_sqlite(range_key: str, anchor_date: str = None):
    if anchor_date:
        try:
            base = datetime.strptime(anchor_date, "%Y-%m-%d").replace(tzinfo=TW_TZ)
        except Exception:
            base = datetime.now(TW_TZ)
    else:
        base = datetime.now(TW_TZ)

    now = datetime.now(TW_TZ)

    if range_key == "1h":
        # 1h 維持即時最近一小時
        end = now
        start = end - timedelta(hours=1)
        bucket = "5min"
        labels = [f"{i * 5}分" for i in range(12)]

    elif range_key == "1d":
        # 1d = 指定那一天 00:00 ~ 23:59:59
        start = base.replace(hour=0, minute=0, second=0, microsecond=0)
        end = start + timedelta(days=1)
        bucket = "hour"
        labels = [f"{str(i).zfill(2)}:00" for i in range(24)]

    elif range_key == "7d":
        # 以 anchor_date 為結尾日
        end = base.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=1)
        start = end - timedelta(days=7)
        bucket = "day"
        labels = [(start + timedelta(days=i)).strftime("%m/%d") for i in range(7)]

    elif range_key == "30d":
        end = base.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=1)
        start = end - timedelta(days=30)
        bucket = "day"
        labels = [(start + timedelta(days=i)).strftime("%m/%d") for i in range(30)]

    else:  # 1y
        end = base.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=1)
        start = end - timedelta(days=365)
        bucket = "month"
        labels = []
        cur = start.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
        while cur < end:
            labels.append(cur.strftime("%Y-%m"))
            if cur.month == 12:
                cur = cur.replace(year=cur.year + 1, month=1)
            else:
                cur = cur.replace(month=cur.month + 1)

    return start, end, bucket, labels

def _bucket_label(dt_obj, range_key):
    if dt_obj.tzinfo is None:
        dt_obj = dt_obj.replace(tzinfo=TW_TZ)
    else:
        dt_obj = dt_obj.astimezone(TW_TZ)

    if range_key == "1h":
        return f"{(dt_obj.minute // 5) * 5}分"
    elif range_key == "1d":
        return f"{dt_obj.hour:02d}:00"
    elif range_key in ("7d", "30d"):
        return dt_obj.strftime("%m/%d")
    elif range_key == "1y":
        return dt_obj.strftime("%Y-%m")
    return None

def _generate_dashboard_data(range_key="1h", anchor_date=None):
    start, end, bucket, default_labels = _dashboard_range_to_sqlite(range_key, anchor_date)

    if POSTGRES_ENABLED:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT
                id,
                user_id,
                event_type,
                result_count,
                success,
                response_time_ms,
                lat,
                lon,
                area_name,
                query_text,
                created_at
            FROM analytics_events
            WHERE created_at >= %s AND created_at <= %s
            ORDER BY created_at DESC
        """, (start, end))
        rows = cur.fetchall()
        conn.close()

        events = [dict(r) for r in rows]
        for e in events:
            if isinstance(e.get("created_at"), datetime):
                dt = e["created_at"]
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=TW_TZ)
                dt = dt.astimezone(TW_TZ)
                e["created_at"] = dt.isoformat()
    else:
        conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        cur = conn.cursor()
        cur.execute("""
            SELECT *
            FROM analytics_events
            WHERE created_at >= ? AND created_at <= ?
            ORDER BY created_at DESC
        """, (start.isoformat(), end.isoformat()))
        rows = cur.fetchall()
        conn.close()

        events = [dict(r) for r in rows]

    valid_query_events = [
        e for e in events
        if e["event_type"] == "location_query" and int(e.get("response_time_ms") or 0) > 0
    ]

    total_queries = len(valid_query_events)
    user_ids = [e["user_id"] for e in valid_query_events if e["user_id"]]
    active_users = len(set(user_ids))

    success_events = valid_query_events
    success_count = len([e for e in success_events if int(e.get("success") or 0) == 1])
    success_rate = round((success_count / len(success_events)) * 100, 1) if success_events else 0.0

    response_values = [int(e["response_time_ms"]) for e in valid_query_events if e.get("response_time_ms") is not None]

    instant_responses = [t for t in response_values if t < 50]
    valid_responses = [t for t in response_values if t >= 50]

    avg_response = round(sum(valid_responses) / len(valid_responses)) if valid_responses else 0

    no_result_count = len([e for e in success_events if int(e.get("result_count") or 0) == 0])
    error_count = len([e for e in events if e["event_type"] == "error" or int(e.get("success") or 0) == 0])

    new_users = 0
    returning_users = 0

    if POSTGRES_ENABLED:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        for uid in set(user_ids):
            cur.execute("""
                SELECT MIN(created_at) AS first_seen, COUNT(*) AS cnt
                FROM analytics_events
                WHERE user_id = %s
            """, (uid,))
            r = cur.fetchone()
            if not r:
                continue
            first_seen = r.get("first_seen")
            cnt = r.get("cnt") or 0
            if first_seen:
                if isinstance(first_seen, str):
                    first_seen = datetime.fromisoformat(first_seen.replace("Z", "+00:00"))
                if first_seen.tzinfo is None:
                    first_seen = first_seen.replace(tzinfo=TW_TZ)

                if first_seen >= start:
                    new_users += 1
            if cnt >= 2:
                returning_users += 1
        conn.close()
    else:
        conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        cur = conn.cursor()
        for uid in set(user_ids):
            cur.execute("""
                SELECT MIN(created_at) AS first_seen, COUNT(*) AS cnt
                FROM analytics_events
                WHERE user_id = ?
            """, (uid,))
            r = cur.fetchone()
            if not r:
                continue
            first_seen = r["first_seen"]
            cnt = r["cnt"] or 0
            if first_seen and first_seen >= start.isoformat():
                new_users += 1
            if cnt >= 2:
                returning_users += 1
        conn.close()

    retention_rate = round((returning_users / active_users) * 100, 1) if active_users else 0.0

    trend_map_queries = {label: 0 for label in default_labels}
    trend_map_users = {label: set() for label in default_labels}

    for e in events:
        try:
            raw_time = e.get("created_at") or e.get("time")
            if not raw_time:
                continue

            dt_obj = datetime.fromisoformat(str(raw_time).replace("Z", "+00:00"))
            if dt_obj.tzinfo is None:
                dt_obj = dt_obj.replace(tzinfo=TW_TZ)
            else:
                dt_obj = dt_obj.astimezone(TW_TZ)

            label = _bucket_label(dt_obj, range_key)
            if label not in trend_map_queries:
                continue

            if e.get("event_type") == "location_query" and int(e.get("response_time_ms") or 0) > 0:
                trend_map_queries[label] += 1

            uid = (e.get("user_id") or "").strip()
            if uid:
                trend_map_users[label].add(uid)

        except Exception:
            continue

    trend_queries = [trend_map_queries[label] for label in default_labels]
    trend_users = [len(trend_map_users[label]) for label in default_labels]

    hourly_map = {f"{i:02d}:00": 0 for i in range(24)}
    for e in events:
        try:
            raw_time = e.get("created_at") or e.get("time")
            if not raw_time:
                continue

            dt_obj = datetime.fromisoformat(str(raw_time).replace("Z", "+00:00"))
            if dt_obj.tzinfo is None:
                dt_obj = dt_obj.replace(tzinfo=TW_TZ)
            else:
                dt_obj = dt_obj.astimezone(TW_TZ)

            hourly_key = f"{dt_obj.hour:02d}:00"
            if hourly_key in hourly_map:
                hourly_map[hourly_key] += 1
        except Exception:
            continue

    type_counts = {
        "定位查詢": len([e for e in events if e["event_type"] == "location_query" and int(e.get("response_time_ms") or 0) > 0]),
        "文字查詢": len([e for e in events if e["event_type"] == "text_query"]),
        "點擊結果": len([e for e in events if e["event_type"] == "search_result"]),
        "錯誤": len([e for e in events if e["event_type"] == "error"]),
    }

    area_counter = {}
    for e in events:
        area = e.get("area_name") or "其他區域"
        area_counter[area] = area_counter.get(area, 0) + 1
    areas = sorted(area_counter.items(), key=lambda x: x[1], reverse=True)[:8]

    event_rows = []
    visible_events = [
        e for e in events
        if not (e.get("event_type") == "location_query" and int(e.get("response_time_ms") or 0) <= 0)
    ]
    for e in visible_events[:10]:
        event_rows.append({
            "time": e.get("created_at", ""),
            "user_id": e.get("user_id", "") or "-",
            "event_type": e.get("event_type", ""),
            "result_count": e.get("result_count", 0) or 0,
            "response_time_ms": e.get("response_time_ms", 0) or 0,
            "success": bool(int(e.get("success") or 0))
        })

    response_sorted = sorted(valid_responses)
    median_value = response_sorted[len(response_sorted)//2] if response_sorted else 0
    p95_index = min(len(response_sorted)-1, int(len(response_sorted)*0.95)) if response_sorted else 0
    p95_value = response_sorted[p95_index] if response_sorted else 0

    return {
        "summary": {
            "total_queries": total_queries,
            "active_users": active_users,
            "success_rate": success_rate,
            "avg_response": avg_response,
            "no_result_count": no_result_count,
            "error_count": error_count,
            "retention_rate": retention_rate,
            "instant_responses": len(instant_responses)
        },
        "trend": {
            "labels": default_labels,
            "queries": trend_queries,
            "users": trend_users
        },
        "hourly": {
            "labels": list(hourly_map.keys()),
            "values": list(hourly_map.values())
        },
        "typeData": {
            "labels": list(type_counts.keys()),
            "values": list(type_counts.values())
        },
        "areas": areas,
        "events": event_rows,
        "detail": {
            "totalQueries": {
                "peak": max(trend_queries) if trend_queries else 0,
                "low": min(trend_queries) if trend_queries else 0,
                "avgPerPoint": round(total_queries / len(default_labels)) if default_labels else 0,
                "topTimePoints": sorted(
                    [{"label": default_labels[i], "value": trend_queries[i]} for i in range(len(default_labels))],
                    key=lambda x: x["value"],
                    reverse=True
                )[:5]
            },
            "activeUsers": {
                "inactiveUsersEstimate": max(0, total_queries - active_users),
                "avgQueriesPerUser": f"{(total_queries / active_users):.2f}" if active_users else "0.00",
                "topUserSamples": []
            },
            "successRate": {
                "successCount": success_count,
                "failedCount": max(0, len(success_events) - success_count),
                "successRate": success_rate
            },
            "avgResponse": {
                "min": min(response_values) if response_values else 0,
                "median": median_value,
                "p95": p95_value,
                "max": max(response_values) if response_values else 0
            },
            "newUsers": {
                "newUsers": new_users,
                "existingUsers": max(0, active_users - new_users),
                "newUserRate": f"{(new_users / active_users * 100):.1f}" if active_users else "0.0"
            },
            "retentionRate": {
                "returningUsers": returning_users,
                "oneTimeUsers": max(0, active_users - returning_users),
                "retentionRate": retention_rate
            },
            "noResultCount": {
                "noResultCount": no_result_count,
                "noResultRate": f"{(no_result_count / total_queries * 100):.1f}" if total_queries else "0.0",
                "samples": []
            },
            "errorCount": {
                "errorCount": error_count,
                "errorRate": f"{(error_count / total_queries * 100):.1f}" if total_queries else "0.0",
                "samples": []
            }
        }
    }



# === Demand Gap Dashboard v165：去重、需求群聚與建議設點分析 ===
_GAP_SUMMARY_CACHE = {}
_GAP_SUMMARY_CACHE_TTL = int(os.getenv("GAP_SUMMARY_CACHE_TTL_SECONDS", "180"))


def _gap_cache_get(key):
    try:
        item = _GAP_SUMMARY_CACHE.get(key)
        if not item:
            return None
        ts, data = item
        if time.time() - ts <= _GAP_SUMMARY_CACHE_TTL:
            return data
    except Exception:
        pass
    return None


def _gap_cache_set(key, data):
    try:
        _GAP_SUMMARY_CACHE[key] = (time.time(), data)
        if len(_GAP_SUMMARY_CACHE) > 30:
            oldest = sorted(_GAP_SUMMARY_CACHE.items(), key=lambda kv: kv[1][0])[:10]
            for k, _ in oldest:
                _GAP_SUMMARY_CACHE.pop(k, None)
    except Exception:
        pass


def _safe_float(v, default=None):
    try:
        if v is None or v == "":
            return default
        return float(v)
    except Exception:
        return default


def _gap_parse_dt(v):
    try:
        if isinstance(v, datetime):
            return v
        s = str(v or "").strip()
        if not s:
            return None
        # 支援 PostgreSQL / SQLite 常見字串
        s = s.replace("Z", "+00:00")
        return datetime.fromisoformat(s)
    except Exception:
        try:
            return datetime.strptime(str(v)[:19], "%Y-%m-%d %H:%M:%S")
        except Exception:
            return None


def _gap_day_key(v):
    dt = _gap_parse_dt(v)
    if not dt:
        return "unknown"
    try:
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        dt = dt.astimezone(TW_TZ)
    except Exception:
        pass
    return dt.strftime("%Y-%m-%d")


def _gap_minutes(v):
    dt = _gap_parse_dt(v)
    if not dt:
        return 0
    try:
        return int(dt.timestamp() // 60)
    except Exception:
        return 0


def _gap_user_key(uid):
    if uid:
        return hashlib.sha256(str(uid).encode("utf-8")).hexdigest()[:12]
    return "anon"


def _gap_cell(lat, lon, decimals=3):
    try:
        return f"{round(float(lat), decimals):.{decimals}f},{round(float(lon), decimals):.{decimals}f}"
    except Exception:
        return "unknown"


def _gap_cell_center(cell):
    try:
        a, b = str(cell).split(",", 1)
        return float(a), float(b)
    except Exception:
        return None, None


def _gap_haversine_m(lat1, lon1, lat2, lon2):
    try:
        lat1, lon1, lat2, lon2 = map(float, [lat1, lon1, lat2, lon2])
        R = 6371000.0
        p1, p2 = math.radians(lat1), math.radians(lat2)
        dp = math.radians(lat2 - lat1)
        dl = math.radians(lon2 - lon1)
        a = math.sin(dp/2)**2 + math.cos(p1)*math.cos(p2)*math.sin(dl/2)**2
        return 2 * R * math.asin(math.sqrt(a))
    except Exception:
        return 0


def _gap_google_maps_url(lat, lon):
    try:
        return f"https://www.google.com/maps/search/?api=1&query={float(lat):.6f},{float(lon):.6f}"
    except Exception:
        return ""


def _gap_level(score, unique_users=0, active_days=0):
    try:
        s = float(score or 0)
    except Exception:
        s = 0
    # v2 不只看分數，也看是否跨使用者/跨日期，避免單人連續查詢造成假熱點
    if s >= 80 and (unique_users >= 2 or active_days >= 2):
        return "高可信缺口"
    if s >= 45:
        return "中可信缺口"
    if s >= 18:
        return "低可信缺口"
    return "觀察中"


def _gap_action_label(row):
    no_result = int(row.get("no_result_count") or 0)
    low_result = int(row.get("low_result_count") or 0)
    slow = int(row.get("slow_query_count") or 0)
    total = int(row.get("effective_queries") or row.get("total_queries") or 0)
    unique_users = int(row.get("unique_users") or 0)
    active_days = int(row.get("active_days") or 0)
    no_rate = no_result / max(total, 1)
    low_rate = low_result / max(total, 1)
    slow_rate = slow / max(total, 1)

    confidence = ""
    if unique_users < 2 and active_days < 2:
        confidence = "（但目前獨立性較低，需再觀察）"

    if no_result >= 3 or (total >= 5 and no_rate >= 0.35):
        return "優先現地/地圖確認：疑似設施不足或資料未收錄" + confidence
    if low_result >= 4 or (total >= 6 and low_rate >= 0.55):
        return "優先補資料：檢查附近商場、車站、公園、學校是否漏收" + confidence
    if slow >= 4 or (total >= 6 and slow_rate >= 0.45):
        return "優先補本地資料：降低 OSM 或外部查詢依賴" + confidence
    if total >= 8 or unique_users >= 3:
        return "持續觀察：需求量足夠，可列入人工抽樣清單"
    return "先觀察：資料量仍少"


def _gap_suggestion(row):
    no_result = int(row.get("no_result_count") or 0)
    low_result = int(row.get("low_result_count") or 0)
    slow = int(row.get("slow_query_count") or 0)
    total = int(row.get("effective_queries") or row.get("total_queries") or 0)
    if no_result >= 3 or (total >= 5 and no_result / max(total, 1) >= 0.35):
        return "可能設施不足或資料缺漏，建議優先檢查"
    if low_result >= 4 or (total >= 6 and low_result / max(total, 1) >= 0.50):
        return "候選結果偏少，可能需要補資料或擴充設施"
    if slow >= 4:
        return "查詢耗時偏高，可能依賴外部資料或資料分布不足"
    if total >= 8:
        return "需求量較高，可列為持續觀察區域"
    return "資料量較少，先觀察"


def _gap_sample_event(e):
    lat = _safe_float(e.get("lat"))
    lon = _safe_float(e.get("lon"))
    if lat is None or lon is None:
        return None
    return {
        "created_at": str(e.get("created_at") or ""),
        "lat": round(lat, 6),
        "lon": round(lon, 6),
        "result_count": int(e.get("result_count") or 0),
        "success": int(e.get("success") or 0),
        "response_time_ms": int(e.get("response_time_ms") or 0),
        "area_name": (e.get("area_name") or "其他區域"),
        "map_url": _gap_google_maps_url(lat, lon)
    }


def _gap_add_metrics(obj, event, low_threshold, slow_ms):
    rc = int(event.get("result_count") or 0)
    rt = int(event.get("response_time_ms") or 0)
    success = int(event.get("success") or 0) == 1
    obj["effective_queries"] = obj.get("effective_queries", 0) + 1
    obj["total_queries"] = obj.get("total_queries", 0) + 1  # 相容前端舊欄位
    obj["no_result_count"] = obj.get("no_result_count", 0) + (1 if rc == 0 else 0)
    obj["low_result_count"] = obj.get("low_result_count", 0) + (1 if rc <= low_threshold else 0)
    obj["slow_query_count"] = obj.get("slow_query_count", 0) + (1 if rt >= slow_ms else 0)
    obj["success_count"] = obj.get("success_count", 0) + (1 if success else 0)
    if rt > 0:
        obj.setdefault("response_values", []).append(rt)
    obj.setdefault("user_set", set()).add(event.get("user_key") or "anon")
    obj.setdefault("day_set", set()).add(event.get("day_key") or "unknown")
    obj["raw_queries"] = obj.get("raw_queries", 0) + int(event.get("raw_weight") or 1)


def _gap_finish_row(r):
    vals = r.pop("response_values", [])
    user_set = r.pop("user_set", set())
    day_set = r.pop("day_set", set())
    total = int(r.get("effective_queries") or r.get("total_queries") or 0)
    avg_rt = round(sum(vals) / len(vals)) if vals else 0
    r["avg_response_ms"] = avg_rt
    r["unique_users"] = len(user_set) if isinstance(user_set, set) else int(r.get("unique_users") or 0)
    r["active_days"] = len(day_set) if isinstance(day_set, set) else int(r.get("active_days") or 0)
    r["no_result_rate"] = round((int(r.get("no_result_count") or 0) / max(total, 1)) * 100, 1)
    r["low_result_rate"] = round((int(r.get("low_result_count") or 0) / max(total, 1)) * 100, 1)
    r["slow_query_rate"] = round((int(r.get("slow_query_count") or 0) / max(total, 1)) * 100, 1)

    # Demand Gap Score v2：加入去重後有效需求、獨立使用者與跨日期，降低單人連續查詢灌分
    score = (
        int(r.get("no_result_count") or 0) * 5
        + int(r.get("low_result_count") or 0) * 2
        + int(r.get("slow_query_count") or 0) * 1
        + int(r.get("effective_queries") or 0) * 1
        + int(r.get("unique_users") or 0) * 3
        + int(r.get("active_days") or 0) * 2
    )
    # 若幾乎只有單一使用者同一天，分數打折，但不完全刪除，避免早期資料看不到訊號
    if int(r.get("unique_users") or 0) <= 1 and int(r.get("active_days") or 0) <= 1:
        score *= 0.65
        r["confidence_note"] = "單一使用者/單日訊號，需再觀察"
    elif int(r.get("unique_users") or 0) <= 1:
        score *= 0.80
        r["confidence_note"] = "使用者數偏少，需搭配現地確認"
    else:
        r["confidence_note"] = "可信度較高"

    r["gap_score"] = round(score, 2)
    r["gap_level"] = _gap_level(score, int(r.get("unique_users") or 0), int(r.get("active_days") or 0))
    r["suggestion"] = _gap_suggestion(r)
    r["action_label"] = _gap_action_label(r)
    if r.get("lat") is not None and r.get("lon") is not None:
        r["map_url"] = _gap_google_maps_url(r.get("lat"), r.get("lon"))
    return r


def _gap_cluster_rows(rows, radius_m=500):
    """把相近缺口格點合併為需求群，輸出建議中心點。"""
    candidates = []
    for r in rows:
        lat = _safe_float(r.get("lat"))
        lon = _safe_float(r.get("lon"))
        if lat is None or lon is None:
            continue
        # 只把真的有缺口訊號的點拿去群聚
        if int(r.get("no_result_count") or 0) <= 0 and int(r.get("low_result_count") or 0) <= 0 and int(r.get("slow_query_count") or 0) <= 0:
            continue
        candidates.append(dict(r))

    candidates.sort(key=lambda x: (float(x.get("gap_score") or 0), int(x.get("effective_queries") or 0)), reverse=True)
    used = set()
    clusters = []

    for i, seed in enumerate(candidates):
        if i in used:
            continue
        members = []
        seed_lat, seed_lon = float(seed["lat"]), float(seed["lon"])
        for j, r in enumerate(candidates):
            if j in used:
                continue
            d = _gap_haversine_m(seed_lat, seed_lon, r.get("lat"), r.get("lon"))
            if d <= radius_m:
                used.add(j)
                rr = dict(r)
                rr["distance_to_seed_m"] = round(d, 1)
                members.append(rr)

        if not members:
            continue
        weight_sum = 0.0
        lat_sum = 0.0
        lon_sum = 0.0
        for m in members:
            w = max(float(m.get("gap_score") or 0), 1.0)
            weight_sum += w
            lat_sum += float(m.get("lat") or 0) * w
            lon_sum += float(m.get("lon") or 0) * w
        center_lat = lat_sum / max(weight_sum, 1)
        center_lon = lon_sum / max(weight_sum, 1)
        radius = max([_gap_haversine_m(center_lat, center_lon, m.get("lat"), m.get("lon")) for m in members] or [0])

        area_counts = {}
        for m in members:
            area = m.get("area_name") or "其他區域"
            area_counts[area] = area_counts.get(area, 0) + int(m.get("effective_queries") or 1)
        area_name = sorted(area_counts.items(), key=lambda kv: kv[1], reverse=True)[0][0] if area_counts else "其他區域"

        agg = {
            "cluster_id": f"C{len(clusters)+1}",
            "center": f"{center_lat:.5f},{center_lon:.5f}",
            "lat": round(center_lat, 6),
            "lon": round(center_lon, 6),
            "area_name": area_name,
            "point_count": len(members),
            "radius_m": round(radius),
            "effective_queries": sum(int(m.get("effective_queries") or 0) for m in members),
            "total_queries": sum(int(m.get("effective_queries") or 0) for m in members),
            "raw_queries": sum(int(m.get("raw_queries") or 0) for m in members),
            "no_result_count": sum(int(m.get("no_result_count") or 0) for m in members),
            "low_result_count": sum(int(m.get("low_result_count") or 0) for m in members),
            "slow_query_count": sum(int(m.get("slow_query_count") or 0) for m in members),
            "unique_users": sum(int(m.get("unique_users") or 0) for m in members),
            "active_days": len(set([str(m.get("day_hint") or "") for m in members if m.get("day_hint")])) or max([int(m.get("active_days") or 0) for m in members] or [0]),
            "member_grids": [m.get("grid") for m in members[:8]],
            "sample_queries": sum([m.get("sample_queries") or [] for m in members], [])[:6],
            "map_url": _gap_google_maps_url(center_lat, center_lon),
        }
        agg = _gap_finish_row({**agg, "response_values": sum([m.get("response_values_raw") or [] for m in members], []), "user_set": set(), "day_set": set()})
        # _gap_finish_row 會以空 set 覆蓋 unique_users；補回聚合值並重算關鍵欄位
        agg["unique_users"] = max(sum(int(m.get("unique_users") or 0) for m in members), 0)
        agg["active_days"] = max([int(m.get("active_days") or 0) for m in members] or [0])
        agg["gap_score"] = round(sum(float(m.get("gap_score") or 0) for m in members) + agg["point_count"] * 3, 2)
        agg["gap_level"] = _gap_level(agg["gap_score"], agg["unique_users"], agg["active_days"])
        agg["suggestion"] = _gap_suggestion(agg)
        agg["action_label"] = _gap_action_label(agg)
        if agg["unique_users"] < 2 and agg["active_days"] < 2:
            agg["confidence_note"] = "可能受單人重複查詢影響，展示前建議人工確認"
        else:
            agg["confidence_note"] = "已合併附近點位，較適合做公共設施檢查"
        clusters.append(agg)

    clusters.sort(key=lambda x: (float(x.get("gap_score") or 0), int(x.get("effective_queries") or 0)), reverse=True)
    return clusters


def _build_gap_summary(range_key="30d", anchor_date=None):
    if range_key not in ("1h", "1d", "7d", "30d", "1y"):
        range_key = "30d"

    start, end, _, _ = _dashboard_range_to_sqlite(range_key, anchor_date)

    events = []
    osm_summary = {
        "total_source_calls": 0,
        "osm_calls": 0,
        "osm_success_calls": 0,
        "avg_osm_elapsed_ms": 0,
        "avg_non_osm_elapsed_ms": 0,
        "max_osm_elapsed_ms": 0,
        "osm_reasons": []
    }

    if POSTGRES_ENABLED:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT id, user_id, event_type, result_count, success, response_time_ms,
                   lat, lon, area_name, query_text, created_at
            FROM analytics_events
            WHERE created_at >= %s AND created_at <= %s
              AND event_type = 'location_query'
              AND COALESCE(response_time_ms, 0) > 0
            ORDER BY created_at ASC
        """, (start, end))
        events = [dict(r) for r in cur.fetchall()]

        try:
            cur.execute("""
                SELECT
                  COUNT(*) AS total_source_calls,
                  COUNT(*) FILTER (WHERE used_osm = TRUE OR source_name = 'osm') AS osm_calls,
                  COUNT(*) FILTER (WHERE (used_osm = TRUE OR source_name = 'osm') AND success = TRUE) AS osm_success_calls,
                  AVG(elapsed_ms) FILTER (WHERE used_osm = TRUE OR source_name = 'osm') AS avg_osm_elapsed_ms,
                  AVG(elapsed_ms) FILTER (WHERE NOT (used_osm = TRUE OR source_name = 'osm')) AS avg_non_osm_elapsed_ms,
                  MAX(elapsed_ms) FILTER (WHERE used_osm = TRUE OR source_name = 'osm') AS max_osm_elapsed_ms
                FROM source_query_logs
                WHERE created_at >= %s AND created_at <= %s
            """, (start, end))
            r = dict(cur.fetchone() or {})
            osm_summary.update({
                "total_source_calls": int(r.get("total_source_calls") or 0),
                "osm_calls": int(r.get("osm_calls") or 0),
                "osm_success_calls": int(r.get("osm_success_calls") or 0),
                "avg_osm_elapsed_ms": round(float(r.get("avg_osm_elapsed_ms") or 0), 2),
                "avg_non_osm_elapsed_ms": round(float(r.get("avg_non_osm_elapsed_ms") or 0), 2),
                "max_osm_elapsed_ms": int(r.get("max_osm_elapsed_ms") or 0),
            })
            cur.execute("""
                SELECT COALESCE(reason, 'unknown') AS reason, COUNT(*) AS count
                FROM source_query_logs
                WHERE created_at >= %s AND created_at <= %s
                  AND (used_osm = TRUE OR source_name = 'osm')
                GROUP BY COALESCE(reason, 'unknown')
                ORDER BY count DESC
                LIMIT 8
            """, (start, end))
            osm_summary["osm_reasons"] = [dict(x) for x in cur.fetchall()]
        except Exception as e:
            logging.warning(f"gap osm summary skipped: {e}")

        conn.close()
    else:
        conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        cur = conn.cursor()
        cur.execute("""
            SELECT id, user_id, event_type, result_count, success, response_time_ms,
                   lat, lon, area_name, query_text, created_at
            FROM analytics_events
            WHERE created_at >= ? AND created_at <= ?
              AND event_type = 'location_query'
              AND COALESCE(response_time_ms, 0) > 0
            ORDER BY created_at ASC
        """, (start.isoformat(), end.isoformat()))
        events = [dict(r) for r in cur.fetchall()]
        conn.close()

    raw_total_queries = len(events)
    LOW_RESULT_THRESHOLD = int(os.getenv("GAP_LOW_RESULT_THRESHOLD", "2"))
    SLOW_QUERY_MS = int(os.getenv("GAP_SLOW_QUERY_MS", "5000"))
    DEDUPE_MINUTES = int(os.getenv("GAP_DEDUPE_MINUTES", "10"))
    CLUSTER_RADIUS_M = int(os.getenv("GAP_CLUSTER_RADIUS_M", "500"))

    # 1) 同人同地短時間去重：同 user、同約 100m 格點、10 分鐘內，只算一筆有效需求
    deduped = []
    last_seen = {}
    duplicate_skipped = 0
    for e in events:
        lat = _safe_float(e.get("lat"))
        lon = _safe_float(e.get("lon"))
        if lat is None or lon is None:
            continue
        user_key = _gap_user_key(e.get("user_id"))
        cell_key = _gap_cell(lat, lon, 3)
        minute = _gap_minutes(e.get("created_at"))
        # 沒 user_id 時，用較短時間窗，避免把不同使用者誤合併
        identity = user_key if user_key != "anon" else f"anon:{cell_key}"
        dedupe_key = (identity, cell_key)
        last_min = last_seen.get(dedupe_key)
        window = DEDUPE_MINUTES if user_key != "anon" else min(3, DEDUPE_MINUTES)
        if last_min is not None and minute and (minute - last_min) <= window:
            duplicate_skipped += 1
            continue
        last_seen[dedupe_key] = minute
        ee = dict(e)
        ee["user_key"] = user_key
        ee["cell_key"] = cell_key
        ee["day_key"] = _gap_day_key(e.get("created_at"))
        ee["raw_weight"] = 1
        deduped.append(ee)

    total_queries = len(deduped)
    no_result_count = 0
    low_result_count = 0
    slow_query_count = 0
    success_count = 0
    response_values = []
    area_map = {}
    grid_map = {}
    all_users = set()
    all_days = set()

    for e in deduped:
        rc = int(e.get("result_count") or 0)
        rt = int(e.get("response_time_ms") or 0)
        success = int(e.get("success") or 0) == 1
        area = (e.get("area_name") or "其他區域").strip() or "其他區域"
        all_users.add(e.get("user_key") or "anon")
        all_days.add(e.get("day_key") or "unknown")

        if success:
            success_count += 1
        if rc == 0:
            no_result_count += 1
        if rc <= LOW_RESULT_THRESHOLD:
            low_result_count += 1
        if rt >= SLOW_QUERY_MS:
            slow_query_count += 1
        if rt > 0:
            response_values.append(rt)

        if area not in area_map:
            area_map[area] = {
                "area_name": area,
                "effective_queries": 0,
                "total_queries": 0,
                "raw_queries": 0,
                "no_result_count": 0,
                "low_result_count": 0,
                "slow_query_count": 0,
                "success_count": 0,
                "response_values": [],
                "user_set": set(),
                "day_set": set(),
            }
        _gap_add_metrics(area_map[area], e, LOW_RESULT_THRESHOLD, SLOW_QUERY_MS)

        lat = _safe_float(e.get("lat"))
        lon = _safe_float(e.get("lon"))
        if lat is not None and lon is not None:
            # 100m 級別格點：先精準聚合，再由 cluster 合成約 500m 建議設點區
            glat = round(lat, 3)
            glon = round(lon, 3)
            gkey = f"{glat:.3f},{glon:.3f}"
            if gkey not in grid_map:
                grid_map[gkey] = {
                    "grid": gkey,
                    "lat": glat,
                    "lon": glon,
                    "area_name": area,
                    "effective_queries": 0,
                    "total_queries": 0,
                    "raw_queries": 0,
                    "no_result_count": 0,
                    "low_result_count": 0,
                    "slow_query_count": 0,
                    "success_count": 0,
                    "response_values": [],
                    "response_values_raw": [],
                    "user_set": set(),
                    "day_set": set(),
                    "day_hint": e.get("day_key"),
                    "sample_queries": [],
                    "map_url": _gap_google_maps_url(glat, glon),
                }
            g = grid_map[gkey]
            _gap_add_metrics(g, e, LOW_RESULT_THRESHOLD, SLOW_QUERY_MS)
            if rt > 0:
                g.setdefault("response_values_raw", []).append(rt)
            sample = _gap_sample_event(e)
            if sample and (rc == 0 or rc <= LOW_RESULT_THRESHOLD or rt >= SLOW_QUERY_MS):
                if len(g.get("sample_queries") or []) < 5:
                    g["sample_queries"].append(sample)

    area_rows = [_gap_finish_row(dict(v)) for v in area_map.values()]
    area_rows.sort(key=lambda x: (x["gap_score"], x["effective_queries"]), reverse=True)

    hotspot_rows = [_gap_finish_row(dict(v)) for v in grid_map.values()]
    hotspot_rows.sort(key=lambda x: (x["gap_score"], x["effective_queries"]), reverse=True)

    clusters = _gap_cluster_rows(hotspot_rows, radius_m=CLUSTER_RADIUS_M)

    avg_response = round(sum(response_values) / len(response_values)) if response_values else 0
    top_area = area_rows[0]["area_name"] if area_rows else "-"
    top_cluster = clusters[0]["center"] if clusters else "-"

    return {
        "ok": True,
        "version": "demand_gap_v2_dedupe_cluster",
        "range": range_key,
        "anchor_date": anchor_date,
        "generated_at": datetime.now(TW_TZ).isoformat(),
        "thresholds": {
            "low_result_threshold": LOW_RESULT_THRESHOLD,
            "slow_query_ms": SLOW_QUERY_MS,
            "dedupe_minutes": DEDUPE_MINUTES,
            "cluster_radius_m": CLUSTER_RADIUS_M,
            "cache_ttl_seconds": _GAP_SUMMARY_CACHE_TTL,
        },
        "summary": {
            "raw_total_queries": raw_total_queries,
            "duplicate_skipped": duplicate_skipped,
            "total_queries": total_queries,
            "effective_queries": total_queries,
            "unique_users": len(all_users),
            "active_days": len(all_days),
            "success_count": success_count,
            "no_result_count": no_result_count,
            "low_result_count": low_result_count,
            "slow_query_count": slow_query_count,
            "avg_response_ms": avg_response,
            "top_gap_area": top_area,
            "top_gap_cluster": top_cluster,
            "cluster_count": len(clusters),
            "no_result_rate": round((no_result_count / max(total_queries, 1)) * 100, 1),
            "low_result_rate": round((low_result_count / max(total_queries, 1)) * 100, 1),
            "slow_query_rate": round((slow_query_count / max(total_queries, 1)) * 100, 1),
        },
        "demand_clusters": clusters[:30],
        "recommended_sites": clusters[:10],
        "area_gaps": area_rows[:30],
        "hotspots": hotspot_rows[:80],
        "precise_hotspots": hotspot_rows[:30],
        "osm_summary": osm_summary,
        "interpretation": [
            "v2 先去除同一使用者、同一地點、短時間內的重複查詢，避免單人連續查詢把缺口分數灌高。",
            "v2 會把附近約 500 公尺內的缺口點合併成需求群，產生建議中心點，比單一查詢點更適合用來討論補資料或新增設施。",
            "建議設點不是直接代表一定要新建廁所，而是代表該區值得先做地圖/現地檢查：可能是資料漏收、室內場域資訊不足，或真的設施覆蓋不足。",
            "若同一需求群有多名獨立使用者、跨多天查詢、查無/低覆蓋比例高，可信度會比單人單日查詢更高。",
            "OSM fallback 或慢查詢高的區域，通常優先做本地資料補強，降低外部 API 延遲。"
        ]
    }


@app.route("/dashboard/gap", methods=["GET"])
def dashboard_gap_page():
    """公共設施需求缺口分析頁。"""
    return render_template("gap.html")


@app.route("/api/gap-summary", methods=["GET"])
def api_gap_summary():
    """公共設施需求缺口分析 API：去重、群聚、建議設點。"""
    try:
        range_key = (request.args.get("range") or "30d").strip()
        if range_key not in ("1h", "1d", "7d", "30d", "1y"):
            range_key = "30d"
        anchor_date = (request.args.get("anchor_date") or "").strip() or None
        force = (request.args.get("force") or "0").strip() == "1"

        cache_key = f"v165:{range_key}:{anchor_date or ''}"
        if not force:
            cached = _gap_cache_get(cache_key)
            if cached is not None:
                out = dict(cached)
                out["cached"] = True
                return jsonify(out)

        data = _build_gap_summary(range_key, anchor_date)
        data["cached"] = False
        _gap_cache_set(cache_key, data)
        return jsonify(data)
    except Exception as e:
        logging.error(f"/api/gap-summary failed: {e}", exc_info=True)
        return jsonify({"ok": False, "error": str(e)}), 500

@app.route("/dashboard", methods=["GET"])
def dashboard_page():
    return render_template("dashboard.html")

@app.route("/api/shadow-ranking-metrics")
def api_shadow_ranking_metrics():
    """Shadow Ranking 比較 API。"""
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "error": "Postgres not enabled"}), 503
    production_version = (request.args.get("production") or "trust_score_2_0").strip() or "trust_score_2_0"
    shadow_version = (request.args.get("shadow") or "nts_1_0").strip() or "nts_1_0"
    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT production_model_version, shadow_model_version,
                   COUNT(*) AS shadow_rows, COUNT(DISTINCT query_id) AS query_count,
                   MIN(created_at) AS first_time, MAX(created_at) AS last_time
            FROM recommendation_shadow_logs
            WHERE production_model_version = %s AND shadow_model_version = %s
            GROUP BY production_model_version, shadow_model_version
        """, (production_version, shadow_version))
        shadow_summary = cur.fetchone() or {
            "production_model_version": production_version,
            "shadow_model_version": shadow_version,
            "shadow_rows": 0,
            "query_count": 0,
            "first_time": None,
            "last_time": None,
        }
        cur.execute("""
            WITH clicked AS (
                SELECT a.id AS action_id, a.created_at AS action_time, a.query_id, a.toilet_id,
                       p.rank AS production_rank, s.rank AS shadow_rank,
                       p.toilet_name, p.distance_m,
                       p.nts_score AS production_score, s.nts_score AS shadow_score
                FROM user_actions a
                JOIN recommendation_logs p ON a.query_id = p.query_id AND a.toilet_id = p.toilet_id
                LEFT JOIN recommendation_shadow_logs s ON a.query_id = s.query_id AND a.toilet_id = s.toilet_id
                  AND s.production_model_version = %s AND s.shadow_model_version = %s
                WHERE a.action_type = 'click_navigation' AND p.model_version = %s
            )
            SELECT COUNT(*) AS clicked_items,
                   ROUND(AVG(production_rank)::numeric, 2) AS avg_production_clicked_rank,
                   ROUND(AVG(shadow_rank)::numeric, 2) AS avg_shadow_clicked_rank,
                   SUM(CASE WHEN production_rank = 1 THEN 1 ELSE 0 END) AS production_rank1_clicks,
                   SUM(CASE WHEN shadow_rank = 1 THEN 1 ELSE 0 END) AS shadow_rank1_clicks,
                   SUM(CASE WHEN shadow_rank IS NULL THEN 1 ELSE 0 END) AS unmatched_shadow_clicks
            FROM clicked
        """, (production_version, shadow_version, production_version))
        click_compare = cur.fetchone()
        cur.execute("""
            WITH clicked AS (
                SELECT a.id AS action_id, p.rank AS production_rank, s.rank AS shadow_rank
                FROM user_actions a
                JOIN recommendation_logs p ON a.query_id = p.query_id AND a.toilet_id = p.toilet_id
                LEFT JOIN recommendation_shadow_logs s ON a.query_id = s.query_id AND a.toilet_id = s.toilet_id
                  AND s.production_model_version = %s AND s.shadow_model_version = %s
                WHERE a.action_type = 'click_navigation' AND p.model_version = %s
            )
            SELECT 'production' AS model, production_rank AS rank, COUNT(*) AS click_count
            FROM clicked GROUP BY production_rank
            UNION ALL
            SELECT 'shadow' AS model, shadow_rank AS rank, COUNT(*) AS click_count
            FROM clicked WHERE shadow_rank IS NOT NULL GROUP BY shadow_rank
            ORDER BY model, rank
        """, (production_version, shadow_version, production_version))
        rank_distribution = cur.fetchall()
        cur.execute("""
            SELECT a.created_at AS action_time, p.query_id, p.toilet_name,
                   p.rank AS production_rank, s.rank AS shadow_rank,
                   p.nts_score AS production_score, s.nts_score AS shadow_score, p.distance_m
            FROM user_actions a
            JOIN recommendation_logs p ON a.query_id = p.query_id AND a.toilet_id = p.toilet_id
            LEFT JOIN recommendation_shadow_logs s ON a.query_id = s.query_id AND a.toilet_id = s.toilet_id
              AND s.production_model_version = %s AND s.shadow_model_version = %s
            WHERE a.action_type = 'click_navigation' AND p.model_version = %s
            ORDER BY a.created_at DESC
            LIMIT 20
        """, (production_version, shadow_version, production_version))
        recent_shadow_clicks = cur.fetchall()
        conn.close()
        return jsonify({
            "ok": True,
            "production_version": production_version,
            "shadow_version": shadow_version,
            "shadow_summary": shadow_summary,
            "click_compare": click_compare,
            "rank_distribution": rank_distribution,
            "recent_shadow_clicks": recent_shadow_clicks,
        })
    except Exception as e:
        logging.error(f"/api/shadow-ranking-metrics failed: {e}", exc_info=True)
        return jsonify({"ok": False, "error": str(e)}), 500


@app.route("/dashboard/nts", methods=["GET"])
def dashboard_nts_page():
    """獨立的 NTS 行為分析頁：版本比較 + OSM fallback 效率分析。"""
    html = """
<!doctype html>
<html lang="zh-Hant">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width,initial-scale=1" />
  <title>NTS 排序行為分析</title>
  <style>
    :root{--bg:#f4f6fb;--card:#fff;--text:#1f2937;--muted:#6b7280;--line:#e5e7eb;--accent:#2563eb;--good:#059669;--warn:#d97706;--bad:#dc2626;--soft:#f8fafc;}
    *{box-sizing:border-box} body{margin:0;background:var(--bg);color:var(--text);font-family:-apple-system,BlinkMacSystemFont,"Segoe UI","Noto Sans TC",Arial,sans-serif;}
    .wrap{max-width:1220px;margin:0 auto;padding:24px 18px 48px}.top{display:flex;justify-content:space-between;align-items:flex-start;gap:16px;margin-bottom:18px}.title h1{margin:0;font-size:30px;letter-spacing:.02em}.title p{margin:8px 0 0;color:var(--muted)}
    .nav{display:flex;gap:10px;align-items:center;flex-wrap:wrap}.btn,.select{border:1px solid var(--line);background:#fff;border-radius:12px;padding:10px 14px;color:var(--text);text-decoration:none;font-weight:700}.btn:hover{border-color:var(--accent)}.select{min-width:220px}
    .grid{display:grid;grid-template-columns:repeat(5,1fr);gap:14px;margin:18px 0}@media(max-width:960px){.grid{grid-template-columns:repeat(2,1fr)}}@media(max-width:560px){.grid{grid-template-columns:1fr}.top{display:block}.nav{margin-top:12px}}
    .card{background:var(--card);border-radius:18px;padding:18px;box-shadow:0 8px 24px rgba(15,23,42,.06)}.k{color:var(--muted);font-size:13px;font-weight:700}.v{font-size:30px;font-weight:800;margin-top:8px}.s{font-size:13px;color:var(--muted);margin-top:8px}.section{background:var(--card);border-radius:18px;padding:18px;margin-top:16px;box-shadow:0 8px 24px rgba(15,23,42,.06)}
    .section h2{font-size:19px;margin:0 0 12px}.hint{color:var(--muted);font-size:13px;margin-bottom:12px;line-height:1.6}table{width:100%;border-collapse:collapse;font-size:14px}th,td{text-align:left;padding:12px;border-bottom:1px solid var(--line);vertical-align:top}th{color:#374151;background:#f9fafb}.rate{font-weight:800;color:var(--good)}.empty{color:var(--muted);padding:18px}.bar{height:8px;background:#eef2ff;border-radius:999px;overflow:hidden;min-width:90px}.bar>span{display:block;height:100%;background:var(--accent);border-radius:999px}.split{display:grid;grid-template-columns:1fr 1fr;gap:16px}@media(max-width:960px){.split{grid-template-columns:1fr}}
    .loading{color:var(--muted);padding:14px}.err{color:#b91c1c;background:#fee2e2;border:1px solid #fecaca;padding:12px;border-radius:12px;display:none}.tag{display:inline-block;background:#eef2ff;color:#3730a3;border-radius:999px;padding:4px 8px;font-size:12px;font-weight:700}.tag2{background:#ecfdf5;color:#047857}.tag0{background:#f3f4f6;color:#4b5563}.pos{color:var(--good);font-weight:800}.neg{color:var(--bad);font-weight:800}.neu{color:var(--muted);font-weight:800}.toolbar{display:flex;gap:10px;align-items:center;justify-content:space-between;flex-wrap:wrap}.mini{font-size:12px;color:var(--muted)}.pill{display:inline-flex;align-items:center;gap:6px;border-radius:999px;padding:6px 10px;background:var(--soft);border:1px solid var(--line);font-size:12px;font-weight:700;color:#475569}
    .explain-row{display:flex;gap:10px;flex-wrap:wrap;margin:14px 0 8px}.explain-btn{border:1px solid var(--line);background:#fff;border-radius:12px;padding:10px 14px;font-weight:800;cursor:pointer;color:#1f2937}.explain-btn:hover{border-color:var(--accent);color:var(--accent)}
    .modal-mask{position:fixed;inset:0;background:rgba(15,23,42,.45);display:none;align-items:center;justify-content:center;padding:18px;z-index:9999}.modal-mask.show{display:flex}.modal-box{width:min(760px,100%);max-height:86vh;overflow:auto;background:#fff;border-radius:20px;box-shadow:0 24px 70px rgba(15,23,42,.25);padding:22px}.modal-head{display:flex;justify-content:space-between;gap:12px;align-items:flex-start;margin-bottom:12px}.modal-head h2{margin:0;font-size:22px}.modal-close{border:0;background:#f3f4f6;border-radius:10px;width:38px;height:38px;font-size:22px;cursor:pointer}.modal-close:hover{background:#e5e7eb}.modal-box h3{margin:18px 0 8px;font-size:16px}.modal-box p,.modal-box li{line-height:1.7;color:#374151}.modal-box ul{padding-left:22px}.compare-mini{width:100%;border-collapse:collapse;margin-top:10px}.compare-mini th,.compare-mini td{border-bottom:1px solid var(--line);padding:10px;text-align:left}.compare-mini th{background:#f9fafb;color:#374151}
  </style>
</head>
<body>
  <div class="wrap">
    <div class="top">
      <div class="title">
        <h1>NTS 排序行為分析</h1>
        <p>比較 NTS 1.0 與 Trust Score 2.0 在真實使用者導航點擊與 OSM fallback 效率上的差異</p>
        <div class="explain-row">
          <button type="button" class="explain-btn" onclick="openExplainModal('nts1')">說明 NTS 1.0</button>
          <button type="button" class="explain-btn" onclick="openExplainModal('trust2')">說明 Trust Score 2.0</button>
        </div>
      </div>
      <div class="nav">
        <a class="btn" href="/dashboard">← 回總覽儀表板</a>
        <select id="versionSelect" class="select">
          <option value="all">全部版本</option>
          <option value="nts_1_0" selected>NTS 1.0 baseline</option>
          <option value="trust_score_2_0">Trust Score 2.0</option>
        </select>
      </div>
    </div>

    <div id="errorBox" class="err"></div>
    <div id="loading" class="loading">載入 NTS 行為資料中...</div>

    <div id="content" style="display:none">
      <div class="section">
        <div class="toolbar">
          <div>
            <h2>版本比較總表</h2>
            <div class="hint">並排比較 NTS 1.0 與 Trust Score 2.0。Trust Score 2.0 剛上線時會先顯示 0，跑一段時間後即可比較。</div>
          </div>
          <span class="pill">版本依 recommendation_logs.model_version 分組</span>
        </div>
        <div id="compareTable"></div>
      </div>

      <div class="grid">
        <div class="card"><div class="k">查詢數</div><div id="qCount" class="v">--</div><div class="s">Distinct query_id</div></div>
        <div class="card"><div class="k">推薦展示筆數</div><div id="recRows" class="v">--</div><div class="s">Top-k 推薦列數</div></div>
        <div class="card"><div class="k">導航點擊數</div><div id="navClicks" class="v">--</div><div class="s">click_navigation</div></div>
        <div class="card"><div class="k">查詢導航率</div><div id="queryRate" class="v">--</div><div class="s">點擊數 / 查詢數</div></div>
        <div class="card"><div class="k">推薦點擊率</div><div id="recRate" class="v">--</div><div class="s">點擊數 / 展示筆數</div></div>
      </div>

      <div class="section">
        <h2>版本資料量</h2>
        <div class="hint">確認 NTS 1.0 與 Trust Score 2.0 是否分開累積資料。</div>
        <div id="versionCounts"></div>
      </div>

      <div class="split">
        <div class="section">
          <h2>各 Rank 點擊率</h2>
          <div class="hint">觀察使用者是否主要點擊排序前面的推薦結果。</div>
          <div id="rankTable"></div>
        </div>
        <div class="section">
          <h2>NTS 分數區間點擊率</h2>
          <div class="hint">觀察 NTS 分數越高，導航點擊率是否越高。</div>
          <div id="scoreTable"></div>
        </div>
      </div>

      <div class="section">
        <div class="toolbar">
          <div>
            <h2>資料來源效率分析 / OSM fallback</h2>
            <div class="hint">觀察 csv、saved、osm、total 的查詢次數與耗時。OSM fallback 目標是：只有本地候選不足時才啟用，降低 Overpass 延遲風險。</div>
          </div>
          <span class="pill">讀取 /api/source-query-metrics</span>
        </div>
        <div id="sourceMetrics"></div>
      </div>

      <div class="section">
        <h2>OSM fallback 觸發原因</h2>
        <div class="hint">total 紀錄中的 reason 可用來判斷查詢是否使用 OSM、是否因候選不足而補查 OSM。</div>
        <div id="sourceReasons"></div>
      </div>

      <div class="section">
        <div class="toolbar">
          <div>
            <h2>Shadow Ranking：2.0 實際推薦 vs 1.0 後台比較</h2>
            <div class="hint">使用者實際看到 Trust Score 2.0，後台同步用 NTS 1.0 重新排序同一批推薦結果，比較使用者點擊的廁所在兩套模型中的名次。</div>
          </div>
          <span class="pill">讀取 /api/shadow-ranking-metrics</span>
        </div>
        <div id="shadowSummary"></div>
        <div id="shadowRankTable" style="margin-top:12px"></div>
        <div id="shadowRecent" style="margin-top:12px"></div>
      </div>

      <div class="section">
        <h2>最近導航點擊紀錄</h2>
        <div class="hint">檢查推薦結果與使用者點擊是否成功串接。</div>
        <div id="recentTable"></div>
      </div>
    </div>
  </div>


  <div id="explainModal" class="modal-mask" onclick="closeExplainModal(event)">
    <div class="modal-box" role="dialog" aria-modal="true" aria-labelledby="explainTitle" onclick="event.stopPropagation()">
      <div class="modal-head">
        <h2 id="explainTitle">模型說明</h2>
        <button type="button" class="modal-close" onclick="closeExplainModal()" aria-label="關閉">×</button>
      </div>
      <div id="explainBody"></div>
    </div>
  </div>

<script>
const $ = (id)=>document.getElementById(id);
const MODEL_EXPLAINS = {
  nts1: {
    title: 'NTS 1.0：固定權重 baseline 在做什麼？',
    body: `
      <p><b>NTS 1.0</b> 是本研究的「基準排序模型」。它的目的不是追求最複雜，而是先建立一套穩定、可解釋、可被驗證的公共廁所推薦排序方式。</p>

      <h3>一、它解決什麼問題？</h3>
      <p>一般找廁所系統常只看距離，但「最近」不一定代表「最適合」。例如最近的地點可能是資料未驗證、地址不完整、狀態異常，或根本已經被判定不可信。NTS 1.0 的核心就是把推薦問題從「找最近」提升成「找距離接近且資料比較可靠的廁所」。</p>

      <h3>二、它怎麼排序？</h3>
      <p>NTS 1.0 會把每一個候選廁所拆成四個節點分數，再用固定權重加總：</p>
      <table class="compare-mini">
        <tr><th>節點</th><th>代表意義</th><th>目前用途</th></tr>
        <tr><td>Distance 距離</td><td>離使用者越近分數越高</td><td>確保推薦結果仍然接近使用者</td></tr>
        <tr><td>Trust 可信度</td><td>資料來源與驗證狀態是否可信</td><td>避免未驗證或 rejected 資料排太前面</td></tr>
        <tr><td>Info 完整度</td><td>地址、樓層、入口提示、開放時間是否完整</td><td>提高使用者實際找到廁所的機率</td></tr>
        <tr><td>Status 狀態</td><td>是否有維修、停用、故障、正常等資訊</td><td>降低不可用廁所被推薦的風險</td></tr>
      </table>

      <h3>三、為什麼叫 baseline？</h3>
      <p>因為 NTS 1.0 使用固定規則，方便作為後續升級版本的比較基準。之後 Trust Score 2.0、OSM fallback、Shadow Ranking 都要和它比較，才能知道升級到底有沒有讓結果更好。</p>

      <h3>四、Dashboard 在看什麼？</h3>
      <ul>
        <li><b>Rank 點擊率</b>：第 1 名、第 2 名、第 3 名被點導航的比例。</li>
        <li><b>NTS 分數區間點擊率</b>：NTS 分數越高，使用者是否越容易點導航。</li>
        <li><b>最近導航紀錄</b>：每次使用者點導航時，那筆推薦當時的名次、距離、NTS、Trust 分數。</li>
      </ul>

      <h3>五、目前 NTS 1.0 的意義</h3>
      <p>如果 Rank 1 點擊率明顯高於後面名次，或高 NTS 分數區間的點擊率比較高，就代表 NTS 排序和使用者實際選擇有初步一致性。這可以作為研究中的真實使用者行為證據。</p>

      <table class="compare-mini">
        <tr><th>定位</th><td>固定權重、可解釋的排序基準線</td></tr>
        <tr><th>優點</th><td>簡單、穩定、可解釋，適合做 baseline</td></tr>
        <tr><th>限制</th><td>Trust 分數較固定，較難反映資料新鮮度、細部驗證品質與最近回報狀態</td></tr>
      </table>
    `
  },
  trust2: {
    title: 'Trust Score 2.0：動態可信度模型在做什麼？',
    body: `
      <p><b>Trust Score 2.0</b> 是 NTS 1.0 的升級版。它不是把整個系統推翻，而是把原本比較固定的 Trust 節點，升級成會依資料狀態變化的「動態可信度模型」。</p>

      <h3>一、為什麼需要 2.0？</h3>
      <p>NTS 1.0 裡，政府資料或 OSM 通常會拿到固定高分，使用者新增資料則依 approved / pending / rejected 給固定分數。但真實情境比較複雜：政府資料也可能很久沒更新，使用者新增資料如果資訊完整且後台已驗證，也可能很可靠。因此 2.0 的目標是讓可信度更接近真實資料品質。</p>

      <h3>二、Trust Score 2.0 多考慮了什麼？</h3>
      <table class="compare-mini">
        <tr><th>因素</th><th>說明</th><th>效果</th></tr>
        <tr><td>資料來源</td><td>政府資料、OSM、使用者新增資料給不同基礎分</td><td>保留來源差異</td></tr>
        <tr><td>驗證狀態</td><td>approved、pending、rejected 影響可信度</td><td>防止未驗證資料直接變高分</td></tr>
        <tr><td>verification_score</td><td>後台人工檢核分數可影響 Trust</td><td>讓後台檢核結果進入排序</td></tr>
        <tr><td>資訊完整度</td><td>地址、樓層、入口提示、開放時間完整會加分</td><td>鼓勵可找到、可使用的資料</td></tr>
        <tr><td>資料新鮮度</td><td>近期更新資料加分，太久未更新資料降分</td><td>避免過期資料長期佔高位</td></tr>
        <tr><td>狀態文字</td><td>維修、停用、故障、待確認、正常可用等字詞會影響狀態分數</td><td>更接近即時可用性</td></tr>
      </table>

      <h3>三、OSM fallback 在做什麼？</h3>
      <p>OSM / Overpass 可以補足政府資料不足的地方，但即時查詢很慢，也容易 timeout。所以 2.0 不是每次都查 OSM，而是先查本地資料：政府資料 + 使用者新增資料。只有當候選結果少於設定門檻，例如少於 2 筆時，才啟用 OSM fallback。</p>
      <ul>
        <li><b>沒用 OSM</b>：代表本地資料已足夠，速度通常較快。</li>
        <li><b>有用 OSM</b>：代表本地資料不足，需要外部資料補位，但耗時可能增加。</li>
        <li><b>Dashboard 會記錄</b>：csv、saved、osm、total 的查詢次數、平均耗時、是否 used_osm。</li>
      </ul>

      <h3>四、Shadow Ranking 在做什麼？</h3>
      <p>這是最重要的研究升級。使用者實際看到的是 <b>Trust Score 2.0</b> 的排序結果，但後台會用同一批候選廁所偷偷再跑一次 <b>NTS 1.0</b> 排序。注意：它不會重新查 OSM、CSV 或 Neon，只是用同一批資料重算分數與排序，所以效能負擔很小。</p>
      <p>這樣可以公平比較：同一次查詢、同一批候選資料，如果使用者點了某一間廁所，這間在 2.0 是第幾名？在 1.0 shadow ranking 又是第幾名？</p>

      <h3>五、我們要觀察什麼？</h3>
      <ul>
        <li><b>Rank 1 點擊率</b>：2.0 排第一的結果是否更常被點。</li>
        <li><b>查詢導航率</b>：每次查詢後，使用者是否更常點導航。</li>
        <li><b>NTS 高分區間點擊率</b>：高分結果是否真的比較吸引使用者。</li>
        <li><b>Shadow 比較</b>：使用者點擊的廁所在 2.0 的排名是否比 1.0 更前面。</li>
        <li><b>OSM 效率</b>：OSM fallback 是否減少不必要的外部查詢與延遲。</li>
      </ul>

      <h3>六、這個版本的研究意義</h3>
      <p>Trust Score 2.0 讓系統從「固定公式排序」往「資料品質會隨驗證、更新與回報而變動」前進。搭配 Shadow Ranking 後，系統不只是上線新模型，而是能用真實使用者導航點擊來驗證新模型是否比舊模型更接近使用者選擇。</p>

      <table class="compare-mini">
        <tr><th>定位</th><td>動態可信度 + OSM fallback + 真實行為驗證版本</td></tr>
        <tr><th>優點</th><td>更能反映資料品質、更新狀態、後台驗證與即時可用性</td></tr>
        <tr><th>注意</th><td>2.0 需要累積足夠查詢與導航點擊後，才適合和 1.0 做正式比較</td></tr>
      </table>
    `
  }
};

function openExplainModal(type){
  const item = MODEL_EXPLAINS[type] || MODEL_EXPLAINS.nts1;
  $('explainTitle').textContent = item.title;
  $('explainBody').innerHTML = item.body;
  $('explainModal').classList.add('show');
}
function closeExplainModal(e){
  if(e && e.target && e.target.id !== 'explainModal') return;
  $('explainModal').classList.remove('show');
}
document.addEventListener('keydown', (e)=>{ if(e.key === 'Escape' && $('explainModal')) $('explainModal').classList.remove('show'); });

function num(v){ const n = Number(v); return Number.isFinite(n) ? n : 0; }
function fmt(n){ if(n===null||n===undefined||n==='') return '--'; return Number(n).toLocaleString(); }
function pct(v){ if(v===null||v===undefined||v==='') return '--'; return `${v}%`; }
function esc(s){
  const map = {'&':'&amp;','<':'&lt;','>':'&gt;','\"':'&quot;',"'":'&#39;'};
  return String(s ?? '').replace(/[&<>\"']/g, m => map[m] || m);
}
function bar(rate){ const v=Math.max(0, Math.min(100, Number(rate)||0)); return `<div class="bar"><span style="width:${v}%"></span></div>`; }
function table(headers, rows, empty='目前沒有資料'){
  if(!rows || rows.length===0) return `<div class="empty">${empty}</div>`;
  return `<table><thead><tr>${headers.map(h=>`<th>${h}</th>`).join('')}</tr></thead><tbody>${rows.join('')}</tbody></table>`;
}
function deltaCell(v1, v2, suffix='%'){
  if(v1===null || v1===undefined || v2===null || v2===undefined || v1==='' || v2==='') return '<span class="neu">--</span>';
  const d = num(v2) - num(v1);
  const cls = d > 0 ? 'pos' : (d < 0 ? 'neg' : 'neu');
  const sign = d > 0 ? '+' : '';
  return `<span class="${cls}">${sign}${d.toFixed(2)}${suffix}</span>`;
}
function getRankRate(data, rank){
  const row = (data.rank_click_rate||[]).find(x => Number(x.rank) === Number(rank));
  return row ? row.click_rate_percent : null;
}
function getScoreRate(data, range){
  const row = (data.nts_score_click_rate||[]).find(x => x.nts_score_range === range);
  return row ? row.click_rate_percent : null;
}
async function fetchJson(url){
  const res = await fetch(url, {cache:'no-store'});
  const data = await res.json();
  if(!data.ok) throw new Error(data.error || 'API 回傳失敗');
  return data;
}
async function loadCompareTable(){
  const [v1, v2] = await Promise.all([
    fetchJson('/api/nts-behavior?version=nts_1_0'),
    fetchJson('/api/nts-behavior?version=trust_score_2_0')
  ]);
  const s1 = v1.summary || {}, s2 = v2.summary || {};
  const rows = [
    ['查詢數', fmt(s1.query_count), fmt(s2.query_count), ''],
    ['推薦展示筆數', fmt(s1.recommendation_rows), fmt(s2.recommendation_rows), ''],
    ['導航點擊數', fmt(s1.navigation_clicks), fmt(s2.navigation_clicks), ''],
    ['查詢導航率', pct(s1.click_rate_by_query_percent), pct(s2.click_rate_by_query_percent), deltaCell(s1.click_rate_by_query_percent, s2.click_rate_by_query_percent)],
    ['推薦點擊率', pct(s1.click_rate_by_recommendation_percent), pct(s2.click_rate_by_recommendation_percent), deltaCell(s1.click_rate_by_recommendation_percent, s2.click_rate_by_recommendation_percent)],
    ['Rank 1 點擊率', pct(getRankRate(v1,1)), pct(getRankRate(v2,1)), deltaCell(getRankRate(v1,1), getRankRate(v2,1))],
    ['Rank 2 點擊率', pct(getRankRate(v1,2)), pct(getRankRate(v2,2)), deltaCell(getRankRate(v1,2), getRankRate(v2,2))],
    ['90–100 分區間點擊率', pct(getScoreRate(v1,'90-100')), pct(getScoreRate(v2,'90-100')), deltaCell(getScoreRate(v1,'90-100'), getScoreRate(v2,'90-100'))],
    ['80–89 分區間點擊率', pct(getScoreRate(v1,'80-89')), pct(getScoreRate(v2,'80-89')), deltaCell(getScoreRate(v1,'80-89'), getScoreRate(v2,'80-89'))]
  ];
  $('compareTable').innerHTML = table(['指標','NTS 1.0','Trust Score 2.0','變化'], rows.map(r=>`<tr><td>${r[0]}</td><td>${r[1]}</td><td>${r[2]}</td><td>${r[3] || '<span class="mini">跑量後比較</span>'}</td></tr>`));
}
async function loadSourceMetrics(){
  const version = $('versionSelect').value;
  const data = await fetchJson(`/api/source-query-metrics?version=${encodeURIComponent(version)}`);
  $('sourceMetrics').innerHTML = table(['版本','來源','呼叫次數','使用 OSM 次數','平均耗時','最大耗時','結果總數','成功次數'], (data.by_source||[]).map(r=>
    `<tr><td><span class="tag ${r.model_version==='trust_score_2_0'?'tag2':'tag0'}">${esc(r.model_version)}</span></td><td>${esc(r.source_name)}</td><td>${fmt(r.call_count)}</td><td>${fmt(r.used_osm_count)}</td><td>${fmt(r.avg_elapsed_ms)} ms</td><td>${fmt(r.max_elapsed_ms)} ms</td><td>${fmt(r.total_result_count)}</td><td>${fmt(r.success_count)}</td></tr>`
  ), '目前沒有 source_query_logs 資料，部署 Trust Score 2.0 + OSM metrics 後會開始累積。');
  $('sourceReasons').innerHTML = table(['版本','原因','次數','平均總耗時'], (data.total_reason||[]).map(r=>
    `<tr><td><span class="tag ${r.model_version==='trust_score_2_0'?'tag2':'tag0'}">${esc(r.model_version)}</span></td><td>${esc(r.reason)}</td><td>${fmt(r.count)}</td><td>${fmt(r.avg_elapsed_ms)} ms</td></tr>`
  ), '目前沒有 total reason 資料。');
}
async function loadShadowMetrics(){
  try{
    const data = await fetchJson('/api/shadow-ranking-metrics?production=trust_score_2_0&shadow=nts_1_0');
    const s = data.shadow_summary || {};
    const c = data.click_compare || {};
    $('shadowSummary').innerHTML = table(['指標','數值'], [
      `<tr><td>Production model</td><td><span class="tag tag2">${esc(data.production_version||'trust_score_2_0')}</span></td></tr>`,
      `<tr><td>Shadow model</td><td><span class="tag tag0">${esc(data.shadow_version||'nts_1_0')}</span></td></tr>`,
      `<tr><td>Shadow 查詢數</td><td>${fmt(s.query_count)}</td></tr>`,
      `<tr><td>Shadow 推薦列數</td><td>${fmt(s.shadow_rows)}</td></tr>`,
      `<tr><td>已點擊且可比較筆數</td><td>${fmt(c.clicked_items)}</td></tr>`,
      `<tr><td>2.0 被點擊平均名次</td><td>${fmt(c.avg_production_clicked_rank)}</td></tr>`,
      `<tr><td>1.0 shadow 被點擊平均名次</td><td>${fmt(c.avg_shadow_clicked_rank)}</td></tr>`,
      `<tr><td>2.0 Rank1 點擊數</td><td>${fmt(c.production_rank1_clicks)}</td></tr>`,
      `<tr><td>1.0 shadow Rank1 點擊數</td><td>${fmt(c.shadow_rank1_clicks)}</td></tr>`
    ], '尚無 shadow ranking 資料。請確認 NTS_MODEL_VERSION=trust_score_2_0 且 SHADOW_NTS_ENABLE=1，並累積導航點擊。');
    $('shadowRankTable').innerHTML = table(['模型','被點擊名次','點擊數'], (data.rank_distribution||[]).map(r=>
      `<tr><td>${esc(r.model)}</td><td>${esc(r.rank)}</td><td>${fmt(r.click_count)}</td></tr>`
    ), '尚無 rank distribution 資料。');
    $('shadowRecent').innerHTML = table(['時間','廁所','2.0 Rank','1.0 Shadow Rank','2.0 分數','1.0 分數','距離'], (data.recent_shadow_clicks||[]).map(r=>
      `<tr><td>${esc(r.action_time)}</td><td>${esc(r.toilet_name)}</td><td>${esc(r.production_rank)}</td><td>${esc(r.shadow_rank)}</td><td>${esc(r.production_score)}</td><td>${esc(r.shadow_score)}</td><td>${Number(r.distance_m||0).toFixed(1)}m</td></tr>`
    ), '尚無最近 shadow 點擊資料。');
  }catch(e){
    $('shadowSummary').innerHTML = `<div class="empty">Shadow metrics 尚未可用：${esc(e.message)}</div>`;
    $('shadowRankTable').innerHTML = '';
    $('shadowRecent').innerHTML = '';
  }
}

async function loadNtsBehavior(){
  const version = $('versionSelect').value;
  $('loading').style.display='block'; $('content').style.display='none'; $('errorBox').style.display='none';
  try{
    const data = await fetchJson(`/api/nts-behavior?version=${encodeURIComponent(version)}`);
    const s = data.summary || {};
    $('qCount').textContent = fmt(s.query_count);
    $('recRows').textContent = fmt(s.recommendation_rows);
    $('navClicks').textContent = fmt(s.navigation_clicks);
    $('queryRate').textContent = pct(s.click_rate_by_query_percent);
    $('recRate').textContent = pct(s.click_rate_by_recommendation_percent);

    $('versionCounts').innerHTML = table(['版本','推薦展示','查詢數'], (data.version_counts||[]).map(r=>
      `<tr><td><span class="tag ${r.model_version==='trust_score_2_0'?'tag2':'tag0'}">${esc(r.model_version)}</span></td><td>${fmt(r.recommendation_rows)}</td><td>${fmt(r.query_count)}</td></tr>`
    ));
    $('rankTable').innerHTML = table(['Rank','展示','點擊','點擊率',''], (data.rank_click_rate||[]).map(r=>
      `<tr><td>${esc(r.rank)}</td><td>${fmt(r.shown_count)}</td><td>${fmt(r.click_count)}</td><td class="rate">${pct(r.click_rate_percent)}</td><td>${bar(r.click_rate_percent)}</td></tr>`
    ));
    $('scoreTable').innerHTML = table(['分數區間','展示','點擊','點擊率',''], (data.nts_score_click_rate||[]).map(r=>
      `<tr><td>${esc(r.nts_score_range)}</td><td>${fmt(r.shown_count)}</td><td>${fmt(r.click_count)}</td><td class="rate">${pct(r.click_rate_percent)}</td><td>${bar(r.click_rate_percent)}</td></tr>`
    ));
    $('recentTable').innerHTML = table(['時間','版本','Rank','廁所','距離','NTS','Trust','Info','Status'], (data.recent_clicks||[]).map(r=>
      `<tr><td>${esc(r.action_time)}</td><td>${esc(r.model_version)}</td><td>${esc(r.rank)}</td><td>${esc(r.toilet_name)}</td><td>${Number(r.distance_m||0).toFixed(1)}m</td><td>${esc(r.nts_score)}</td><td>${esc(r.trust_score)}</td><td>${esc(r.info_score)}</td><td>${esc(r.status_score)}</td></tr>`
    ));
    try { await loadCompareTable(); } catch(e) { $('compareTable').innerHTML = `<div class="empty">版本比較暫時無法載入：${esc(e.message)}</div>`; }
    try { await loadSourceMetrics(); } catch(e) { $('sourceMetrics').innerHTML = `<div class="empty">資料來源效率暫時無法載入：${esc(e.message)}</div>`; $('sourceReasons').innerHTML = ''; }
    try { await loadShadowMetrics(); } catch(e) { $('shadowSummary').innerHTML = `<div class="empty">Shadow metrics 暫時無法載入：${esc(e.message)}</div>`; $('shadowRankTable').innerHTML = ''; $('shadowRecent').innerHTML = ''; }
    $('loading').style.display='none'; $('content').style.display='block';
  }catch(e){
    $('loading').style.display='none'; $('errorBox').style.display='block'; $('errorBox').textContent = '載入失敗：' + e.message;
  }
}
$('versionSelect').addEventListener('change', loadNtsBehavior);
document.addEventListener('DOMContentLoaded', loadNtsBehavior);
</script>
</body>
</html>
    """
    return Response(html, mimetype="text/html; charset=utf-8")



@app.route("/api/source-query-metrics")
def api_source_query_metrics():
    """
    資料來源查詢耗時分析 API
    用法：
    /api/source-query-metrics
    /api/source-query-metrics?version=trust_score_2_0
    """
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "error": "Postgres not enabled"}), 503

    version = (request.args.get("version") or "all").strip() or "all"

    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)

        cur.execute("""
            SELECT
                COALESCE(model_version, 'unknown') AS model_version,
                source_name,
                COUNT(*) AS call_count,
                SUM(CASE WHEN used_osm THEN 1 ELSE 0 END) AS used_osm_count,
                ROUND(AVG(elapsed_ms)::numeric, 2) AS avg_elapsed_ms,
                MAX(elapsed_ms) AS max_elapsed_ms,
                SUM(result_count) AS total_result_count,
                SUM(CASE WHEN success THEN 1 ELSE 0 END) AS success_count
            FROM source_query_logs
            WHERE (%s = 'all' OR model_version = %s)
            GROUP BY COALESCE(model_version, 'unknown'), source_name
            ORDER BY model_version, source_name
        """, (version, version))
        by_source = cur.fetchall()

        cur.execute("""
            SELECT
                COALESCE(model_version, 'unknown') AS model_version,
                reason,
                COUNT(*) AS count,
                ROUND(AVG(elapsed_ms)::numeric, 2) AS avg_elapsed_ms
            FROM source_query_logs
            WHERE (%s = 'all' OR model_version = %s)
              AND source_name = 'total'
            GROUP BY COALESCE(model_version, 'unknown'), reason
            ORDER BY model_version, reason
        """, (version, version))
        total_reason = cur.fetchall()

        conn.close()
        return jsonify({
            "ok": True,
            "version": version,
            "by_source": by_source,
            "total_reason": total_reason
        })
    except Exception as e:
        logging.error(f"/api/source-query-metrics failed: {e}", exc_info=True)
        return jsonify({"ok": False, "error": str(e)}), 500


@app.route("/api/nts-behavior")
def api_nts_behavior():
    """
    NTS 行為分析 API
    用法：
    /api/nts-behavior
    /api/nts-behavior?version=nts_1_0
    /api/nts-behavior?version=trust_score_2_0
    """
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "error": "Postgres not enabled"}), 503

    version = (request.args.get("version") or "all").strip() or "all"

    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)

        cur.execute("""
            SELECT
                COALESCE(model_version, 'unknown') AS model_version,
                COUNT(*) AS recommendation_rows,
                COUNT(DISTINCT query_id) AS query_count
            FROM recommendation_logs
            GROUP BY COALESCE(model_version, 'unknown')
            ORDER BY model_version
        """)
        version_counts = cur.fetchall()

        cur.execute("""
            WITH filtered AS (
                SELECT *
                FROM recommendation_logs
                WHERE (%s = 'all' OR model_version = %s)
            ),
            clicks AS (
                SELECT DISTINCT a.id
                FROM user_actions a
                JOIN filtered r
                  ON a.query_id = r.query_id
                 AND a.toilet_id = r.toilet_id
                WHERE a.action_type = 'click_navigation'
            )
            SELECT
                COUNT(*) AS recommendation_rows,
                COUNT(DISTINCT query_id) AS query_count,
                (SELECT COUNT(*) FROM clicks) AS navigation_clicks,
                ROUND((SELECT COUNT(*) FROM clicks)::numeric / NULLIF(COUNT(*), 0) * 100, 2) AS click_rate_by_recommendation_percent,
                ROUND((SELECT COUNT(*) FROM clicks)::numeric / NULLIF(COUNT(DISTINCT query_id), 0) * 100, 2) AS click_rate_by_query_percent
            FROM filtered
        """, (version, version))
        summary = cur.fetchone()

        cur.execute("""
            WITH filtered AS (
                SELECT *
                FROM recommendation_logs
                WHERE (%s = 'all' OR model_version = %s)
            ),
            impressions AS (
                SELECT rank, COUNT(*) AS shown_count
                FROM filtered
                GROUP BY rank
            ),
            clicks AS (
                SELECT r.rank, COUNT(DISTINCT a.id) AS click_count
                FROM user_actions a
                JOIN filtered r
                  ON a.query_id = r.query_id
                 AND a.toilet_id = r.toilet_id
                WHERE a.action_type = 'click_navigation'
                GROUP BY r.rank
            )
            SELECT
                i.rank,
                i.shown_count,
                COALESCE(c.click_count, 0) AS click_count,
                ROUND(COALESCE(c.click_count, 0)::numeric / NULLIF(i.shown_count, 0) * 100, 2) AS click_rate_percent
            FROM impressions i
            LEFT JOIN clicks c ON i.rank = c.rank
            ORDER BY i.rank ASC
        """, (version, version))
        rank_click_rate = cur.fetchall()

        cur.execute("""
            WITH filtered AS (
                SELECT *
                FROM recommendation_logs
                WHERE (%s = 'all' OR model_version = %s)
            ),
            shown AS (
                SELECT
                    r.id,
                    r.query_id,
                    r.toilet_id,
                    r.rank,
                    r.nts_score,
                    CASE WHEN a.id IS NULL THEN 0 ELSE 1 END AS clicked
                FROM filtered r
                LEFT JOIN user_actions a
                  ON r.query_id = a.query_id
                 AND r.toilet_id = a.toilet_id
                 AND a.action_type = 'click_navigation'
            ),
            grouped AS (
                SELECT
                    CASE
                        WHEN nts_score >= 90 THEN '90-100'
                        WHEN nts_score >= 80 THEN '80-89'
                        WHEN nts_score >= 70 THEN '70-79'
                        WHEN nts_score >= 60 THEN '60-69'
                        ELSE '<60'
                    END AS nts_score_range,
                    COUNT(*) AS shown_count,
                    SUM(clicked) AS click_count,
                    ROUND(SUM(clicked)::numeric / NULLIF(COUNT(*), 0) * 100, 2) AS click_rate_percent
                FROM shown
                GROUP BY
                    CASE
                        WHEN nts_score >= 90 THEN '90-100'
                        WHEN nts_score >= 80 THEN '80-89'
                        WHEN nts_score >= 70 THEN '70-79'
                        WHEN nts_score >= 60 THEN '60-69'
                        ELSE '<60'
                    END
            )
            SELECT *
            FROM grouped
            ORDER BY
                CASE nts_score_range
                    WHEN '90-100' THEN 1
                    WHEN '80-89' THEN 2
                    WHEN '70-79' THEN 3
                    WHEN '60-69' THEN 4
                    ELSE 5
                END
        """, (version, version))
        nts_score_click_rate = cur.fetchall()

        cur.execute("""
            WITH filtered AS (
                SELECT *
                FROM recommendation_logs
                WHERE (%s = 'all' OR model_version = %s)
            )
            SELECT
                a.created_at AS action_time,
                a.action_type,
                r.model_version,
                r.query_id,
                r.rank,
                r.toilet_name,
                r.distance_m,
                r.nts_score,
                r.distance_score,
                r.trust_score,
                r.info_score,
                r.status_score
            FROM user_actions a
            JOIN filtered r
              ON a.query_id = r.query_id
             AND a.toilet_id = r.toilet_id
            WHERE a.action_type = 'click_navigation'
            ORDER BY a.created_at DESC
            LIMIT 20
        """, (version, version))
        recent_clicks = cur.fetchall()

        conn.close()
        return jsonify({
            "ok": True,
            "version": version,
            "version_counts": version_counts,
            "summary": summary,
            "rank_click_rate": rank_click_rate,
            "nts_score_click_rate": nts_score_click_rate,
            "recent_clicks": recent_clicks
        })

    except Exception as e:
        logging.error(f"/api/nts-behavior failed: {e}", exc_info=True)
        return jsonify({"ok": False, "error": str(e)}), 500



@app.route("/api/dashboard", methods=["GET"])
@app.route("/api/dashboard", methods=["GET"])
def api_dashboard():
    range_key = (request.args.get("range") or "1h").strip()
    if range_key not in ("1h", "1d", "7d", "30d", "1y"):
        range_key = "1h"

    anchor_date = (request.args.get("anchor_date") or "").strip() or None
    return jsonify(_generate_dashboard_data(range_key, anchor_date))

# === Webhook ===
@app.route("/callback", methods=["POST"])
def callback():
    signature = request.headers.get("X-Line-Signature")
    body = request.get_data(as_text=True)
    try:
        handler.handle(body, signature)
    except InvalidSignatureError:
        abort(400)
    return "OK"

@app.route("/", methods=["GET"])
def home():
    return "Toilet bot is running!", 200

# === 共用狀態 ===
user_locations = {}
pending_delete_confirm = {}
user_search_count = {}
user_loc_mode = {}  # 新增：記錄使用者目前查廁所模式（"normal" or "ai"）

# 建議：高併發時避免競態
_dict_lock = threading.Lock()
def set_user_location(uid, latlon):
    with _dict_lock:
        user_locations[uid] = latlon

def get_user_location(uid):
    with _dict_lock:
        return user_locations.get(uid)

def set_user_loc_mode(uid, mode):
    with _dict_lock:
        user_loc_mode[uid] = mode

def get_user_loc_mode(uid):
    with _dict_lock:
        return user_loc_mode.get(uid, "normal")

# === 共用執行緒池（避免每次臨時建立） ===
_pool = ThreadPoolExecutor(max_workers=2)

def build_nearby_toilets(uid, lat, lon, radius=500):
    # 預設使用 NTS 排序；若要回到純距離排序，可設定 TOILET_SORT_ALGO=distance_only
    algo = os.getenv("TOILET_SORT_ALGO", "nts_score").strip().lower()
    model_version = os.getenv("NTS_MODEL_VERSION", "nts_1_0").strip() or "nts_1_0"

    # OSM fallback 策略：先查本地/Neon 資料，不足再查 OSM
    try:
        osm_fallback_min = int(os.getenv("OSM_FALLBACK_MIN_RESULTS", "2"))
    except Exception:
        osm_fallback_min = 2
    osm_fallback_min = max(0, osm_fallback_min)
    osm_enabled = os.getenv("OSM_FALLBACK_ENABLE", "1") == "1"

    # === Grid cache key（加入 algo/model_version/OSM 策略，避免切換後吃到舊快取）===
    lat_g = grid_coord(lat)
    lon_g = grid_coord(lon)
    query_key = f"nearby:{algo}:{model_version}:osm{int(osm_enabled)}:min{osm_fallback_min}:{lat_g},{lon_g},{radius}"

    cached = get_cached_data(query_key)
    if cached:
        logging.debug(f"[cache hit] nearby {query_key}")
        return cached

    query_id_for_source = "SRC_" + uuid.uuid4().hex[:16]
    total_start = time.time()
    csv_res, saved_res, osm_res = [], [], []

    # === 第一階段：只查本地/Neon/政府資料，不先打 OSM，降低延遲 ===
    futures = []
    try:
        futures.append(("csv", _pool.submit(query_public_csv_toilets, lat, lon, radius)))
        futures.append(("saved", _pool.submit(query_saved_toilets, lat, lon, radius)))

        for name, fut in futures:
            source_start = time.time()
            try:
                res = fut.result(timeout=LOC_QUERY_TIMEOUT_SEC)
                elapsed_ms = int((time.time() - source_start) * 1000)
                if name == "csv":
                    csv_res = res or []
                else:
                    saved_res = res or []
                log_source_query(
                    query_id=query_id_for_source,
                    uid=uid,
                    source_name=name,
                    result_count=len(res or []),
                    elapsed_ms=elapsed_ms,
                    success=True,
                    reason="primary_local_search",
                    used_osm=False
                )
            except FuturesTimeoutError:
                elapsed_ms = int((time.time() - source_start) * 1000)
                logging.warning(f"{name} 查詢逾時")
                log_source_query(query_id_for_source, uid, name, 0, elapsed_ms, False, "timeout", "timeout", False)
            except Exception as e:
                elapsed_ms = int((time.time() - source_start) * 1000)
                logging.warning(f"{name} 查詢失敗: {e}")
                log_source_query(query_id_for_source, uid, name, 0, elapsed_ms, False, "error", str(e), False)
    finally:
        for _, fut in futures:
            if not fut.done():
                fut.cancel()

    quick_no_osm = _merge_and_dedupe_lists(csv_res, saved_res)

    # === 第二階段：候選不足才查 OSM ===
    used_osm = False
    if osm_enabled and len(quick_no_osm) < osm_fallback_min:
        used_osm = True
        source_start = time.time()
        try:
            osm_res = query_overpass_toilets(lat, lon, radius) or []
            elapsed_ms = int((time.time() - source_start) * 1000)
            log_source_query(
                query_id=query_id_for_source,
                uid=uid,
                source_name="osm",
                result_count=len(osm_res),
                elapsed_ms=elapsed_ms,
                success=True,
                reason=f"fallback_candidates_lt_{osm_fallback_min}",
                used_osm=True
            )
        except Exception as e:
            elapsed_ms = int((time.time() - source_start) * 1000)
            logging.warning(f"osm fallback 查詢失敗: {e}")
            log_source_query(query_id_for_source, uid, "osm", 0, elapsed_ms, False, f"fallback_candidates_lt_{osm_fallback_min}", str(e), True)
    else:
        # 記錄 skipped，之後可統計省下多少 OSM 查詢
        log_source_query(
            query_id=query_id_for_source,
            uid=uid,
            source_name="osm",
            result_count=0,
            elapsed_ms=0,
            success=True,
            reason=f"skipped_candidates_gte_{osm_fallback_min}" if osm_enabled else "osm_disabled",
            used_osm=False
        )

    quick = _merge_and_dedupe_lists(csv_res, saved_res, osm_res)

    if algo == "distance_only":
        sort_toilets(quick)
    else:
        quick = sort_toilets_nts(quick)

    result = quick[:LOC_MAX_RESULTS]

    total_elapsed_ms = int((time.time() - total_start) * 1000)
    log_source_query(
        query_id=query_id_for_source,
        uid=uid,
        source_name="total",
        result_count=len(result),
        elapsed_ms=total_elapsed_ms,
        success=True,
        reason="used_osm" if used_osm else "without_osm",
        used_osm=used_osm
    )

    # === 寫入 cache（Grid cache）===
    save_cache(query_key, result)

    return result

# === TextMessage ===
# === TextMessage ===
@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    if _too_old_to_reply(event):
        logging.warning("[handle_text] event too old; skip reply.")
        return

    uid = event.source.user_id
    text_raw = event.message.text or ""

    # =========================
    # 🔧 強化文字正規化
    # =========================
    text_norm = text_raw.strip()
    text = text_norm.lower()
    text_key = " ".join(text.split())  # 壓掉 \n / \t / 多空白

    # =========================
    # 🔥 英文 Nearby Toilets 最優先容錯（不靠完全比對）
    # =========================
    if ("nearby" in text_key) and (("toilet" in text_key) or ("restroom" in text_key)):
        set_user_loc_mode(uid, "normal")
        try:
            safe_reply(
                event,
                make_location_quick_reply(
                    L(
                        uid,
                        "📍 請點下方『發送我的位置』，我會幫你找最近的廁所",
                        "📍 Please share your location and I will find nearby toilets for you"
                    ),
                    mode="normal"
                )
            )
        except Exception as e:
            logging.error(f"[nearby] quick reply failed: {e}", exc_info=True)
            safe_reply(
                event,
                TextSendMessage(
                    text=L(uid, "❌ 系統錯誤，請稍後再試", "❌ System error. Please try again later.")
                )
            )
        return

    # =========================
    # 🚫 重複事件 / 同意條款 gate
    # =========================
    if is_duplicate_and_mark_event(event):
        return

    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg)
        return

    reply_messages = []

    # =========================
    # ✅ 中英文文字指令 → cmd
    # =========================
    TEXT_TO_CMD = {
        # 附近廁所
        "附近廁所": "nearby",
        "nearby toilets": "nearby",
        "nearby": "nearby",
        "toilets nearby": "nearby",

        # AI 推薦
        "ai推薦附近廁所": "nearby_ai",
        "ai nearby toilets": "nearby_ai",
        "ai recommend": "nearby_ai",
        "ai recommendation": "nearby_ai",

        # 切換回一般模式
        "切換回一般模式": "mode_normal",
        "switch to normal": "mode_normal",
        "normal mode": "mode_normal",

        # 我的最愛
        "我的最愛": "favs",
        "my favorites": "favs",
        "favorites": "favs",

        # 我的貢獻
        "我的貢獻": "contrib",
        "my contributions": "contrib",
        "contributions": "contrib",

        # 新增廁所
        "新增廁所": "add",
        "add toilet": "add",
        "add a toilet": "add",

        # 意見回饋
        "意見回饋": "feedback",
        "feedback": "feedback",

        # 合作信箱
        "合作信箱": "contact",
        "contact": "contact",

        # 狀態回報
        "狀態回報": "status",
        "status report": "status",
        "report status": "status",

        # 成就
        "成就": "ach",
        "achievements": "ach",

        # 徽章
        "徽章": "badges",
        "badges": "badges",

        # 使用回顧
        "使用回顧": "review",
        "usage summary": "review",
        "review": "review",

        # 使用說明
        "使用說明": "help",
        "help": "help",
    }

    # 三段式 lookup（最穩）
    cmd = TEXT_TO_CMD.get(text_norm)
    if cmd is None:
        cmd = TEXT_TO_CMD.get(text)
    if cmd is None:
        cmd = TEXT_TO_CMD.get(text_key)

    # =========================
    # ✅ cmd 分派（原本邏輯全部保留）    # =========================
    # ✅ cmd 分派（原本邏輯全部保留）
    # =========================
    if cmd == "nearby":
        start_ts = time.time()
        set_user_loc_mode(uid, "normal")
        safe_reply(
            event,
            make_location_quick_reply(
                L(uid,
                  "📍 請點下方『發送我的位置』，我會幫你找最近的廁所",
                  "📍 Please share your location and I will find nearby toilets for you"),
                mode="normal"
            )
        )
        return

    elif cmd == "nearby_ai":
        start_ts = time.time()
        set_user_loc_mode(uid, "ai")
        safe_reply(
            event,
            make_location_quick_reply(
                L(uid,
                  "📍 請傳送你現在的位置，我會用 AI 幫你挑附近最適合的廁所",
                  "📍 Please share your location. I will use AI to pick the best nearby toilets."),
                mode="ai"
            )
        )
        return

    elif cmd == "mode_normal":
        set_user_loc_mode(uid, "normal")
        safe_reply(
            event,
            make_location_quick_reply(
                L(uid,
                  "✅ 已切換回一般模式，請點『發送我的位置』我會幫你找最近的廁所",
                  "✅ Switched to normal mode. Please share your location to find nearby toilets."),
                mode="normal"
            )
        )
        return

    elif cmd == "favs":
        favs = get_user_favorites(uid)
        if not favs:
            reply_messages.append(TextSendMessage(text=L(uid, "你尚未收藏任何廁所", "You have no favorites yet.")))
        else:
            loc = get_user_location(uid)
            if loc:
                lat, lon = loc
                for f in favs:
                    f["distance"] = haversine(lat, lon, f["lat"], f["lon"])
            msg = create_toilet_flex_messages(favs, uid=uid)
            reply_messages.append(FlexSendMessage(L(uid, "我的最愛", "My Favorites"), msg))

    elif cmd == "contrib":
        msg = create_my_contrib_flex(uid)
        if msg:
            reply_messages.append(FlexSendMessage(L(uid, "我新增的廁所", "My Contributions"), msg))
        else:
            reply_messages.append(TextSendMessage(text=L(uid, "你還沒有新增過廁所喔。", "You haven't added any toilets yet.")))

    elif cmd == "add":
        base = f"{_base_url()}/add"
        loc = get_user_location(uid)
        if loc:
            la, lo = loc
            url = f"{base}?uid={quote(uid)}&lat={la}&lon={lo}#openExternalBrowser=1"
        else:
            url = f"{base}?uid={quote(uid)}#openExternalBrowser=1"
        reply_messages.append(TextSendMessage(text=L(uid, f"請前往此頁新增廁所：\n{url}", f"Please add a toilet here:\n{url}")))

    elif cmd == "feedback":
        form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
        reply_messages.append(TextSendMessage(text=L(
            uid,
            f"💡 請透過下列連結回報問題或提供意見：\n{form_url}",
            f"💡 Please send feedback via:\n{form_url}"
        )))

    elif cmd == "contact":
        email = os.getenv("FEEDBACK_EMAIL", "hello@example.com")
        ig_url = "https://www.instagram.com/toiletmvp?igsh=MWRvMnV2MTNyN2RkMw=="
        reply_messages.append(TextSendMessage(text=L(
            uid,
            f"📬 合作信箱：{email}\n\n📸 官方IG: {ig_url}",
            f"📬 Contact: {email}\n\n📸 IG: {ig_url}"
        )))

    elif cmd == "status":
        url = _status_liff_url(uid=uid)
        safe_reply(event, TextSendMessage(text=L(uid, f"⚡ 開啟狀態回報：\n{url}", f"⚡ Open status report:\n{url}")))
        return

    elif cmd == "ach":
        reply_url = f"{PUBLIC_URL}/achievements_liff?uid={uid}&lang={get_user_lang(uid)}"
        safe_reply(event, TextSendMessage(text=L(uid, f"查看成就 👉 {reply_url}", f"View achievements 👉 {reply_url}")))
        return

    elif cmd == "badges":
        reply_url = f"{PUBLIC_URL}/badges_liff?uid={uid}&lang={get_user_lang(uid)}"
        safe_reply(event, TextSendMessage(text=L(uid, f"查看徽章 👉 {reply_url}", f"View badges 👉 {reply_url}")))
        return

    elif cmd == "review":
        summary = build_usage_review_text(uid)
        reply_messages.append(TextSendMessage(text=summary))

    elif cmd == "help":
        reply_messages.append(TextSendMessage(text=L(
            uid,
            "📌 使用說明：\n・點「附近廁所」或直接傳位置\n・可加入最愛、回饋、看 AI 摘要\n・也可切換 AI 推薦模式",
            "📌 Help:\n• Tap 'Nearby Toilets' or send location\n• Add favorites, leave feedback, view AI summary\n• You can also switch to AI recommendation mode"
        )))

    # =========================
    # ✅ 永遠不沉默
    # =========================
    if reply_messages:
        safe_reply(event, reply_messages)
    else:
        safe_reply(
            event,
            TextSendMessage(text=L(
                uid,
                "我沒有看懂你的指令 🙏\n你可以試試：附近廁所 / 使用說明",
                "I didn’t understand 🙏\nTry: Nearby Toilets / Help"
            ))
        )

# === LocationMessage ===
@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
    if _too_old_to_reply(event):
        logging.warning("[handle_location] event too old; skip reply.")
        return
    uid = event.source.user_id
    show_loading(uid, seconds=15)
    lat = event.message.latitude
    lon = event.message.longitude

    # 記錄查詢次數（寫 DB）
    try:
        conn = _get_db()
        cur = conn.cursor()
        cur.execute(
            "INSERT INTO search_log (user_id, lat, lon, ts) VALUES (?,?,?,?)",
            (uid, norm_coord(lat), norm_coord(lon),
             datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S"))
        )
        conn.commit()
        conn.close()
    except Exception as e:
        logging.warning(f"記錄查詢次數失敗: {e}")

    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg)
        return

    if is_duplicate_and_mark_event(event):
        return

    # 記下使用者最近一次的位置
    set_user_location(uid, (lat, lon))

    if not _try_acquire_loc_slot():
        safe_reply(event, make_retry_location_text())
        return

    start_ts = time.time()
    area_name = get_area_name(lat, lon)

    try:
        query_id = make_query_id()

        toilets = build_nearby_toilets(uid, lat, lon)
        elapsed_ms = int((time.time() - start_ts) * 1000)

        if toilets:
            log_recommendation_results(
                query_id=query_id,
                uid=uid,
                user_lat=lat,
                user_lon=lon,
                toilets=toilets,
                limit=5
            )
            log_shadow_recommendation_results(
                query_id=query_id,
                uid=uid,
                user_lat=lat,
                user_lon=lon,
                toilets=toilets,
                limit=5
            )

        elapsed_ms = int((time.time() - start_ts) * 1000)

        if elapsed_ms > 0:
            log_analytics_event(
                user_id=uid,
                event_type="location_query",
                result_count=len(toilets or []),
                success=1,
                response_time_ms=elapsed_ms,
                lat=lat,
                lon=lon,
                area_name=area_name
            )

        if toilets:
            # 產出廁所 carousel，並帶入 query_id，讓導航點擊可回連到本次推薦紀錄
            msg = create_toilet_flex_messages(toilets, uid=uid, query_id=query_id)

            # 看目前是一般模式還是 AI 模式
            mode = get_user_loc_mode(uid)

            if mode == "ai":
                # 🧠 AI 模式：把 AI 推薦文字塞成「第一個 bubble」
                ai_text = build_ai_nearby_recommendation(uid, toilets)

                if ai_text:
                    ai_bubble = {
                        "type": "bubble",
                        "body": {
                            "type": "box",
                            "layout": "vertical",
                            "contents": [
                                {
                                    "type": "text",
                                    "text": L(uid, "🤖 AI 推薦分析", "🤖 AI Recommendation"),
                                    "weight": "bold",
                                    "size": "lg",
                                    "wrap": True,
                                },
                                {
                                    "type": "text",
                                    "text": ai_text,
                                    "size": "sm",
                                    "color": "#444444",
                                    "wrap": True,
                                },
                            ]
                        }
                    }
                    try:
                        # 安全插入到 carousel 最前面
                        if isinstance(msg, dict) and msg.get("type") == "carousel":
                            msg.setdefault("contents", [])
                            contents = msg.get("contents")
                            if isinstance(contents, list):
                                contents.insert(0, ai_bubble)
                    except Exception as e:
                        logging.warning(f"插入 AI bubble 失敗: {e}")

                # 👉 訊息數量：1 則 Flex + 1 則 quick-reply 文字
                messages = [
                    FlexSendMessage(L(uid, "附近廁所（AI 模式）", "Nearby Toilets (AI Mode)"), msg),
                    make_location_quick_reply(L(uid, "想用 AI 再分析其他位置嗎？", "Want AI to analyze another location?")),
                ]

            else:
                # ⚡ 一般模式：原本行為不變
                messages = [
                    FlexSendMessage(L(uid, "附近廁所", "Nearby Toilets"), msg),
                    make_location_quick_reply(
                        L(uid, "想換個地點再找嗎？", "Want to search another location?")
                    ),
                ]

            safe_reply(event, messages)
        else:
            safe_reply(event, make_no_toilet_quick_reply(uid, lat, lon))

    except Exception as e:
        elapsed_ms = int((time.time() - start_ts) * 1000)
        log_analytics_event(
            user_id=uid,
            event_type="error",
            result_count=0,
            success=0,
            response_time_ms=elapsed_ms,
            lat=lat,
            lon=lon,
            area_name=area_name,
            query_text=str(e)[:200]
        )
        logging.error(f"nearby error: {e}", exc_info=True)
        safe_reply(event, TextSendMessage(text=L(uid, "系統忙線中，請稍後再試 🙏", "System is busy. Please try again later 🙏")))
    finally:
        _release_loc_slot()

# === Postback ===
@handler.add(PostbackEvent)
def handle_postback(event):
    uid = event.source.user_id
    data_raw = (event.postback.data or "").strip()

    # =========================
    # 0️⃣ 解析 postback 參數（支援任何順序 / URL encode）
    #    支援：
    #      switch=more&lang=en
    #      switch=main&lang=zh
    #      cmd=nearby&lang=en
    # =========================
    decoded = data_raw
    qs = {}
    _lang = _cmd = _switch = None

    try:
        decoded = unquote(data_raw)
        qs = parse_qs(decoded, keep_blank_values=True)

        _lang   = (qs.get("lang")   or [None])[0]
        _cmd    = (qs.get("cmd")    or [None])[0]
        _switch = (qs.get("switch") or [None])[0]
    except Exception:
        # 解析失敗就走 fallback（保留原字串）
        qs = {}
    # ✅ 只在『切換語言/切換選單』時更新語言；避免一般功能 postback 夾帶 lang 把語言又切回去

    # ✅ richmenuswitch：只做「切換確認」，不要走 gate/不要觸發其它功能
    #    （避免你覺得「沒切成功」其實只是 LINE UI 快取/後端沒回覆）
    if _switch in ("more", "main"):
        # 若切換選單時有帶 lang，才更新使用者語言（切換 menu 才允許改語言，避免一般 cmd 夾帶 lang 造成誤切）
        if _lang in ("en", "zh"):
            try:
                set_user_lang(uid, _lang)
            except Exception as e:
                logging.error(f"set_user_lang failed (switch): uid={uid} lang={_lang} err={e}", exc_info=True)

        # 讀回目前語言（確保真的寫進 DB）
        lang_now = get_user_lang(uid)
        if _lang in ("en", "zh") and lang_now != _lang:
            logging.warning(f"language mismatch after switch: uid={uid} expect={_lang} got={lang_now}")

        safe_reply(
            event,
            TextSendMessage(text=("✅ Menu switched" if lang_now == "en" else "✅ 已切換選單"))
        )
        return

    # ✅ 如果有 cmd，統一收斂成 cmd=xxx（讓你下面原本 cmd 分派能命中）
    if _cmd:
        data = f"cmd={_cmd}"
    else:
        data = decoded  # 保留原字串（例如 lang=en / set_lang:en 這種）

    # =========================
    # 1️⃣ 語言切換（最優先）
    # =========================
    if data in ("lang=en", "lang=zh"):
        try:
            lang = "en" if data == "lang=en" else "zh"
            set_user_lang(uid, lang)
            safe_reply(
                event,
                TextSendMessage(
                    text=("✅ Language switched to English" if lang == "en" else "✅ 已切換為中文")
                )
            )
        except Exception as e:
            logging.error(f"切換語言失敗: {e}", exc_info=True)
            safe_reply(event, TextSendMessage(text=T("lang_switch_fail", uid=uid)))
        return

    if data == "set_lang:en":
        set_user_lang(uid, "en")
        safe_reply(event, TextSendMessage(text=T("lang_switched_en", lang="en")))
        return

    if data == "set_lang:zh":
        set_user_lang(uid, "zh")
        safe_reply(event, TextSendMessage(text=T("lang_switched_zh", lang="zh")))
        return

    # =========================
    # 2️⃣ 重複事件擋掉
    # =========================
    if is_duplicate_and_mark_event(event):
        return

    # =========================
    # 3️⃣ 同意條款 gate
    # =========================
    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg)
        return

    # =========================
    # 🗑️ 我的貢獻：確認 / 刪除 / 取消
    # =========================
    if data.startswith("confirm_delete_my_toilet:"):
        toilet_id = data.split(":", 1)[1].strip()
        safe_reply(event, TextSendMessage(
            text=L(uid, "⚠️ 確定要刪除這筆你新增的廁所嗎？", "⚠️ Delete this submitted toilet?"),
            quick_reply=QuickReply(items=[
                QuickReplyButton(action=PostbackAction(label=L(uid, "確認刪除", "Confirm delete"), data=f"delete_my_toilet:{toilet_id}", display_text=L(uid, "確認刪除", "Confirm delete"))),
                QuickReplyButton(action=PostbackAction(label=L(uid, "取消", "Cancel"), data="cancel_delete_my_toilet", display_text=L(uid, "取消", "Cancel"))),
            ])
        ))
        return

    if data.startswith("delete_my_toilet:"):
        toilet_id = data.split(":", 1)[1].strip()
        ok, reason = delete_my_contribution(uid, toilet_id)
        if ok:
            safe_reply(event, TextSendMessage(text=L(uid, "✅ 已刪除你新增的廁所", "✅ Deleted.")))
        else:
            logging.warning(f"delete_my_toilet failed: uid={uid} id={toilet_id} reason={reason}")
            safe_reply(event, TextSendMessage(text=L(uid, "❌ 刪除失敗，資料可能不存在或不是你新增的", "❌ Delete failed.")))
        return

    if data == "cancel_delete_my_toilet":
        safe_reply(event, TextSendMessage(text=L(uid, "已取消刪除", "Delete cancelled.")))
        return

    # =========================
    # ⭐ 我的最愛：加入 / 移除
    # data format from Flex:
    #   add:{quoted_name}:{lat}:{lon}
    #   remove_fav:{quoted_name}:{lat}:{lon}
    # =========================
    if data.startswith("add:"):
        try:
            _, name_q, lat_s, lon_s = data.split(":", 3)
            name = unquote(name_q).strip()
            ok = add_to_favorites(uid, {
                "name": name,
                "lat": lat_s,
                "lon": lon_s,
                "address": ""
            })
            if ok:
                safe_reply(event, TextSendMessage(text=L(uid, "✅ 已加入最愛", "✅ Added to favorites")))
                log_user_action(
                    query_id="",
                    uid=uid,
                    toilet_id=f"{name}|{lat_s}|{lon_s}",
                    action_type="add_favorite",
                    extra_info=json.dumps({"name": name, "lat": lat_s, "lon": lon_s}, ensure_ascii=False)
                )
            else:
                safe_reply(event, TextSendMessage(text=L(uid, "❌ 加入最愛失敗", "❌ Failed to add favorite")))
        except Exception as e:
            logging.error(f"add favorite postback failed: {e}", exc_info=True)
            safe_reply(event, TextSendMessage(text=L(uid, "❌ 加入最愛失敗", "❌ Failed to add favorite")))
        return

    if data.startswith("remove_fav:"):
        try:
            _, name_q, lat_s, lon_s = data.split(":", 3)
            name = unquote(name_q).strip()
            ok = remove_from_favorites(uid, name, lat_s, lon_s)
            if ok:
                safe_reply(event, TextSendMessage(text=L(uid, "✅ 已移除最愛", "✅ Removed from favorites")))
            else:
                safe_reply(event, TextSendMessage(text=L(uid, "❌ 移除失敗，可能已不在最愛中", "❌ Remove failed or already removed")))
        except Exception as e:
            logging.error(f"remove favorite postback failed: {e}", exc_info=True)
            safe_reply(event, TextSendMessage(text=L(uid, "❌ 移除最愛失敗", "❌ Failed to remove favorite")))
        return
    
    try:
        # ==========================================================
        # 3.5️⃣ Rich Menu 統一指令：cmd=xxxx
        # ==========================================================
        if data.startswith("cmd="):
            cmd = data.split("=", 1)[1].strip().split("&", 1)[0]
            if cmd in ("noop_main", "noop_more"):
                return

            # =========================
            # ✅ 新增：附近廁所（重點）
            # =========================
            if cmd == "nearby":
                mode = get_user_loc_mode(uid)
                safe_reply(
                    event,
                    make_location_quick_reply(
                        L(uid,
                          "📍 請點下方『傳送我的位置』，我立刻幫你找廁所",
                          "📍 Please share your location and I’ll find nearby toilets for you"),
                        mode=mode,
                        uid=uid
                    )
                )
                return

            # 我的最愛
            if cmd == "favs":
                favs = get_user_favorites(uid)
                if not favs:
                    safe_reply(event, TextSendMessage(text=L(uid, "你尚未收藏任何廁所", "You have no favorites yet.")))
                    return

                loc = get_user_location(uid)
                if loc:
                    lat, lon = loc
                    for f in favs:
                        f["distance"] = haversine(lat, lon, f["lat"], f["lon"])

                msg = create_toilet_flex_messages(favs, uid=uid)
                safe_reply(event, FlexSendMessage(L(uid, "我的最愛", "My Favorites"), msg))
                return

            # 使用說明
            if cmd == "help":
                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    "📌 使用說明：\n・點「附近廁所」或直接傳位置\n・可加入最愛、回饋、看 AI 摘要\n・也可切換 AI 推薦模式",
                    "📌 Help:\n• Tap 'Nearby Toilets' or send location\n• Add favorites, leave feedback, view AI summary\n• You can also switch to AI recommendation mode"
                )))
                return

            # 新增廁所
            if cmd == "add":
                base = f"{_base_url()}/add"
                loc = get_user_location(uid)
                if loc:
                    la, lo = loc
                    url = f"{base}?uid={quote(uid)}&lat={la}&lon={lo}#openExternalBrowser=1"
                else:
                    url = f"{base}?uid={quote(uid)}#openExternalBrowser=1"

                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    f"請前往此頁新增廁所：\n{url}",
                    f"Please add a toilet here:\n{url}"
                )))
                return

            # 我的貢獻
            if cmd == "contrib":
                msg = create_my_contrib_flex(uid)
                if msg:
                    safe_reply(event, FlexSendMessage(L(uid, "我新增的廁所", "My Contributions"), msg))
                else:
                    safe_reply(event, TextSendMessage(text=L(uid, "你還沒有新增過廁所喔。", "You haven't added any toilets yet.")))
                return

            # 意見回饋
            if cmd == "feedback":
                form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    f"💡 請透過下列連結回報問題或提供意見：\n{form_url}",
                    f"💡 Please send feedback via:\n{form_url}"
                )))
                return

            # 狀態回報
            if cmd == "status":
                url = _status_liff_url(uid=uid)
                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    f"⚡ 開啟狀態回報：\n{url}",
                    f"⚡ Open status report:\n{url}"
                )))
                return

            # 成就
            if cmd == "ach":
                reply_url = f"{PUBLIC_URL}/achievements_liff?uid={uid}&lang={get_user_lang(uid)}"
                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    f"查看成就 👉 {reply_url}",
                    f"View achievements 👉 {reply_url}"
                )))
                return

            # 徽章
            if cmd == "badges":
                reply_url = f"{PUBLIC_URL}/badges_liff?uid={uid}&lang={get_user_lang(uid)}"
                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    f"查看徽章 👉 {reply_url}",
                    f"View badges 👉 {reply_url}"
                )))
                return

            # 使用回顧
            if cmd == "review":
                summary = build_usage_review_text(uid)
                safe_reply(event, TextSendMessage(text=summary))
                return

            return

        # =========================
        # 4️⃣ Quick Reply：一般位置
        # =========================
        if data == "ask_location":
            mode = get_user_loc_mode(uid)
            safe_reply(
                event,
                make_location_quick_reply(
                    L(uid,
                      "📍 請點下方『傳送我的位置』，我立刻幫你找廁所",
                      "📍 Please share your location and I’ll find nearby toilets for you"),
                    mode=mode,
                    uid=uid
                )
            )
            return

        # =========================
        # 5️⃣ Quick Reply：AI 位置
        # =========================
        if data == "ask_ai_location":
            set_user_loc_mode(uid, "ai")
            safe_reply(
                event,
                make_location_quick_reply(
                    L(uid,
                      "📍 請傳送你的位置，我會用 AI 幫你挑附近最適合的廁所",
                      "📍 Please share your location. I will use AI to pick the best nearby toilets."),
                    mode="ai",
                    uid=uid
                )
            )
            return

    except Exception as e:
        logging.error(f"❌ 處理 postback 失敗: {e}", exc_info=True)

# === 新增廁所頁面 ===
@app.route("/add", methods=["GET"])
def render_add_page():
    uid = request.args.get("uid", "")
    lat = request.args.get("lat", "")
    lon = request.args.get("lon", "")
    preset_address = ""

    if lat and lon:
        try:
            ua_email = os.getenv("CONTACT_EMAIL", "you@example.com")
            url = f"https://nominatim.openstreetmap.org/reverse?format=jsonv2&lat={lat}&lon={lon}&addressdetails=1"
            headers = {"User-Agent": f"ToiletBot/1.0 (+{ua_email})"}
            resp = requests.get(url, headers=headers, timeout=10)
            if resp.status_code == 200:
                data = resp.json()
                a = data.get("address", {})
                pretty = " ".join(filter(None, [
                    a.get("country", ""),
                    a.get("state", a.get("region", "")),
                    a.get("city", a.get("town", a.get("village", a.get("county", "")))),
                    a.get("suburb", a.get("neighbourhood", "")),
                    a.get("road", ""),
                    a.get("house_number", ""),
                    a.get("postcode", "")
                ])).strip()
                preset_address = pretty or data.get("display_name", "")
        except Exception as e:
            logging.warning(f"reverse geocode 失敗: {e}")

    return render_template(
        "submit_toilet.html",
        preset_address=preset_address,
        preset_lat=lat,
        preset_lon=lon
    )

ADMIN_TOKEN = os.getenv("ADMIN_TOKEN", "")

@app.route("/api/events")
def api_events():
    if not _maintenance_auth_ok():
        return jsonify({"ok": False, "message": "unauthorized"}), 401

    conn = _get_db()
    cur = conn.cursor()

    cur.execute("""
        SELECT created_at, user_id, event_type,
               result_count, response_time_ms, success
        FROM analytics_events
        WHERE response_time_ms > 0
        ORDER BY created_at DESC
        LIMIT 100
    """)

    rows = cur.fetchall()

    events = []
    for r in rows:
        events.append({
            "time": str(r[0]),
            "user": mask_user_id(r[1]),
            "type": r[2],
            "result": r[3],
            "response_time": r[4],
            "status": "success" if r[5] else "failed"
        })

    cur.close()
    conn.close()

    return jsonify(events)

@app.route("/api/line-insights")
def api_line_insights():
    if not _maintenance_auth_ok():
        return jsonify({"ok": False, "message": "unauthorized"}), 401

    try:
        headers = {
            "Authorization": f"Bearer {CHANNEL_ACCESS_TOKEN}"
        }

        tw_now = datetime.now(timezone(timedelta(hours=8)))
        query_date = (tw_now.date() - timedelta(days=1)).isoformat()

        followers = 0
        targeted = 0
        blocks = 0
        block_rate = 0.0
        gender = []
        age = []
        area = []
        app_type = []
        subscription_period = []

        r = requests.get(
            f"https://api.line.me/v2/bot/insight/followers?date={query_date}",
            headers=headers,
            timeout=10
        )
        if r.status_code == 200:
            j = r.json()
            followers = j.get("followers", 0) or 0
            targeted = j.get("targetedReaches", 0) or 0
            blocks = j.get("blocks", 0) or 0
            block_rate = round((blocks / followers) * 100, 1) if followers else 0.0
        else:
            logging.warning(f"followers insight failed: {r.status_code} {r.text}")

        r2 = requests.get(
            "https://api.line.me/v2/bot/insight/demographic",
            headers=headers,
            timeout=10
        )
        if r2.status_code == 200:
            j = r2.json()

            gender = [
                {"label": item.get("gender"), "percentage": item.get("percentage", 0)}
                for item in j.get("genders", [])
            ]
            age = [
                {"label": item.get("age"), "percentage": item.get("percentage", 0)}
                for item in j.get("ages", [])
            ]
            area = [
                {"label": item.get("area"), "percentage": item.get("percentage", 0)}
                for item in j.get("areas", [])
            ]
            app_type = [
                {"label": item.get("appType"), "percentage": item.get("percentage", 0)}
                for item in j.get("appTypes", [])
            ]
            subscription_period = [
                {"label": item.get("subscriptionPeriod"), "percentage": item.get("percentage", 0)}
                for item in j.get("subscriptionPeriods", [])
            ]
        else:
            logging.warning(f"demographic insight failed: {r2.status_code} {r2.text}")

        return jsonify({
            "followers": followers,
            "targetedReaches": targeted,
            "blocks": blocks,
            "blockRate": block_rate,
            "gender": gender,
            "age": age,
            "area": area,
            "appType": app_type,
            "subscriptionPeriod": subscription_period
        })
    except Exception as e:
        logging.exception("api_line_insights failed")
        return jsonify({
            "followers": 0,
            "targetedReaches": 0,
            "blocks": 0,
            "blockRate": 0,
            "gender": [],
            "age": [],
            "area": [],
            "appType": [],
            "subscriptionPeriod": [],
            "error": str(e)
        }), 200
    

# === Auto Verification 1.1：使用者新增廁所自動驗證（全球座標 + 場域感知 + 高速批次） ===
def _valid_global_coordinate(lat, lon):
    """只檢查是否為合法地球座標，不再寫死台灣。"""
    try:
        lat = float(lat); lon = float(lon)
    except Exception:
        return False
    return -90 <= lat <= 90 and -180 <= lon <= 180


def _primary_region_risk(lat, lon):
    """
    選用功能：主要服務區域風險。
    預設不啟用，避免誤殺海外資料。
    若未來要限制主要服務區，可在 Render 設：
      AUTO_VERIFY_PRIMARY_BBOX=21.5,118.0,26.5,123.5
    格式：min_lat,min_lon,max_lat,max_lon
    """
    bbox = (os.getenv("AUTO_VERIFY_PRIMARY_BBOX") or "").strip()
    if not bbox:
        return False
    try:
        min_lat, min_lon, max_lat, max_lon = [float(x.strip()) for x in bbox.split(",")]
        lat = float(lat); lon = float(lon)
        return not (min_lat <= lat <= max_lat and min_lon <= lon <= max_lon)
    except Exception:
        return False



# === Auto Verification 1.5.1：地理資料品質驗證輔助函式（缺漏修正） ===
def _normalize_text_for_verify(text):
    """Normalize text for rule-based verification / duplicate checks."""
    s = str(text or "").strip().lower()
    s = re.sub(r"[\s\u3000,，。．.、;；:：/\\|｜()（）\[\]【】{}<>《》\-＿_]+", "", s)
    return s


def _has_meaningful_address(address):
    """地址是否有基本辨識度；不是一定要完整門牌，但不能只有極短文字。"""
    s = _normalize_text_for_verify(address)
    if len(s) < 5:
        return False
    weak = {"無", "沒有", "未知", "不清楚", "none", "null", "na", "n/a"}
    return s not in weak


def _address_coordinate_check(lat, lon, address):
    """
    地址—座標一致性檢查。
    預設關閉外部 geocoding，避免批次驗證變慢；設定 AUTO_VERIFY_GEOCODE_ENABLE=1 後啟用。
    回傳：(flag, distance_m, reason)；flag 為 None 表示不標記。
    """
    if os.getenv("AUTO_VERIFY_GEOCODE_ENABLE", "0") != "1":
        return None, None, None
    if not address or not _valid_global_coordinate(lat, lon):
        return None, None, None
    try:
        g_lat, g_lon = geocode_address(address)
        if g_lat is None or g_lon is None:
            return "address_geocode_failed", None, "地址無法轉換為座標，建議人工確認"
        d = haversine(float(lat), float(lon), float(g_lat), float(g_lon))
        if d >= float(os.getenv("AUTO_VERIFY_ADDR_COORD_HIGH_M", "800")):
            return "address_coordinate_mismatch_high", round(d, 1), f"地址轉換座標與填寫座標相差約 {round(d)} 公尺"
        if d >= float(os.getenv("AUTO_VERIFY_ADDR_COORD_MEDIUM_M", "250")):
            return "address_coordinate_mismatch_medium", round(d, 1), f"地址轉換座標與填寫座標相差約 {round(d)} 公尺"
        return None, round(d, 1), None
    except Exception as e:
        logging.warning(f"address-coordinate check failed: {e}")
        return None, None, None


def _spatial_context_signal(lat, lon, context=None, exclude_id=None, radius_m=None):
    """
    空間孤立/離群標記：只作 soft flag，不直接 rejected。
    目標是抓「附近完全沒有參考資料且本身資訊不足」的可疑資料；偏鄉資料不能被誤殺。
    """
    if not _valid_global_coordinate(lat, lon):
        return {"nearby_count": 0, "nearest_m": None, "flag": None}
    if radius_m is None:
        radius_m = float(os.getenv("AUTO_VERIFY_SPATIAL_RADIUS_M", "800"))
    if not (context and isinstance(context, dict) and isinstance(context.get("items"), list)):
        context = _build_auto_verify_context()
    nearby = 0
    nearest = None
    try:
        lat_f = float(lat); lon_f = float(lon)
        for r in context.get("items") or []:
            try:
                if exclude_id is not None and str(r.get("id")) == str(exclude_id) and (r.get("source") in ("neon", "user_toilets", "user_added")):
                    continue
                r_lat = float(r.get("lat")); r_lon = float(r.get("lon"))
            except Exception:
                continue
            if not _in_bbox(r_lat, r_lon, lat_f, lon_f, radius_m):
                continue
            try:
                d = haversine(lat_f, lon_f, r_lat, r_lon)
            except Exception:
                continue
            if d <= radius_m:
                nearby += 1
                if nearest is None or d < nearest:
                    nearest = d
        flag = None
        if nearby == 0:
            flag = "spatial_outlier_candidate"
        return {"nearby_count": nearby, "nearest_m": round(nearest, 1) if nearest is not None else None, "flag": flag}
    except Exception:
        return {"nearby_count": 0, "nearest_m": None, "flag": None}

def _text_similarity(a, b):
    a = (a or "").strip().lower()
    b = (b or "").strip().lower()
    if not a or not b:
        return 0.0
    return SequenceMatcher(None, a, b).ratio()


def _compact_toilet_name(name):
    s = (name or "").strip().lower()
    for token in ["廁所", "公廁", "男廁", "女廁", "無障礙", "親子", "性別友善", "toilet", "restroom", "wc"]:
        s = s.replace(token, "")
    return re.sub(r"\s+", "", s)


def _facility_context(name="", address="", floor_hint="", entrance_hint="", access_note=""):
    """
    粗略判斷新增資料所屬場域，讓缺樓層/入口的扣分更合理。
    outdoor：公園、流動公廁、宮廟、加油站等，通常不一定需要樓層。
    shop：便利商店/店家型，是否開放給外部使用較不確定，需較保守。
    indoor_complex：商場、車站、醫院、學校、大樓等，樓層/入口資訊較重要。
    generic：名稱太籠統或資訊不足。
    """
    text = " ".join([str(name or ""), str(address or ""), str(floor_hint or ""), str(entrance_hint or ""), str(access_note or "")]).lower()

    shop_keywords = [
        "7-11", "711", "統一超商", "全家", "familymart", "萊爾富", "ok超商", "ok mart",
        "全聯", "寶雅", "小北", "屈臣氏", "康是美", "麥當勞", "mos", "星巴克",
        "便利商店", "超商"
    ]
    indoor_keywords = [
        "百貨", "商場", "購物中心", "mall", "車站", "捷運", "高鐵", "火車站", "轉運站",
        "醫院", "診所", "學校", "大學", "高中", "國中", "國小", "校區",
        "大樓", "辦公", "地下街", "機場", "航廈", "市場", "影城", "圖書館", "美術館", "博物館"
    ]
    outdoor_keywords = [
        "公園", "流動公廁", "活動廁所", "宮", "廟", "寺", "教堂", "戲台", "加油站",
        "服務區", "休息站", "停車場", "海邊", "步道", "廣場", "河濱", "運動場"
    ]

    if any(k.lower() in text for k in shop_keywords):
        return "shop"
    if any(k.lower() in text for k in indoor_keywords):
        return "indoor_complex"
    if any(k.lower() in text for k in outdoor_keywords):
        return "outdoor"
    return "generic"


def _is_test_or_garbage_name(name):
    s = (name or "").strip().lower()
    if not s:
        return True
    garbage = {"test", "testing", "aaa", "aaaa", "123", "111", "測試", "測試資料", "無", "none", "null"}
    return s in garbage


def _build_auto_verify_context():
    """
    高速批次驗證用：一次載入 user_toilets + public_toilets.csv。
    避免每驗證一筆就重新掃 DB / CSV，讓 reverify 速度大幅提升。
    """
    items = []

    if POSTGRES_ENABLED:
        try:
            conn = _pg_connect()
            cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
            cur.execute("""
                SELECT id, name, address, lat, lon, verification_status, source
                FROM user_toilets
                WHERE lat IS NOT NULL AND lon IS NOT NULL
                LIMIT 20000
            """)
            for r in cur.fetchall():
                try:
                    items.append({
                        "source": r.get("source") or "user_toilets",
                        "id": r.get("id"),
                        "name": r.get("name") or "",
                        "address": r.get("address") or "",
                        "lat": float(r.get("lat")),
                        "lon": float(r.get("lon")),
                        "verification_status": r.get("verification_status") or "pending"
                    })
                except Exception:
                    continue
            conn.close()
        except Exception as e:
            logging.warning(f"_build_auto_verify_context user_toilets failed: {e}")

    try:
        if os.path.exists(TOILETS_FILE_PATH):
            with open(TOILETS_FILE_PATH, "r", encoding="utf-8-sig", newline="") as f:
                reader = csv.DictReader(f)
                for row in reader:
                    try:
                        lat = float(row.get("latitude") or row.get("lat") or "")
                        lon = float(row.get("longitude") or row.get("lon") or "")
                    except Exception:
                        continue
                    items.append({
                        "source": "public_csv",
                        "id": row.get("number") or row.get("id") or "",
                        "name": row.get("name") or "",
                        "address": row.get("address") or "",
                        "lat": lat,
                        "lon": lon,
                        "verification_status": "approved"
                    })
    except Exception as e:
        logging.warning(f"_build_auto_verify_context public_csv failed: {e}")

    return {"items": items, "built_at": time.time()}



_CHAIN_BRANDS = {
    "7-11": ["7-11", "7-eleven", "711", "統一超商"],
    "familymart": ["全家", "familymart"],
    "hilife": ["萊爾富", "hilife"],
    "okmart": ["ok超商", "ok mart"],
    "pxmart": ["全聯"],
    "poya": ["寶雅"],
    "simplemart": ["美廉社"],
    "mcdonalds": ["麥當勞", "mcdonald"],
    "starbucks": ["星巴克", "starbucks"],
}

_GENERIC_DUP_NAMES = {
    "廁所", "公廁", "公共廁所", "男廁", "女廁", "洗手間", "化妝室",
    "toilet", "restroom", "wc", "bathroom", "無障礙廁所", "親子廁所"
}


def _detect_chain_brand(text):
    """回傳連鎖品牌 key；同品牌不等於重複，只能當弱輔助。"""
    s = (text or "").strip().lower()
    if not s:
        return ""
    for brand, aliases in _CHAIN_BRANDS.items():
        for a in aliases:
            if a.lower() in s:
                return brand
    return ""


def _strip_chain_brand_for_dup(text):
    """移除連鎖品牌與廁所通用詞，留下門市/場域識別用。"""
    s = _compact_toilet_name(text or "")
    for aliases in _CHAIN_BRANDS.values():
        for a in aliases:
            s = s.replace(a.lower().replace(" ", ""), "")
    s = re.sub(r"[-_()（）・,，。．\s]+", "", s)
    return s


def _is_generic_duplicate_name(text):
    """判斷名稱是否太籠統；籠統名稱不能作為重複資料的強證據。"""
    raw = (text or "").strip().lower()
    compact = _compact_toilet_name(raw)
    no_brand = _strip_chain_brand_for_dup(raw)
    if not raw:
        return True
    if raw in _GENERIC_DUP_NAMES or compact in _GENERIC_DUP_NAMES:
        return True
    # 只剩品牌或只剩很短字串，例如 7-11、全家、寶雅、廁所
    if len(no_brand) <= 1:
        return True
    return False


def _strong_name_similarity_for_dup(a, b):
    """
    名稱相似度只作為輔助：
    - 泛稱或連鎖品牌本身不當強證據
    - 先移除「廁所/公廁」與品牌名，再比對門市/場域識別字
    """
    if _is_generic_duplicate_name(a) or _is_generic_duplicate_name(b):
        return 0.0

    a_core = _strip_chain_brand_for_dup(a)
    b_core = _strip_chain_brand_for_dup(b)
    raw_sim = _text_similarity(a, b)
    core_sim = _text_similarity(a_core, b_core)

    # 如果兩邊都是同一連鎖品牌，但沒有明確門市/場域識別，不用名稱判重複
    brand_a = _detect_chain_brand(a)
    brand_b = _detect_chain_brand(b)
    if brand_a and brand_b and brand_a == brand_b and (len(a_core) < 2 or len(b_core) < 2):
        return 0.0

    return max(raw_sim * 0.85, core_sim)


def _address_similarity_for_dup(a, b):
    """地址比名稱更重要，但兩邊都要有足夠長度才可靠。"""
    a = (a or "").strip()
    b = (b or "").strip()
    if len(a) < 5 or len(b) < 5:
        return 0.0
    return _text_similarity(a, b)


def _duplicate_level(distance_m, name_sim, addr_sim, same_brand=False):
    """
    Duplicate Detection 1.2：距離優先、地址優先，名稱只輔助。
    回傳 high / medium / low / none。
    """
    try:
        d = float(distance_m)
    except Exception:
        return "none"

    # 地址高度相似 + 很近，才是最穩的重複證據
    if d <= 30 and addr_sim >= 0.72:
        return "high"

    # 非泛稱的明確場域/門市名稱高度相似，且距離很近
    if d <= 25 and name_sim >= 0.88:
        return "high"

    # 同品牌不能單獨判重複；必須還有地址或明確名稱輔助
    if same_brand and d <= 20 and (addr_sim >= 0.60 or name_sim >= 0.82):
        return "high"

    if d <= 50 and addr_sim >= 0.62:
        return "medium"
    if d <= 40 and name_sim >= 0.82:
        return "medium"
    if same_brand and d <= 35 and (addr_sim >= 0.52 or name_sim >= 0.76):
        return "medium"

    # 極近但沒有文字證據，只能當低風險提醒，不直接讓資料 pending
    if d <= 10 and (addr_sim >= 0.35 or name_sim >= 0.55):
        return "low"

    return "none"


def find_similar_toilets(lat, lon, name="", address="", radius_m=50, limit=8, context=None, exclude_id=None):
    """
    找疑似重複廁所資料。
    Duplicate Detection 1.2：
    - 距離是必要前提；距離遠不因名稱相似就判重複。
    - 地址相似度比名稱更重要。
    - 「7-11 / 全家 / 公廁」這類泛稱或品牌名不能當重複主證據。
    """
    out = []
    try:
        lat = float(lat); lon = float(lon)
    except Exception:
        return []

    target_name = name or ""
    target_addr = address or ""
    target_brand = _detect_chain_brand(target_name)

    if not (context and isinstance(context, dict) and isinstance(context.get("items"), list)):
        context = _build_auto_verify_context()

    for r in context.get("items") or []:
        try:
            # 批次重驗時，避免把自己判成自己的重複資料
            if exclude_id is not None and str(r.get("id")) == str(exclude_id) and (r.get("source") in ("neon", "user_toilets", "user_added")):
                continue
            t_lat = float(r.get("lat")); t_lon = float(r.get("lon"))
        except Exception:
            continue
        if not _in_bbox(t_lat, t_lon, lat, lon, radius_m):
            continue
        try:
            d = haversine(lat, lon, t_lat, t_lon)
        except Exception:
            continue
        if d > radius_m:
            continue

        nm = r.get("name") or ""
        ad = r.get("address") or ""
        cand_brand = _detect_chain_brand(nm)
        same_brand = bool(target_brand and cand_brand and target_brand == cand_brand)
        name_sim = _strong_name_similarity_for_dup(target_name, nm)
        addr_sim = _address_similarity_for_dup(target_addr, ad)
        level = _duplicate_level(d, name_sim, addr_sim, same_brand=same_brand)

        if level != "none":
            out.append({
                "source": r.get("source") or "user_toilets",
                "id": r.get("id") or "",
                "name": nm,
                "address": ad,
                "distance_m": round(d, 1),
                "name_similarity": round(name_sim, 3),
                "address_similarity": round(addr_sim, 3),
                "same_brand": same_brand,
                "duplicate_level": level,
                "verification_status": r.get("verification_status") or "pending"
            })

    level_order = {"high": 0, "medium": 1, "low": 2}
    out.sort(key=lambda x: (
        level_order.get(x.get("duplicate_level"), 9),
        float(x.get("distance_m") or 9999),
        -max(float(x.get("address_similarity") or 0), float(x.get("name_similarity") or 0))
    ))
    return out[:limit]


def auto_verify_user_toilet(toilet, context=None, exclude_id=None):
    """
    Auto Verification 1.5.4：群眾地理資料品質驗證完整版（實用修正版）。
    只輸出三種 verification_status：approved / pending / rejected。

    設計原則：
    - rejected 只保留給明顯錯誤：非法座標、空白/測試名稱。
    - pending 只保留給真正需要人工確認的資料：高度/中度重複、名稱太籠統、地址缺失且場域不清。
    - shop_access_unclear、missing_entrance_hint、spatial_outlier_candidate 預設是 soft flag，會提醒但不一定把資料打成 pending。
    - 避免 1.5 過嚴導致大量資料從 approved 變 pending。
    """
    name = (toilet.get("name") or "").strip()
    address = (toilet.get("address") or "").strip()
    lat = toilet.get("lat")
    lon = toilet.get("lon")
    level = (toilet.get("level") or "").strip()
    floor_hint = (toilet.get("floor_hint") or "").strip()
    entrance_hint = (toilet.get("entrance_hint") or "").strip()
    access_note = (toilet.get("access_note") or "").strip()
    open_hours = (toilet.get("open_hours") or "").strip()

    score = 82
    flags = []
    reasons = []
    soft_flags = set()

    # 1) 基本欄位與座標合法性
    if _is_test_or_garbage_name(name):
        score -= 80
        flags.append("invalid_or_test_name")
        reasons.append("名稱空白或疑似測試資料")

    coord_ok = _valid_global_coordinate(lat, lon)
    if not coord_ok:
        score -= 95
        flags.append("invalid_coordinate")
        reasons.append("座標不是合法地球座標")
    elif _primary_region_risk(lat, lon):
        score -= 2
        flags.append("outside_primary_region")
        soft_flags.add("outside_primary_region")
        reasons.append("資料位於目前主要服務區域外，建議人工確認")

    facility_type = _facility_context(name, address, floor_hint, entrance_hint, access_note)

    # 2) 名稱品質：只判是否可辨識，不拿泛稱當重複主證據
    generic_names = {"廁所", "公廁", "男廁", "女廁", "無名稱", "toilet", "restroom", "wc", "洗手間", "化妝室"}
    compact_name = _normalize_text_for_verify(name)
    compact_generic = {_normalize_text_for_verify(x) for x in generic_names}
    if not name or len(compact_name) < 2 or name.lower() in generic_names or compact_name in compact_generic:
        score -= 25
        flags.append("name_too_generic")
        reasons.append("名稱過短或過於籠統")
    else:
        score += 7

    # 3) 資料完整度：依場域不同設定門檻
    has_address = _has_meaningful_address(address)
    has_floor = bool(floor_hint or level)
    has_entrance = bool(entrance_hint or access_note)
    has_access_info = bool(entrance_hint or access_note or open_hours)

    if has_address:
        score += 10
    else:
        # 缺地址不一定 pending；要看名稱和場域是否足夠清楚
        score -= 4
        flags.append("missing_address")
        soft_flags.add("missing_address")
        reasons.append("缺少可辨識地址或場域位置")

    if facility_type == "indoor_complex":
        if has_floor:
            score += 7
        else:
            score -= 3
            flags.append("missing_floor_hint")
            soft_flags.add("missing_floor_hint")
            reasons.append("多樓層或室內場域缺少樓層資訊")
        if has_entrance:
            score += 7
        else:
            score -= 3
            flags.append("missing_entrance_hint")
            soft_flags.add("missing_entrance_hint")
            reasons.append("室內或大型場域缺少入口/位置提示")
    elif facility_type == "shop":
        if has_floor:
            score += 3
        # 店家型資料：沒有開放/入口說明時先提醒，不直接全打 pending
        if has_access_info:
            score += 7
        else:
            score -= 3
            flags.append("shop_access_unclear")
            soft_flags.add("shop_access_unclear")
            reasons.append("店家型資料缺少是否開放或入口說明")
        if not has_address:
            score -= 10
            flags.append("shop_missing_address")
            reasons.append("店家型資料缺少地址，需人工確認")
    elif facility_type == "outdoor":
        if has_entrance:
            score += 6
        elif not has_address:
            score -= 2
            flags.append("outdoor_location_unclear")
            soft_flags.add("outdoor_location_unclear")
            reasons.append("戶外場域缺少地址或位置提示")
    else:
        if has_floor:
            score += 3
        if has_entrance:
            score += 4
        else:
            score -= 1
            flags.append("missing_entrance_hint")
            soft_flags.add("missing_entrance_hint")

    if open_hours:
        score += 2

    # 4) 重複資料偵測：距離 + 地址優先，名稱弱化
    similar = []
    if coord_ok:
        similar = find_similar_toilets(lat, lon, name=name, address=address, radius_m=80, limit=8, context=context, exclude_id=exclude_id)

    high_dup = [s_item for s_item in similar if s_item.get("duplicate_level") == "high"]
    medium_dup = [s_item for s_item in similar if s_item.get("duplicate_level") == "medium"]
    low_dup = [s_item for s_item in similar if s_item.get("duplicate_level") == "low"]

    # 1.5.4：重複資料改為「嚴格重複才進 pending」
    # 原本 high duplicate 太容易把靠近官方/既有資料的點全部打成 pending。
    # 現在 possible_duplicate_high / medium 先作為提醒；只有幾乎同點、且有強文字證據時，才標 strict_duplicate。
    strict_dup = []
    if high_dup:
        flags.append("possible_duplicate_high")
        soft_flags.add("possible_duplicate_high")
        reasons.append("附近已有相似廁所資料，系統標記為疑似重複提醒")
        for s_item in high_dup:
            try:
                d_val = float(s_item.get("distance_m") or 9999)
                name_val = float(s_item.get("name_similarity") or 0)
                addr_val = float(s_item.get("address_similarity") or 0)
                src_val = str(s_item.get("source") or "").lower()
                # 極近 + 地址或明確名稱高度相似，才是需要人工合併/確認的嚴格重複。
                # public_csv 只當參考來源，除非幾乎同點且地址/名稱非常像，否則不硬擋。
                if d_val <= 8 and (addr_val >= 0.78 or name_val >= 0.90):
                    strict_dup.append(s_item)
                elif src_val not in ("public_csv", "government") and d_val <= 12 and (addr_val >= 0.70 or name_val >= 0.86):
                    strict_dup.append(s_item)
            except Exception:
                pass
        if strict_dup:
            score -= 18
            flags.append("strict_duplicate")
            reasons.append("疑似與既有資料幾乎同點且文字高度相似，需人工確認是否合併")
        else:
            score -= 2
    elif medium_dup:
        flags.append("possible_duplicate_medium")
        soft_flags.add("possible_duplicate_medium")
        reasons.append("附近有相似廁所資料，僅作維護提醒")
        score -= 1
    elif low_dup:
        flags.append("possible_duplicate_low")
        soft_flags.add("possible_duplicate_low")

    # 5) 地址—座標一致性：預設不啟用 geocoding；啟用後仍以 pending 為主，不直接 rejected
    addr_flag, addr_dist, addr_reason = _address_coordinate_check(lat, lon, address)
    if addr_flag:
        flags.append(addr_flag)
        reasons.append(addr_reason or "地址與座標可能不一致")
        if addr_flag.endswith("high"):
            score -= 8
        elif addr_flag.endswith("medium"):
            score -= 3
        else:
            score -= 4
        soft_flags.add(addr_flag)

    # 6) 空間孤立/離群：soft flag；只有資料也不足時才 pending
    spatial = _spatial_context_signal(lat, lon, context=context, exclude_id=exclude_id) if coord_ok else {}
    if spatial.get("flag"):
        flags.append(spatial["flag"])
        soft_flags.add(spatial["flag"])
        if not has_address or "name_too_generic" in flags:
            score -= 3
            reasons.append("附近缺少參考資料且本筆資訊不足，建議人工確認")
        else:
            score -= 1

    score = max(0, min(100, int(round(score))))

    hard_reject = {"invalid_coordinate", "invalid_or_test_name"}
    # 1.5.4 實用化：只把真正需要人工處理的項目列為 hard pending。
    # high/medium duplicate、缺入口、店家開放不明都只當維護提醒，不直接卡住自動通過。
    hard_pending = {"name_too_generic", "strict_duplicate"}

    if any(f in flags for f in hard_reject):
        status = "rejected"
    elif any(f in flags for f in hard_pending):
        status = "pending"
    elif "shop_missing_address" in flags and score < 60:
        status = "pending"
    elif facility_type == "indoor_complex" and ("missing_floor_hint" in flags or "missing_entrance_hint" in flags) and score < 50:
        status = "pending"
    elif "missing_address" in flags and facility_type == "generic" and score < 48:
        status = "pending"
    elif any(f.startswith("address_coordinate_mismatch_high") for f in flags) and score < 52:
        status = "pending"
    elif "outside_primary_region" in flags and score < 48:
        status = "pending"
    elif score >= 45:
        status = "approved"
    else:
        status = "pending"

    if not reasons:
        if status == "approved":
            reasons.append("資料完整且未發現明顯重複，系統自動判定為低風險")
        elif status == "pending":
            reasons.append("資料可用但仍建議後台確認")
        else:
            reasons.append("資料存在明顯錯誤，系統建議排除")

    return {
        "verification_status": status,
        "auto_verification_score": score,
        "auto_verification_result": status,
        "auto_verification_reason": "；".join(dict.fromkeys(reasons)),
        "risk_flags": sorted(set(flags)),
        "similar_toilets": similar[:5],
        "facility_type": facility_type,
        "verification_version": "auto_verify_1_5_4",
        "soft_flags": sorted(soft_flags),
        "address_coordinate_distance_m": addr_dist,
        "spatial_context": spatial,
    }

# === 使用者新增廁所 API ===
@app.route("/submit_toilet", methods=["POST"])
def submit_toilet():
    if not POSTGRES_ENABLED:
        return {"success": False, "message": "資料庫尚未啟用，無法新增廁所"}, 503
    try:
        data = request.get_json(force=True, silent=False) or {}

        uid   = (data.get("user_id") or "web").strip()
        name  = (data.get("name") or "").strip()
        addr  = (data.get("address") or "").strip()

        level          = (data.get("level") or "").strip()
        floor_hint     = (data.get("floor_hint") or "").strip()
        entrance_hint  = (data.get("entrance_hint") or "").strip()
        access_note    = (data.get("access_note") or "").strip()
        open_hours     = (data.get("open_hours") or "").strip()

        lat_in = (data.get("lat") or "").strip()
        lon_in = (data.get("lon") or "").strip()
        logging.info(f"📥 收到新增廁所表單: name={name!r}, lat={lat_in!r}, lon={lon_in!r}")

        # 必填檢查
        if not name or not addr:
            return {"success": False, "message": "請提供『廁所名稱』與『地址』"}, 400

        # 位置描述基本檢查
        if floor_hint and len(floor_hint) < 4:
            return {"success": False, "message": "『位置描述』太短，請至少 4 個字"}, 400

        # 未提供位置描述則嘗試由名稱推斷
        if not floor_hint:
            inferred = _floor_from_name(name)
            if inferred:
                floor_hint = inferred

        # 座標解析與地理編碼
        lat_f, lon_f = (None, None)
        if lat_in and lon_in:
            lat_f, lon_f = _parse_lat_lon(lat_in, lon_in)
        if lat_f is None or lon_f is None:
            lat_f, lon_f = geocode_address(addr)
        if lat_f is None or lon_f is None:
            return {"success": False, "message": "地址轉換失敗，請修正地址或提供座標"}, 400

        lat_s, lon_s = norm_coord(lat_f), norm_coord(lon_f)

        # Auto Verification 1.0：表單送出後自動判定 approved / pending / rejected
        candidate = {
            "user_id": uid,
            "name": name,
            "address": addr,
            "lat": float(lat_s),
            "lon": float(lon_s),
            "level": level,
            "floor_hint": floor_hint,
            "entrance_hint": entrance_hint,
            "access_note": access_note,
            "open_hours": open_hours,
        }
        av = auto_verify_user_toilet(candidate)
        verification_status = av["verification_status"]
        verification_score = int(av["auto_verification_score"])
        verification_reason = av["auto_verification_reason"]
        risk_flags_json = json.dumps(av.get("risk_flags") or [], ensure_ascii=False)
        similar_json = json.dumps(av.get("similar_toilets") or [], ensure_ascii=False)

        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO user_toilets (
                user_id, name, address, lat, lon,
                level, floor_hint, entrance_hint,
                access_note, open_hours,
                verification_status, verification_score, verification_reason,
                auto_verification_score, auto_verification_result,
                auto_verification_reason, risk_flags, similar_toilets_json,
                created_at, updated_at, source
            )
            VALUES (
                %s, %s, %s, %s, %s,
                %s, %s, %s,
                %s, %s,
                %s, %s, %s,
                %s, %s,
                %s, %s, %s,
                NOW(), NOW(), 'neon'
            )
            ON CONFLICT (user_id, name, lat, lon)
            DO UPDATE SET
                address = EXCLUDED.address,
                level = EXCLUDED.level,
                floor_hint = EXCLUDED.floor_hint,
                entrance_hint = EXCLUDED.entrance_hint,
                access_note = EXCLUDED.access_note,
                open_hours = EXCLUDED.open_hours,
                verification_status = EXCLUDED.verification_status,
                verification_score = EXCLUDED.verification_score,
                verification_reason = EXCLUDED.verification_reason,
                auto_verification_score = EXCLUDED.auto_verification_score,
                auto_verification_result = EXCLUDED.auto_verification_result,
                auto_verification_reason = EXCLUDED.auto_verification_reason,
                risk_flags = EXCLUDED.risk_flags,
                similar_toilets_json = EXCLUDED.similar_toilets_json,
                updated_at = NOW()
            RETURNING id
        """, (
            uid, name, addr, float(lat_s), float(lon_s),
            level, floor_hint, entrance_hint,
            access_note, open_hours,
            verification_status, verification_score, verification_reason,
            verification_score, verification_status,
            verification_reason, risk_flags_json, similar_json,
        ))
        new_id = cur.fetchone()[0]
        conn.commit()
        conn.close()
        try: _CACHE.clear()
        except Exception: pass

        if verification_status == "approved":
            msg = f"✅ 已收到 {name}，系統自動驗證為低風險，已加入推薦資料。"
        elif verification_status == "rejected":
            msg = f"⚠️ 已收到 {name}，但系統判定資料風險較高，暫不加入推薦。原因：{verification_reason}"
        else:
            msg = f"✅ 已收到 {name}，目前列為待確認資料。原因：{verification_reason}"

        logging.info(f"📝 submit_toilet 已寫入 Neon id={new_id} name={name} status={verification_status} score={verification_score}")
        return {
            "success": True,
            "message": msg,
            "id": new_id,
            "verification_status": verification_status,
            "auto_verification_score": verification_score,
            "auto_verification_result": verification_status,
            "risk_flags": av.get("risk_flags") or [],
            "similar_toilets": av.get("similar_toilets") or [],
            "facility_type": av.get("facility_type")
        }

    except Exception as e:
        logging.error(f"❌ 新增廁所錯誤:\n{traceback.format_exc()}")
        return {"success": False, "message": "伺服器錯誤"}, 500


# === Admin：重新自動判定既有使用者新增資料 ===
@app.route("/admin/reverify-user-toilets", methods=["POST", "GET"])
def admin_reverify_user_toilets():
    if not _maintenance_auth_ok():
        return jsonify({"ok": False, "message": "unauthorized"}), 401
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "message": "postgres disabled"}), 503

    apply_update = (request.args.get("apply") or "0").strip() != "0"
    limit = int(request.args.get("limit") or "500")
    updated = 0
    preview = []
    counts = {"approved": 0, "pending": 0, "rejected": 0}

    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT id, user_id, name, address, lat, lon, level, floor_hint,
                   entrance_hint, access_note, open_hours, verification_status
            FROM user_toilets
            ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST
            LIMIT %s
        """, (limit,))
        rows = cur.fetchall()

        verify_context = _build_auto_verify_context()

        for r in rows:
            av = auto_verify_user_toilet(r, context=verify_context, exclude_id=r.get("id"))
            st = av["verification_status"]
            counts[st] = counts.get(st, 0) + 1
            preview.append({
                "id": r.get("id"),
                "name": r.get("name"),
                "old_status": r.get("verification_status") or "pending",
                "new_status": st,
                "score": av["auto_verification_score"],
                "facility_type": av.get("facility_type"),
                "reason": av["auto_verification_reason"],
                "risk_flags": av.get("risk_flags") or [],
                "verification_version": av.get("verification_version"),
                "soft_flags": av.get("soft_flags") or [],
                "address_coordinate_distance_m": av.get("address_coordinate_distance_m"),
                "spatial_context": av.get("spatial_context") or {}
            })
            if apply_update:
                cur.execute("""
                    UPDATE user_toilets
                    SET verification_status = %s,
                        verification_score = %s,
                        verification_reason = %s,
                        auto_verification_score = %s,
                        auto_verification_result = %s,
                        auto_verification_reason = %s,
                        risk_flags = %s,
                        similar_toilets_json = %s,
                        updated_at = NOW()
                    WHERE id = %s
                """, (
                    st,
                    int(av["auto_verification_score"]),
                    av["auto_verification_reason"],
                    int(av["auto_verification_score"]),
                    st,
                    av["auto_verification_reason"],
                    json.dumps(av.get("risk_flags") or [], ensure_ascii=False),
                    json.dumps(av.get("similar_toilets") or [], ensure_ascii=False),
                    r.get("id")
                ))
                updated += 1

        if apply_update:
            conn.commit()
        conn.close()
        try: _CACHE.clear()
        except Exception: pass
        return jsonify({
            "ok": True,
            "apply": apply_update,
            "scanned": len(rows),
            "updated": updated,
            "counts": counts,
            "preview": preview[:30]
        })
    except Exception as e:
        logging.error(f"admin_reverify_user_toilets failed: {e}", exc_info=True)
        return jsonify({"ok": False, "message": str(e)}), 500



# === Auto Maintenance Dashboard：自動驗證維護頁 ===
def _parse_risk_flags_value(value):
    """Parse risk_flags stored as JSON text/list into a safe list[str]."""
    if value is None:
        return []
    if isinstance(value, list):
        return [str(x) for x in value if x not in (None, "")]
    if isinstance(value, (dict, tuple)):
        return [str(x) for x in value]
    raw = str(value).strip()
    if not raw:
        return []
    try:
        data = json.loads(raw)
        if isinstance(data, list):
            return [str(x) for x in data if x not in (None, "")]
        if isinstance(data, dict):
            return [str(k) for k, v in data.items() if v]
    except Exception:
        pass
    # fallback: support comma separated or python-list-like text
    raw = raw.strip("[]")
    parts = [x.strip().strip("'\"") for x in raw.split(',')]
    return [x for x in parts if x]


def _parse_similar_toilets_value(value):
    if value is None:
        return []
    if isinstance(value, list):
        return value
    raw = str(value).strip()
    if not raw:
        return []
    try:
        data = json.loads(raw)
        return data if isinstance(data, list) else []
    except Exception:
        return []


def _maintenance_auth_ok():
    if not ADMIN_TOKEN:
        logging.critical("ADMIN_TOKEN not set; rejecting admin request")
        return False

    json_token = ""
    try:
        data = request.get_json(silent=True) if request.is_json else None
        if isinstance(data, dict):
            json_token = data.get("token") or ""
    except Exception:
        json_token = ""

    token = (
        request.headers.get("X-Admin-Token")
        or request.args.get("token")
        or json_token
        or ""
    ).strip()
    return token == ADMIN_TOKEN


@app.route("/api/maintenance-summary", methods=["GET"])
def api_maintenance_summary():
    """Auto Verification / maintenance queue summary.
    Used by /dashboard/maintenance. Requires ADMIN_TOKEN when configured.
    """
    if not _maintenance_auth_ok():
        return jsonify({"ok": False, "message": "unauthorized"}), 401
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "message": "postgres disabled"}), 503

    try:
        limit = max(1, min(int(request.args.get("limit") or "500"), 3000))
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT
                id, name, address, lat, lon,
                verification_status, verification_score, verification_reason,
                auto_verification_score, auto_verification_result, auto_verification_reason,
                risk_flags, similar_toilets_json,
                created_at, updated_at
            FROM user_toilets
            ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST
            LIMIT %s
        """, (limit,))
        rows = cur.fetchall()

        recent_review_logs = []
        try:
            cur.execute("""
                SELECT
                    id, toilet_id, toilet_name,
                    old_status, new_status,
                    old_score, new_score, auto_verification_score,
                    reviewer, action_reason, reject_reason,
                    risk_flags, created_at
                FROM user_toilet_review_logs
                ORDER BY created_at DESC
                LIMIT 30
            """)
            recent_review_logs = cur.fetchall()
        except Exception as log_err:
            logging.warning(f"maintenance review logs skipped: {log_err}")
            recent_review_logs = []

        conn.close()

        status_counts = {"approved": 0, "pending": 0, "rejected": 0, "unknown": 0}
        score_values = []
        flag_counts = {}
        queues = {
            "pending": [],
            "possible_duplicate": [],
            "possible_duplicate_high": [],
            "possible_duplicate_medium": [],
            "possible_duplicate_low": [],
            "strict_duplicate": [],
            "duplicate_high": [],
            "duplicate_medium": [],
            "duplicate_low": [],
            "shop_access_unclear": [],
            "generic_name": [],
            "address_coordinate_mismatch": [],
            "spatial_outlier": [],
            "outside_primary_region": [],
            "rejected": [],
            "low_score": []
        }

        def row_item(r, flags=None, similar=None):
            flags = flags if flags is not None else _parse_risk_flags_value(r.get("risk_flags"))
            similar = similar if similar is not None else _parse_similar_toilets_value(r.get("similar_toilets_json"))
            return {
                "id": r.get("id"),
                "name": r.get("name") or "",
                "address": r.get("address") or "",
                "status": r.get("verification_status") or "unknown",
                "score": r.get("auto_verification_score") if r.get("auto_verification_score") is not None else r.get("verification_score"),
                "reason": r.get("auto_verification_reason") or r.get("verification_reason") or "",
                "risk_flags": flags,
                "similar_count": len(similar),
                "similar_toilets": similar[:3],
                "updated_at": r.get("updated_at").isoformat() if hasattr(r.get("updated_at"), "isoformat") else str(r.get("updated_at") or "")
            }

        for r in rows:
            status = (r.get("verification_status") or "unknown").lower()
            if status not in status_counts:
                status_counts["unknown"] += 1
            else:
                status_counts[status] += 1

            try:
                sc = r.get("auto_verification_score")
                if sc is None:
                    sc = r.get("verification_score")
                if sc is not None:
                    score_values.append(float(sc))
            except Exception:
                pass

            flags = _parse_risk_flags_value(r.get("risk_flags"))
            similar = _parse_similar_toilets_value(r.get("similar_toilets_json"))
            for f in flags:
                flag_counts[f] = flag_counts.get(f, 0) + 1

            item = row_item(r, flags, similar)
            if status == "pending" and len(queues["pending"]) < 80:
                queues["pending"].append(item)
            if status == "rejected" and len(queues["rejected"]) < 80:
                queues["rejected"].append(item)
            if any(f.startswith("possible_duplicate") for f in flags) and len(queues["possible_duplicate"]) < 80:
                queues["possible_duplicate"].append(item)
            if "possible_duplicate_high" in flags:
                if len(queues["possible_duplicate_high"]) < 80:
                    queues["possible_duplicate_high"].append(item)
                if len(queues["duplicate_high"]) < 80:
                    queues["duplicate_high"].append(item)
            if "possible_duplicate_medium" in flags:
                if len(queues["possible_duplicate_medium"]) < 80:
                    queues["possible_duplicate_medium"].append(item)
                if len(queues["duplicate_medium"]) < 80:
                    queues["duplicate_medium"].append(item)
            if "possible_duplicate_low" in flags:
                if len(queues["possible_duplicate_low"]) < 80:
                    queues["possible_duplicate_low"].append(item)
                if len(queues["duplicate_low"]) < 80:
                    queues["duplicate_low"].append(item)
            if "strict_duplicate" in flags and len(queues["strict_duplicate"]) < 80:
                queues["strict_duplicate"].append(item)
            if any(f.startswith("address_coordinate_mismatch") for f in flags) and len(queues["address_coordinate_mismatch"]) < 80:
                queues["address_coordinate_mismatch"].append(item)
            if "spatial_outlier_candidate" in flags and len(queues["spatial_outlier"]) < 80:
                queues["spatial_outlier"].append(item)
            if "shop_access_unclear" in flags and len(queues["shop_access_unclear"]) < 80:
                queues["shop_access_unclear"].append(item)
            if "name_too_generic" in flags and len(queues["generic_name"]) < 80:
                queues["generic_name"].append(item)
            if "outside_primary_region" in flags and len(queues["outside_primary_region"]) < 80:
                queues["outside_primary_region"].append(item)
            try:
                item_score = float(item.get("score") or 0)
                if item_score < 70 and len(queues["low_score"]) < 80:
                    queues["low_score"].append(item)
            except Exception:
                pass

        total = len(rows)
        avg_score = round(sum(score_values) / len(score_values), 2) if score_values else 0
        top_flags = [
            {"flag": k, "count": v}
            for k, v in sorted(flag_counts.items(), key=lambda kv: kv[1], reverse=True)
        ]

        review_logs_out = []
        for log_row in recent_review_logs or []:
            review_logs_out.append({
                "id": log_row.get("id"),
                "toilet_id": log_row.get("toilet_id"),
                "toilet_name": log_row.get("toilet_name") or "",
                "old_status": log_row.get("old_status") or "",
                "new_status": log_row.get("new_status") or "",
                "old_score": log_row.get("old_score"),
                "new_score": log_row.get("new_score"),
                "auto_verification_score": log_row.get("auto_verification_score"),
                "reviewer": log_row.get("reviewer") or "",
                "action_reason": log_row.get("action_reason") or "",
                "reject_reason": log_row.get("reject_reason") or "",
                "risk_flags": _parse_risk_flags_value(log_row.get("risk_flags")),
                "created_at": log_row.get("created_at").isoformat() if hasattr(log_row.get("created_at"), "isoformat") else str(log_row.get("created_at") or "")
            })

        return jsonify({
            "ok": True,
            "scanned": total,
            "summary": {
                "total": total,
                "approved": status_counts.get("approved", 0),
                "pending": status_counts.get("pending", 0),
                "rejected": status_counts.get("rejected", 0),
                "unknown": status_counts.get("unknown", 0),
                "avg_auto_score": avg_score,
                "risk_flag_types": len(flag_counts),
                "risk_flag_total": sum(flag_counts.values()),
                "pending_rate": round((status_counts.get("pending", 0) / total * 100), 2) if total else 0,
                "verification_version": "auto_verify_1_5_4"
            },
            "flag_counts": top_flags,
            "queues": queues,
            "review_logs": review_logs_out
        })
    except Exception as e:
        logging.error(f"/api/maintenance-summary failed: {e}", exc_info=True)
        return jsonify({"ok": False, "message": str(e)}), 500





@app.route("/api/user-toilets-admin", methods=["GET"])
def api_user_toilets_admin():
    """List user-added toilets for manual review / full data inspection.

    Query params:
      token: ADMIN_TOKEN
      status: all | approved | pending | rejected
      flag: optional risk flag substring/exact tag
      q: optional keyword for name/address/reason
      limit: 1..500
      offset: >=0
    """
    if not _maintenance_auth_ok():
        return jsonify({"ok": False, "message": "unauthorized"}), 401
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "message": "postgres disabled"}), 503

    try:
        status = (request.args.get("status") or "all").strip().lower()
        flag = (request.args.get("flag") or "").strip()
        q = (request.args.get("q") or "").strip()
        limit = max(1, min(int(request.args.get("limit") or "100"), 500))
        offset = max(0, int(request.args.get("offset") or "0"))

        where = []
        params = []
        if status in ("approved", "pending", "rejected"):
            where.append("LOWER(COALESCE(verification_status,'')) = %s")
            params.append(status)
        if q:
            like = f"%{q}%"
            where.append("""
                (
                    name ILIKE %s OR address ILIKE %s OR
                    COALESCE(auto_verification_reason,'') ILIKE %s OR
                    COALESCE(verification_reason,'') ILIKE %s OR
                    COALESCE(risk_flags,'') ILIKE %s
                )
            """)
            params.extend([like, like, like, like, like])
        if flag:
            like_flag = f"%{flag}%"
            where.append("COALESCE(risk_flags,'') ILIKE %s")
            params.append(like_flag)

        where_sql = "WHERE " + " AND ".join(where) if where else ""

        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute(f"SELECT COUNT(*) AS c FROM user_toilets {where_sql}", tuple(params))
        total = int((cur.fetchone() or {}).get("c") or 0)

        cur.execute(f"""
            SELECT
                id, user_id, name, address, lat, lon,
                level, floor_hint, entrance_hint, access_note, open_hours,
                source,
                verification_status, verification_score, verification_reason,
                auto_verification_score, auto_verification_result, auto_verification_reason,
                risk_flags, similar_toilets_json,
                verified_at, verified_by, reject_reason,
                created_at, updated_at
            FROM user_toilets
            {where_sql}
            ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST, id DESC
            LIMIT %s OFFSET %s
        """, tuple(params + [limit, offset]))
        rows = cur.fetchall()
        conn.close()

        items = []
        for r in rows:
            flags = _parse_risk_flags_value(r.get("risk_flags"))
            similar = _parse_similar_toilets_value(r.get("similar_toilets_json"))
            items.append({
                "id": r.get("id"),
                "name": r.get("name") or "",
                "address": r.get("address") or "",
                "lat": r.get("lat"),
                "lon": r.get("lon"),
                "level": r.get("level") or "",
                "floor_hint": r.get("floor_hint") or "",
                "entrance_hint": r.get("entrance_hint") or "",
                "access_note": r.get("access_note") or "",
                "open_hours": r.get("open_hours") or "",
                "source": r.get("source") or "",
                "status": r.get("verification_status") or "unknown",
                "verification_score": r.get("verification_score"),
                "auto_verification_score": r.get("auto_verification_score"),
                "score": r.get("auto_verification_score") if r.get("auto_verification_score") is not None else r.get("verification_score"),
                "verification_reason": r.get("verification_reason") or "",
                "auto_verification_reason": r.get("auto_verification_reason") or "",
                "reason": r.get("auto_verification_reason") or r.get("verification_reason") or "",
                "risk_flags": flags,
                "similar_count": len(similar),
                "similar_toilets": similar[:5],
                "verified_at": r.get("verified_at").isoformat() if hasattr(r.get("verified_at"), "isoformat") else str(r.get("verified_at") or ""),
                "verified_by": r.get("verified_by") or "",
                "reject_reason": r.get("reject_reason") or "",
                "created_at": r.get("created_at").isoformat() if hasattr(r.get("created_at"), "isoformat") else str(r.get("created_at") or ""),
                "updated_at": r.get("updated_at").isoformat() if hasattr(r.get("updated_at"), "isoformat") else str(r.get("updated_at") or "")
            })

        return jsonify({
            "ok": True,
            "total": total,
            "limit": limit,
            "offset": offset,
            "items": items
        })
    except Exception as e:
        logging.error(f"/api/user-toilets-admin failed: {e}", exc_info=True)
        return jsonify({"ok": False, "message": str(e)}), 500


# === Maintenance Action 1.0：後台人工快速審核 ===
@app.route("/api/user-toilet-review", methods=["POST"])
def api_user_toilet_review():
    """Manually review a user-added toilet from the maintenance dashboard.

    Expected JSON:
    {
      "token": "ADMIN_TOKEN",
      "id": 123,
      "status": "approved" | "rejected",
      "reason": "optional note",
      "verified_by": "admin_dashboard"
    }
    """
    try:
        data = request.get_json(silent=True) or {}
        if not _maintenance_auth_ok():
            return jsonify({"ok": False, "message": "unauthorized"}), 401
        if not POSTGRES_ENABLED:
            return jsonify({"ok": False, "message": "postgres disabled"}), 503

        toilet_id = data.get("id") or data.get("toilet_id")
        try:
            toilet_id = int(toilet_id)
        except Exception:
            return jsonify({"ok": False, "message": "invalid toilet id"}), 400

        status = str(data.get("status") or "").strip().lower()
        allowed = {"approved", "pending", "rejected"}
        if status not in allowed:
            return jsonify({"ok": False, "message": "invalid status"}), 400

        reason = str(data.get("reason") or "").strip()
        verified_by = str(data.get("verified_by") or "admin_dashboard").strip()[:80]

        if status == "approved":
            default_reason = "人工審核通過"
            reject_reason = None
        elif status == "rejected":
            default_reason = "人工審核不通過"
            reject_reason = reason or default_reason
        else:
            default_reason = "人工保留待審"
            reject_reason = None

        final_reason = default_reason if not reason else f"{default_reason}：{reason}"

        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT
                id, name,
                verification_status,
                verification_score,
                verification_reason,
                auto_verification_score,
                auto_verification_result,
                auto_verification_reason,
                risk_flags,
                reject_reason
            FROM user_toilets
            WHERE id = %s
        """, (toilet_id,))
        exists = cur.fetchone()
        if not exists:
            conn.close()
            return jsonify({"ok": False, "message": "toilet not found"}), 404

        # Manual review should not overwrite the scoring model with fixed 100/50/0.
        # Keep the original automatic score as the verification_score so the score
        # continues to represent Auto Verification quality rather than the button clicked.
        try:
            original_score = exists.get("auto_verification_score")
            if original_score is None:
                original_score = exists.get("verification_score")
            score = int(original_score or 0)
        except Exception:
            score = 0

        cur.execute("""
            UPDATE user_toilets
            SET verification_status = %s,
                verification_score = %s,
                verification_reason = %s,
                verified_at = NOW(),
                verified_by = %s,
                reject_reason = %s,
                updated_at = NOW()
            WHERE id = %s
            RETURNING
                id, name, address, lat, lon,
                verification_status, verification_score, verification_reason,
                auto_verification_score, auto_verification_result, auto_verification_reason,
                risk_flags, similar_toilets_json,
                verified_at, verified_by, reject_reason, updated_at
        """, (status, score, final_reason, verified_by, reject_reason, toilet_id))
        row = cur.fetchone()

        # 寫入人工審核紀錄：保留前後狀態，方便追蹤誰在何時做了什麼。
        try:
            cur.execute("""
                INSERT INTO user_toilet_review_logs (
                    toilet_id, toilet_name,
                    old_status, new_status,
                    old_score, new_score,
                    auto_verification_score,
                    reviewer, action_reason, reject_reason,
                    risk_flags
                ) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
            """, (
                toilet_id,
                exists.get("name") or "",
                exists.get("verification_status") or "",
                status,
                exists.get("verification_score"),
                score,
                exists.get("auto_verification_score"),
                verified_by,
                final_reason,
                reject_reason,
                exists.get("risk_flags") or ""
            ))
        except Exception as log_err:
            logging.warning(f"insert user_toilet_review_logs failed: {log_err}")

        conn.commit()
        conn.close()

        try:
            _CACHE.clear()
        except Exception:
            pass

        return jsonify({
            "ok": True,
            "message": "updated",
            "item": {
                "id": row.get("id"),
                "name": row.get("name"),
                "status": row.get("verification_status"),
                "verification_score": row.get("verification_score"),
                "verification_reason": row.get("verification_reason"),
                "verified_at": row.get("verified_at").isoformat() if hasattr(row.get("verified_at"), "isoformat") else str(row.get("verified_at") or ""),
                "verified_by": row.get("verified_by") or "",
                "reject_reason": row.get("reject_reason") or ""
            }
        })
    except Exception as e:
        logging.error(f"/api/user-toilet-review failed: {e}", exc_info=True)
        return jsonify({"ok": False, "message": str(e)}), 500

@app.route("/dashboard/maintenance", methods=["GET"])
def dashboard_maintenance():
    return render_template("maintenance.html")


# === 背景排程（預留） ===
def auto_predict_cleanliness_background():
    while True:
        try:
            logging.info("🌀 背景排程啟動中（未來可加入自動統計）")
        except Exception as e:
            logging.error(f"❌ 背景任務出錯：{e}")
        time.sleep(1800)

# === 啟動 ===
if __name__ == "__main__":
    # auto_predict_cleanliness_background is currently log-only, so keep it disabled
    # to avoid wasting a background thread and polluting production logs.
    # threading.Thread(target=auto_predict_cleanliness_background, daemon=True).start()
    threading.Thread(target=_self_keepalive_background, daemon=True).start()

    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
