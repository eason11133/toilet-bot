import os
import csv
import json
import logging
import sqlite3
import requests
import traceback
import heapq
import math
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
import gspread
from oauth2client.service_account import ServiceAccountCredentials
from datetime import datetime, timezone, timedelta
from openai import OpenAI
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
MAX_SHEET_ROWS      = int(os.getenv("MAX_SHEET_ROWS", "4000"))     # 只讀尾端 N 列

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

# ======================== Sheets 安全外掛層（沿用你現有的設定即可） ========================
SHEETS_MAX_CONCURRENCY = int(os.getenv("SHEETS_MAX_CONCURRENCY", "4"))
SHEETS_RETRY_MAX = int(os.getenv("SHEETS_RETRY_MAX", "6"))
SHEETS_READ_TTL_SEC = int(os.getenv("SHEETS_READ_TTL_SEC", "45"))
SHEETS_CACHE_MAX_ROWS = int(os.getenv("SHEETS_CACHE_MAX_ROWS", "20000"))

_sheets_sem = threading.Semaphore(SHEETS_MAX_CONCURRENCY)
_read_cache = {}            # key: (sheet_id, ws_title, op) -> {ts, val}
_cache_lock = threading.Lock()
_gsheet_lock = threading.Lock()
_fallback_lock = threading.Lock()

def _is_quota_or_retryable(exc: Exception) -> bool:
    s = str(exc).lower()
    return ("429" in s or "quota" in s or "rate limit" in s or
            "timeout" in s or "timed out" in s or "503" in s or "500" in s)

def delay_request():
    delay_time = random.uniform(0.5, 1.5)  # 隨機延遲時間，根據需求調整
    time.sleep(delay_time)

def _with_retry(func, *args, **kwargs):
    backoff = 0.7
    last_exc = None
    for i in range(SHEETS_RETRY_MAX):
        try:
            with _sheets_sem:
                return func(*args, **kwargs)
        except Exception as e:
            last_exc = e
            if _is_quota_or_retryable(e):
                delay_request()
                sleep_s = backoff * (2 ** i) + random.uniform(0, 0.25*i)
                time.sleep(sleep_s)
                continue
            raise
    raise last_exc if last_exc else RuntimeError("Sheets retry exhausted")

def batch_query_sheets(query_keys):
    # 同時查詢多個快取的資料
    results = []
    for key in query_keys:
        cached_data = get_cached_data(key)
        if cached_data:
            results.append(cached_data)
        else:
            results.append(None)  # 若無快取，會再進行 API 請求
    return results

def retry_request(func, *args, **kwargs):
    retries = 3
    for i in range(retries):
        try:
            return func(*args, **kwargs)
        except Exception as e:
            if i < retries - 1:
                time.sleep(2 ** i)  # Exponential backoff
                continue
            else:
                raise e

class SafeWS:
    def __init__(self, ws, sheet_id: str, name: str):
        self._ws = ws
        self._sheet_id = sheet_id
        self._name = name

    # ---------- 讀取（含快取） ----------
    def get_all_values(self):
        key = (self._sheet_id, self._name, "get_all_values")
        now = time.time()
        with _cache_lock:
            c = _read_cache.get(key)
            if c and now - c["ts"] < SHEETS_READ_TTL_SEC:
                return c["val"]

        def _do():
            return self._ws.get_all_values()

        val = _with_retry(_do)
        # 只快取合理大小，避免把整個超大表塞進記憶體
        if isinstance(val, list) and len(val) <= SHEETS_CACHE_MAX_ROWS:
            with _cache_lock:
                _read_cache[key] = {"ts": now, "val": val}
        return val

    def row_values(self, i):
        return _with_retry(self._ws.row_values, i)

    # ✅ 新增：給 _get_header_and_tail / 輕量估算總列數用
    def col_values(self, i):
        return _with_retry(self._ws.col_values, i)

    # ✅ 新增：給區段讀取（如 "A2:AZ100"）
    def get(self, rng):
        return _with_retry(self._ws.get, rng)

    # ---------- 寫入（成功後失效快取） ----------
    def _invalidate(self):
        key = (self._sheet_id, self._name, "get_all_values")
        with _cache_lock:
            _read_cache.pop(key, None)

    def update(self, rng, values):
        def _do():
            return self._ws.update(rng, values)
        out = _with_retry(_do)
        self._invalidate()
        return out

    def append_row(self, values, value_input_option="RAW"):
        def _do():
            return self._ws.append_row(values, value_input_option=value_input_option)
        out = _with_retry(_do)
        self._invalidate()
        return out

    def delete_rows(self, index):
        def _do():
            return self._ws.delete_rows(index)
        out = _with_retry(_do)
        self._invalidate()
        return out

    # ---------- 其他 ----------
    def worksheet(self, title):
        # 取得同試算表內的其他工作表，持續沿用 SafeWS 包裝
        return self.__class__(self._ws.worksheet(title), self._sheet_id, title)

    @property
    def title(self):
        return self._ws.title

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
    }
})


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
    1) key 模式（推薦）：T("no_result", uid=uid)  → 從 TEXTS 抓 zh/en
    2) zh/en 模式（相容舊碼）：T("附近沒有廁所", uid=uid, en="No toilets nearby")
    3) API 模式：T("missing_params", lang=_api_lang())
    4) 支援 format：T("added_fav_ok", uid=uid, name="xxx")
    """
    l = resolve_lang(uid=uid, lang=lang)

    # key 模式：en is None，且 key 在 TEXTS
    if en is None and isinstance(key_or_zh, str) and key_or_zh in TEXTS:
        s = TEXTS[key_or_zh].get(l, TEXTS[key_or_zh].get("zh", "")) or ""
    else:
        # zh/en 模式（相容）
        s = (en if l == "en" else key_or_zh) if en is not None else (key_or_zh or "")

    # format（容錯）
    try:
        return s.format(**fmt)
    except Exception:
        return s

# ---- 舊函式相容層（全部導到 T）----

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
    _ensure_sheets_ready()
    ok = (worksheet is not None) and (feedback_sheet is not None) and (consent_ws is not None)
    status = 200 if ok else 503
    msg = "ready" if ok else "not-ready"
    headers = {
        "Content-Type": "text/plain; charset=utf-8",
        "Cache-Control": "no-store",
        "X-Robots-Tag": "noindex",
    }
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
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_toilets_lat_lon ON user_toilets(lat, lon)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_toilets_created_at ON user_toilets(created_at)")

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
        conn.commit()
        conn.close()
        logging.info("✅ Postgres persistent store ready")
    except Exception as e:
        logging.error(f"❌ init_persistent_store failed: {e}")

PUBLIC_HEADERS = [
    "country","city","village","number","name","address","administration",
    "latitude","longitude","grade","type2","type","exec","diaper"
]
if not os.path.exists(TOILETS_FILE_PATH):
    with open(TOILETS_FILE_PATH, "w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(PUBLIC_HEADERS)

# === Google Sheets 設定 ===
GSHEET_SCOPE = ['https://spreadsheets.google.com/feeds', 'https://www.googleapis.com/auth/drive']
GSHEET_CREDENTIALS_JSON = os.getenv("GSHEET_CREDENTIALS_JSON")
TOILET_SPREADSHEET_ID = "1Vg3tiqlXcXjcic2cAWCG-xTXfNzcI7wegEnZx8Ak7ys"
FEEDBACK_SPREADSHEET_ID = "15Ram7EZ9QMN6SZAVYQFNpL5gu4vTaRn4M5mpWUKmmZk"

# === 同意書設定 ===
CONSENT_SHEET_TITLE = "consent"
CONSENT_PAGE_URL = os.getenv("CONSENT_PAGE_URL", "https://school-i9co.onrender.com/consent")

gc = worksheet = feedback_sheet = consent_ws = None

# === 狀態回報設定 ===
STATUS_SHEET_TITLE = "status"
status_ws = None

# 近點/快取/有效期
_STATUS_NEAR_M = 35
_STATUS_TTL_HOURS = 6
_status_index_cache = {"ts": 0, "data": {}}
# _STATUS_INDEX_TTL is defined in global config section (see above)
# MAX_SHEET_ROWS is defined in global config section (see above)
def _a1_col(n: int) -> str:
    if n <= 0:
        return "A"
    out = []
    while n > 0:
        n, r = divmod(n - 1, 26)
        out.append(chr(65 + r))
    return "".join(reversed(out))


def _get_header_and_tail(ws, max_rows: int = MAX_SHEET_ROWS):
    try:
        max_rows = int(max_rows)
        if max_rows <= 0:
            max_rows = 1
    except Exception:
        max_rows = 1000  

    try:
        header = ws.row_values(1) or []
        if not header:
            return [], []

        col_a = ws.col_values(1) or []
        last_row = len(col_a)
        if last_row < 2:  
            return header, []

        start_row = max(2, last_row - max_rows + 1)

        end_col = _a1_col(max(1, len(header)))
        rng = f"A{start_row}:{end_col}{last_row}"

        data = ws.get(rng) or []
        return header, data

    except Exception as e:
        logging.warning(f"_get_header_and_tail primary path failed: {e}")

        # === Fallback：一次抓，然後只保留尾端 max_rows，避免佔記憶體 ===
        try:
            rows = ws.get_all_values() or []
            if not rows:
                return [], []
            header = rows[0]
            data = rows[1:]
            if len(data) > max_rows:
                data = data[-max_rows:]
            return header, data
        except Exception as e2:
            logging.warning(f"_get_header_and_tail fallback failed: {e2}")
            return [], []

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
    toilets.sort(key=lambda x: (int(x.get("distance", 1e9)), -_findability_bonus(x)))
    return toilets

# === 初始化 Google Sheets（包 SafeWS；其餘不變） ===
def init_gsheet():
    global gc, worksheet, feedback_sheet, consent_ws, status_ws
    try:
        if not GSHEET_CREDENTIALS_JSON:
            logging.critical("❌ 缺少 GSHEET_CREDENTIALS_JSON")
            return  # 不 raise，讓服務先活著
        creds_dict = json.loads(GSHEET_CREDENTIALS_JSON)
        creds = ServiceAccountCredentials.from_json_keyfile_dict(creds_dict, GSHEET_SCOPE)
        gc = gspread.authorize(creds)

        worksheet_raw = gc.open_by_key(TOILET_SPREADSHEET_ID).sheet1
        fb_spread = gc.open_by_key(FEEDBACK_SPREADSHEET_ID)
        feedback_raw = fb_spread.sheet1

        try:
            consent_raw = fb_spread.worksheet(CONSENT_SHEET_TITLE)
        except gspread.exceptions.WorksheetNotFound:
            consent_raw = fb_spread.add_worksheet(title=CONSENT_SHEET_TITLE, rows=1000, cols=10)
            consent_raw.update("A1:F1", [["user_id","agreed","display_name","source_type","ua","timestamp"]])

        worksheet = SafeWS(worksheet_raw, TOILET_SPREADSHEET_ID, worksheet_raw.title)
        feedback_sheet = SafeWS(feedback_raw, FEEDBACK_SPREADSHEET_ID, feedback_raw.title)
        consent_ws = SafeWS(consent_raw, FEEDBACK_SPREADSHEET_ID, consent_raw.title)
        
        try:
            status_raw = fb_spread.worksheet(STATUS_SHEET_TITLE)
        except gspread.exceptions.WorksheetNotFound:
            status_raw = fb_spread.add_worksheet(title=STATUS_SHEET_TITLE, rows=1000, cols=10)
            status_raw.update("A1:G1", [["lat","lon","status","user_id","display_name","note","timestamp"]])

        status_ws = SafeWS(status_raw, FEEDBACK_SPREADSHEET_ID, status_raw.title)

        logging.info("✅ Sheets 初始化完成")
    except Exception as e:
        logging.critical(f"❌ Sheets 初始化失敗（改為延後再試）: {e}")
        return

def _ensure_sheets_ready():
    if any(x is None for x in (worksheet, feedback_sheet, consent_ws)):
        try:
            init_gsheet()
        except Exception:
            # 保持靜默，呼叫端要自己容錯（例如回空結果 / 優雅降級）
            pass

init_gsheet()

# === 使用者新增廁所 ===
TOILET_REQUIRED_HEADER = [
    "user_id", "name", "address", "lat", "lon",
    "level", "floor_hint", "entrance_hint", "access_note", "open_hours",
    "timestamp"
]

def ensure_toilet_sheet_header(ws):
    _ensure_sheets_ready()
    if ws is None:
        return TOILET_REQUIRED_HEADER[:]
    try:
        header = ws.row_values(1) or []
        if not header:
            ws.update("A1", [TOILET_REQUIRED_HEADER])
            return TOILET_REQUIRED_HEADER[:]

        changed = False
        for col in TOILET_REQUIRED_HEADER:
            if col not in header:
                header.append(col)
                changed = True
        if changed:
            ws.update("A1", [header])
        return header
    except Exception as e:
        logging.error(f"ensure_toilet_sheet_header 失敗：{e}")
        return header if 'header' in locals() and header else TOILET_REQUIRED_HEADER[:]

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
        return 0

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

# === 更精準的防重複（新） ===

_DEDUPE_LOCK = threading.Lock()

# 事件類型專屬時間窗（秒）— 可用環境變數調整
TEXT_DEDUPE_WINDOW = int(os.getenv("TEXT_DEDUPE_WINDOW", "15"))
LOC_DEDUPE_WINDOW  = int(os.getenv("LOC_DEDUPE_WINDOW",  "10"))
PB_DEDUPE_WINDOW   = int(os.getenv("PB_DEDUPE_WINDOW",   "120"))

# 定位事件短時間重複的距離閾值（公尺）
LOC_DEDUPE_DISTANCE_M = float(os.getenv("LOC_DEDUPE_DISTANCE_M", "8"))

# 最近處理事件時間索引
_RECENT_EVENTS = getattr(globals(), "_RECENT_EVENTS", {})  # 若前面已有同名 dict，沿用

def _now():
    return time.time()

def _purge_expired(now_ts: float):
    """輕量清理：移除超過最大去重窗的舊記錄，避免 dict 無限成長"""
    max_win = max(TEXT_DEDUPE_WINDOW, LOC_DEDUPE_WINDOW, PB_DEDUPE_WINDOW, 180)
    cutoff = now_ts - float(max_win)
    for k, ts in list(_RECENT_EVENTS.items()):
        if ts < cutoff:
            _RECENT_EVENTS.pop(k, None)

def _event_type_and_key(event):
    """回傳 (etype, key, window_sec)

    ✅ 去重 key 優先順序：
    1) webhook_event_id（若 SDK 有帶）
    2) message.id（MessageEvent）
    3) fallback：user_id + payload + timestamp（同一事件重送 timestamp 通常相同）
    """
    uid = getattr(getattr(event, "source", None), "user_id", "") or ""
    ts = getattr(event, "timestamp", 0) or 0  # ms
    weid = getattr(event, "webhook_event_id", None) or getattr(event, "webhookEventId", None)

    # Message id
    mid = None
    try:
        mid = getattr(getattr(event, "message", None), "id", None)
    except Exception:
        pass

    # Text
    if isinstance(getattr(event, "message", None), TextMessage):
        etype = "text"
        window = TEXT_DEDUPE_WINDOW
        txt = (getattr(event.message, "text", "") or "").strip().lower()
        if weid:
            key = f"weid:{weid}"
        elif mid:
            key = f"mid:{mid}"
        else:
            key = f"text|{uid}|{txt}|ts:{ts}"
        return etype, key, window

    # Location
    if isinstance(getattr(event, "message", None), LocationMessage):
        etype = "loc"
        window = LOC_DEDUPE_WINDOW
        lat = getattr(event.message, "latitude", None)
        lon = getattr(event.message, "longitude", None)
        base = f"loc|{uid}|{norm_coord(lat)}:{norm_coord(lon)}|ts:{ts}"
        if weid:
            key = f"weid:{weid}"
        elif mid:
            key = f"mid:{mid}"
        else:
            key = base
        return etype, key, window

    # Postback（沒有 message）
    etype = "pb"
    window = PB_DEDUPE_WINDOW
    data = getattr(getattr(event, "postback", None), "data", "") or ""
    if weid:
        key = f"weid:{weid}"
    else:
        key = f"pb|{uid}|{data}|ts:{ts}"
    return etype, key, window

def is_duplicate_and_mark_event(event) -> bool:
    now_ts = _now()
    etype, key, window = _event_type_and_key(event)

    # 為 Location 加上「距離 + 時間」規則
    if etype == "loc":
        try:
            uid = event.source.user_id
            lat = float(event.message.latitude)
            lon = float(event.message.longitude)
            last = get_user_location(uid)
        except Exception:
            last = None
        else:
            if last:
                try:
                    d = haversine(lat, lon, float(last[0]), float(last[1]))
                except Exception:
                    d = 1e9
                with _DEDUPE_LOCK:
                    last_ts = _RECENT_EVENTS.get(f"loc_ts|{uid}", 0.0)
                    if (now_ts - last_ts) < LOC_DEDUPE_WINDOW and d <= LOC_DEDUPE_DISTANCE_M:
                        logging.info(f"🔁 skip duplicate loc: uid={uid} d={int(d)}m Δt={round(now_ts-last_ts,2)}s")
                        return True
                    _RECENT_EVENTS[f"loc_ts|{uid}"] = now_ts  # 更新最後定位時間

    # 一般路徑：key + window
    with _DEDUPE_LOCK:
        last_ts = _RECENT_EVENTS.get(key)
        if last_ts is not None and (now_ts - last_ts) < window:
            logging.info(f"🔁 skip duplicate {etype}: key={key}")
            return True
        _RECENT_EVENTS[key] = now_ts
        _purge_expired(now_ts)

    return False

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
    _ensure_sheets_ready()
    if not user_id or consent_ws is None:
        return False
    try:
        if not user_id or consent_ws is None:
            return False
        now = time.time()
        hit = _consent_cache.get(user_id)
        if hit and (now - hit[0] < _CONSENT_TTL):
            return hit[1]

        rows = consent_ws.get_all_values()
        if not rows or len(rows) < 2:
            _consent_cache[user_id] = (now, False)
            return False
        header = rows[0]; data = rows[1:]
        try:
            i_uid = header.index("user_id")
            i_ag  = header.index("agreed")
        except ValueError:
            _consent_cache[user_id] = (now, False)
            return False
        ok = False
        for r in data:
            if len(r) <= max(i_uid, i_ag):
                continue
            if (r[i_uid] or "").strip() == user_id and _booly(r[i_ag]):
                ok = True
                break
        _consent_cache[user_id] = (now, ok)
        return ok
    except Exception as e:
        logging.warning(f"查詢同意失敗: {e}")
        return False

def upsert_consent(user_id: str, agreed: bool, display_name: str, source_type: str, ua: str, ts_iso: str):
    _ensure_sheets_ready()
    if consent_ws is None:
        return False
    try:
        rows = consent_ws.get_all_values()
        if not rows:
            consent_ws.update("A1:F1", [["user_id","agreed","display_name","source_type","ua","timestamp"]])
            rows = [["user_id","agreed","display_name","source_type","ua","timestamp"]]
        header = rows[0]; data = rows[1:]

        idx = {h:i for i,h in enumerate(header)}
        for k in ["user_id","agreed","display_name","source_type","ua","timestamp"]:
            if k not in idx:
                header.append(k); idx[k] = len(header)-1
        if len(header) != len(rows[0]):
            consent_ws.update("A1", [header])

        row_to_update = None
        for i, r in enumerate(data, start=2):
            if len(r) > idx["user_id"] and (r[idx["user_id"]] or "").strip() == user_id:
                row_to_update = i
                break

        row_values = [""] * len(header)
        row_values[idx["user_id"]] = user_id or ""
        row_values[idx["agreed"]] = "true" if agreed else "false"
        row_values[idx["display_name"]] = display_name or ""
        row_values[idx["source_type"]] = source_type or ""
        row_values[idx["ua"]] = ua or ""
        row_values[idx["timestamp"]] = ts_iso or datetime.utcnow().isoformat()

        if row_to_update:
            consent_ws.update(f"A{row_to_update}", [row_values])
        else:
            consent_ws.append_row(row_values, value_input_option="USER_ENTERED")
        # 更新本機快取
        _consent_cache[user_id] = (time.time(), bool(agreed))
        return True
    except Exception as e:
        logging.error(f"寫入/更新同意失敗: {e}")
        return False

def ensure_consent_or_prompt(user_id: str):
    if has_consented(user_id):
        return None
    tip = (
        "🛡️ 使用前請先完成同意：\n"
        f"{CONSENT_PAGE_URL}\n\n"
        "若不同意，部分功能將無法提供。"
    )
    return TextSendMessage(text=tip)

# === 從 Google Sheets 查使用者新增廁所 ===
# 設定 SQLite 資料庫位置
CACHE_DB_PATH = os.path.join(os.path.dirname(__file__), "cache.db")
# 建立 SQLite 連線
def create_cache_db():
    if not os.path.exists(CACHE_DB_PATH):
        conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
        cursor = conn.cursor()
        cursor.execute("""
        CREATE TABLE IF NOT EXISTS sheets_cache (
            query_key TEXT PRIMARY KEY,
            data TEXT,
            timestamp REAL
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
    cursor.execute("SELECT data, timestamp FROM sheets_cache WHERE query_key = ?", (query_key,))
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
    INSERT OR REPLACE INTO sheets_cache (query_key, data, timestamp)
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
                created_at or datetime.utcnow()
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
            created_at or datetime.utcnow().isoformat()
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
def query_sheet_toilets(user_lat, user_lon, radius=500):
    _ensure_sheets_ready()
    if worksheet is None:
        return []

    try:
        SHEET_MAX_ITEMS = int(os.getenv("SHEET_MAX_ITEMS", "120"))
    except Exception:
        SHEET_MAX_ITEMS = 120

    toilets_heap = []

    try:
        header, data = _get_header_and_tail(worksheet, MAX_SHEET_ROWS)
        if not header or not data:
            return []

        idx = _toilet_sheet_indices(header)
        if idx.get("lat") is None or idx.get("lon") is None:
            return []

        lat = float(user_lat)
        lon = float(user_lon)
        dlat = radius / 111000.0
        dlon = radius / (111000.0 * max(0.1, math.cos(math.radians(lat))))

        min_lat, max_lat = lat - dlat, lat + dlat
        min_lon, max_lon = lon - dlon, lon + dlon

        for row in data:
            if len(row) <= max(idx["lat"], idx["lon"]):
                continue

            try:
                t_lat = float(row[idx["lat"]])
                t_lon = float(row[idx["lon"]])
            except Exception:
                continue

            if not (min_lat <= t_lat <= max_lat and min_lon <= t_lon <= max_lon):
                continue

            dist = haversine(lat, lon, t_lat, t_lon)
            if dist > radius:
                continue

            name = (
                row[idx["name"]].strip()
                if idx["name"] is not None and len(row) > idx["name"]
                else "無名稱"
            )
            address = (
                row[idx["address"]].strip()
                if idx["address"] is not None and len(row) > idx["address"]
                else ""
            )

            floor_hint = _floor_from_name(name)

            item = {
                "name": name,
                "lat": float(norm_coord(t_lat)),
                "lon": float(norm_coord(t_lon)),
                "address": address,
                "distance": dist,
                "type": "sheet",
                "floor_hint": floor_hint,
            }

            heapq.heappush(toilets_heap, (-dist, item))
            if len(toilets_heap) > SHEET_MAX_ITEMS:
                heapq.heappop(toilets_heap)

        toilets = [item for _, item in sorted(toilets_heap, key=lambda x: -x[0])]
        return toilets

    except Exception as e:
        logging.error(f"讀取 Google Sheets 廁所主資料錯誤: {e}")
        return []

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
            WHERE lat BETWEEN %s AND %s AND lon BETWEEN %s AND %s
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
def query_public_csv_toilets(user_lat, user_lon, radius=500):
    if not os.path.exists(TOILETS_FILE_PATH):
        return []

    heap = []  
    limit = LOC_MAX_RESULTS

    try:
        with open(TOILETS_FILE_PATH, "r", encoding="utf-8-sig", newline="") as f:
            reader = csv.DictReader(f)

            for row in reader:
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
        logging.error(f"讀 public_toilets.csv 失敗：{e}")
        return []

    return [item for _, _, item in sorted(heap, key=lambda x: -x[0])]

# === 合併 + 去重 ===
def _merge_and_dedupe_lists(*lists, dist_th=35, name_sim_th=0.55):
    all_pts = []
    for l in lists:
        if l: all_pts.extend(l)
    all_pts.sort(key=lambda x: x["distance"])

    merged = []
    for p in all_pts:
        dup = False
        for q in merged:
            try:
                near = haversine(p["lat"], p["lon"], q["lat"], q["lon"]) <= dist_th
            except Exception:
                near = False
            sim = SequenceMatcher(None, (p.get("name") or "").lower(), (q.get("name") or "").lower()).ratio()
            if near and sim >= name_sim_th:
                dup = True
                break
        if not dup:
            merged.append(p)
    return merged

# === 最愛管理 ===
# favorites.txt 是純文字/CSV 檔，於多執行緒環境下需要鎖避免同時讀寫造成破檔
# （例如同一時間多位使用者點收藏/取消收藏）
_FAV_LOCK = threading.Lock()

def add_to_favorites(uid, toilet):
    try:
        if not uid or not toilet:
            return
        lat_s = norm_coord(toilet.get("lat"))
        lon_s = norm_coord(toilet.get("lon"))
        name  = (toilet.get("name") or "").strip()
        addr  = toilet.get("address", "") or ""
        if not name:
            return

        with _FAV_LOCK:
            with open(FAVORITES_FILE_PATH, "a", encoding="utf-8", newline="") as f:
                writer = csv.writer(f)
                writer.writerow([uid, name, lat_s, lon_s, addr])
    except Exception as e:
        logging.error(f"加入最愛失敗: {e}")

def remove_from_favorites(uid, name, lat, lon):
    try:
        if not uid or not name:
            return False
        lat_s = norm_coord(lat)
        lon_s = norm_coord(lon)

        with _FAV_LOCK:
            rows = []
            changed = False
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
        logging.error(f"移除最愛失敗: {e}")
        return False

def get_user_favorites(uid):
    favs = []
    if not uid:
        return favs
    try:
        with _FAV_LOCK:
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
                        "lat": row[2],
                        "lon": row[3],
                        "address": row[4],
                    })
        return favs
    except Exception as e:
        logging.error(f"讀取最愛失敗: {e}")
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

    user_lat = float(user_lat)
    user_lon = float(user_lon)

    public_csv_toilets = query_public_csv_toilets(user_lat, user_lon, radius=500) or []
    saved_toilets = query_saved_toilets(user_lat, user_lon, radius=500) or []
    sheet_toilets = query_sheet_toilets(user_lat, user_lon, radius=500) or []
    osm_toilets = query_overpass_toilets(user_lat, user_lon, radius=500) or []

    all_toilets = _merge_and_dedupe_lists(public_csv_toilets, saved_toilets, sheet_toilets, osm_toilets)
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
    _ensure_sheets_ready()
    if feedback_sheet is None:
        return None

    # k 上限，避免一次吃太多列
    try:
        NOWCAST_MAX_K = int(os.getenv("NOWCAST_MAX_K", "8"))
    except Exception:
        NOWCAST_MAX_K = 8
    if k is None or not isinstance(k, int) or k <= 0:
        k = LAST_N_HISTORY
    k = min(k, NOWCAST_MAX_K)

    # 目標座標轉為 float，用於比較
    try:
        target_lat = float(lat)
        target_lon = float(lon)
    except Exception:
        return None

    try:
        header, data = _get_header_and_tail(feedback_sheet, MAX_SHEET_ROWS)
        if not header or not data:
            return None

        idx = _feedback_indices(header)
        i_lat, i_lon = idx.get("lat"), idx.get("lon")
        if i_lat is None or i_lon is None:
            return None

        def close(a, b):
            try:
                return abs(float(a) - float(b)) <= tol
            except Exception:
                return False

        # 只保留同座標的最近 k 筆
        same_rows = []
        for r in data:
            # 長度檢查
            if max(i_lat, i_lon) >= len(r):
                continue
            if close(r[i_lat], target_lat) and close(r[i_lon], target_lon):
                same_rows.append(r)
                if len(same_rows) >= k * 3:
                    # 多抓一點備用，稍後按時間取前 k
                    break

        if not same_rows:
            return None

        # 若有 created 欄位就按時間新到舊排，再取前 k 筆
        i_created = idx.get("created")
        if i_created is not None:
            try:
                same_rows.sort(key=lambda x: (x[i_created] if len(x) > i_created else ""), reverse=True)
            except Exception:
                pass

        recent = same_rows[:k]
        if not recent:
            return None

        # 一次走訪，同時計算模型分數與備用簡化分數
        vals_model = []
        vals_simple = []
        for r in recent:
            sc, rr, pp, aa = _pred_from_row(r, idx)
            if isinstance(sc, (int, float)):
                try:
                    vals_model.append(float(sc))
                except Exception:
                    pass
            # 簡化分數隨手備著，避免之後再跑一次
            s2 = _simple_score(rr, pp, aa)
            if isinstance(s2, (int, float)):
                vals_simple.append(float(s2))

        # 沒有模型分數就用簡化分數
        vals = vals_model[:] if vals_model else vals_simple[:]
        if not vals:
            return None

        # 若模型分數全相同（極常見於少量樣本），改用簡化分數以打開分佈
        if vals_model and len(vals_model) >= 2:
            try:
                if max(vals_model) - min(vals_model) < 1e-6 and vals_simple:
                    vals = vals_simple[:]
            except Exception:
                pass

        n = len(vals)
        mean = round(sum(vals) / n, 2)

        if n == 1:
            return {"mean": mean, "lower": mean, "upper": mean, "n": 1}

        try:
            s = statistics.stdev(vals)
        except statistics.StatisticsError:
            s = 0.0

        se = s / (n ** 0.5)
        lower = max(1.0, round(mean - 1.96 * se, 2))
        upper = min(5.0, round(mean + 1.96 * se, 2))
        return {"mean": mean, "lower": lower, "upper": upper, "n": n}

    except Exception as e:
        logging.error(f"❌ compute_nowcast_ci 失敗: {e}")
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
                # 用 norm_coord（字串）讓之後比對試算表座標更穩定
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

# === 回饋 ===
@app.route("/submit_feedback", methods=["POST"])
def submit_feedback():
    _ensure_sheets_ready()
    logging.info(f"[submit_feedback] content_type={request.content_type}")
    logging.info(f"[submit_feedback] form={request.form.to_dict(flat=True)}")
    logging.info(f"[submit_feedback] args={request.args.to_dict(flat=True)}")

    try:
        payload_json = request.get_json(silent=True)
        if payload_json and isinstance(payload_json, dict) and len(payload_json) > 0:
            data = payload_json
            src = "json"
            getv = lambda k, d="": (data.get(k) if data.get(k) is not None else d)
            debug_dump = str(data)
        else:
            data = request.form
            src = "form"
            getv = lambda k, d="": (data.get(k, d) if data.get(k, d) is not None else d)
            try:
                debug_dump = str(data.to_dict(flat=True))
            except Exception:
                debug_dump = "<form>"

        # ✅ 基本欄位（統一用 getv）
        name = (getv("name", "") or "").strip()
        address = (getv("address", "") or "").strip()

        # ✅ 修正重點：lat/lon 也統一用 getv，並允許從 args 補救
        lat_raw = ((getv("lat", "") or request.args.get("lat") or "")).strip()
        lon_raw = ((getv("lon", "") or request.args.get("lon") or "")).strip()

        lat_f, lon_f = _parse_lat_lon(lat_raw, lon_raw)
        if lat_f is None or lon_f is None:
            return (
                "座標格式錯誤\n"
                f"src={src}\n"
                f"lat_raw={lat_raw}\n"
                f"lon_raw={lon_raw}\n"
                f"payload={debug_dump}"
            ), 400

        lat = norm_coord(lat_f)
        lon = norm_coord(lon_f)

        # ✅ 其他欄位（統一用 getv）
        rating = ((getv("rating", "") or "")).strip()
        toilet_paper = ((getv("toilet_paper", "") or "")).strip()
        accessibility = ((getv("accessibility", "") or "")).strip()
        time_of_use = ((getv("time_of_use", "") or "")).strip()
        comment = ((getv("comment", "") or "")).strip()
        floor_hint = ((getv("floor_hint", "") or "")).strip()

        # ✅ 必填檢查（與前端 required 對齊）
        missing = []
        if not name: missing.append("name")
        if not rating: missing.append("rating")
        if not lat_raw: missing.append("lat")
        if not lon_raw: missing.append("lon")
        if not toilet_paper: missing.append("toilet_paper")
        if not accessibility: missing.append("accessibility")

        if missing:
            return (
                "缺少必要欄位（需要：name、rating、toilet_paper、accessibility、lat、lon）\n"
                f"missing={missing}\n"
                f"src={src}\n"
                f"收到：name={name}, rating={rating}, paper={toilet_paper}, access={accessibility}, lat={lat_raw}, lon={lon_raw}\n"
                f"payload={debug_dump}"
            ), 400

        # ✅ rating 檢查
        try:
            r = int(rating)
            if r < 1 or r > 10:
                return "清潔度評分必須在 1 到 10 之間", 400
        except ValueError:
            return "清潔度評分必須是數字", 400

        if floor_hint and len(floor_hint) < 1:
            return "『位置描述』太短，請至少 4 個字", 400

        if not floor_hint:
            inferred = _floor_from_name(name)
            if inferred:
                floor_hint = inferred

        paper_map = {"有": 1, "沒有": 0, "沒注意": 0}
        access_map = {"有": 1, "沒有": 0, "沒注意": 0}
        cur_feat = [r, paper_map.get(toilet_paper, 0), access_map.get(accessibility, 0)]

        hist_feats = []
        try:
            rows = feedback_sheet.get_all_values()
            header = rows[0]; data_rows = rows[1:]
            idx = _feedback_indices(header)

            def close(a, b, tol=1e-6):
                try: return abs(float(a) - float(b)) <= tol
                except: return False

            same_coord = []
            for row in data_rows:
                if idx["lat"] is None or idx["lon"] is None:
                    break
                if len(row) <= max(idx["lat"], idx["lon"]):
                    continue
                if close(row[idx["lat"]], lat) and close(row[idx["lon"]], lon):
                    same_coord.append(row)

            if idx["created"] is not None:
                same_coord.sort(key=lambda x: x[idx["created"]], reverse=True)
            recent = same_coord[:LAST_N_HISTORY]

            if idx["rating"] is not None:
                for row in recent:
                    try:
                        rr = int((row[idx["rating"]] or "").strip())
                    except:
                        continue
                    pp = (row[idx["paper"]] or "").strip() if idx["paper"] is not None else "沒注意"
                    aa = (row[idx["access"]] or "").strip() if idx["access"] is not None else "沒注意"
                    hist_feats.append([rr, paper_map.get(pp,0), access_map.get(aa,0)])
        except Exception as e:
            logging.warning(f"讀歷史回饋失敗，僅用單筆特徵預測：{e}")

        pred_with_hist = expected_from_feats([cur_feat] + hist_feats) or expected_from_feats([cur_feat]) or "未預測"

        feedback_sheet.append_row([
            name, address, rating, toilet_paper, accessibility, time_of_use,
            comment, pred_with_hist, lat, lon, datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S"),
            floor_hint
        ], value_input_option="USER_ENTERED")

        uid = (request.args.get("uid") or "").strip()
        lang = (request.args.get("lang") or "").strip().lower()
        target = f"/toilet_feedback_by_coord/{lat}/{lon}"
        if uid:
            target = _append_uid_lang(target, uid, (lang if lang in ("en","zh") else _user_lang_q(uid)))
        return redirect(target)

    except Exception as e:
        logging.error(f"❌ 提交回饋表單錯誤: {e}", exc_info=True)
        return "提交失敗", 500

# === 讀座標的回饋清單 ===
def get_feedbacks_by_coord(lat, lon, tol=1e-6):
    _ensure_sheets_ready()
    if feedback_sheet is None:
        return []
    try:
        header, data = _get_header_and_tail(feedback_sheet, MAX_SHEET_ROWS)
        if not header or not data:
            return []

        # 🔧 補上這行
        idx = _feedback_indices(header)

        def close(a, b):
            try: return abs(float(a) - float(b)) <= tol
            except: return False

        out = []
        for r in data:
            if idx["lat"] is None or idx["lon"] is None:
                break
            if len(r) <= max(idx["lat"], idx["lon"]):
                continue
            if close(r[idx["lat"]], lat) and close(r[idx["lon"]], lon):
                def val(key):
                    i = idx[key]
                    return (r[i] if i is not None and len(r) > i else "").strip()
                out.append({
                    "rating": val("rating"),
                    "toilet_paper": val("paper"),
                    "accessibility": val("access"),
                    "time_of_use": val("time"),
                    "comment": safe_html(val("comment")),
                    "cleanliness_score": val("pred"),
                    "created_at": val("created"),
                })
        out.sort(key=lambda d: d.get("created_at", ""), reverse=True)
        return out
    except Exception as e:
        logging.error(f"❌ 讀取回饋列表（座標）錯誤: {e}")
        return []

# === 座標聚合統計 ===
def get_feedback_summary_by_coord(lat, lon, tol=1e-6):
    _ensure_sheets_ready()
    if feedback_sheet is None:
        return "尚無回饋資料"
    try:
        header, data = _get_header_and_tail(feedback_sheet, MAX_SHEET_ROWS)
        if not header or not data:
            return "尚無回饋資料"

        # 🔧 補上這行
        idx = _feedback_indices(header)

        if idx["lat"] is None or idx["lon"] is None:
            return "（表頭缺少 lat/lon 欄位）"

        def close(a, b):
            try: return abs(float(a) - float(b)) <= tol
            except: return False

        matched = []
        for r in data:
            if len(r) <= max(idx["lat"], idx["lon"]):
                continue
            if close(r[idx["lat"]], lat) and close(r[idx["lon"]], lon):
                matched.append(r)

        if not matched:
            return "尚無回饋資料"

        paper_counts = {"有": 0, "沒有": 0}
        access_counts = {"有": 0, "沒有": 0}
        scores = []
        comments = []

        for r in matched:
            sc, rr, pp, aa = _pred_from_row(r, idx)
            if isinstance(sc, (int, float)):
                scores.append(float(sc))
            if pp in paper_counts: paper_counts[pp] += 1
            if aa in access_counts: access_counts[aa] += 1
            if idx["comment"] is not None and len(r) > idx["comment"]:
                c = (r[idx["comment"]] or "").strip()
                if c:
                    comments.append(c)

        avg_score = round(sum(scores) / len(scores), 2) if scores else "未預測"

        summary = f"🔍 筆數：{len(matched)}\n"
        summary += f"🧼 平均清潔分數：{avg_score}\n"
        summary += f"🧻 衛生紙：{'有' if paper_counts['有'] >= paper_counts['沒有'] else '沒有'}\n"
        summary += f"♿ 無障礙：{'有' if access_counts['有'] >= access_counts['沒有'] else '沒有'}\n"
        if comments:
            # 你現在拿 comments[-1]，因為 _get_header_and_tail 取尾巴，
            # 通常最後一筆就是最新，這邏輯 OK。
            summary += f"💬 最新留言：{comments[-1]}"
        return summary
    except Exception as e:
        logging.error(f"❌ 查詢回饋統計（座標）錯誤: {e}")
        return "讀取錯誤"

# === 指示燈索引 ===
_feedback_index_cache = {"ts": 0, "data": {}}
# _FEEDBACK_INDEX_TTL is defined in global config section (see above)
def build_feedback_index():
    _ensure_sheets_ready()
    if feedback_sheet is None:
        return {}

    global _feedback_index_cache

    now = time.time()
    # ⚠️ 注意這裡用的是「有底線」的 TTL 變數
    if (now - _feedback_index_cache["ts"] < _FEEDBACK_INDEX_TTL) and _feedback_index_cache["data"]:
        return _feedback_index_cache["data"]

    # 可調：最多聚合多少個座標點，避免 bucket 爆掉
    try:
        FEEDBACK_INDEX_MAX_KEYS = int(os.getenv("FEEDBACK_INDEX_MAX_KEYS", "800"))
    except Exception:
        FEEDBACK_INDEX_MAX_KEYS = 800

    try:
        header, data = _get_header_and_tail(feedback_sheet, MAX_SHEET_ROWS)
        if not header or not data:
            _feedback_index_cache = {"ts": now, "data": {}}
            return {}

        idx = _feedback_indices(header)
        i_lat = idx.get("lat"); i_lon = idx.get("lon")
        if i_lat is None or i_lon is None:
            _feedback_index_cache = {"ts": now, "data": {}}
            return {}
        
        bucket = {}
        for r in data:
            # 基本長度檢查
            if max(i_lat, i_lon) >= len(r):
                continue
            try:
                lat_s = norm_coord(r[i_lat])
                lon_s = norm_coord(r[i_lon])
            except Exception:
                continue
            if not lat_s or not lon_s:
                continue

            key = (lat_s, lon_s)

            # 控制 key 數量上限：已有的可以累加，新 key 超過上限就跳過
            if key not in bucket and len(bucket) >= FEEDBACK_INDEX_MAX_KEYS:
                continue

            rec = bucket.setdefault(
                key,
                {"paper_has": 0, "paper_no": 0, "acc_has": 0, "acc_no": 0, "sum": 0.0, "n": 0}
            )

            sc, rr, pp, aa = _pred_from_row(r, idx)

            # 紙巾／無障礙累計
            if pp == "有":
                rec["paper_has"] += 1
            elif pp == "沒有":
                rec["paper_no"] += 1

            if aa == "有":
                rec["acc_has"] += 1
            elif aa == "沒有":
                rec["acc_no"] += 1

            # 分數累計
            if isinstance(sc, (int, float)):
                try:
                    rec["sum"] += float(sc)
                    rec["n"] += 1
                except Exception:
                    pass

        # 輸出
        out = {}
        for key, v in bucket.items():
            paper_total = v["paper_has"] + v["paper_no"]
            access_total = v["acc_has"] + v["acc_no"]
            paper = "有" if (paper_total > 0 and v["paper_has"] >= v["paper_no"]) else ("沒有" if paper_total > 0 else "?")
            access = "有" if (access_total > 0 and v["acc_has"] >= v["acc_no"]) else ("沒有" if access_total > 0 else "?")
            avg = round(v["sum"] / v["n"], 2) if v["n"] > 0 else None
            out[key] = {"paper": paper, "access": access, "avg": avg}

        _feedback_index_cache = {"ts": now, "data": out}
        return out

    except Exception as e:
        logging.warning(f"建立指示燈索引失敗：{e}")
        _feedback_index_cache["ts"] = now
        _feedback_index_cache["data"] = {}
        return {}

def submit_status_update(lat, lon, status_text, user_id="", display_name="", note=""):
    _ensure_sheets_ready()
    if status_ws is None:
        return False
    try:
        row = [
            norm_coord(lat), norm_coord(lon),
            status_text.strip(), user_id or "", display_name or "",
            (note or "").strip(),
            datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S"),
        ]
        status_ws.append_row(row, value_input_option="USER_ENTERED")
        _status_index_cache["ts"] = 0  # 立刻失效快取
        return True
    except Exception as e:
        logging.error(f"寫入狀態失敗: {e}")
        return False

def _is_close_m(lat1, lon1, lat2, lon2, th=_STATUS_NEAR_M):
    try:
        return haversine(float(lat1), float(lon1), float(lat2), float(lon2)) <= th
    except:
        return False

def build_status_index():
    _ensure_sheets_ready()
    if status_ws is None:
        return {}

    now = time.time()
    # ✅ 修正：使用有底線的 TTL 變數（你前面定義的是 _STATUS_INDEX_TTL）
    if (now - _status_index_cache["ts"] < _STATUS_INDEX_TTL) and _status_index_cache["data"]:
        return _status_index_cache["data"]

    # 上限保護，避免大量新座標把記憶體撐爆（可用環境變數覆寫）
    try:
        STATUS_INDEX_MAX_KEYS = int(os.getenv("STATUS_INDEX_MAX_KEYS", "800"))
    except Exception:
        STATUS_INDEX_MAX_KEYS = 800

    out = {}
    try:
        header, data = _get_header_and_tail(status_ws, MAX_SHEET_ROWS)
        if not header or not data:
            _status_index_cache.update(ts=now, data={})
            return {}

        idx = {h: i for i, h in enumerate(header)}
        i_lat = idx.get("lat"); i_lon = idx.get("lon")
        i_status = idx.get("status"); i_ts = idx.get("timestamp")
        if None in (i_lat, i_lon, i_status):
            _status_index_cache.update(ts=now, data={})
            return {}

        def fresh(ts_s: str) -> bool:
            if not ts_s:
                return False
            try:
                dt = datetime.strptime(ts_s, "%Y-%m-%d %H:%M:%S")
                return (datetime.utcnow() - dt).total_seconds() <= _STATUS_TTL_HOURS * 3600
            except Exception:
                return False

        # 以「已合併清單」維護代表點；每筆資料只與既有代表點比 35m（_STATUS_NEAR_M）內是否更新
        merged = []
        for r in data:
            # 邊界保護
            if max(i_lat, i_lon, i_status) >= len(r):
                continue

            lat_s, lon_s = norm_coord(r[i_lat]), norm_coord(r[i_lon])
            st = (r[i_status] or "").strip()
            ts = (r[i_ts] if i_ts is not None and i_ts < len(r) else "")

            if not fresh(ts):
                continue

            placed = False
            # 嘗試合併到既有代表點（距離 <= _STATUS_NEAR_M）
            for m in merged:
                if _is_close_m(lat_s, lon_s, m["lat"], m["lon"]):
                    # 取較新的那筆
                    if ts > m["ts"]:
                        m.update(lat=lat_s, lon=lon_s, status=st, ts=ts)
                    placed = True
                    break

            if not placed:
                # 上限保護：超過上限不再加入新群組，但仍允許更新既有群組（見上面）
                if len(merged) < STATUS_INDEX_MAX_KEYS:
                    merged.append({"lat": lat_s, "lon": lon_s, "status": st, "ts": ts})
                else:
                    # 已滿就略過新位置，避免無上限成長
                    continue

        # 轉成輸出格式
        for m in merged:
            out[(m["lat"], m["lon"])] = {"status": m["status"], "ts": m["ts"]}

        _status_index_cache.update(ts=now, data=out)
        return out

    except Exception as e:
        logging.warning(f"建立狀態索引失敗：{e}")
        _status_index_cache["ts"] = now
        _status_index_cache["data"] = {}
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
    try:
        _ensure_sheets_ready()
        ws = status_ws
        if not ws:
            return []
        try:
            header, data = _get_header_and_tail(ws)
        except Exception:
            header, data = _get_header_and_tail(ws, MAX_SHEET_ROWS)
            if not header:
                return []

        ix = {h: i for i, h in enumerate(header)}
        out = []
        for r in data:
            def g(k):
                i = ix.get(k); 
                return (r[i].strip() if (i is not None and i < len(r)) else "")
            out.append({
                "lat": g("lat"), "lon": g("lon"),
                "status": g("status"),
                "user_id": g("user_id"),
                "display_name": g("display_name"),
                "timestamp": g("timestamp"),
            })
        return out
    except Exception as e:
        logging.error(f"_read_status_rows error: {e}")
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
    _ensure_sheets_ready()

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
    if worksheet is None or feedback_sheet is None:
        return render_template("toilet_feedback.html", toilet_name=toilet_name,
                               summary="（暫時無法連到雲端資料）",
                               feedbacks=[], address="", avg_pred_score=("N/A" if lang=="en" else "未預測"), lat="", lon="", liff_id=liff_id, uid=uid, lang=(lang if lang in ["en","zh"] else "zh"))
    try:
        address = "未知地址"
        rows = worksheet.get_all_values()
        data = rows[1:]
        for row in data:
            if len(row) > 1 and row[1] == toilet_name:
                address = (row[2] if len(row) > 2 else "") or "未知地址"
                break

        if address == "未知地址":
            return render_template("toilet_feedback.html", toilet_name=toilet_name,
                                   summary="請改用座標版入口（卡片上的『查詢回饋（座標）』）。",
                                   feedbacks=[], address="", avg_pred_score=("N/A" if lang=="en" else "未預測"), lat="", lon="", liff_id=liff_id, uid=uid, lang=(lang if lang in ["en","zh"] else "zh"))

        rows_fb = feedback_sheet.get_all_values()
        header = rows_fb[0]; data_fb = rows_fb[1:]
        idx = _feedback_indices(header)
        if idx["address"] is None:
            return render_template("toilet_feedback.html", toilet_name=toilet_name,
                                   summary="（表頭缺少『地址』欄位）", feedbacks=[], address=address,
                                   avg_pred_score=("N/A" if lang=="en" else "未預測"), lat="", lon="", liff_id=liff_id, uid=uid, lang=(lang if lang in ["en","zh"] else "zh"))

        matched = [r for r in data_fb
                   if len(r) > idx["address"] and (r[idx["address"]] or "").strip() == address.strip()]

        fbs = []
        nums = []
        for r in matched:
            def val(k):
                i = idx[k]
                return (r[i] if i is not None and len(r) > i else "").strip()
            sc, rr, pp, aa = _pred_from_row(r, idx)
            try: nums.append(float(sc))
            except: pass
            fbs.append({
                "rating": val("rating"),
                "toilet_paper": val("paper"),
                "accessibility": val("access"),
                "time_of_use": val("time"),
                "comment": safe_html(val("comment")),
                "cleanliness_score": str(sc) if sc is not None else "",
                "created_at": val("created"),
            })
        fbs.sort(key=lambda d: d.get("created_at",""), reverse=True)
        avg_pred_score = round(sum(nums)/len(nums), 2) if nums else "未預測"

        if matched:
            paper_counts = {"有": 0, "沒有": 0}
            access_counts = {"有": 0, "沒有": 0}
            for r in matched:
                _, _, pp, aa = _pred_from_row(r, idx)
                if pp in paper_counts: paper_counts[pp] += 1
                if aa in access_counts: access_counts[aa] += 1
            avg = avg_pred_score
            summary = f"🔍 筆數：{len(matched)}\n🧼 平均清潔分數：{avg}\n🧻 衛生紙：{'有' if paper_counts['有']>=paper_counts['沒有'] else '沒有'}\n♿ 無障礙：{'有' if access_counts['有']>=access_counts['沒有'] else '沒有'}\n"
        else:
            summary = "尚無回饋資料"

        return render_template("toilet_feedback.html",
                               toilet_name=toilet_name, summary=summary,
                               feedbacks=fbs, address=address,
                               avg_pred_score=avg_pred_score, lat="", lon="", liff_id=liff_id, uid=uid, lang=(lang if lang in ["en","zh"] else "zh"))
    except Exception as e:
        logging.error(f"❌ 渲染回饋頁面錯誤: {e}")
        return "查詢失敗", 500

# === 新路由 ===
@app.route("/toilet_feedback_by_coord/<lat>/<lon>")
def toilet_feedback_by_coord(lat, lon):
    _ensure_sheets_ready()

    liff_id = _get_liff_status_id()

    # ✅ 語言：優先用 querystring ?lang=，沒有就用資料庫記錄（需帶 uid）
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
    if feedback_sheet is None:
        return render_template("toilet_feedback.html",
                               toilet_name=f"廁所（{lat}, {lon}）",
                               summary="（暫時無法連到雲端資料）",
                               feedbacks=[], address=f"{lat},{lon}",
                               avg_pred_score=("N/A" if lang=="en" else "未預測"), lat=lat, lon=lon,
                               liff_id=liff_id, uid=uid, lang=(lang if lang in ["en","zh"] else "zh"))
    try:
        name = f"廁所（{lat}, {lon}）"
        summary = get_feedback_summary_by_coord(lat, lon)
        feedbacks = get_feedbacks_by_coord(lat, lon)

        header, data = _get_header_and_tail(feedback_sheet, MAX_SHEET_ROWS)
        if not header:
            header = []
        if not data:
            data = []

        idx = _feedback_indices(header)

        def close(a, b, tol=1e-6):
            try: return abs(float(a) - float(b)) <= tol
            except: return False

        scores = []
        for r in data:
            if len(r) <= max(idx["lat"], idx["lon"]):
                continue
            if close(r[idx["lat"]], lat) and close(r[idx["lon"]], lon):
                sc, _, _, _ = _pred_from_row(r, idx)
                if isinstance(sc, (int, float)):
                    scores.append(float(sc))
        avg_pred_score = round(sum(scores)/len(scores), 2) if scores else "未預測"

        return render_template(
            "toilet_feedback.html",
            toilet_name=name,
            summary=summary,
            feedbacks=feedbacks,
            address=f"{lat},{lon}",
            avg_pred_score=avg_pred_score,
            lat=lat,
            lon=lon,
            liff_id=liff_id, uid=uid, lang=(lang if lang in ["en","zh"] else "zh")
        )
    except Exception as e:
        logging.error(f"❌ 渲染回饋頁面（座標）錯誤: {e}")
        return "查詢失敗", 500

# === 清潔度趨勢（名稱版別名） ===
@app.route("/get_clean_trend/<path:toilet_name>")
def get_clean_trend_by_name(toilet_name):
    _ensure_sheets_ready()
    if feedback_sheet is None:
        return {"success": True, "data": []}, 200

    try:
        header, data = _get_header_and_tail(feedback_sheet, MAX_SHEET_ROWS)
        if not header or not data:
            return {"success": True, "data": []}, 200
        idx = _feedback_indices(header)

        name_idx = idx.get("name")
        lat_idx = idx.get("lat")
        lon_idx = idx.get("lon")
        created_idx = idx.get("created")

        if name_idx is None or lat_idx is None or lon_idx is None:
            # 表頭缺少必要欄位
            return {"success": True, "data": []}, 200

        # 找出同名的所有紀錄，取出座標
        matched = [r for r in data if len(r) > name_idx and (r[name_idx] or "").strip() == toilet_name.strip()]
        if not matched:
            return {"success": True, "data": []}, 200

        # 以最新一筆的座標為主
        if created_idx is not None:
            matched.sort(key=lambda x: (x[created_idx] if len(x) > created_idx else ""), reverse=True)
        ref = matched[0]
        lat = ref[lat_idx] if len(ref) > lat_idx else ""
        lon = ref[lon_idx] if len(ref) > lon_idx else ""

        # 轉呼叫座標版（邏輯一致）
        return get_clean_trend_by_coord(lat, lon)

    except Exception as e:
        logging.error(f"❌ 趨勢 API（名稱版）錯誤: {e}")
        return {"success": False, "data": []}, 500

# === 清潔度趨勢 API ===
@app.route("/get_clean_trend_by_coord/<lat>/<lon>")
def get_clean_trend_by_coord(lat, lon):
    _ensure_sheets_ready()
    if feedback_sheet is None:
        return {"success": True, "data": []}, 200 
    try:
        header, data = _get_header_and_tail(feedback_sheet, MAX_SHEET_ROWS)
        if not header or not data:
            return {"success": True, "data": []}, 200
        
        idx = _feedback_indices(header)

        if idx["lat"] is None or idx["lon"] is None:
            return {"success": False, "data": []}, 200

        # ✅ 放寬比對精度到 1e-4
        def close(a, b, tol=1e-4):
            try: return abs(float(a) - float(b)) <= tol
            except: return False

        matched_rows = []
        for r in data:
            if len(r) <= max(idx["lat"], idx["lon"]):
                continue
            if close(r[idx["lat"]], lat) and close(r[idx["lon"]], lon):
                matched_rows.append(r)

        if not matched_rows:
            return {"success": True, "data": []}, 200

        recomputed = []
        for r in matched_rows:
            created = r[idx["created"]] if idx["created"] is not None and len(r) > idx["created"] else ""
            sc, rr, pp, aa = _pred_from_row(r, idx)
            if sc is None:
                sc = _simple_score(rr, pp, aa)
            if isinstance(sc, (int, float)):
                # ✅ 順便把時間也回出去，前端畫圖更穩
                recomputed.append({"t": created, "score": round(float(sc), 2)})

        if not recomputed:
            return {"success": True, "data": []}, 200

        # 如果全部分數完全一樣，再嘗試用簡化版分數
        vals = [p["score"] for p in recomputed]
        if len(vals) >= 2 and (max(vals) - min(vals) < 1e-6):
            forced = []
            for r in matched_rows:
                created = r[idx["created"]] if idx["created"] is not None and len(r) > idx["created"] else ""
                _, rr, pp, aa = _pred_from_row(r, idx)
                sc2 = _simple_score(rr, pp, aa)
                if sc2 is not None:
                    forced.append({"t": created, "score": round(float(sc2), 2)})
            if forced:
                recomputed = forced

        # ✅ 確保時間排序
        recomputed.sort(key=lambda d: d["t"])
        return {"success": True, "data": recomputed}, 200

    except Exception as e:
        logging.error(f"❌ 趨勢 API（座標）錯誤: {e}")
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
    TW_TZ = timezone(timedelta(hours=8))

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
    """
    依照座標讀取 feedback_sheet 的回饋紀錄，
    丟給 OpenAI 做摘要，依使用者語言回傳中 / 英文 JSON。
    """
    uid = (request.args.get("uid") or "").strip()  # ✅ 先放最前面，避免 except 用不到 uid

    try:
        _ensure_sheets_ready()
        if feedback_sheet is None:
            return jsonify({
                "success": False,
                "message": L(uid, "回饋表尚未就緒，請稍後再試", "Feedback sheet not ready, please try again later")
            }), 503

        if client is None:
            return jsonify({
                "success": False,
                "message": L(uid, "AI 金鑰尚未設定", "AI key not configured")
            }), 500

        # === 語言判斷 ===
        lang = resolve_lang(uid=uid, lang=request.args.get("lang"))

        # ✅ 讓 system 也跟語言一致（避免混語）
        lang_rule = "請使用繁體中文回答。" if lang != "en" else "Please answer in English."
        system_msg = (
            f"You analyze restroom feedback and summarize it clearly. {lang_rule}"
            if lang == "en"
            else f"你負責分析廁所回饋並清楚摘要重點。{lang_rule}"
        )

        # 驗證 lat / lon
        try:
            lat_f = float(lat)
            lon_f = float(lon)
        except Exception:
            return jsonify({
                "success": False,
                "message": L(uid, "lat/lon 格式錯誤", "Invalid latitude / longitude")
            }), 400

        # 1️⃣ 從雲端回饋表抓資料
        header, data = _get_header_and_tail(feedback_sheet, MAX_SHEET_ROWS)
        if not header or not data:
            return jsonify({
                "success": True,
                "summary": "",  # 讓前端依 lang 顯示自己的 no_data 文案，避免混語
                "data": [],
                "has_data": False
            }), 200

        idx = _feedback_indices(header)
        if idx["lat"] is None or idx["lon"] is None:
            return jsonify({
                "success": False,
                "message": L(uid, "缺少 lat/lon 欄位", "lat/lon column missing")
            }), 400

        def close(a, b, tol=1e-4):
            try:
                return abs(float(a) - float(b)) <= tol
            except Exception:
                return False

        matched = []
        for r in data:
            if len(r) <= max(idx["lat"], idx["lon"]):
                continue
            if not (close(r[idx["lat"]], lat_f) and close(r[idx["lon"]], lon_f)):
                continue

            def v(key):
                i = idx.get(key)
                return (r[i] if i is not None and i < len(r) else "").strip()

            matched.append({
                "rating":     v("rating"),
                "paper":      v("paper"),
                "access":     v("access"),
                "comment":    v("comment"),
                "created_at": v("created"),
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
        ts = payload.get("ts") or datetime.utcnow().isoformat()

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
def create_toilet_flex_messages(toilets, uid=None):
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

        actions.append({
            "type": "uri",
            "label": L(uid, "導航", "Navigate"),
            "uri": f"https://www.google.com/maps/search/?api=1&query={lat_s},{lon_s}"
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
    _ensure_sheets_ready()
    if worksheet is None:
        return []
    items = []
    try:
        rows = worksheet.get_all_values()
        if not rows or len(rows) < 2:
            return items
        header = rows[0]; data = rows[1:]
        idx = _toilet_sheet_indices(header)
        for i, r in enumerate(data, start=2):
            if idx["user_id"] is None: break
            if len(r) <= idx["user_id"]: continue
            if r[idx["user_id"]] != uid: continue
            try:
                lat = float(r[idx["lat"]]); lon = float(r[idx["lon"]])
            except:
                continue
            items.append({
                "row_index": i,
                "name": (r[idx["name"]] if idx["name"] is not None and len(r)>idx["name"] else "無名稱"),
                "address": (r[idx["address"]] if idx["address"] is not None and len(r)>idx["address"] else ""),
                "lat": float(norm_coord(lat)),
                "lon": float(norm_coord(lon)),
                "created": (r[idx["created"]] if idx["created"] is not None and len(r)>idx["created"] else ""),
            })
        return items
    except Exception as e:
        logging.error(f"讀取我的貢獻失敗：{e}")
        return items

def create_my_contrib_flex(uid):
    contribs = get_user_contributions(uid)
    if not contribs:
        return None

    bubbles = []
    for it in contribs[:10]:
        lat_s = norm_coord(it["lat"])
        lon_s = norm_coord(it["lon"])
        addr_raw = it.get('address','') or ""
        addr_param = quote(addr_raw or "-")

        actions = [
            {
                "type": "uri",
                "label": L(uid, "導航", "Navigate"),
                "uri": f"https://www.google.com/maps/search/?api=1&query={lat_s},{lon_s}"
            },
            {
                "type": "uri",
                "label": L(uid, "查詢回饋（座標）", "View feedback (coord)"),
                "uri": _append_uid_lang(f"https://school-i9co.onrender.com/toilet_feedback_by_coord/{lat_s}/{lon_s}", uid, _user_lang_q(uid))
            },
            {
                "type": "uri",
                "label": L(uid, "廁所回饋", "Leave feedback"),
                "uri": (
                    f"https://school-i9co.onrender.com/feedback_form/{quote(it['name'])}/{addr_param}"
                    f"?lat={lat_s}&lon={lon_s}&address={quote(addr_raw)}"
                )
            },
            {
                "type": "postback",
                "label": L(uid, "刪除此貢獻", "Delete this contribution"),
                "data": f"confirm_delete_my_toilet:{it['row_index']}"
            }
        ]

        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {"type": "text", "text": it["name"], "size": "lg", "weight": "bold", "wrap": True},
                    {"type": "text", "text": it.get("address") or L(uid, "（無地址）", "(No address)"),
                     "size": "sm", "color": "#666666", "wrap": True},
                    {"type": "text", "text": it.get("created",""), "size": "xs", "color": "#999999"}
                ]
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

    return {"type":"carousel", "contents": bubbles}


# === Dashboard ===
_DASHBOARD_RANGE_SECONDS = {
    "1h": 3600,
    "1d": 86400,
    "7d": 7 * 86400,
    "30d": 30 * 86400,
    "1y": 365 * 86400,
}


def _dashboard_range_to_sqlite(range_key: str):
    now = datetime.utcnow()

    if range_key == "1h":
        start = now - timedelta(hours=1)
        labels = [f"{i*5}分" for i in range(12)]
    elif range_key == "1d":
        start = now - timedelta(days=1)
        labels = [f"{str(i).zfill(2)}:00" for i in range(24)]
    elif range_key == "7d":
        start = now - timedelta(days=7)
        labels = [f"{i+1}" for i in range(7)]
    elif range_key == "30d":
        start = now - timedelta(days=30)
        labels = [f"{i+1}" for i in range(30)]
    else:
        start = now - timedelta(days=365)
        labels = [f"{i+1}月" for i in range(12)]

    return start, now, labels


def _bucket_label(dt_obj, range_key):
    if range_key == "1h":
        return f"{(dt_obj.minute // 5) * 5}分"
    if range_key == "1d":
        return f"{dt_obj.hour:02d}:00"
    if range_key in ("7d", "30d"):
        return f"{dt_obj.day}"
    return f"{dt_obj.month}月"


def _generate_dashboard_data(range_key="1h"):
    start, end, default_labels = _dashboard_range_to_sqlite(range_key)

    if POSTGRES_ENABLED:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT id, user_id, event_type, result_count, success, response_time_ms, lat, lon, area_name, query_text,
                   created_at AT TIME ZONE 'UTC' AS created_at
            FROM analytics_events
            WHERE created_at >= %s AND created_at <= %s
            ORDER BY created_at DESC
        """, (start, end))
        rows = cur.fetchall()
        conn.close()
        events = [dict(r) for r in rows]
        for e in events:
            if isinstance(e.get("created_at"), datetime):
                e["created_at"] = e["created_at"].isoformat()
    else:
        conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        cur = conn.cursor()

        cur.execute("""
            SELECT * FROM analytics_events
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

    response_values = [int(e["response_time_ms"]) for e in events if e.get("response_time_ms") is not None]
    avg_response = round(sum(response_values) / len(response_values)) if response_values else 0

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
            if first_seen and first_seen >= start:
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
            dt_obj = datetime.fromisoformat(e["created_at"])
        except Exception:
            continue
        label = _bucket_label(dt_obj, range_key)
        if label not in trend_map_queries:
            continue
        if e["event_type"] == "location_query" and int(e.get("response_time_ms") or 0) > 0:
            trend_map_queries[label] += 1
        if e.get("user_id"):
            trend_map_users[label].add(e["user_id"])

    trend_queries = [trend_map_queries[label] for label in default_labels]
    trend_users = [len(trend_map_users[label]) for label in default_labels]

    hourly_map = {f"{i:02d}:00": 0 for i in range(24)}
    for e in events:
        try:
            dt_obj = datetime.fromisoformat(e["created_at"])
            hourly_map[f"{dt_obj.hour:02d}:00"] += 1
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

    response_sorted = sorted(response_values)
    median_value = response_sorted[len(response_sorted)//2] if response_sorted else 0
    p95_index = min(len(response_sorted)-1, int(len(response_sorted)*0.95)) if response_sorted else 0
    p95_value = response_sorted[p95_index] if response_sorted else 0

    return {
        "summary": {
            "totalQueries": total_queries,
            "activeUsers": active_users,
            "successRate": success_rate,
            "avgResponse": avg_response,
            "newUsers": new_users,
            "retentionRate": retention_rate,
            "noResultCount": no_result_count,
            "errorCount": error_count
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


@app.route("/dashboard", methods=["GET"])
def dashboard_page():
    return render_template("dashboard.html")


@app.route("/api/dashboard", methods=["GET"])
def api_dashboard():
    range_key = (request.args.get("range") or "1h").strip()
    if range_key not in ("1h", "1d", "7d", "30d", "1y"):
        range_key = "1h"
    return jsonify(_generate_dashboard_data(range_key))

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
    # === Grid cache key（第一步）===
    lat_g = grid_coord(lat)
    lon_g = grid_coord(lon)
    query_key = f"nearby:{lat_g},{lon_g},{radius}"

    cached = get_cached_data(query_key)
    if cached:
        logging.debug(f"[cache hit] nearby {query_key}")
        return cached

    futures = []
    csv_res, saved_res, sheet_res, osm_res = [], [], [], []

    try:
        futures.append(("csv",   _pool.submit(query_public_csv_toilets, lat, lon, radius)))
        futures.append(("saved", _pool.submit(query_saved_toilets,      lat, lon, radius)))
        futures.append(("sheet", _pool.submit(query_sheet_toilets,      lat, lon, radius)))
        futures.append(("osm",   _pool.submit(query_overpass_toilets,   lat, lon, radius)))

        for name, fut in futures:
            try:
                res = fut.result(timeout=LOC_QUERY_TIMEOUT_SEC)
                if   name == "csv":   csv_res   = res or []
                elif name == "saved": saved_res = res or []
                elif name == "sheet": sheet_res = res or []
                else:                  osm_res   = res or []
            except FuturesTimeoutError:
                logging.warning(f"{name} 查詢逾時")
            except Exception as e:
                logging.warning(f"{name} 查詢失敗: {e}")

    finally:
        for _, fut in futures:
            if not fut.done():
                fut.cancel()

    quick = _merge_and_dedupe_lists(csv_res, saved_res, sheet_res, osm_res)
    sort_toilets(quick)
    result = quick[:LOC_MAX_RESULTS]

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
    # 🧹 pending_delete_confirm（維持你原本邏輯）
    # =========================
    if uid in pending_delete_confirm:
        # 假設你原本是做 yes/no 確認
        confirm = text_key in ("yes", "y", "是", "確認")
        if confirm:
            handle_confirm_delete(uid)
            safe_reply(event, TextSendMessage(text=L(uid, "✅ 已刪除", "✅ Deleted")))
        else:
            safe_reply(event, TextSendMessage(text=L(uid, "❌ 已取消", "❌ Cancelled")))
        pending_delete_confirm.discard(uid)
        return

    # =========================
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
        base = "https://school-i9co.onrender.com/add"
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
        toilets = build_nearby_toilets(uid, lat, lon)
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
            # 先產出原本的廁所 carousel
            msg = create_toilet_flex_messages(toilets, uid=uid)

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
        safe_reply(event, TextSendMessage(text="✅ Language switched to English"))
        return

    if data == "set_lang:zh":
        set_user_lang(uid, "zh")
        safe_reply(event, TextSendMessage(text="✅ 已切換為中文"))
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
                base = "https://school-i9co.onrender.com/add"
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

# === Sheets 寫入保護：超過 1e7 cells 就 fallback 到本機儲存 ===
_toilet_sheet_over_quota = False
_toilet_sheet_over_quota_ts = 0

def _fallback_store_toilet_row_locally(row_values):
    # CSV + SQLite 都不是 thread-safe，需要鎖住整段
    with _fallback_lock:

        # 1) 附加到 public_toilets.csv
        try:
            if not os.path.exists(TOILETS_FILE_PATH):
                with open(TOILETS_FILE_PATH, "w", encoding="utf-8", newline="") as f:
                    writer = csv.writer(f)
                    writer.writerow(PUBLIC_HEADERS)

            header = ensure_toilet_sheet_header(worksheet)
            idx = {h:i for i,h in enumerate(header)}

            def v(col):
                try:
                    return row_values[idx[col]]
                except Exception:
                    return ""

            name = v("name")
            addr = v("address")
            lat_s = v("lat")
            lon_s = v("lon")

            with open(TOILETS_FILE_PATH, "a", encoding="utf-8", newline="") as f:
                writer = csv.writer(f)
                writer.writerow([
                    "00000","0000000","未知里","USERADD",
                    name, addr, "使用者補充",
                    lat_s, lon_s,
                    "普通級","公共場所","未知","使用者","0"
                ])

        except Exception as e:
            logging.warning(f"備份至本地 CSV 失敗：{e}")

        # 2) 寫入 Postgres / SQLite
        try:
            header = ensure_toilet_sheet_header(worksheet)
            idx = {h:i for i,h in enumerate(header)}

            def v(col):
                try:
                    return row_values[idx[col]]
                except:
                    return ""

            if POSTGRES_ENABLED:
                conn = _pg_connect()
                cur = conn.cursor()
                cur.execute("""
                    INSERT INTO user_toilets (
                        user_id, name, address, lat, lon,
                        level, floor_hint, entrance_hint,
                        access_note, open_hours, created_at, updated_at
                    )
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                """, (
                    v("user_id"), v("name"), v("address"),
                    float(v("lat")), float(v("lon")),
                    v("level"), v("floor_hint"), v("entrance_hint"),
                    v("access_note"), v("open_hours"),
                    datetime.utcnow(), datetime.utcnow()
                ))
                conn.commit()
                conn.close()
            else:
                conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
                cur = conn.cursor()
                cur.execute("""
                CREATE TABLE IF NOT EXISTS user_toilets (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id TEXT, name TEXT, address TEXT,
                    lat TEXT, lon TEXT,
                    level TEXT, floor_hint TEXT, entrance_hint TEXT,
                    access_note TEXT, open_hours TEXT, timestamp TEXT
                )
                """)
                cur.execute("""
                    INSERT INTO user_toilets (
                        user_id, name, address, lat, lon,
                        level, floor_hint, entrance_hint,
                        access_note, open_hours, timestamp
                    )
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    v("user_id"), v("name"), v("address"),
                    v("lat"), v("lon"),
                    v("level"), v("floor_hint"), v("entrance_hint"),
                    v("access_note"), v("open_hours"),
                    v("timestamp")
                ))
                conn.commit()
                conn.close()

        except Exception as e:
            logging.warning(f"備份至資料庫失敗：{e}")

def _append_toilet_row_safely(ws, row_values):
    global _toilet_sheet_over_quota, _toilet_sheet_over_quota_ts

    if _toilet_sheet_over_quota:
        _fallback_store_toilet_row_locally(row_values)
        return ("fallback", "Google 試算表已達儲存上限，改為暫存本機。")

    try:
        with _gsheet_lock:
            ws.append_row(row_values, value_input_option="USER_ENTERED")
        return ("ok", "已寫入 Google 試算表")

    except Exception as e:
        s = str(e)
        if "10000000" in s or "above the limit" in s:
            logging.error("🧱 Google 試算表達到 1e7 cells 上限，啟用本機暫存。")
            _toilet_sheet_over_quota = True
            _toilet_sheet_over_quota_ts = time.time()
            logging.error("❌ Sheets 已滿，SQLite fallback 已停用，請處理資料儲存策略")
            return ("fallback", "Google 試算表已達儲存上限，改為暫存本機。")

        raise

def _get_db():
    return sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)

def _ensure_pending_table():
    conn = _get_db()
    cur = conn.cursor()
    cur.execute("""
    CREATE TABLE IF NOT EXISTS pending_gsheet (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        payload_json TEXT NOT NULL,
        created_ts REAL
    )
    """)
    conn.commit(); conn.close()

_ensure_pending_table()

# === 查詢紀錄 search_log ===
def _ensure_search_table():
    conn = _get_db()
    cur = conn.cursor()
    cur.execute("""
    CREATE TABLE IF NOT EXISTS search_log (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id TEXT,
        lat TEXT,
        lon TEXT,
        ts TEXT
    )
    """)
    conn.commit()
    conn.close()

_ensure_search_table()

def _ensure_user_lang_table():
    conn = _get_db()
    cur = conn.cursor()
    cur.execute("""
    CREATE TABLE IF NOT EXISTS user_lang (
        user_id TEXT PRIMARY KEY,
        lang TEXT
    )
    """)
    conn.commit()
    conn.close()

_ensure_user_lang_table()

def _ensure_search_index():
    conn = _get_db()
    cur = conn.cursor()
    cur.execute("CREATE INDEX IF NOT EXISTS idx_search_user ON search_log(user_id)")
    conn.commit()
    conn.close()

_ensure_search_index()
# === 查詢紀錄 search_log ===
def _ensure_ai_quota_table():
    conn = _get_db()
    cur = conn.cursor()
    cur.execute("""
    CREATE TABLE IF NOT EXISTS ai_quota (
        key TEXT,
        date TEXT,
        count INTEGER,
        PRIMARY KEY(key, date)
    )
    """)
    conn.commit()
    conn.close()

_ensure_ai_quota_table()

def _queue_pending_row(row_values):
    try:
        conn = _get_db(); cur = conn.cursor()
        cur.execute("INSERT INTO pending_gsheet (payload_json, created_ts) VALUES (?, ?)",
                    (json.dumps(row_values, ensure_ascii=False), time.time()))
        conn.commit(); conn.close()
    except Exception as e:
        logging.warning(f"queue pending failed: {e}")

def _drain_pending(limit=200):
    _ensure_sheets_ready()
    if worksheet is None:
        return 0, "worksheet not ready"

    conn = _get_db(); cur = conn.cursor()
    cur.execute("SELECT id, payload_json FROM pending_gsheet ORDER BY id ASC LIMIT ?", (limit,))
    rows = cur.fetchall()
    if not rows:
        conn.close(); return 0, "empty"

    ok = 0
    for row_id, payload in rows:
        try:
            vals = json.loads(payload)
            with _gsheet_lock:
                worksheet.append_row(vals, value_input_option="USER_ENTERED")
            cur.execute("DELETE FROM pending_gsheet WHERE id=?", (row_id,))
            ok += 1
        except Exception as e:
            logging.warning(f"backfill append failed: {e}")
            break
    conn.commit(); conn.close()
    return ok, "done"

ADMIN_TOKEN = os.getenv("ADMIN_TOKEN", "")

@app.route("/admin/backfill", methods=["POST"])
def admin_backfill():
    token = (request.headers.get("X-Admin-Token") or "").strip()
    if not ADMIN_TOKEN or token != ADMIN_TOKEN:
        return {"ok": False, "message": "unauthorized"}, 401

    n, note = _drain_pending(limit=500)
    return {"ok": True, "written": n, "note": note}, 200


# === 使用者新增廁所 API ===
@app.route("/submit_toilet", methods=["POST"])
def submit_toilet():
    if not POSTGRES_ENABLED:
        _ensure_sheets_ready()
        if worksheet is None:
            return {"success": False, "message": "雲端表格暫時無法連線，請稍後再試"}, 503
    try:
        data = request.get_json(force=True, silent=False) or {}
        logging.info(f"📥 收到表單資料: {data}")

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

        if POSTGRES_ENABLED:
            conn = _pg_connect()
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO user_toilets (
                    user_id, name, address, lat, lon,
                    level, floor_hint, entrance_hint,
                    access_note, open_hours, created_at, updated_at
                )
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                RETURNING id
            """, (
                uid, name, addr, float(lat_s), float(lon_s),
                level, floor_hint, entrance_hint,
                access_note, open_hours,
                datetime.utcnow(), datetime.utcnow()
            ))
            new_id = cur.fetchone()[0]
            conn.commit()
            conn.close()
            logging.info(f"📝 submit_toilet 已寫入 Postgres id={new_id} name={name}")
            return {"success": True, "message": f"✅ 已新增廁所 {name}", "id": new_id}

        # 佈局表頭 & 寫入欄位
        header = ensure_toilet_sheet_header(worksheet)
        idx = {h: i for i, h in enumerate(header)}

        row_values = [""] * len(header)
        def put(col, val):
            if col in idx:
                row_values[idx[col]] = val

        put("user_id", uid)
        put("name", name)
        put("address", addr)
        put("lat", lat_s)
        put("lon", lon_s)
        put("level", level)
        put("floor_hint", floor_hint)
        put("entrance_hint", entrance_hint)
        put("access_note", access_note)
        put("open_hours", open_hours)
        put("timestamp", datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S"))

        status, note = _append_toilet_row_safely(worksheet, row_values)
        logging.info(f"📝 submit_toilet 寫入狀態: {status} ({note}) name={name}")

        if status == "ok":
            return {"success": True, "message": f"✅ 已新增廁所 {name}"}
        else:
            return {"success": True, "message": f"✅ 已暫存 {name}（雲端表已滿，稍後可批次補寫）"}

    except Exception as e:
        logging.error(f"❌ 新增廁所錯誤:\n{traceback.format_exc()}")
        return {"success": False, "message": "伺服器錯誤"}, 500

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
    threading.Thread(target=auto_predict_cleanliness_background, daemon=True).start()
    threading.Thread(target=_self_keepalive_background, daemon=True).start()

    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
