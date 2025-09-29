import os
import csv
import json
import logging
import sqlite3
import requests
import traceback
from math import radians, cos, sin, asin, sqrt
from flask_cors import CORS
from flask import Flask, request, abort, render_template, redirect, url_for, Response
from dotenv import load_dotenv
from urllib.parse import quote, unquote
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError, LineBotApiError
from linebot.models import (
    MessageEvent, TextMessage, LocationMessage,
    FlexSendMessage, PostbackEvent, TextSendMessage, LocationAction, MessageAction
)
from linebot.models import QuickReply, QuickReplyButton
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeoutError
import gspread
from oauth2client.service_account import ServiceAccountCredentials
from datetime import datetime
import joblib
import threading
import time
import statistics
from difflib import SequenceMatcher
import random
import re

load_dotenv()
try:
    import pandas as pd
except Exception:
    pd = None

# === 全域設定 ===
LOC_MAX_CONCURRENCY = int(os.getenv("LOC_MAX_CONCURRENCY", "8"))     # 同時最多幾個使用者在跑附近查詢
LOC_QUERY_TIMEOUT_SEC = float(os.getenv("LOC_QUERY_TIMEOUT_SEC", "3.0"))  # 各資料源逾時（秒）
LOC_MAX_RESULTS = int(os.getenv("LOC_MAX_RESULTS", "5"))             # 最多回幾個
SHOW_SEARCHING_BUBBLE = False
_LOC_SEM = threading.Semaphore(LOC_MAX_CONCURRENCY)

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
_MAX_USED_TOKENS = 50000  # 防止集合無限成長

def _mark_token_used(tok: str):
    try:
        _USED_REPLY_TOKENS.add(tok)
        if len(_USED_REPLY_TOKENS) > _MAX_USED_TOKENS:
            _USED_REPLY_TOKENS.clear()  # 簡單清理
    except Exception:
        pass

def _is_token_used(tok: str) -> bool:
    return tok in _USED_REPLY_TOKENS

# ======================== Sheets 安全外掛層（新增，不動原功能） ========================
SHEETS_MAX_CONCURRENCY = int(os.getenv("SHEETS_MAX_CONCURRENCY", "4"))
SHEETS_RETRY_MAX = int(os.getenv("SHEETS_RETRY_MAX", "6"))
SHEETS_READ_TTL_SEC = int(os.getenv("SHEETS_READ_TTL_SEC", "30"))
SHEETS_CACHE_MAX_ROWS = int(os.getenv("SHEETS_CACHE_MAX_ROWS", "20000"))

_sheets_sem = threading.Semaphore(SHEETS_MAX_CONCURRENCY)
_read_cache = {}            # key: (sheet_id, ws_title, op) -> {ts, val}
_cache_lock = threading.Lock()

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
        if len(val) <= SHEETS_CACHE_MAX_ROWS:
            with _cache_lock:
                _read_cache[key] = {"ts": now, "val": val}
        return val

    def _invalidate(self):
        key = (self._sheet_id, self._name, "get_all_values")
        with _cache_lock:
            _read_cache.pop(key, None)

    def update(self, rng, values):
        def _do():
            return self._ws.update(rng, values)
        out = _with_retry(_do); self._invalidate(); return out

    def append_row(self, values, value_input_option="RAW"):
        def _do():
            return self._ws.append_row(values, value_input_option=value_input_option)
        out = _with_retry(_do); self._invalidate(); return out

    def delete_rows(self, index):
        def _do():
            return self._ws.delete_rows(index)
        out = _with_retry(_do); self._invalidate(); return out

    # 轉發
    def row_values(self, i):           return _with_retry(self._ws.row_values, i)
    def worksheet(self, title):        return self.__class__(self._ws.worksheet(title), self._sheet_id, title)
    @property
    def title(self):                   return self._ws.title

# consent 背景排隊（429 時不回 500）
_consent_q = []
_consent_lock = threading.Lock()
def _start_consent_worker():
    def loop():
        while True:
            job = None
            with _consent_lock:
                if _consent_q:
                    job = _consent_q.pop(0)
            if not job:
                time.sleep(0.2); continue
            try:
                job()
            except Exception as e:
                logging.error(f"Consent worker error: {e}")
    threading.Thread(target=loop, daemon=True).start()
_start_consent_worker()

def make_location_quick_reply(prompt_text="📍 請分享你的位置"):
    return TextSendMessage(
        text=prompt_text,
        quick_reply=QuickReply(items=[
            QuickReplyButton(action=LocationAction(label="傳送我的位置"))
        ])
    )

def make_retry_location_text(text="現在查詢人數有點多，我排一下隊；你可再傳一次位置或稍候幾秒～"):
    return TextSendMessage(
        text=text,
        quick_reply=QuickReply(items=[
            QuickReplyButton(action=LocationAction(label="傳送我的位置"))
        ])
    )
def make_no_toilet_quick_reply(uid, lat=None, lon=None,
                               text="附近沒有廁所 😥 要不要補上一間？"):
    base = "https://school-i9co.onrender.com/add"
    if lat is not None and lon is not None:
        add_url = f"{base}?uid={quote(uid)}&lat={lat}&lon={lon}#openExternalBrowser=1"
    else:
        add_url = f"{base}?uid={quote(uid)}#openExternalBrowser=1"

    return TextSendMessage(
        text=text,
        quick_reply=QuickReply(items=[
            QuickReplyButton(action=LocationAction(label="傳送我的位置")),
            QuickReplyButton(action=MessageAction(label="新增廁所", text="新增廁所"))
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
    try:
        # 通用安全與快取政策
        resp.headers.setdefault("Cache-Control", "no-store")
        resp.headers.setdefault("Pragma", "no-cache")
        resp.headers.setdefault("X-Content-Type-Options", "nosniff")
        resp.headers.setdefault("X-Frame-Options", "DENY")
        resp.headers.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")

        path = (request.path or "").lower()

        if path.startswith("/consent") or path.startswith("/api/consent"):
            # 🔓 完全放寬 CSP，避免擋到 LIFF
            resp.headers["Content-Security-Policy"] = (
                "default-src * data: blob: filesystem: about: 'unsafe-inline' 'unsafe-eval';"
            )
        else:
            # ✅ 其他頁面：允許常見 CDN 載入 Chart.js；並加上 connect-src 以便 fetch
            csp = [
                "default-src 'self'",
                "img-src 'self' data: https:",
                "script-src 'self' 'unsafe-inline' https://cdn.jsdelivr.net https://cdnjs.cloudflare.com https://unpkg.com",
                "style-src 'self' 'unsafe-inline'",
                "connect-src 'self' https:",
                "font-src 'self' data: https:",
                "frame-ancestors 'none'",
            ]
            # 用「直接指定」取代 setdefault，確保覆蓋舊值
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

_CACHE = {}

def get_nearby_toilets(uid, lat, lon):
    key = f"{lat},{lon}"
    if key in _CACHE:
        return _CACHE[key]
    
    # 若快取中不存在該位置，則發送請求
    toilets = query_public_csv_toilets(lat, lon)
    _CACHE[key] = toilets  # 快取結果
    return toilets

# === 檔案 ===
DATA_DIR = os.path.join(os.getcwd(), "data")
TOILETS_FILE_PATH = os.path.join(DATA_DIR, "public_toilets.csv")
FAVORITES_FILE_PATH = os.path.join(DATA_DIR, "favorites.txt")
os.makedirs(DATA_DIR, exist_ok=True)

if not os.path.exists(FAVORITES_FILE_PATH):
    open(FAVORITES_FILE_PATH, "a", encoding="utf-8").close()

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
_STATUS_INDEX_TTL = 60

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
_ENRICH_CACHE = {}
_ENRICH_TTL = 120

def enrich_nearby_places(lat, lon, radius=500):
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
                    if e["type"] == "node":
                        clat, clon = e.get("lat"), e.get("lon")
                    else:
                        c = e.get("center") or {}
                        clat, clon = c.get("lat"), c.get("lon")
                    if clat is None or clon is None:
                        continue
                    t = e.get("tags", {}) or {}
                    nm = t.get("name")
                    if nm:
                        out.append({"name": nm, "lat": float(clat), "lon": float(clon)})
                _ENRICH_CACHE[key] = (now, out)
                return out
        except Exception:
            continue
    _ENRICH_CACHE[key] = (now, [])
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

# === 防重複 ===
DEDUPE_WINDOW = int(os.getenv("DEDUPE_WINDOW", "10"))
_RECENT_EVENTS = {}

def is_duplicate_and_mark(key: str, window: int = DEDUPE_WINDOW) -> bool:
    now = time.time()
    ts = _RECENT_EVENTS.get(key)
    if ts is not None and (now - ts) < window:
        logging.info(f"🔁 skip duplicate: {key}")
        return True
    _RECENT_EVENTS[key] = now
    if len(_RECENT_EVENTS) > 5000 or (len(_RECENT_EVENTS) > 1000):
        for k, tstamp in list(_RECENT_EVENTS.items()):
            if now - tstamp > window:
                _RECENT_EVENTS.pop(k, None)
    return False

def is_redelivery(event) -> bool:
    try:
        dc = getattr(event, "delivery_context", None)
        return bool(getattr(dc, "is_redelivery", False))
    except Exception:
        return False

LINE_REPLY_MAX = 5

def safe_reply(event, messages):
    try:
        tok = event.reply_token
        if _is_token_used(tok):
            logging.warning("[safe_reply] duplicate reply_token detected; skip sending.")
            return

        # ✅ 最多 5 則，多的砍掉（或自行改成合併文字）
        if isinstance(messages, list) and len(messages) > LINE_REPLY_MAX:
            logging.warning(f"[safe_reply] messages too many ({len(messages)}), truncating to {LINE_REPLY_MAX}.")
            messages = messages[:LINE_REPLY_MAX]

        line_bot_api.reply_message(tok, messages)
        _mark_token_used(tok)

    except LineBotApiError as e:
        # 解析錯誤訊息
        try:
            msg_txt = getattr(getattr(e, "error", None), "message", "") or str(e)
        except Exception:
            msg_txt = str(e)

        # 重送（redelivery）一律不回覆（避免重複）
        if is_redelivery(event):
            logging.warning(f"[safe_reply] redelivery detected; skip. err={msg_txt}")
            return

        # reply_token 無效或已過期 → 不再 fallback 到 push（避免狂刷）
        if "Invalid reply token" in msg_txt:
            logging.warning(f"[safe_reply] invalid reply token; skip. err={msg_txt}")
            return

        # 其他錯誤只記錄
        logging.warning(f"[safe_reply] reply_message failed (no push). err={msg_txt}")

def _too_old_to_reply(event, limit_seconds=55):
    try:
        evt_ms = int(getattr(event, "timestamp", 0))  # 毫秒
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
CACHE_DB_PATH = "cache.db"

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
        conn = sqlite3.connect(CACHE_DB_PATH)
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
    conn = sqlite3.connect(CACHE_DB_PATH)
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
    conn = sqlite3.connect(CACHE_DB_PATH)
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

# 查詢廁所資料
def query_sheet_toilets(user_lat, user_lon, radius=500):
    _ensure_sheets_ready()
    if worksheet is None:
        return []

    query_key = f"{user_lat},{user_lon},{radius}"
    cached_data = get_cached_data(query_key)
    if cached_data:
        return cached_data

    toilets = []
    try:
        rows = worksheet.get_all_values()
        header = rows[0] if rows else []
        data = rows[1:]

        idx = _toilet_sheet_indices(header)

        for row in data:
            # 基本欄位不齊就跳過
            if len(row) < 5:
                continue

            name = (row[idx["name"]] if idx["name"] is not None and len(row) > idx["name"] else "").strip() or "無名稱"
            address = (row[idx["address"]] if idx["address"] is not None and len(row) > idx["address"] else "").strip()

            try:
                t_lat = float(row[idx["lat"]]) if idx["lat"] is not None and len(row) > idx["lat"] else None
                t_lon = float(row[idx["lon"]]) if idx["lon"] is not None and len(row) > idx["lon"] else None
            except Exception:
                t_lat = t_lon = None
            if t_lat is None or t_lon is None:
                continue

            dist = haversine(user_lat, user_lon, t_lat, t_lon)
            if dist > radius:
                continue

            # 只讀你要的三個欄位（若無給空字串）
            level         = (row[idx["level"]] if idx["level"] is not None and len(row) > idx["level"] else "").strip()
            floor_hint_ws = (row[idx["floor_hint"]] if idx["floor_hint"] is not None and len(row) > idx["floor_hint"] else "").strip()
            open_hours    = (row[idx["open_hours"]] if idx["open_hours"] is not None and len(row) > idx["open_hours"] else "").strip()

            # 若沒樓層提示就用名稱推斷
            auto_floor = _floor_from_name(name)
            floor_hint = floor_hint_ws or level or auto_floor

            toilets.append({
                "name": name,
                "lat": float(norm_coord(t_lat)),
                "lon": float(norm_coord(t_lon)),
                "address": address,
                "distance": dist,
                "type": "sheet",
                "level": level,
                "floor_hint": floor_hint,
                "open_hours": open_hours,
            })
    except Exception as e:
        logging.error(f"讀取 Google Sheets 廁所主資料錯誤: {e}")

    # 可選：釋放大列表幫助記憶體回收
    try:
        del rows
    except Exception:
        pass

    save_cache(query_key, toilets)
    return sorted(toilets, key=lambda x: x["distance"])

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
                resp = requests.post(url, data=query, headers=headers, timeout=min(8, _left()))
                ctype = (resp.headers.get("Content-Type") or "").lower()
                if resp.status_code != 200 or "json" not in ctype:
                    last_err = RuntimeError(f"overpass non-json {resp.status_code}")
                    continue

                data = resp.json()
                elements = data.get("elements", [])
                toilets = []
                for elem in elements:
                    if "center" in elem:
                        t_lat, t_lon = elem["center"]["lat"], elem["center"]["lon"]
                    elif elem.get("type") == "node":
                        t_lat, t_lon = elem["lat"], elem["lon"]
                    else:
                        continue

                    tags = elem.get("tags", {}) or {}
                    name = tags.get("name", "無名稱")
                    address = tags.get("addr:full", "") or tags.get("addr:street", "") or ""
                    floor_hint = _floor_from_tags(tags) or _floor_from_name(name)

                    # ✅ 新增：把 OSM 的欄位帶進物件
                    level_val   = tags.get("level") or tags.get("addr:floor") or ""
                    open_hours  = tags.get("opening_hours") or ""
                    entranceval = tags.get("entrance") or ""

                    toilets.append({
                        "name": name,
                        "lat": float(norm_coord(t_lat)),
                        "lon": float(norm_coord(t_lon)),
                        "address": address,
                        "distance": haversine(lat, lon, t_lat, t_lon),
                        "type": "osm",
                        "floor_hint": floor_hint,

                        # 新增欄位，供 Flex 顯示
                        "level": level_val,
                        "open_hours": open_hours,
                        "entrance_hint": entranceval,
                    })

                # 只有在拿到資料時才做 enrich（避免多餘請求）
                try:
                    nearby_named = enrich_nearby_places(lat, lon, radius=500)
                    if nearby_named:
                        for t in toilets:
                            if (not t.get("name")) or t["name"] == "無名稱":
                                best = None; best_d = 61
                                for p in nearby_named:
                                    d = haversine(t["lat"], t["lon"], p["lat"], p["lon"])
                                    if d < best_d:
                                        best_d = d; best = p
                                if best:
                                    t["place_hint"] = best["name"]
                except Exception:
                    pass

                return sorted(toilets, key=lambda x: x["distance"])
            except Exception as e:
                last_err = e
                logging.warning(f"Overpass API 查詢失敗（endpoint {idx}）: {e}")
        logging.warning(f"Overpass 半徑 {r} 失敗：{last_err}")
    return []

# === 讀取 public_toilets.csv ===
def query_public_csv_toilets(user_lat, user_lon, radius=500):
    pts = []
    if not os.path.exists(TOILETS_FILE_PATH):
        return pts
    try:
        with open(TOILETS_FILE_PATH, "r", encoding="utf-8-sig", newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                try:
                    t_lat = float(row.get("latitude"))
                    t_lon = float(row.get("longitude"))
                except Exception:
                    continue
                dist = haversine(user_lat, user_lon, t_lat, t_lon)
                if dist <= radius:
                    name = (row.get("name") or "無名稱").strip()
                    addr = (row.get("address") or "").strip()
                    floor_hint = _floor_from_name(name)
                    pts.append({
                        "name": name,
                        "lat": float(norm_coord(t_lat)),
                        "lon": float(norm_coord(t_lon)),
                        "address": addr,
                        "distance": dist,
                        "type": "public_csv",
                        "grade": row.get("grade", ""),
                        "category": row.get("type2", ""),
                        "floor_hint": floor_hint
                    })
    except Exception as e:
        logging.error(f"讀 public_toilets.csv 失敗：{e}")
    return sorted(pts, key=lambda x: x["distance"])

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
def add_to_favorites(uid, toilet):
    try:
        lat_s = norm_coord(toilet['lat'])
        lon_s = norm_coord(toilet['lon'])
        with open(FAVORITES_FILE_PATH, "a", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow([uid, toilet['name'], lat_s, lon_s, toilet.get('address','')])
    except Exception as e:
        logging.error(f"加入最愛失敗: {e}")

def remove_from_favorites(uid, name, lat, lon):
    try:
        lat_s = norm_coord(lat)
        lon_s = norm_coord(lon)
        rows = []
        changed = False
        with open(FAVORITES_FILE_PATH, "r", encoding="utf-8", newline="") as f:
            reader = csv.reader(f)
            for row in reader:
                if len(row) < 5:
                    rows.append(row); continue
                if not (row[0] == uid and row[1] == name and row[2] == lat_s and row[3] == lon_s):
                    rows.append(row)
                else:
                    changed = True
        with open(FAVORITES_FILE_PATH, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerows(rows)
        return changed
    except Exception as e:
        logging.error(f"移除最愛失敗: {e}")
        return False

def get_user_favorites(uid):
    favs = []
    try:
        with open(FAVORITES_FILE_PATH, "r", encoding="utf-8", newline="") as f:
            reader = csv.reader(f)
            for row in reader:
                if len(row) < 5:
                    continue
                if row[0] == uid:
                    favs.append({
                        "name": row[1],
                        "lat": float(row[2]),
                        "lon": float(row[3]),
                        "address": row[4],
                        "distance": 0,
                        "type": "favorite"
                    })
    except Exception as e:
        logging.error(f"讀取最愛失敗: {e}")
    return favs

# === 地址轉經緯度 ===
def geocode_address(address):
    try:
        ua_email = os.getenv("CONTACT_EMAIL", "you@example.com")
        url = f"https://nominatim.openstreetmap.org/search?format=json&q={quote(address)}"
        headers = {"User-Agent": f"ToiletBot/1.0 (+{ua_email})"}
        resp = requests.get(url, headers=headers, timeout=10)
        data = resp.json()
        if resp.status_code == 200 and data:
            return float(data[0]['lat']), float(data[0]['lon'])
    except Exception as e:
        logging.error(f"地址轉經緯度失敗: {e}")
    return None, None

# === 附近廁所 API ===
@app.route("/nearby_toilets", methods=["GET"])
def nearby_toilets():
    user_lat = request.args.get('lat')
    user_lon = request.args.get('lon')
    if not user_lat or not user_lon:
        return {"error": "缺少位置參數"}, 400

    user_lat = float(user_lat)
    user_lon = float(user_lon)

    public_csv_toilets = query_public_csv_toilets(user_lat, user_lon, radius=500) or []
    sheet_toilets = query_sheet_toilets(user_lat, user_lon, radius=500) or []
    osm_toilets = query_overpass_toilets(user_lat, user_lon, radius=500) or []

    all_toilets = _merge_and_dedupe_lists(public_csv_toilets, sheet_toilets, osm_toilets)
    sort_toilets(all_toilets)

    if not all_toilets:
        return {"message": "附近找不到廁所"}, 404
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
    try:
        rows = feedback_sheet.get_all_values()
        if not rows or len(rows) < 2:
            return None

        header = rows[0]
        idx = _feedback_indices(header)
        data = rows[1:]

        if idx["lat"] is None or idx["lon"] is None:
            return None

        def close(a, b):
            try:
                return abs(float(a) - float(b)) <= tol
            except:
                return False

        same = [r for r in data
                if len(r) > max(idx["lat"], idx["lon"])
                and close(r[idx["lat"]], lat) and close(r[idx["lon"]], lon)]
        if not same:
            return None

        if idx["created"] is not None:
            same.sort(key=lambda x: x[idx["created"]], reverse=True)
        recent = same[:k]

        vals = []
        for r in recent:
            sc, rr, pp, aa = _pred_from_row(r, idx)
            if isinstance(sc, (int, float)):
                vals.append(float(sc))
        if not vals:
            return None

        if len(vals) >= 2 and (max(vals) - min(vals) < 1e-6):
            vals = []
            for r in recent:
                sc, rr, pp, aa = _pred_from_row(r, idx)
                sc2 = _simple_score(rr, pp, aa)
                if sc2 is not None:
                    vals.append(sc2)
            if not vals:
                return None

        mean = round(sum(vals) / len(vals), 2)
        if len(vals) == 1:
            return {"mean": mean, "lower": mean, "upper": mean, "n": 1}

        try:
            s = statistics.stdev(vals)
        except statistics.StatisticsError:
            s = 0.0
        se = s / (len(vals) ** 0.5)
        lower = max(1.0, round(mean - 1.96 * se, 2))
        upper = min(5.0, round(mean + 1.96 * se, 2))
        return {"mean": mean, "lower": lower, "upper": upper, "n": len(vals)}
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
        return {"ok": False, "message": "參數錯誤"}, 400

    # 白名單檢查，避免髒資料
    allowed = {"有人排隊", "缺衛生紙", "暫停使用", "恢復正常"}
    if status_text not in allowed:
        return {"ok": False, "message": "不支援的狀態"}, 400

    try:
        ok = submit_status_update(lat, lon, status_text, user_id, display_name, note)
        return ({"ok": True}, 200) if ok else ({"ok": False, "message": "寫入失敗"}, 500)
    except Exception as e:
        logging.error(f"/api/status_report 寫入失敗: {e}")
        return {"ok": False, "message": "server error"}, 500

# === 回饋 ===
@app.route("/submit_feedback", methods=["POST"])
def submit_feedback():
    _ensure_sheets_ready()
    try:
        data = request.form
        name = (data.get("name","") or "").strip()
        address = (data.get("address","") or "").strip()

        lat_raw = data.get("lat","")
        lon_raw = data.get("lon","")
        lat_f, lon_f = _parse_lat_lon(lat_raw, lon_raw)
        if lat_f is None or lon_f is None:
            return "座標格式錯誤", 400
        lat = norm_coord(lat_f)
        lon = norm_coord(lon_f)

        rating = (data.get("rating","") or "").strip()
        toilet_paper = (data.get("toilet_paper","") or "").strip()
        accessibility = (data.get("accessibility","") or "").strip()
        time_of_use = (data.get("time_of_use","") or "").strip()
        comment = (data.get("comment","") or "").strip()
        floor_hint = (data.get("floor_hint","") or "").strip()

        if not all([name, rating, lat, lon]):
            return "缺少必要欄位（需要：name、rating、lat、lon）", 400

        try:
            r = int(rating)
            if r < 1 or r > 10:
                return "清潔度評分必須在 1 到 10 之間", 400
        except ValueError:
            return "清潔度評分必須是數字", 400

        if floor_hint and len(floor_hint) < 4:
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
        ])

        return redirect(url_for("feedback_form", toilet_name=name, address=address or "") + f"?lat={lat}&lon={lon}")
    except Exception as e:
        logging.error(f"❌ 提交回饋表單錯誤: {e}")
        return "提交失敗", 500

# === 讀座標的回饋清單 ===
def get_feedbacks_by_coord(lat, lon, tol=1e-6):
    _ensure_sheets_ready()
    if feedback_sheet is None:
        return []
    try:
        rows = feedback_sheet.get_all_values()
        if not rows or len(rows) < 2:
            return []
        header = rows[0]
        idx = _feedback_indices(header)
        data = rows[1:]

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
                    "comment": val("comment"),
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
        rows = feedback_sheet.get_all_values()
        if not rows or len(rows) < 2:
            return "尚無回饋資料"

        header = rows[0]
        idx = _feedback_indices(header)
        data = rows[1:]

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
            summary += f"💬 最新留言：{comments[-1]}"
        return summary
    except Exception as e:
        logging.error(f"❌ 查詢回饋統計（座標）錯誤: {e}")
        return "讀取錯誤"

# === 指示燈索引 ===
_feedback_index_cache = {"ts": 0, "data": {}}
_FEEDBACK_INDEX_TTL = 60

def build_feedback_index():
    _ensure_sheets_ready()
    if feedback_sheet is None:
        return {} 
    global _feedback_index_cache
    now = time.time()
    if now - _feedback_index_cache["ts"] < _FEEDBACK_INDEX_TTL and _feedback_index_cache["data"]:
        return _feedback_index_cache["data"]

    result = {}
    try:
        rows = feedback_sheet.get_all_values()
        if not rows or len(rows) < 2:
            _feedback_index_cache = {"ts": now, "data": {}}
            return result
        header = rows[0]; data = rows[1:]
        idx = _feedback_indices(header)

        bucket = {}
        for r in data:
            try:
                if idx["lat"] is None or idx["lon"] is None:
                    continue
                lat_s = norm_coord(r[idx["lat"]])
                lon_s = norm_coord(r[idx["lon"]])
            except Exception:
                continue
            rec = bucket.setdefault((lat_s, lon_s), {"paper": {"有":0,"沒有":0}, "access":{"有":0,"沒有":0}, "scores":[]})
            sc, rr, pp, aa = _pred_from_row(r, idx)
            if pp in rec["paper"]: rec["paper"][pp] += 1
            if aa in rec["access"]: rec["access"][aa] += 1
            if isinstance(sc, (int, float)): rec["scores"].append(float(sc))

        out = {}
        for key, v in bucket.items():
            paper = "有" if v["paper"]["有"] >= v["paper"]["沒有"] and sum(v["paper"].values())>0 else ("沒有" if sum(v["paper"].values())>0 else "?")
            access = "有" if v["access"]["有"] >= v["access"]["沒有"] and sum(v["access"].values())>0 else ("沒有" if sum(v["access"].values())>0 else "?")
            avg = round(sum(v["scores"])/len(v["scores"]),2) if v["scores"] else None
            out[key] = {"paper": paper, "access": access, "avg": avg}

        _feedback_index_cache = {"ts": now, "data": out}
        return out
    except Exception as e:
        logging.warning(f"建立指示燈索引失敗：{e}")
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
    """回傳 {(lat_s,lon_s): {'status': '有人排隊', 'ts': '...'}}，只保留最近一筆且在有效期內"""
    _ensure_sheets_ready()
    if status_ws is None:
        return {}

    now = time.time()
    if now - _status_index_cache["ts"] < _STATUS_INDEX_TTL and _status_index_cache["data"]:
        return _status_index_cache["data"]

    out = {}
    try:
        rows = status_ws.get_all_values()
        if not rows or len(rows) < 2:
            _status_index_cache.update(ts=now, data={})
            return {}
        header = rows[0]; data = rows[1:]
        idx = {h:i for i,h in enumerate(header)}
        i_lat = idx.get("lat"); i_lon = idx.get("lon")
        i_status = idx.get("status"); i_ts = idx.get("timestamp")
        if None in (i_lat, i_lon, i_status):
            _status_index_cache.update(ts=now, data={})
            return {}

        def fresh(ts_s):
            if not ts_s: return False
            try:
                dt = datetime.strptime(ts_s, "%Y-%m-%d %H:%M:%S")
                return (datetime.utcnow() - dt).total_seconds() <= _STATUS_TTL_HOURS*3600
            except:
                return False

        merged = []
        for r in data:
            if max(i_lat, i_lon, i_status) >= len(r): continue
            lat_s, lon_s = norm_coord(r[i_lat]), norm_coord(r[i_lon])
            st = (r[i_status] or "").strip()
            ts = (r[i_ts] if i_ts is not None and len(r) > i_ts else "")
            if not fresh(ts):
                continue

            placed = False
            for m in merged:
                if _is_close_m(lat_s, lon_s, m["lat"], m["lon"]):
                    if ts > m["ts"]:
                        m.update(lat=lat_s, lon=lon_s, status=st, ts=ts)
                    placed = True
                    break
            if not placed:
                merged.append({"lat": lat_s, "lon": lon_s, "status": st, "ts": ts})

        for m in merged:
            out[(m["lat"], m["lon"])] = {"status": m["status"], "ts": m["ts"]}

        _status_index_cache.update(ts=now, data=out)
        return out
    except Exception as e:
        logging.warning(f"建立狀態索引失敗：{e}")
        return {}

# === 舊路由保留===
@app.route("/toilet_feedback/<toilet_name>")
def toilet_feedback(toilet_name):
    _ensure_sheets_ready()
    if worksheet is None or feedback_sheet is None:
        return render_template("toilet_feedback.html", toilet_name=toilet_name,
                               summary="（暫時無法連到雲端資料）",
                               feedbacks=[], address="", avg_pred_score="未預測", lat="", lon="")
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
                                   feedbacks=[], address="", avg_pred_score="未預測", lat="", lon="")

        rows_fb = feedback_sheet.get_all_values()
        header = rows_fb[0]; data_fb = rows_fb[1:]
        idx = _feedback_indices(header)
        if idx["address"] is None:
            return render_template("toilet_feedback.html", toilet_name=toilet_name,
                                   summary="（表頭缺少『地址』欄位）", feedbacks=[], address=address,
                                   avg_pred_score="未預測", lat="", lon="")

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
                "comment": val("comment"),
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
                               avg_pred_score=avg_pred_score, lat="", lon="")
    except Exception as e:
        logging.error(f"❌ 渲染回饋頁面錯誤: {e}")
        return "查詢失敗", 500

# === 新路由 ===
@app.route("/toilet_feedback_by_coord/<lat>/<lon>")
def toilet_feedback_by_coord(lat, lon):
    _ensure_sheets_ready()
    if feedback_sheet is None:
        return render_template("toilet_feedback.html",
                               toilet_name=f"廁所（{lat}, {lon}）",
                               summary="（暫時無法連到雲端資料）",
                               feedbacks=[], address=f"{lat},{lon}",
                               avg_pred_score="未預測", lat=lat, lon=lon)
    try:
        name = f"廁所（{lat}, {lon}）"
        summary = get_feedback_summary_by_coord(lat, lon)
        feedbacks = get_feedbacks_by_coord(lat, lon)

        rows = feedback_sheet.get_all_values()
        header = rows[0]; data = rows[1:]
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
            lon=lon
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
        rows = feedback_sheet.get_all_values()
        if not rows or len(rows) < 2:
            return {"success": True, "data": []}, 200

        header = rows[0]
        idx = _feedback_indices(header)
        data = rows[1:]

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
        rows = feedback_sheet.get_all_values()
        if not rows or len(rows) < 2:
            return {"success": True, "data": []}, 200

        header = rows[0]
        idx = _feedback_indices(header)
        data = rows[1:]

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

# === 同意頁面 / 隱私頁 ===
@app.route("/consent", methods=["GET"])
def render_consent_page():
    return render_template("consent.html")

@app.route("/privacy", methods=["GET"])
def render_privacy_page():
    return render_template("privacy_policy.html")

# 狀態 LIFF 頁面
@app.route("/status_liff")
def status_liff_page():
    liff_id = os.getenv("LIFF_ID_STATUS", "")
    return render_template("status_liff.html", liff_id=liff_id)

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
def create_toilet_flex_messages(toilets, show_delete=False, uid=None):
    indicators = build_feedback_index()
    status_map = build_status_index()
    bubbles = []
    for toilet in toilets[:5]:
        actions = []

        lat_s = norm_coord(toilet['lat'])
        lon_s = norm_coord(toilet['lon'])
        addr_text = toilet.get('address') or "（無地址，使用座標）"

        title = toilet.get('name') or ""
        if (not title) or title == "無名稱":
            ph = toilet.get("place_hint")
            title = f"{ph}（附近）廁所" if ph else "（未命名）廁所"

        # 只讀三個欄位（可能為空）
        lvl   = (toilet.get("level") or "").strip()
        pos   = (toilet.get("floor_hint") or "").strip()
        hours = (toilet.get("open_hours") or "").strip()

        # 額外顯示行（避免重覆；自動截斷需有 _short_txt）
        extra_lines = []
        st_obj = status_map.get((lat_s, lon_s))
        if st_obj and st_obj.get("status"):
            st = st_obj["status"]
            emoji = "🟡" if st == "有人排隊" else ("🧻" if st == "缺衛生紙" else ("⛔" if st == "暫停使用" else "✅"))
            extra_lines.append({
                "type": "text",
                "text": _short_txt(f"{emoji} 狀態：{st}"),
                "size": "sm", "color": "#666666", "wrap": True
            })

        if lvl or pos:
            # 兩者都有且不同 → 顯示「樓層」與「位置」兩行；否則合併成一行
            if lvl and pos and (lvl.strip().lower() != pos.strip().lower()):
                extra_lines.append({
                    "type": "text",
                    "text": _short_txt(f"🏷 樓層：{lvl}"),
                    "size": "sm", "color": "#666666", "wrap": True
                })
                extra_lines.append({
                    "type": "text",
                    "text": _short_txt(f"🧭 位置：{pos}"),
                    "size": "sm", "color": "#666666", "wrap": True
                })
            else:
                val = pos or lvl
                extra_lines.append({
                    "type": "text",
                    "text": _short_txt(f"🧭 位置/樓層：{val}"),
                    "size": "sm", "color": "#666666", "wrap": True
                })
        if hours:
            extra_lines.append({
                "type": "text",
                "text": _short_txt(f"🕒 開放：{hours}"),
                "size": "sm", "color": "#666666", "wrap": True
            })

        # 指示燈文字
        ind = indicators.get((lat_s, lon_s), {"paper": "?", "access": "?", "avg": None})
        star_text = f"⭐{ind['avg']}" if ind.get("avg") is not None else "⭐—"
        paper_text = "🧻有" if ind.get("paper") == "有" else ("🧻無" if ind.get("paper") == "沒有" else "🧻—")
        access_text = "♿有" if ind.get("access") == "有" else ("♿無" if ind.get("access") == "沒有" else "♿—")

        # 按鈕
        actions.append({
            "type": "uri",
            "label": "導航",
            "uri": f"https://www.google.com/maps/search/?api=1&query={lat_s},{lon_s}"
        })
        actions.append({
            "type": "uri",
            "label": "查詢回饋",
            "uri": f"https://school-i9co.onrender.com/toilet_feedback_by_coord/{lat_s}/{lon_s}"
        })
        addr_raw = toilet.get('address') or ""
        addr_param = quote(addr_raw or "-")
        actions.append({
            "type": "uri",
            "label": "廁所回饋",
            "uri": (
                "https://school-i9co.onrender.com/feedback_form/"
                f"{quote(title)}/{addr_param}"
                f"?lat={lat_s}&lon={lon_s}&address={quote(addr_raw)}"
            )
        })

        if toilet.get("type") == "favorite" and uid:
            actions.append({
                "type": "postback",
                "label": "移除最愛",
                "data": f"remove_fav:{quote(title)}:{lat_s}:{lon_s}"
            })
        elif toilet.get("type") not in ["user", "favorite"] and uid:
            actions.append({
                "type": "postback",
                "label": "加入最愛",
                "data": f"add:{quote(title)}:{lat_s}:{lon_s}"
            })

        # 主體內容：原本前三行 + extra_lines + 距離
        body_contents = [
            {"type": "text", "text": title, "weight": "bold", "size": "lg", "wrap": True},
            {"type": "text", "text": f"{paper_text}  {access_text}  {star_text}", "size": "sm", "color": "#555555", "wrap": True},
            {"type": "text", "text": addr_text, "size": "sm", "color": "#666666", "wrap": True},
        ] + extra_lines + [
            {"type": "text", "text": f"{int(toilet.get('distance', 0))} 公尺", "size": "sm", "color": "#999999"}
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
        lat_s = norm_coord(it["lat"]); lon_s = norm_coord(it["lon"])
        addr_raw = it.get('address','') or ""
        addr_param = quote(addr_raw or "-")
        actions = [
            {"type":"uri","label":"導航","uri":f"https://www.google.com/maps/search/?api=1&query={lat_s},{lon_s}"},
            {"type":"uri","label":"查詢回饋（座標）","uri":f"https://school-i9co.onrender.com/toilet_feedback_by_coord/{lat_s}/{lon_s}"},
            {"type":"uri","label":"廁所回饋",
             "uri":(
                f"https://school-i9co.onrender.com/feedback_form/{quote(it['name'])}/{addr_param}"
                f"?lat={lat_s}&lon={lon_s}&address={quote(addr_raw)}"
             )},
            {"type":"postback","label":"刪除此貢獻","data":f"confirm_delete_my_toilet:{it['row_index']}"}
        ]
        bubble = {
            "type":"bubble",
            "body":{
                "type":"box","layout":"vertical","contents":[
                    {"type":"text","text":it["name"],"size":"lg","weight":"bold","wrap":True},
                    {"type":"text","text":it.get("address") or "（無地址）","size":"sm","color":"#666666","wrap":True},
                    {"type":"text","text":it['created'], "size":"xs","color":"#999999"}
                ]
            },
            "footer":{
                "type":"box","layout":"vertical","spacing":"sm",
                "contents":[{"type":"button","style":"primary","height":"sm","action":actions[0]}] + [
                    {"type":"button","style":"secondary","height":"sm","action":a} for a in actions[1:]
                ]
            }
        }
        bubbles.append(bubble)
    return {"type":"carousel","contents":bubbles}

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

# 建議：高併發時避免競態
_dict_lock = threading.Lock()
def set_user_location(uid, latlon):
    with _dict_lock:
        user_locations[uid] = latlon

def get_user_location(uid):
    with _dict_lock:
        return user_locations.get(uid)

def _status_liff_url(lat, lon):
    try:
        host = request.host
    except Exception:
        host = os.getenv("PUBLIC_URL","").replace("https://","").replace("http://","").strip("/")
    la, lo = norm_coord(lat), norm_coord(lon)
    return f"https://{host}/status_liff?lat={la}&lon={lo}"

# === 共用執行緒池（避免每次臨時建立） ===
_pool = ThreadPoolExecutor(max_workers=2)

def build_nearby_toilets(uid, lat, lon, radius=500):
    futures = []
    csv_res, sheet_res, osm_res = [], [], []

    try:
        futures.append(("csv",  _pool.submit(query_public_csv_toilets, lat, lon, radius)))
        futures.append(("sheet", _pool.submit(query_sheet_toilets,      lat, lon, radius)))
        futures.append(("osm",  _pool.submit(query_overpass_toilets,    lat, lon, radius)))

        for name, fut in futures:
            try:
                res = fut.result(timeout=LOC_QUERY_TIMEOUT_SEC)
                if   name == "csv":  csv_res  = res or []
                elif name == "sheet": sheet_res = res or []
                else:                 osm_res  = res or []
            except FuturesTimeoutError:
                logging.warning(f"{name} 查詢逾時")
            except Exception as e:
                logging.warning(f"{name} 查詢失敗: {e}")
    finally:
        for _, fut in futures:
            if not fut.done():
                fut.cancel()

    quick = _merge_and_dedupe_lists(csv_res, sheet_res, osm_res)
    sort_toilets(quick)
    return quick[:LOC_MAX_RESULTS]

# === TextMessage ===
@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    if _too_old_to_reply(event):
        logging.warning("[handle_text] event too old; skip reply.")
        return
    uid = event.source.user_id
    text_raw = event.message.text or ""
    text = text_raw.strip().lower()

    if is_duplicate_and_mark(f"text|{uid}|{text}"):
        return

    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg)
        return

    reply_messages = []

    if uid in pending_delete_confirm:
        info = pending_delete_confirm[uid]
        if text == "確認刪除":
            if info.get("mode") == "sheet_row":
                _ensure_sheets_ready()
                ok = False
                try:
                    worksheet.delete_rows(int(info["row"]))
                    ok = True
                except Exception as e:
                    logging.error(f"刪主資料列失敗：{e}")
                msg = "✅ 已刪除你的貢獻" if ok else "❌ 刪除失敗"
            else:
                success = remove_from_favorites(uid, info["name"], info["lat"], info["lon"])
                msg = "✅ 已刪除該廁所" if success else "❌ 移除失敗"
            del pending_delete_confirm[uid]
            reply_messages.append(TextSendMessage(text=msg))
        elif text == "取消":
            del pending_delete_confirm[uid]
            reply_messages.append(TextSendMessage(text="❌ 已取消刪除"))
        else:
            reply_messages.append(TextSendMessage(text="⚠️ 請輸入『確認刪除』或『取消』"))

    elif text == "附近廁所":
        try:
            safe_reply(event, make_location_quick_reply("📍 請點下方『發送我的位置』，我會幫你找最近的廁所"))
        except Exception as e:
            logging.error(f"附近廁所 quick reply 失敗: {e}")
            safe_reply(event, TextSendMessage(text="❌ 系統錯誤，請稍後再試"))
        return  # 確保這個事件處理完畢，不會往下執行其他回覆

    elif text == "我的最愛":
        favs = get_user_favorites(uid)
        if not favs:
            reply_messages.append(TextSendMessage(text="你尚未收藏任何廁所"))
        else:
            loc = get_user_location(uid)
            if loc:
                lat, lon = loc
                for f in favs:
                    f["distance"] = haversine(lat, lon, f["lat"], f["lon"])
            msg = create_toilet_flex_messages(favs, show_delete=True, uid=uid)
            reply_messages.append(FlexSendMessage("我的最愛", msg))

    elif text == "我的貢獻":
        msg = create_my_contrib_flex(uid)
        if msg:
            reply_messages.append(FlexSendMessage("我新增的廁所", msg))
        else:
            reply_messages.append(TextSendMessage(text="你還沒有新增過廁所喔。"))

    elif text == "新增廁所":
        base = "https://school-i9co.onrender.com/add"
        loc = get_user_location(uid)
        if loc:
            la, lo = loc
            url = f"{base}?uid={quote(uid)}&lat={la}&lon={lo}#openExternalBrowser=1"
        else:
            url = f"{base}?uid={quote(uid)}#openExternalBrowser=1"
        reply_messages.append(TextSendMessage(text=f"請前往此頁新增廁所：\n{url}"))

    elif text == "意見回饋":
        form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
        reply_messages.append(TextSendMessage(text=f"💡 請透過下列連結回報問題或提供意見：\n{form_url}"))

    elif text == "合作信箱":
        email = os.getenv("FEEDBACK_EMAIL", "hello@example.com")
        ig_url = "https://www.instagram.com/toiletmvp?igsh=MWRvMnV2MTNyN2RkMw=="
        reply_messages.append(TextSendMessage(
            text=f"📬 合作信箱：{email}\n\n 📸 官方IG: {ig_url}"
        ))
    elif text == "狀態":
        loc = get_user_location(uid)
        if not loc:
            safe_reply(event, make_location_quick_reply("📍 請先傳送你的位置，我會開啟回報頁面"))
        else:
            la, lo = loc
            url = f"https://{request.host}/status_liff?lat={norm_coord(la)}&lon={norm_coord(lo)}#openExternalBrowser=1"
            safe_reply(event, TextSendMessage(text=f"請點此回報附近廁所狀態：\n{url}"))
   
    
    if reply_messages:
        safe_reply(event, reply_messages)
# === LocationMessage ===
@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
    if _too_old_to_reply(event):
        logging.warning("[handle_location] event too old; skip reply.")
        return
    uid = event.source.user_id
    lat = event.message.latitude
    lon = event.message.longitude

    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg)
        return

    key = f"loc|{uid}|{round(lat,5)},{round(lon,5)}"
    if is_duplicate_and_mark(key):
        return

    set_user_location(uid, (lat, lon))

    # === 併發閥門（原本就有）
    if not _try_acquire_loc_slot():
        safe_reply(event, make_retry_location_text())
        return

    try:
        toilets = build_nearby_toilets(uid, lat, lon)

        if toilets:
            msg = create_toilet_flex_messages(toilets, show_delete=False, uid=uid)
            # 一次 reply 多則 OK，但避免先送「搜尋中」
            safe_reply(event, [
                FlexSendMessage("附近廁所", msg),
                make_location_quick_reply("想換個地點再找嗎？")
            ])
        try:
            url = _status_liff_url(lat, lon)
            safe_reply(event, TextSendMessage(text=f"⚡ 也可以直接回報狀態：\n{url}"))
        except Exception:
            pass

        else:
            # ✅ 沒有結果 → 顯示「傳送我的位置」＋「新增廁所」兩顆泡泡
            safe_reply(event, make_no_toilet_quick_reply(
                uid, lat, lon,
                text="附近沒有廁所 😥 要不要補上一間，或換個點再試？"
            ))

    except Exception as e:
        logging.error(f"nearby error: {e}", exc_info=True)
        safe_reply(event, TextSendMessage(text="系統忙線中，請稍後再試 🙏"))
    finally:
        _release_loc_slot()

# === Postback ===
@handler.add(PostbackEvent)
def handle_postback(event):
    uid = event.source.user_id
    data = event.postback.data or ""

    if is_duplicate_and_mark(f"pb|{uid}|{data}"):
        return

    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg); return

    try:
        if data == "ask_location":
            safe_reply(event, make_location_quick_reply("📍 請點『傳送我的位置』，我立刻幫你找廁所"))
            return
        
        if data.startswith("add:"):
            _, qname, lat, lon = data.split(":", 3)
            name = unquote(qname)
            toilet = {
                "name": name,
                "lat": float(lat),
                "lon": float(lon),
                "address": f"{lat},{lon}",
                "distance": 0,
                "type": "sheet"
            }
            add_to_favorites(uid, toilet)
            safe_reply(event, TextSendMessage(text=f"✅ 已收藏 {name}"))

        elif data.startswith("remove_fav:"):
            _, qname, lat, lon = data.split(":", 3)
            name = unquote(qname)
            success = remove_from_favorites(uid, name, lat, lon)
            msg = "✅ 已移除最愛" if success else "❌ 移除失敗"
            safe_reply(event, TextSendMessage(text=msg))

        elif data.startswith("confirm_delete:"):
            _, qname, qaddr, lat, lon = data.split(":", 4)
            name = unquote(qname)
            pending_delete_confirm[uid] = {
                "mode": "favorite",
                "name": name,
                "lat": norm_coord(lat),
                "lon": norm_coord(lon)
            }
            safe_reply(event, [
                TextSendMessage(text=f"⚠️ 確定要刪除 {name} 嗎？（目前刪除為移除最愛）"),
                TextSendMessage(text="請輸入『確認刪除』或『取消』")
            ])

        elif data.startswith("confirm_delete_my_toilet:"):
            _, row_str = data.split(":", 1)
            pending_delete_confirm[uid] = {
                "mode": "sheet_row",
                "row": int(row_str)
            }
            safe_reply(event, [
                TextSendMessage(text="⚠️ 確定要刪除此『你新增的廁所』嗎？此動作會從主資料表刪除該列。"),
                TextSendMessage(text="請輸入『確認刪除』或『取消』")
            ])

    except Exception as e:
        logging.error(f"❌ 處理 postback 失敗: {e}")

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

# === 使用者新增廁所 API ===
@app.route("/submit_toilet", methods=["POST"])
def submit_toilet():
    _ensure_sheets_ready()                    # ← 新增
    if worksheet is None:                    # ← 新增
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

        if not name or not addr:
            return {"success": False, "message": "請提供『廁所名稱』與『地址』"}, 400

        if floor_hint and len(floor_hint) < 4:
            return {"success": False, "message": "『位置描述』太短，請至少 4 個字"}, 400

        if not floor_hint:
            inferred = _floor_from_name(name)
            if inferred:
                floor_hint = inferred

        lat_f, lon_f = (None, None)
        if lat_in and lon_in:
            lat_f, lon_f = _parse_lat_lon(lat_in, lon_in)

        if lat_f is None or lon_f is None:
            lat_f, lon_f = geocode_address(addr)

        if lat_f is None or lon_f is None:
            return {"success": False, "message": "地址轉換失敗，請修正地址或提供座標"}, 400

        lat_s, lon_s = norm_coord(lat_f), norm_coord(lon_f)

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

        worksheet.append_row(row_values, value_input_option="USER_ENTERED")
        logging.info(f"✅ 廁所資料已寫入 Google Sheets: {name}")

        try:
            if not os.path.exists(TOILETS_FILE_PATH):
                with open(TOILETS_FILE_PATH, "w", encoding="utf-8", newline="") as f:
                    writer = csv.writer(f)
                    writer.writerow(PUBLIC_HEADERS)
            with open(TOILETS_FILE_PATH, "a", encoding="utf-8", newline="") as f:
                writer = csv.writer(f)
                writer.writerow([
                    "00000","0000000","未知里","USERADD", name, addr, "使用者補充",
                    lat_s, lon_s,
                    "普通級","公共場所","未知","使用者","0"
                ])
        except Exception as e:
            logging.warning(f"備份至本地 CSV 失敗：{e}")

        return {"success": True, "message": f"✅ 已新增廁所 {name}"}
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