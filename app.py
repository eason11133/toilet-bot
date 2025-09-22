import os
import csv
import json
import logging
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
    FlexSendMessage, PostbackEvent, TextSendMessage
)
import gspread
from oauth2client.service_account import ServiceAccountCredentials
from datetime import datetime
import joblib
import threading
import time
import statistics
from difflib import SequenceMatcher
from collections import defaultdict
import random
import re
from queue import Queue, Empty, Full

load_dotenv()
try:
    import pandas as pd
except Exception:
    pd = None

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

def _with_retry(func, *args, **kwargs):
    backoff = 0.7
    for i in range(SHEETS_RETRY_MAX):
        try:
            with _sheets_sem:
                return func(*args, **kwargs)
        except Exception as e:
            if _is_quota_or_retryable(e):
                sleep_s = backoff * (2 ** i) + random.uniform(0, 0.25*i)
                time.sleep(sleep_s)
                continue
            raise
    raise

class SafeWS:
    """包裝 gspread worksheet：讀取加 TTL 快取；所有操作加退避與併發閥。"""
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
# ====================== /Sheets 安全外掛層 ======================

# === Fast-ACK 佇列與工人 ===
TASK_Q = Queue(maxsize=int(os.getenv("TASK_QUEUE_SIZE", "5000")))
BOT_WORKERS = int(os.getenv("BOT_WORKERS", "8"))

def _worker_loop():
    while True:
        try:
            job = TASK_Q.get(timeout=0.2)
        except Empty:
            continue
        try:
            job()  # 任務內會用 push_message 回覆
        except Exception as e:
            logging.error(f"[worker] error: {e}", exc_info=True)
        finally:
            TASK_Q.task_done()

for _ in range(BOT_WORKERS):
    threading.Thread(target=_worker_loop, daemon=True).start()

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

logging.getLogger("werkzeug").addFilter(_NoHealthzFilter())

@app.route("/statusz", methods=["GET"])
def statusz():
    payload = {
        "mode": guard.mode,
        "suspended_until": guard.suspended_until,
        "monthly_limit": guard.monthly_limit,
        "monthly_used": guard.monthly_used,
    }
    return Response(json.dumps(payload, ensure_ascii=False),
                    status=200,
                    headers={"Content-Type":"application/json; charset=utf-8","Cache-Control":"no-store"})

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

# === 永久版：MessagingGuard（配額/降級/上限 一次搞定） ===
LINE_LIMIT_COOLDOWN_SEC = int(os.getenv("LINE_LIMIT_COOLDOWN_SEC", str(7*24*3600)))
USER_DAILY_LIMIT = int(os.getenv("USER_DAILY_LIMIT", "6"))
DEGRADE_WARN_REMAIN_PCT = float(os.getenv("DEGRADE_WARN_REMAIN_PCT", "0.15"))
USAGE_POLL_SECONDS = int(os.getenv("USAGE_POLL_SECONDS", "600"))
SEND_UPDATE_CARD = os.getenv("SEND_UPDATE_CARD", "0") == "1"  # 2 張卡改成可開關

CHANNEL_ACCESS_TOKEN = os.getenv("LINE_CHANNEL_ACCESS_TOKEN")
_session = requests.Session()

class Mode:
    NORMAL="NORMAL"
    SAVER="SAVER"
    HARD_STOP="HARD_STOP"

class MessagingGuard:
    def __init__(self):
        self.mode = Mode.NORMAL
        self.suspended_until = 0.0
        self.monthly_limit = None
        self.monthly_used = 0
        self.lock = threading.Lock()
        self.user_daily = defaultdict(lambda: {"date":"", "count":0})
        self._start_usage_poller()

    def reply(self, event, messages, fallback_text_with_url=None):
        uid = getattr(event.source, "user_id", None)
        if not self._allow_send(uid):
            self._log_skip(uid, "reply")
            if fallback_text_with_url and self.mode != Mode.HARD_STOP:
                self._safe_reply_text(event, fallback_text_with_url)
            return False
        ok = self._guard.reply(event, messages, uid)
        if ok: self._bump(uid)
        return ok

    def push(self, uid, messages, fallback_text_with_url=None):
        if not self._allow_send(uid):
            self._log_skip(uid, "push")
            if fallback_text_with_url and self.mode != Mode.HARD_STOP:
                self._safe_push_text(uid, fallback_text_with_url)
            return False
        ok = self._safe_push(uid, messages)
        if ok: self._bump(uid)
        return ok

    # ---- 判斷/統計 ----
    def _allow_send(self, uid):
        now = time.time()
        with self.lock:
            if now < self.suspended_until:
                self.mode = Mode.HARD_STOP
                return False
            if self.mode == Mode.HARD_STOP:
                return False
            if uid:
                today = datetime.utcnow().strftime("%Y-%m-%d")
                rec = self.user_daily[uid]
                if rec["date"] != today:
                    rec["date"], rec["count"] = today, 0
                if rec["count"] >= USER_DAILY_LIMIT:
                    return False
            return True  # SAVER/NORMAL 都允許，由呼叫端決定送什麼內容

    def _bump(self, uid):
        if not uid: return
        today = datetime.utcnow().strftime("%Y-%m-%d")
        rec = self.user_daily[uid]
        if rec["date"] != today:
            rec["date"], rec["count"] = today, 0
        rec["count"] += 1

    def _log_skip(self, uid, kind):
        logging.info("⏭️ guard-skip %s uid=%s mode=%s used=%s limit=%s",
                     kind, uid, self.mode, self.monthly_used, self.monthly_limit)

    # ---- 真正送訊（含 429 熔絲） ----
    def _safe_reply(self, event, messages, uid):
        try:
            line_bot_api.reply_message(event.reply_token, messages)
            return True
        except LineBotApiError as e:
            if self._is_monthly_limit(e): self._trip_fuse(); return False
            logging.warning(f"reply_message 失敗：{e}")
            return False

    def _safe_push(self, uid, messages):
        try:
            guard.push(uid, messages)
            return True
        except LineBotApiError as e:
            if self._is_monthly_limit(e): self._trip_fuse(); return False
            logging.error(f"push_message 失敗：{e}")
            return False

    def _safe_reply_text(self, event, text):
        try:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=text))
        except Exception as e:
            if self._is_monthly_limit(e): self._trip_fuse()

    def _safe_push_text(self, uid, text):
        try:
            guard.push(uid, TextSendMessage(text=text))
        except Exception as e:
            if self._is_monthly_limit(e): self._trip_fuse()

    def _is_monthly_limit(self, err):
        s = str(err).lower()
        return ("you have reached your monthly limit" in s) or ("status_code=429" in s)

    def _trip_fuse(self):
        with self.lock:
            self.suspended_until = time.time() + LINE_LIMIT_COOLDOWN_SEC
            self.mode = Mode.HARD_STOP
        logging.error("🚫 LINE monthly limit reached -> HARD_STOP for %d sec", LINE_LIMIT_COOLDOWN_SEC)

    # ---- 監控：定期抓用量並自動降級 ----
    def _poll_usage_once(self):
        if not CHANNEL_ACCESS_TOKEN: return
        headers = {"Authorization": f"Bearer {CHANNEL_ACCESS_TOKEN}"}
        try:
            r1 = _session.get("https://api.line.me/v2/bot/message/quota", headers=headers, timeout=8)
            if r1.ok:
                data = r1.json()
                if data.get("type") == "limited":
                    self.monthly_limit = int(data.get("value", 0))
                else:
                    self.monthly_limit = None
            r2 = _session.get("https://api.line.me/v2/bot/message/quota/consumption", headers=headers, timeout=8)
            if r2.ok:
                self.monthly_used = int(r2.json().get("totalUsage", 0))
            with self.lock:
                if self.monthly_limit and self.monthly_limit > 0:
                    remain = max(self.monthly_limit - self.monthly_used, 0)
                    ratio = remain / float(self.monthly_limit)
                    if ratio <= DEGRADE_WARN_REMAIN_PCT and self.mode != Mode.HARD_STOP:
                        self.mode = Mode.SAVER
                    elif ratio > (DEGRADE_WARN_REMAIN_PCT + 0.05) and time.time() >= self.suspended_until:
                        self.mode = Mode.NORMAL
                else:
                    if time.time() >= self.suspended_until and self.mode != Mode.HARD_STOP:
                        self.mode = Mode.NORMAL
        except Exception as e:
            logging.warning(f"用量輪詢失敗：{e}")

    def _start_usage_poller(self):
        def loop():
            while True:
                self._poll_usage_once()
                time.sleep(USAGE_POLL_SECONDS)
        threading.Thread(target=loop, daemon=True).start()

guard = MessagingGuard()

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
    global gc, worksheet, feedback_sheet, consent_ws
    try:
        if not GSHEET_CREDENTIALS_JSON:
            raise RuntimeError("缺少 GSHEET_CREDENTIALS_JSON")
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

        # 包裝成 SafeWS，底下所有呼叫維持原 API
        worksheet = SafeWS(worksheet_raw, TOILET_SPREADSHEET_ID, worksheet_raw.title)
        feedback_sheet = SafeWS(feedback_raw, FEEDBACK_SPREADSHEET_ID, feedback_raw.title)
        consent_ws = SafeWS(consent_raw, FEEDBACK_SPREADSHEET_ID, consent_raw.title)

        logging.info("✅ Sheets 初始化完成（含 consent；啟用 SafeWS 快取/重試/併發控管）")
    except Exception as e:
        logging.critical(f"❌ Sheets 初始化失敗: {e}")
        raise

init_gsheet()

# === 使用者新增廁所 ===
TOILET_REQUIRED_HEADER = [
    "user_id", "name", "address", "lat", "lon",
    "level", "floor_hint", "entrance_hint", "access_note", "open_hours",
    "timestamp"
]

def ensure_toilet_sheet_header(ws):
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

def safe_reply(event, messages):
    try:
        line_bot_api.reply_message(event.reply_token, messages)
    except LineBotApiError as e:
        msg_txt = ""
        try:
            msg_txt = getattr(getattr(e, "error", None), "message", "") or str(e)
        except Exception:
            msg_txt = str(e)
        if is_redelivery(event) or ("Invalid reply token" in msg_txt):
            logging.warning(f"reply_message 失敗但不 push（避免重複）：{msg_txt}")
            return
        logging.warning(f"reply_message 失敗，改用 push：{msg_txt}")
        try:
            uid = getattr(event.source, "user_id", None)
            if uid:
                guard.push(uid, messages)
        except Exception as ex:
            logging.error(f"push_message 也失敗：{ex}")

# === 同意工具 ===
def _booly(v):
    s = str(v).strip().lower()
    return s in ["1", "true", "yes", "y", "同意"]

# （可選微優化）本機同意快取，TTL 預設 10 分鐘；失敗時當未同意（不影響功能）
_consent_cache = {}   # user_id -> (ts, bool)
_CONSENT_TTL = int(os.getenv("CONSENT_TTL_SEC", "600"))

def has_consented(user_id: str) -> bool:
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
def query_sheet_toilets(user_lat, user_lon, radius=500):
    toilets = []
    try:
        rows = worksheet.get_all_values()
        data = rows[1:]
        for row in data:
            if len(row) < 5:
                continue
            name = (row[1] if len(row) > 1 else "").strip() or "無名稱"
            address = (row[2] if len(row) > 2 else "").strip()
            try:
                t_lat = float(row[3]); t_lon = float(row[4])
            except:
                continue
            dist = haversine(user_lat, user_lon, t_lat, t_lon)
            if dist <= radius:
                floor_hint = _floor_from_name(name)
                toilets.append({
                    "name": name,
                    "lat": float(norm_coord(t_lat)),
                    "lon": float(norm_coord(t_lon)),
                    "address": address,
                    "distance": dist,
                    "type": "sheet",
                    "floor_hint": floor_hint
                })
    except Exception as e:
        logging.error(f"讀取 Google Sheets 廁所主資料錯誤: {e}")
    return sorted(toilets, key=lambda x: x["distance"])

# === OSM Overpass ===
def query_overpass_toilets(lat, lon, radius=500):
    overall_deadline = time.time() + 8.0  # 最多 8 秒
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

                    toilets.append({
                        "name": name,
                        "lat": float(norm_coord(t_lat)),
                        "lon": float(norm_coord(t_lon)),
                        "address": address,
                        "distance": haversine(lat, lon, t_lat, t_lon),
                        "type": "osm",
                        "floor_hint": floor_hint
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

# === 回饋 ===
@app.route("/submit_feedback", methods=["POST"])
def submit_feedback():
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
_FEEDBACK_INDEX_TTL = 30

def build_feedback_index():
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

# === 舊路由保留===
@app.route("/toilet_feedback/<toilet_name>")
def toilet_feedback(toilet_name):
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

# === 清潔度趨勢 API ===
@app.route("/get_clean_trend_by_coord/<lat>/<lon>")
def get_clean_trend_by_coord(lat, lon):
    try:
        rows = feedback_sheet.get_all_values()
        if not rows or len(rows) < 2:
            return {"success": True, "data": []}, 200

        header = rows[0]
        idx = _feedback_indices(header)
        data = rows[1:]

        if idx["lat"] is None or idx["lon"] is None:
            return {"success": False, "data": []}, 200

        def close(a, b, tol=1e-6):
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
                recomputed.append((created, float(sc)))

        if not recomputed:
            return {"success": True, "data": []}, 200

        vals = [p for _, p in recomputed]
        if len(vals) >= 2 and (max(vals) - min(vals) < 1e-6):
            forced = []
            for r in matched_rows:
                created = r[idx["created"]] if idx["created"] is not None and len(r) > idx["created"] else ""
                _, rr, pp, aa = _pred_from_row(r, idx)
                sc2 = _simple_score(rr, pp, aa)
                if sc2 is not None:
                    forced.append((created, float(sc2)))
            if forced:
                recomputed = forced

        recomputed.sort(key=lambda t: t[0])
        out = [{"score": round(p, 2)} for _, p in recomputed]
        return {"success": True, "data": out}, 200

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

# === 建立 Flex ===
def create_toilet_flex_messages(toilets, show_delete=False, uid=None):
    indicators = build_feedback_index()
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

        floor_hint = toilet.get("floor_hint")
        floor_text = f"🧭 位置：{floor_hint}" if floor_hint else "🧭 位置：樓層未知"

        ind = indicators.get((lat_s, lon_s), {"paper":"?","access":"?","avg":None})
        star_text = f"⭐{ind['avg']}" if ind.get("avg") is not None else "⭐—"
        paper_text = "🧻有" if ind.get("paper")=="有" else ("🧻無" if ind.get("paper")=="沒有" else "🧻—")
        access_text = "♿有" if ind.get("access")=="有" else ("♿無" if ind.get("access")=="沒有" else "♿—")

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

        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {"type": "text", "text": title, "weight": "bold", "size": "lg", "wrap": True},
                    {"type": "text", "text": f"{paper_text}  {access_text}  {star_text}", "size": "sm", "color": "#555555", "wrap": True},
                    {"type": "text", "text": addr_text, "size": "sm", "color": "#666666", "wrap": True},
                    {"type": "text", "text": floor_text, "size": "sm", "color": "#666666", "wrap": True},
                    {"type": "text", "text": f"{int(toilet.get('distance',0))} 公尺", "size": "sm", "color": "#999999"}
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
    return {"type": "carousel", "contents": bubbles}

# === 列出 我的貢獻 & 刪除 ===
def get_user_contributions(uid):
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

# === 使用者位置資料 ===
user_locations = {}
pending_delete_confirm = {}

def _do_nearby_toilets_and_push(uid, lat, lon):
    # --- 降級模式直接跳過 ---
    if guard.mode in (Mode.SAVER, Mode.HARD_STOP):
        logging.info("⏭️ degrade mode=%s — skip bg push, rely on link", guard.mode)
        return

    try:
        # 先查快的來源（CSV + Sheets），幾百毫秒內可出
        quick = _merge_and_dedupe_lists(
            query_public_csv_toilets(lat, lon) or [],
            query_sheet_toilets(lat, lon) or [],
        )
        sort_toilets(quick)

        if quick:
            msg = create_toilet_flex_messages(quick, show_delete=False, uid=uid)
            guard.push(uid,
                       FlexSendMessage("附近廁所", msg),
                       fallback_text_with_url=f"📉 額度不足，請用網頁查詢： https://school-i9co.onrender.com/toilet_feedback_by_coord/{norm_coord(lat)}/{norm_coord(lon)}")

        # 再跑 OSM（有 8 秒上限）
        osm = query_overpass_toilets(lat, lon, radius=500) or []
        all_pts = _merge_and_dedupe_lists(quick, osm)
        sort_toilets(all_pts)

        if SEND_UPDATE_CARD and len(all_pts) > len(quick):  # 控制是否推更新卡
            msg2 = create_toilet_flex_messages(all_pts, show_delete=False, uid=uid)
            guard.push(uid,
                       FlexSendMessage("附近廁所（更新）", msg2),
                       fallback_text_with_url=f"📉 額度不足，請用網頁查詢： https://school-i9co.onrender.com/toilet_feedback_by_coord/{norm_coord(lat)}/{norm_coord(lon)}")

        elif not quick and not all_pts:
            guard.push(uid,
                       TextSendMessage(text="附近沒有廁所，可能要原地解放了 💦"),
                       fallback_text_with_url=f"📉 額度不足，請用網頁查詢： https://school-i9co.onrender.com/toilet_feedback_by_coord/{norm_coord(lat)}/{norm_coord(lon)}")

    except Exception as e:
        logging.error(f"bg nearby error: {e}", exc_info=True)
        guard.push(uid,
                   TextSendMessage(text="系統忙線中，請稍後再試 🙏"),
                   fallback_text_with_url=f"📉 額度不足，請用網頁查詢： https://school-i9co.onrender.com/toilet_feedback_by_coord/{norm_coord(lat)}/{norm_coord(lon)}")

# === TextMessage ===
@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    uid = event.source.user_id
    text_raw = event.message.text or ""
    text = text_raw.strip().lower()

    if is_duplicate_and_mark(f"text|{uid}|{text}"):
        return

    
    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        guard.reply(event, gate_msg)
        return

    reply_messages = []

    if uid in pending_delete_confirm:
        info = pending_delete_confirm[uid]
        if text == "確認刪除":
            if info.get("mode") == "sheet_row":
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
        loc = user_locations.pop(uid, None)
        if not loc:
            guard.reply(event, TextSendMessage(text="請先傳送位置"))
        else:
            la, lo = loc
            link = f"https://school-i9co.onrender.com/toilet_feedback_by_coord/{norm_coord(la)}/{norm_coord(lo)}"
            # 降級模式：不排背景推送，改回連結
            if guard.mode != Mode.NORMAL:
                guard.reply(event, TextSendMessage(text=f"📉 本月訊息額度緊張，請改用網頁查看：\n{link}"))
                return
            try:
                TASK_Q.put_nowait(lambda uid=uid, la=la, lo=lo: _do_nearby_toilets_and_push(uid, la, lo))
            except Full:
                guard.push(uid, TextSendMessage(text="系統忙線中，請稍候再試 🙏"), fallback_text_with_url=link)
            except Exception as e:
                logging.error(f"enqueue error: {e}", exc_info=True)
                guard.push(uid, TextSendMessage(text="排程失敗，請再傳一次位置 🙏"), fallback_text_with_url=link)

    elif text == "我的最愛":
        favs = get_user_favorites(uid)
        if not favs:
            reply_messages.append(TextSendMessage(text="你尚未收藏任何廁所"))
        else:
            loc = user_locations.get(uid)
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
        loc = user_locations.get(uid)
        if loc:
            la, lo = loc
            url = f"{base}?uid={quote(uid)}&lat={la}&lon={lo}#openExternalBrowser=1"
        else:
            url = f"{base}?uid={quote(uid)}#openExternalBrowser=1"
        reply_messages.append(TextSendMessage(text=f"請前往此頁新增廁所：\n{url}"))

    elif text == "回饋":
        form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
        reply_messages.append(TextSendMessage(text=f"💡 請透過下列連結回報問題或提供意見：\n{form_url}"))

    if reply_messages:
        guard.reply(event, reply_messages)

# === LocationMessage ===
@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
    uid = event.source.user_id
    lat = event.message.latitude
    lon = event.message.longitude

    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        guard.reply(event, gate_msg)
        return

    key = f"loc|{uid}|{round(lat,5)},{round(lon,5)}"
    if is_duplicate_and_mark(key):
        return

    user_locations[uid] = (lat, lon)
    guard.reply(event, TextSendMessage(text="✅ 位置已更新"))

# === Postback ===
@handler.add(PostbackEvent)
def handle_postback(event):
    uid = event.source.user_id
    data = event.postback.data or ""

    if is_duplicate_and_mark(f"pb|{uid}|{data}"):
        return

    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        guard.reply(event, gate_msg)
        return

    try:
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
            guard.reply(event, TextSendMessage(text=f"✅ 已收藏 {name}"))

        elif data.startswith("remove_fav:"):
            _, qname, lat, lon = data.split(":", 3)
            name = unquote(qname)
            success = remove_from_favorites(uid, name, lat, lon)
            msg = "✅ 已移除最愛" if success else "❌ 移除失敗"
            guard.reply(event, TextSendMessage(text=msg))

        elif data.startswith("confirm_delete:"):
            _, qname, qaddr, lat, lon = data.split(":", 4)
            name = unquote(qname)
            pending_delete_confirm[uid] = {
                "mode": "favorite",
                "name": name,
                "lat": norm_coord(lat),
                "lon": norm_coord(lon)
            }
            guard.reply(event, [
                TextSendMessage(text=f"⚠️ 確定要刪除 {name} 嗎？（目前刪除為移除最愛）"),
                TextSendMessage(text="請輸入『確認刪除』或『取消』")
            ])

        elif data.startswith("confirm_delete_my_toilet:"):
            _, row_str = data.split(":", 1)
            pending_delete_confirm[uid] = {
                "mode": "sheet_row",
                "row": int(row_str)
            }
            guard.reply(event, [
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