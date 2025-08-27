import os
import csv
import json
import logging
import requests
import traceback
from math import radians, cos, sin, asin, sqrt
from flask_cors import CORS
from flask import Flask, request, abort, render_template, redirect, url_for
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
import statistics  # 95% CI 用
from difflib import SequenceMatcher

try:
    import pandas as pd
except Exception:
    pd = None

# === 初始化 ===
load_dotenv()
logging.basicConfig(level=logging.INFO)
app = Flask(__name__)
CORS(app)

line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

# 檔案
DATA_DIR = os.path.join(os.getcwd(), "data")
TOILETS_FILE_PATH = os.path.join(DATA_DIR, "public_toilets.csv")  # 公家資料/備份
FAVORITES_FILE_PATH = os.path.join(DATA_DIR, "favorites.txt")     # 仍沿用原檔名，但以 csv 方式讀寫
os.makedirs(DATA_DIR, exist_ok=True)

# 確保 favorites 檔存在
if not os.path.exists(FAVORITES_FILE_PATH):
    open(FAVORITES_FILE_PATH, "a", encoding="utf-8").close()

# 確保 public_toilets.csv 具有表頭（供 DictReader 使用）
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
TOILET_SPREADSHEET_ID = "1Vg3tiqlXcXjcic2cAWCG-xTXfNzcI7wegEnZx8Ak7ys"  # 主資料（使用者新增廁所）
FEEDBACK_SPREADSHEET_ID = "15Ram7EZ9QMN6SZAVYQFNpL5gu4vTaRn4M5mpWUKmmZk"  # 回饋/預測

# ★ 同意書設定
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

# === 初始化 Google Sheets ===
def init_gsheet():
    global gc, worksheet, feedback_sheet, consent_ws
    try:
        if not GSHEET_CREDENTIALS_JSON:
            raise RuntimeError("缺少 GSHEET_CREDENTIALS_JSON")
        creds_dict = json.loads(GSHEET_CREDENTIALS_JSON)
        creds = ServiceAccountCredentials.from_json_keyfile_dict(creds_dict, GSHEET_SCOPE)
        gc = gspread.authorize(creds)

        worksheet = gc.open_by_key(TOILET_SPREADSHEET_ID).sheet1
        fb_spread = gc.open_by_key(FEEDBACK_SPREADSHEET_ID)
        feedback_sheet = fb_spread.sheet1

        # ★ 取得或建立 consent 工作表
        try:
            consent_ws = fb_spread.worksheet(CONSENT_SHEET_TITLE)
        except gspread.exceptions.WorksheetNotFound:
            consent_ws = fb_spread.add_worksheet(title=CONSENT_SHEET_TITLE, rows=1000, cols=10)
            consent_ws.update("A1:F1", [["user_id","agreed","display_name","source_type","ua","timestamp"]])

        logging.info("✅ Sheets 初始化完成（含 consent）")
    except Exception as e:
        logging.critical(f"❌ Sheets 初始化失敗: {e}")
        raise

init_gsheet()

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

# === 防重複（10 秒視為重複） ===
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
                line_bot_api.push_message(uid, messages)
        except Exception as ex:
            logging.error(f"push_message 也失敗：{ex}")

# === 同意工具 ===
def _booly(v):
    s = str(v).strip().lower()
    return s in ["1", "true", "yes", "y", "同意"]

def has_consented(user_id: str) -> bool:
    """查 consent sheet 是否有 agree=true 的紀錄"""
    try:
        if not user_id or consent_ws is None:
            return False
        rows = consent_ws.get_all_values()
        if not rows or len(rows) < 2:
            return False
        header = rows[0]; data = rows[1:]
        try:
            i_uid = header.index("user_id")
            i_ag  = header.index("agreed")
        except ValueError:
            return False
        for r in data:
            if len(r) <= max(i_uid, i_ag):
                continue
            if (r[i_uid] or "").strip() == user_id and _booly(r[i_ag]):
                return True
        return False
    except Exception as e:
        logging.warning(f"查詢同意失敗: {e}")
        return False

def upsert_consent(user_id: str, agreed: bool, display_name: str, source_type: str, ua: str, ts_iso: str):
    """以 user_id 進行 upsert 到 consent sheet"""
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

        # 找舊資料列
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
        return True
    except Exception as e:
        logging.error(f"寫入/更新同意失敗: {e}")
        return False

def ensure_consent_or_prompt(user_id: str):
    """未同意時回傳引導訊息（要在 handler 內用 safe_reply 發送後 return）"""
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
                toilets.append({
                    "name": name,
                    "lat": float(norm_coord(t_lat)),
                    "lon": float(norm_coord(t_lon)),
                    "address": address,
                    "distance": dist,
                    "type": "sheet"
                })
    except Exception as e:
        logging.error(f"讀取 Google Sheets 廁所主資料錯誤: {e}")
    return sorted(toilets, key=lambda x: x["distance"])

# === OSM Overpass（多鏡像） ===
def query_overpass_toilets(lat, lon, radius=500):
    query = f"""
    [out:json][timeout:25];
    (
      node["amenity"="toilets"](around:{radius},{lat},{lon});
      way["amenity"="toilets"](around:{radius},{lat},{lon});
      relation["amenity"="toilets"](around:{radius},{lat},{lon});
    );
    out center;
    """
    endpoints = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.openstreetmap.ru/api/interpreter",
    ]
    ua_email = os.getenv("CONTACT_EMAIL", "you@example.com")
    headers = {"User-Agent": f"ToiletBot/1.0 (+{ua_email})"}

    last_err = None
    for idx, url in enumerate(endpoints):
        try:
            resp = requests.post(url, data=query, headers=headers, timeout=30)
            ctype = (resp.headers.get("Content-Type") or "").lower()
            if resp.status_code != 200 or "json" not in ctype:
                snippet = (resp.text or "")[:200].replace("\n", " ")
                logging.warning(f"Overpass 非 200 或非 JSON (endpoint {idx}): status={resp.status_code}, ctype={ctype}, body~={snippet}")
                last_err = RuntimeError("overpass non-json")
                continue

            data = resp.json()
            elements = data.get("elements", [])
            toilets = []
            for elem in elements:
                if elem["type"] == "node":
                    t_lat, t_lon = elem["lat"], elem["lon"]
                elif "center" in elem:
                    t_lat, t_lon = elem["center"]["lat"], elem["center"]["lon"]
                else:
                    continue

                tags = elem.get("tags", {})
                name = tags.get("name", "無名稱")
                address = tags.get("addr:full", "") or tags.get("addr:street", "") or ""
                toilets.append({
                    "name": name,
                    "lat": float(norm_coord(t_lat)),
                    "lon": float(norm_coord(t_lon)),
                    "address": address,
                    "distance": haversine(lat, lon, t_lat, t_lon),
                    "type": "osm"
                })
            return sorted(toilets, key=lambda x: x["distance"])
        except Exception as e:
            last_err = e
            logging.warning(f"Overpass API 查詢失敗（endpoint {idx}）: {e}")

    logging.error(f"Overpass 全部端點失敗：{last_err}")
    return []

# === 讀本地 public_toilets.csv ===
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
                    pts.append({
                        "name": name,
                        "lat": float(norm_coord(t_lat)),
                        "lon": float(norm_coord(t_lon)),
                        "address": addr,
                        "distance": dist,
                        "type": "public_csv",
                        "grade": row.get("grade", ""),
                        "category": row.get("type2", "")
                    })
    except Exception as e:
        logging.error(f"讀 public_toilets.csv 失敗：{e}")
    return sorted(pts, key=lambda x: x["distance"])

# === 合併 + 簡單去重 ===
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

# === 附近廁所 API（已納入 CSV + 去重） ===
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

    if not all_toilets:
        return {"message": "附近找不到廁所"}, 404
    return {"toilets": all_toilets}, 200

# === 顯示回饋表單（允許沒有 address） ===
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

# === Header 對齊工具 ===
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

# === 從單列資料得到分數 ===
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

# === 以最近 N 筆做「即時預測」與 95% CI ===
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

        if not all([name, rating, lat, lon]):
            return "缺少必要欄位（需要：name、rating、lat、lon）", 400

        try:
            r = int(rating)
            if r < 1 or r > 10:
                return "清潔度評分必須在 1 到 10 之間", 400
        except ValueError:
            return "清潔度評分必須是數字", 400

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
            comment, pred_with_hist, lat, lon, datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")
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

# === 以座標聚合的統計（摘要）— 分數一致化 ===
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

# === 建清單 ===
_feedback_index_cache = {"ts": 0, "data": {}}
_FEEDBACK_INDEX_TTL = 30  # 秒

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

# === 舊路由保留 ===
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

# === 新路由：座標版（上方藍色平均也改成一致邏輯） ===
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

# === 清潔度趨勢 API（座標）— 分數一致化 ===
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
    # 你的檔名是 privacy.html
    return render_template("privacy.html")

# === LIFF 送資料回來的 API ===
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

        ok = upsert_consent(user_id, agreed, display_name, source_type, ua, ts)
        if not ok:
            return {"ok": False, "message": "寫入失敗"}, 500

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

# === 建立 Flex：附近 / 最愛（含指示燈） ===
def create_toilet_flex_messages(toilets, show_delete=False, uid=None):
    indicators = build_feedback_index()
    bubbles = []
    for toilet in toilets[:5]:
        actions = []

        lat_s = norm_coord(toilet['lat'])
        lon_s = norm_coord(toilet['lon'])
        addr_text = toilet.get('address') or "（無地址，使用座標）"

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
                f"{quote(toilet['name'])}/{addr_param}"
                f"?lat={lat_s}&lon={lon_s}&address={quote(addr_raw)}"
            )
        })

        if toilet.get("type") == "favorite" and uid:
            actions.append({
                "type": "postback",
                "label": "移除最愛",
                "data": f"remove_fav:{quote(toilet['name'])}:{lat_s}:{lon_s}"
            })
        elif toilet.get("type") not in ["user", "favorite"] and uid:
            actions.append({
                "type": "postback",
                "label": "加入最愛",
                "data": f"add:{quote(toilet['name'])}:{lat_s}:{lon_s}"
            })

        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {"type": "text", "text": toilet['name'], "weight": "bold", "size": "lg", "wrap": True},
                    {"type": "text", "text": f"{paper_text}  {access_text}  {star_text}", "size": "sm", "color": "#555555", "wrap": True},
                    {"type": "text", "text": addr_text, "size": "sm", "color": "#666666", "wrap": True},
                    {"type": "text", "text": f"{int(toilet['distance'])} 公尺", "size": "sm", "color": "#999999"}
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

# === 列出「我的貢獻」 & 削除 ===
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
                    {"type":"text","text":f"{it['created']}", "size":"xs","color":"#999999"}
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
pending_delete_confirm = {}  # {uid: {..., mode:'favorite'|'sheet_row'}}

# === TextMessage ===
@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    uid = event.source.user_id
    text_raw = event.message.text or ""
    text = text_raw.strip().lower()

    if is_duplicate_and_mark(f"text|{uid}|{text}"):
        return

    # ★ 同意門檻（新舊使用者都要先同意一次）
    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg)
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
                msg = "✅ 已刪除該廁所" if success else "❌ 刪除失敗"
            del pending_delete_confirm[uid]
            reply_messages.append(TextSendMessage(text=msg))
        elif text == "取消":
            del pending_delete_confirm[uid]
            reply_messages.append(TextSendMessage(text="❌ 已取消刪除"))
        else:
            reply_messages.append(TextSendMessage(text="⚠️ 請輸入『確認刪除』或『取消』"))

    elif text == "附近廁所":
        if uid not in user_locations:
            reply_messages.append(TextSendMessage(text="請先傳送位置"))
        else:
            lat, lon = user_locations[uid]
            toilets = _merge_and_dedupe_lists(
                query_public_csv_toilets(lat, lon) or [],
                query_sheet_toilets(lat, lon) or [],
                query_overpass_toilets(lat, lon) or [],
            )
            if not toilets:
                reply_messages.append(TextSendMessage(text="附近沒有廁所，可能要原地解放了 💦"))
            else:
                msg = create_toilet_flex_messages(toilets, show_delete=False, uid=uid)
                reply_messages.append(FlexSendMessage("附近廁所", msg))

    elif text == "我的最愛":
        favs = get_user_favorites(uid)
        if not favs:
            reply_messages.append(TextSendMessage(text="你尚未收藏任何廁所"))
        else:
            if uid in user_locations:
                lat, lon = user_locations[uid]
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
        if uid in user_locations:
            la, lo = user_locations[uid]
            url = f"{base}?uid={quote(uid)}&lat={la}&lon={lo}#openExternalBrowser=1"
        else:
            url = f"{base}#openExternalBrowser=1"
        reply_messages.append(TextSendMessage(text=f"請前往此頁新增廁所：\n{url}"))

    elif text == "回饋":
        form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
        reply_messages.append(TextSendMessage(text=f"💡 請透過下列連結回報問題或提供意見：\n{form_url}"))

    if reply_messages:
        safe_reply(event, reply_messages)

# === LocationMessage ===
@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
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

    user_locations[uid] = (lat, lon)
    safe_reply(event, TextSendMessage(text="✅ 位置已更新"))

# === Postback ===
@handler.add(PostbackEvent)
def handle_postback(event):
    uid = event.source.user_id
    data = event.postback.data or ""

    if is_duplicate_and_mark(f"pb|{uid}|{data}"):
        return

    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg)
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
    try:
        data = request.get_json()
        logging.info(f"📥 收到表單資料: {data}")

        uid = data.get("user_id") or "web"
        name = data.get("name")
        address = data.get("address")
        lat = data.get("lat", "")
        lon = data.get("lon", "")

        if not all([name, address]):
            return {"success": False, "message": "缺少參數"}, 400

        lat_f, lon_f = None, None
        if lat and lon:
            lat_f, lon_f = _parse_lat_lon(lat, lon)
        if lat_f is None or lon_f is None:
            lat_f, lon_f = geocode_address(address)

        if lat_f is None or lon_f is None:
            return {"success": False, "message": "地址轉換失敗"}, 400

        lat_s, lon_s = norm_coord(lat_f), norm_coord(lon_f)

        worksheet.append_row([
            uid, name, address, float(lat_s), float(lon_s),
            datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")
        ])
        logging.info(f"✅ 廁所資料已寫入 Google Sheets: {name}")

        try:
            if not os.path.exists(TOILETS_FILE_PATH):
                with open(TOILETS_FILE_PATH, "w", encoding="utf-8", newline="") as f:
                    writer = csv.writer(f)
                    writer.writerow(PUBLIC_HEADERS)
            with open(TOILETS_FILE_PATH, "a", encoding="utf-8", newline="") as f:
                writer = csv.writer(f)
                writer.writerow([
                    "00000","0000000","未知里","USERADD", name, address, "使用者補充",
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
    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
