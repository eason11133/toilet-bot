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
import statistics  # ✅ 新增：做 95% CI 用

# 可選：安裝了 pandas 就用它避免 sklearn 特徵名稱警告；沒裝也不影響運作
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
TOILETS_FILE_PATH = os.path.join(DATA_DIR, "public_toilets.csv")  # 備份用
FAVORITES_FILE_PATH = os.path.join(DATA_DIR, "favorites.txt")
os.makedirs(DATA_DIR, exist_ok=True)
if not os.path.exists(FAVORITES_FILE_PATH):
    open(FAVORITES_FILE_PATH, "a", encoding="utf-8").close()

# === Google Sheets 設定 ===
GSHEET_SCOPE = ['https://spreadsheets.google.com/feeds', 'https://www.googleapis.com/auth/drive']
GSHEET_CREDENTIALS_JSON = os.getenv("GSHEET_CREDENTIALS_JSON")
TOILET_SPREADSHEET_ID = "1Vg3tiqlXcXjcic2cAWCG-xTXfNzcI7wegEnZx8Ak7ys"  # 主資料（使用者新增）
FEEDBACK_SPREADSHEET_ID = "15Ram7EZ9QMN6SZAVYQFNpL5gu4vTaRn4M5mpWUKmmZk"  # 回饋/預測

gc = worksheet = feedback_sheet = None

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

# === 參數：一起計算預測時納入的「最近回饋筆數」 ===
LAST_N_HISTORY = 5

# === 工具：座標標準化 ===
def norm_coord(x, ndigits=6):
    try:
        return f"{round(float(x), ndigits):.{ndigits}f}"
    except:
        return str(x)

# === 初始化 Google Sheets ===
def init_gsheet():
    global gc, worksheet, feedback_sheet
    try:
        if not GSHEET_CREDENTIALS_JSON:
            raise RuntimeError("缺少 GSHEET_CREDENTIALS_JSON")
        creds_dict = json.loads(GSHEET_CREDENTIALS_JSON)
        creds = ServiceAccountCredentials.from_json_keyfile_dict(creds_dict, GSHEET_SCOPE)
        gc = gspread.authorize(creds)
        worksheet = gc.open_by_key(TOILET_SPREADSHEET_ID).sheet1
        feedback_sheet = gc.open_by_key(FEEDBACK_SPREADSHEET_ID).sheet1
        logging.info("✅ Sheets 初始化完成")
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
    # 偶爾清理
    if len(_RECENT_EVENTS) > 1000:
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

# === 可靠回覆：reply 失敗自動 push（但遇到重送/無效 token 就不 push，避免重複） ===
def safe_reply(event, messages):
    try:
        line_bot_api.reply_message(event.reply_token, messages)
    except LineBotApiError as e:
        msg_txt = ""
        try:
            msg_txt = getattr(getattr(e, "error", None), "message", "") or str(e)
        except Exception:
            msg_txt = str(e)

        # 重送 (redelivery) 或 token 無效，多半代表同一事件被處理過，不再 push 以免重複
        if is_redelivery(event) or ("Invalid reply token" in msg_txt):
            logging.warning(f"reply_message 失敗但不 push（避免重複）：{msg_txt}")
            return

        # 其它錯誤才改用 push
        logging.warning(f"reply_message 失敗，改用 push：{msg_txt}")
        try:
            uid = getattr(event.source, "user_id", None)
            if uid:
                line_bot_api.push_message(uid, messages)
        except Exception as ex:
            logging.error(f"push_message 也失敗：{ex}")

# === 從 Google Sheets 查使用者新增廁所（唯一來源） ===
def query_sheet_toilets(user_lat, user_lon, radius=500):
    toilets = []
    try:
        rows = worksheet.get_all_values()  # 欄位：[user_id,name,address,lat,lon,timestamp]
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
    headers = {"User-Agent": "ToiletBot/1.0 (contact: you@example.com)"}

    last_err = None
    for idx, url in enumerate(endpoints):
        try:
            resp = requests.post(url, data=query, headers=headers, timeout=30)
            ctype = (resp.headers.get("Content-Type") or "").lower()
            if resp.status_code != 200 or "json" not in ctype:
                snippet = (resp.text or "")[:200].replace("\n", " ")
                logging.warning(f"Overpass 非 200 或非 JSON (endpoint {idx}): "
                                f"status={resp.status_code}, ctype={ctype}, body~={snippet}")
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

# === 最愛管理 ===
def add_to_favorites(uid, toilet):
    try:
        lat_s = norm_coord(toilet['lat'])
        lon_s = norm_coord(toilet['lon'])
        with open(FAVORITES_FILE_PATH, "a", encoding="utf-8") as f:
            f.write(f"{uid},{toilet['name']},{lat_s},{lon_s},{toilet.get('address','')}\n")
    except Exception as e:
        logging.error(f"加入最愛失敗: {e}")

def remove_from_favorites(uid, name, lat, lon):
    try:
        lat_s = norm_coord(lat)
        lon_s = norm_coord(lon)
        with open(FAVORITES_FILE_PATH, "r", encoding="utf-8") as f:
            lines = f.readlines()
        with open(FAVORITES_FILE_PATH, "w", encoding="utf-8") as f:
            for line in lines:
                data = line.strip().split(',')
                if not (data[0] == uid and data[1] == name and data[2] == lat_s and data[3] == lon_s):
                    f.write(line)
        return True
    except Exception as e:
        logging.error(f"移除最愛失敗: {e}")
        return False

def get_user_favorites(uid):
    favs = []
    try:
        with open(FAVORITES_FILE_PATH, "r", encoding="utf-8") as f:
            for line in f:
                data = line.strip().split(',')
                if len(data) < 5:
                    continue
                if data[0] == uid:
                    favs.append({
                        "name": data[1],
                        "lat": float(data[2]),
                        "lon": float(data[3]),
                        "address": data[4],
                        "distance": 0,
                        "type": "favorite"
                    })
    except Exception as e:
        logging.error(f"讀取最愛失敗: {e}")
    return favs

# === 地址轉經緯度 ===
def geocode_address(address):
    try:
        url = f"https://nominatim.openstreetmap.org/search?format=json&q={quote(address)}"
        headers = {"User-Agent": "ToiletBot/1.0"}
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

    osm_toilets = query_overpass_toilets(user_lat, user_lon, radius=500) or []
    sheet_toilets = query_sheet_toilets(user_lat, user_lon, radius=500)
    all_toilets = osm_toilets + sheet_toilets

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

# === 清潔度預測（單筆/多筆） ===
def expected_from_feats(feats):
    try:
        if not feats or cleanliness_model is None or label_encoder is None:
            return None
        if pd is not None:
            df = pd.DataFrame(feats, columns=["rating","toilet_paper","accessibility"])
            probs = cleanliness_model.predict_proba(df)
        else:
            probs = cleanliness_model.predict_proba(feats)
        try:
            classes_enc = cleanliness_model.classes_
            labels = label_encoder.inverse_transform(classes_enc.astype(int))
        except Exception:
            labels = cleanliness_model.classes_
        exps = []
        for p_row in probs:
            exps.append(sum(float(p) * float(l) for p, l in zip(p_row, labels)))
        return round(sum(exps) / len(exps), 2) if exps else None
    except Exception as e:
        logging.error(f"❌ 清潔度預測錯誤: {e}")
        return None

# === ✅ 新增：以最近 N 筆做「即時預測」與 95% CI ===
def compute_nowcast_ci(lat, lon, k=LAST_N_HISTORY, tol=1e-6):
    """
    以同座標最近 k 筆回饋，計算即時乾淨度(nowcast)與 95% 信心區間。
    先用表內「預測分數」；若缺值則用模型依 (rating, paper, access) 重算。
    回傳 dict: {'mean':float,'lower':float,'upper':float,'n':int} 或 None
    """
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

        # 篩選同座標
        same = []
        for r in data:
            if len(r) <= max(idx["lat"], idx["lon"]):
                continue
            if close(r[idx["lat"]], lat) and close(r[idx["lon"]], lon):
                same.append(r)

        if not same:
            return None

        # 依建立時間倒序取最近 k 筆
        if idx["created"] is not None:
            same.sort(key=lambda x: x[idx["created"]], reverse=True)
        recent = same[:k]

        paper_map = {"有": 1, "沒有": 0, "沒注意": 0}
        access_map = {"有": 1, "沒有": 0, "沒注意": 0}

        mu_vals = []
        for r in recent:
            mu = None
            # 1) 先用表內的「預測分數」
            if idx["pred"] is not None and len(r) > idx["pred"]:
                try:
                    mu = float((r[idx["pred"]] or "").strip())
                except:
                    mu = None
            # 2) 補算
            if mu is None and cleanliness_model is not None:
                try:
                    rr = None
                    if idx["rating"] is not None and len(r) > idx["rating"]:
                        rr = int((r[idx["rating"]] or "").strip())
                    pp = (r[idx["paper"]] or "").strip() if idx["paper"] is not None and len(r) > idx["paper"] else "沒注意"
                    aa = (r[idx["access"]] or "").strip() if idx["access"] is not None and len(r) > idx["access"] else "沒注意"
                    if rr is not None:
                        feat = [rr, paper_map.get(pp, 0), access_map.get(aa, 0)]
                        mu = expected_from_feats([feat])
                except:
                    pass

            if isinstance(mu, (int, float)):
                mu_vals.append(float(mu))

        n = len(mu_vals)
        if n == 0:
            return None

        mean = round(sum(mu_vals) / n, 2)
        if n == 1:
            return {"mean": mean, "lower": mean, "upper": mean, "n": n}

        try:
            s = statistics.stdev(mu_vals)
        except statistics.StatisticsError:
            s = 0.0
        se = s / (n ** 0.5)
        lower = max(1.0, round(mean - 1.96 * se, 2))
        upper = min(5.0, round(mean + 1.96 * se, 2))
        return {"mean": mean, "lower": lower, "upper": upper, "n": n}
    except Exception as e:
        logging.error(f"❌ compute_nowcast_ci 失敗: {e}")
        return None

# === ✅ 新增：Nowcast API（前端可呼叫） ===
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

# === 回饋：寫入前先把同座標最近 N 筆也納入預測 ===
@app.route("/submit_feedback", methods=["POST"])
def submit_feedback():
    try:
        data = request.form
        name = (data.get("name","") or "").strip()
        address = (data.get("address","") or "").strip()
        lat = norm_coord((data.get("lat","") or "").strip())
        lon = norm_coord((data.get("lon","") or "").strip())
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

        # 撈同座標歷史最近 N 筆
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

# === 以座標聚合的統計（摘要） ===
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
        score_sum = 0.0
        valid_score_count = 0
        comments = []

        for r in matched:
            if idx["pred"] is not None and len(r) > idx["pred"]:
                try:
                    s = float((r[idx["pred"]] or "").strip())
                    score_sum += s
                    valid_score_count += 1
                except:
                    pass
            if idx["paper"] is not None and len(r) > idx["paper"]:
                p = (r[idx["paper"]] or "").strip()
                if p in paper_counts:
                    paper_counts[p] += 1
            if idx["access"] is not None and len(r) > idx["access"]:
                a = (r[idx["access"]] or "").strip()
                if a in access_counts:
                    access_counts[a] += 1
            if idx["comment"] is not None and len(r) > idx["comment"]:
                c = (r[idx["comment"]] or "").strip()
                if c:
                    comments.append(c)

        avg_score = round(score_sum / valid_score_count, 2) if valid_score_count else "未預測"

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

# === 建清單：同座標的指示燈（🧻/♿/⭐）索引 ===
def build_feedback_index():
    """回傳 {(lat_s,lon_s): {'paper':'有/沒有/?','access':'有/沒有/?','avg':float or None}}"""
    result = {}
    try:
        rows = feedback_sheet.get_all_values()
        if not rows or len(rows) < 2:
            return result
        header = rows[0]; data = rows[1:]
        idx = _feedback_indices(header)
        for r in data:
            try:
                lat_s = norm_coord(r[idx["lat"]])
                lon_s = norm_coord(r[idx["lon"]])
            except Exception:
                continue
            rec = result.setdefault((lat_s, lon_s), {"paper": {"有":0,"沒有":0}, "access":{"有":0,"沒有":0}, "scores":[]})
            if idx["paper"] is not None and len(r) > idx["paper"]:
                p = (r[idx["paper"]] or "").strip()
                if p in rec["paper"]: rec["paper"][p] += 1
            if idx["access"] is not None and len(r) > idx["access"]:
                a = (r[idx["access"]] or "").strip()
                if a in rec["access"]: rec["access"][a] += 1
            if idx["pred"] is not None and len(r) > idx["pred"]:
                try: rec["scores"].append(float((r[idx["pred"]] or "").strip()))
                except: pass
        out = {}
        for key, v in result.items():
            paper = "有" if v["paper"]["有"] >= v["paper"]["沒有"] and sum(v["paper"].values())>0 else ("沒有" if sum(v["paper"].values())>0 else "?")
            access = "有" if v["access"]["有"] >= v["access"]["沒有"] and sum(v["access"].values())>0 else ("沒有" if sum(v["access"].values())>0 else "?")
            avg = round(sum(v["scores"])/len(v["scores"]),2) if v["scores"] else None
            out[key] = {"paper": paper, "access": access, "avg": avg}
        return out
    except Exception as e:
        logging.warning(f"建立指示燈索引失敗：{e}")
        return {}

# === 舊路由（名稱→地址）保留 ===
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
            cs = val("pred")
            try: nums.append(float(cs))
            except: pass
            fbs.append({
                "rating": val("rating"),
                "toilet_paper": val("paper"),
                "accessibility": val("access"),
                "time_of_use": val("time"),
                "comment": val("comment"),
                "cleanliness_score": cs,
                "created_at": val("created"),
            })
        fbs.sort(key=lambda d: d.get("created_at",""), reverse=True)
        avg_pred_score = round(sum(nums)/len(nums), 2) if nums else "未預測"

        if matched:
            paper_counts = {"有": 0, "沒有": 0}
            access_counts = {"有": 0, "沒有": 0}
            score_sum = 0.0; valid = 0
            for r in matched:
                if idx["pred"] is not None and len(r) > idx["pred"]:
                    try: score_sum += float((r[idx["pred"]] or "").strip()); valid += 1
                    except: pass
                if idx["paper"] is not None and len(r) > idx["paper"]:
                    p = (r[idx["paper"]] or "").strip()
                    if p in paper_counts: paper_counts[p] += 1
                if idx["access"] is not None and len(r) > idx["access"]:
                    a = (r[idx["access"]] or "").strip()
                    if a in access_counts: access_counts[a] += 1
            avg = round(score_sum/valid, 2) if valid else "未預測"
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

# === 新路由：座標版 ===
@app.route("/toilet_feedback_by_coord/<lat>/<lon>")
def toilet_feedback_by_coord(lat, lon):
    try:
        name = f"廁所（{lat}, {lon}）"
        summary = get_feedback_summary_by_coord(lat, lon)
        feedbacks = get_feedbacks_by_coord(lat, lon)
        nums = []
        for f in feedbacks:
            try: nums.append(float((f.get("cleanliness_score") or "").strip()))
            except: pass
        avg_pred_score = round(sum(nums)/len(nums), 2) if nums else "未預測"

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

# === 清潔度趨勢 API（座標） ===
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

        matched = []
        for r in data:
            if len(r) <= max(idx["lat"], idx["lon"]):
                continue
            if close(r[idx["lat"]], lat) and close(r[idx["lon"]], lon):
                created = r[idx["created"]] if idx["created"] is not None and len(r) > idx["created"] else ""
                pred = r[idx["pred"]] if idx["pred"] is not None and len(r) > idx["pred"] else ""
                matched.append((created, pred))
        matched.sort(key=lambda t: t[0])

        out = []
        for created, pred in matched:
            try: out.append({"score": float(str(pred).strip())})
            except: pass
        return {"success": True, "data": out}
    except Exception as e:
        logging.error(f"❌ 趨勢 API（座標）錯誤: {e}")
        return {"success": False, "data": []}, 500

# === 建立 Flex：附近 / 最愛（含指示燈） ===
def create_toilet_flex_messages(toilets, show_delete=False, uid=None):
    indicators = build_feedback_index()  # {(lat,lon): {'paper','access','avg'}}
    bubbles = []
    for toilet in toilets[:5]:
        actions = []

        lat_s = norm_coord(toilet['lat'])
        lon_s = norm_coord(toilet['lon'])
        addr_text = toilet.get('address') or "（無地址，使用座標）"

        # 指示燈
        ind = indicators.get((lat_s, lon_s), {"paper":"?","access":"?","avg":None})
        star_text = f"⭐{ind['avg']}" if ind.get("avg") is not None else "⭐—"
        paper_text = "🧻有" if ind.get("paper")=="有" else ("🧻無" if ind.get("paper")=="沒有" else "🧻—")
        access_text = "♿有" if ind.get("access")=="有" else ("♿無" if ind.get("access")=="沒有" else "♿—")

        # ✅ 導航
        actions.append({
            "type": "uri",
            "label": "導航",
            "uri": f"https://www.google.com/maps/search/?api=1&query={lat_s},{lon_s}"
        })
        # ✅ 查詢回饋（座標）
        actions.append({
            "type": "uri",
            "label": "查詢回饋（座標）",
            "uri": f"https://school-i9co.onrender.com/toilet_feedback_by_coord/{lat_s}/{lon_s}"
        })
        # ✅ 填回饋（帶座標；address 後備）
        addr_raw = toilet.get('address') or ""
        addr_param = quote(addr_raw or "-")  # 沒地址用 - 佔位避免 404
        actions.append({
            "type": "uri",
            "label": "廁所回饋",
            "uri": (
                "https://school-i9co.onrender.com/feedback_form/"
                f"{quote(toilet['name'])}/{addr_param}"
                f"?lat={lat_s}&lon={lon_s}&address={quote(addr_raw)}"
            )
        })

        # 收藏/移除
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

# === 列出「我的貢獻」 & 刪除（真的刪主資料那一列） ===
def get_user_contributions(uid):
    items = []
    try:
        rows = worksheet.get_all_values()
        if not rows or len(rows) < 2:
            return items
        header = rows[0]; data = rows[1:]
        idx = _toilet_sheet_indices(header)
        for i, r in enumerate(data, start=2):  # 1-based，含表頭
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

    # 去重：同一用戶同一文字，在視窗內不重覆處理
    if is_duplicate_and_mark(f"text|{uid}|{text}"):
        return

    reply_messages = []

    # 刪除確認流程
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
            toilets = (query_sheet_toilets(lat, lon) or []) + (query_overpass_toilets(lat, lon) or [])
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
        reply_messages.append(TextSendMessage(text="請前往此頁新增廁所：\nhttps://school-i9co.onrender.com/add"))

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

    # 去重：同一用戶同一座標（取 5 位小數）在視窗內不重覆處理
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

    # 去重：同一用戶相同 postback data 在視窗內不重覆處理
    if is_duplicate_and_mark(f"pb|{uid}|{data}"):
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
    return render_template("submit_toilet.html")

# （可選）使用者新增廁所 API（保留）
@app.route("/submit_toilet", methods=["POST"])
def submit_toilet():
    try:
        data = request.get_json()
        logging.info(f"📥 收到表單資料: {data}")

        uid = data.get("user_id")
        name = data.get("name")
        address = data.get("address")

        if not all([uid, name, address]):
            return {"success": False, "message": "缺少參數"}, 400

        lat, lon = geocode_address(address)
        if lat is None or lon is None:
            return {"success": False, "message": "地址轉換失敗"}, 400

        worksheet.append_row([uid, name, address, float(norm_coord(lat)), float(norm_coord(lon)), datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")])
        logging.info(f"✅ 廁所資料已寫入 Google Sheets: {name}")

        # （可選）備份 CSV
        try:
            if not os.path.exists(TOILETS_FILE_PATH):
                open(TOILETS_FILE_PATH, "a", encoding="utf-8").close()
            with open(TOILETS_FILE_PATH, "a", encoding="utf-8", newline="") as f:
                writer = csv.writer(f)
                writer.writerow(["00000","0000000","未知里","USERADD", name, address, "使用者補充",
                                norm_coord(lat), norm_coord(lon),
                                "普通級","公共場所","未知","使用者","0",""])
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
