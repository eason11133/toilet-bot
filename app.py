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
from linebot.exceptions import InvalidSignatureError
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
import pandas as pd  # 用於包裝 features，避免 sklearn feature name 警告

# === 初始化 ===
load_dotenv()
logging.basicConfig(level=logging.INFO)
app = Flask(__name__)
CORS(app)

line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

# 檔案路徑（僅保留 favorites.txt；CSV 只做備份，不作查詢來源）
DATA_DIR = os.path.join(os.getcwd(), "data")
TOILETS_FILE_PATH = os.path.join(DATA_DIR, "public_toilets.csv")  # 備份用
FAVORITES_FILE_PATH = os.path.join(DATA_DIR, "favorites.txt")

os.makedirs(DATA_DIR, exist_ok=True)
if not os.path.exists(FAVORITES_FILE_PATH):
    open(FAVORITES_FILE_PATH, "a", encoding="utf-8").close()

# === Google Sheets 設定 ===
GSHEET_SCOPE = ['https://spreadsheets.google.com/feeds', 'https://www.googleapis.com/auth/drive']
GSHEET_CREDENTIALS_JSON = os.getenv("GSHEET_CREDENTIALS_JSON")
TOILET_SPREADSHEET_ID = "1Vg3tiqlXcXjcic2cAWCG-xTXfNzcI7wegEnZx8Ak7ys"  # 使用者新增廁所（主資料）
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

# === 公用：座標標準化，避免浮點誤差 ===
def norm_coord(x, ndigits=6):
    try:
        return f"{round(float(x), ndigits):.{ndigits}f}"
    except:
        return str(x)

# === 初始化 Google Sheets（缺憑證直接中止） ===
def init_gsheet():
    global gc, worksheet, feedback_sheet
    try:
        if not GSHEET_CREDENTIALS_JSON:
            raise RuntimeError("缺少 GSHEET_CREDENTIALS_JSON")
        creds_dict = json.loads(GSHEET_CREDENTIALS_JSON)
        creds = ServiceAccountCredentials.from_json_keyfile_dict(creds_dict, GSHEET_SCOPE)
        gc = gspread.authorize(creds)
        worksheet = gc.open_by_key(TOILET_SPREADSHEET_ID).sheet1        # 主資料
        feedback_sheet = gc.open_by_key(FEEDBACK_SPREADSHEET_ID).sheet1  # 回饋/預測
        logging.info("✅ Sheets 初始化完成")
    except Exception as e:
        logging.critical(f"❌ Sheets 初始化失敗: {e}")
        raise

init_gsheet()

# === 距離 ===
def haversine(lat1, lon1, lat2, lon2):
    try:
        lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
        dlat = lat2 - lat1
        dlon = lon2 - lon1
        a = sin(dlat / 2)**2 + cos(lat1) * cos(lat2) * sin(dlon / 2)**2
        return 2 * asin(sqrt(a)) * 6371000
    except Exception as e:
        logging.error(f"計算距離失敗: {e}")
        return 0

# === Feedback Sheet 欄位解析工具（避免 header 不一致） ===
def _header_idx(header, candidates):
    """大小寫不敏感比對，命中回傳 index，否則 None"""
    hl = [h.strip().lower() for h in header]
    for i, h in enumerate(hl):
        if h in [c.strip().lower() for c in candidates]:
            return i
    return None

def load_feedback_rows():
    """
    回傳 (rows, idx)
      rows: get_all_values() 完整資料（含表頭）
      idx: 需要的欄位索引 dict（可能為 None，呼叫端需判斷）
    支援的欄位別名：
      name: ["name","名稱","廁所名稱"]
      address: ["address","地址"]
      rating: ["rating","評分","清潔度評分"]
      toilet_paper: ["toilet_paper","是否有衛生紙","衛生紙"]
      accessibility: ["accessibility","是否有無障礙設施","無障礙"]
      time_of_use: ["time_of_use","使用時間"]
      comment: ["comment","留言"]
      predicted: ["預測分數","cleanliness_score","predicted","predicted_score"]
      lat: ["lat","緯度"]
      lon: ["lon","經度"]
      created_at: ["created_at","時間","timestamp","created time","created"]
    """
    rows = feedback_sheet.get_all_values()
    if not rows:
        return [], {}
    header = rows[0]
    idx = {
        "name":         _header_idx(header, ["name","名稱","廁所名稱"]),
        "address":      _header_idx(header, ["address","地址"]),
        "rating":       _header_idx(header, ["rating","評分","清潔度評分"]),
        "toilet_paper": _header_idx(header, ["toilet_paper","是否有衛生紙","衛生紙"]),
        "accessibility":_header_idx(header, ["accessibility","是否有無障礙設施","無障礙"]),
        "time_of_use":  _header_idx(header, ["time_of_use","使用時間"]),
        "comment":      _header_idx(header, ["comment","留言"]),
        "predicted":    _header_idx(header, ["預測分數","cleanliness_score","predicted","predicted_score"]),
        "lat":          _header_idx(header, ["lat","緯度"]),
        "lon":          _header_idx(header, ["lon","經度"]),
        "created_at":   _header_idx(header, ["created_at","時間","timestamp","created time","created"]),
    }
    return rows, idx

# === 查使用者新增廁所（唯一來源：主資料表） ===
def query_sheet_toilets(user_lat, user_lon, radius=500):
    toilets = []
    try:
        rows = worksheet.get_all_values()
        if not rows or len(rows) < 2:
            return []
        header, data = rows[0], rows[1:]
        # 假設主資料欄序：[uid, name, address, lat, lon, created_at]
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

# === OSM ===
def query_overpass_toilets(lat, lon, radius=500):
    query = f"""
    [out:json];
    (
      node["amenity"="toilets"](around:{radius},{lat},{lon});
      way["amenity"="toilets"](around:{radius},{lat},{lon});
      relation["amenity"="toilets"](around:{radius},{lat},{lon});
    );
    out center;
    """
    try:
        resp = requests.post(
            "https://overpass-api.de/api/interpreter",
            data=query,
            headers={"User-Agent": "ToiletBot/1.0"},
            timeout=10
        )
        data = resp.json()
    except Exception as e:
        logging.error(f"Overpass API 查詢失敗: {e}")
        return []

    toilets = []
    for elem in data.get("elements", []):
        if elem["type"] == "node":
            t_lat, t_lon = elem["lat"], elem["lon"]
        elif "center" in elem:
            t_lat, t_lon = elem["center"]["lat"], elem["center"]["lon"]
        else:
            continue

        name = elem.get("tags", {}).get("name", "無名稱")
        address = elem.get("tags", {}).get("addr:full", "") or elem.get("tags", {}).get("name", "")
        toilets.append({
            "name": name,
            "lat": float(norm_coord(t_lat)),
            "lon": float(norm_coord(t_lon)),
            "address": address,
            "distance": haversine(lat, lon, t_lat, t_lon),
            "type": "osm"
        })
    return sorted(toilets, key=lambda x: x["distance"])

# === 最愛（以標準化座標字串做鍵） ===
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
                if not (len(data) >= 4 and data[0] == uid and data[1] == name and data[2] == lat_s and data[3] == lon_s):
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

# === 地理編碼（新增廁所用） ===
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

# === API：附近廁所（OSM + 主資料表） ===
@app.route("/nearby_toilets", methods=["GET"])
def nearby_toilets():
    user_lat = request.args.get('lat')
    user_lon = request.args.get('lon')
    if not user_lat or not user_lon:
        return {"error": "缺少位置參數"}, 400

    user_lat = float(user_lat)
    user_lon = float(user_lon)

    osm_toilets = query_overpass_toilets(user_lat, user_lon, radius=500)
    sheet_toilets = query_sheet_toilets(user_lat, user_lon, radius=500)
    all_toilets = osm_toilets + sheet_toilets

    if not all_toilets:
        return {"message": "附近找不到廁所"}, 404
    return {"toilets": all_toilets}, 200

# === 新增廁所（寫 Google Sheets；CSV 只備份） ===
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

        # 寫入主資料表
        worksheet.append_row([
            uid, name, address,
            float(norm_coord(lat)), float(norm_coord(lon)),
            datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")
        ])
        logging.info(f"✅ 廁所資料已寫入 Google Sheets: {name}")

        # 備份 CSV（非查詢來源）
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

# === HTML：回饋表單（請確保模板帶 lat/lon hidden，或由 querystring 注入） ===
@app.route("/feedback_form/<toilet_name>/<address>")
def feedback_form(toilet_name, address):
    return render_template("feedback_form.html", toilet_name=toilet_name, address=address)

# === 提交回饋（lat/lon 必帶；地址可空；寫 Google Sheets） ===
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

        # 用 pandas 包裝 features，避免 sklearn 的 feature name 警告
        X = pd.DataFrame([{
            "rating": r,
            "paper": paper_map.get(toilet_paper, 0),
            "access": access_map.get(accessibility, 0)
        }])

        predicted_score = predict_cleanliness_df(X)

        feedback_sheet.append_row([
            name, address, rating, toilet_paper, accessibility, time_of_use,
            comment, predicted_score, lat, lon, datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")
        ])

        return redirect(url_for("feedback_form", toilet_name=name, address=address or ""))

    except Exception as e:
        logging.error(f"❌ 提交回饋表單錯誤: {e}")
        return "提交失敗", 500

# === 清潔度預測（以 DataFrame 輸入） ===
def predict_cleanliness_df(X_df: pd.DataFrame):
    try:
        if cleanliness_model is None:
            return "未預測"
        probs = cleanliness_model.predict_proba(X_df)[0]
        # 嘗試還原原始標籤
        try:
            classes_enc = cleanliness_model.classes_
            if label_encoder is not None:
                labels = label_encoder.inverse_transform(classes_enc.astype(int))
            else:
                labels = classes_enc
        except Exception:
            labels = cleanliness_model.classes_
        expected = round(sum(float(p) * float(l) for p, l in zip(probs, labels)), 2)
        return expected
    except Exception as e:
        logging.error(f"❌ 清潔度預測錯誤: {e}")
        return "未預測"

# === 以座標聚合的回饋摘要（不依賴固定表頭） ===
def get_feedback_summary_by_coord(lat, lon, tol=1e-6):
    try:
        rows, idx = load_feedback_rows()
        if not rows or not idx or idx.get("lat") is None or idx.get("lon") is None:
            return "讀取錯誤（找不到 lat/lon 欄位）"

        def close(a, b):
            try:
                return abs(float(a) - float(b)) <= tol
            except:
                return False

        data = rows[1:]
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
            # 預測分數
            if idx.get("predicted") is not None and len(r) > idx["predicted"]:
                s = r[idx["predicted"]]
                try:
                    score_sum += float(s)
                    valid_score_count += 1
                except:
                    pass
            # 衛生紙
            if idx.get("toilet_paper") is not None and len(r) > idx["toilet_paper"]:
                p = (r[idx["toilet_paper"]] or "").strip()
                if p in paper_counts:
                    paper_counts[p] += 1
            # 無障礙
            if idx.get("accessibility") is not None and len(r) > idx["accessibility"]:
                a = (r[idx["accessibility"]] or "").strip()
                if a in access_counts:
                    access_counts[a] += 1
            # 留言
            if idx.get("comment") is not None and len(r) > idx["comment"]:
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

# === 舊路由（名稱→地址），相容保留 ===
@app.route("/toilet_feedback/<toilet_name>")
def toilet_feedback(toilet_name):
    try:
        address = "未知地址"
        rows = worksheet.get_all_values()
        if rows and len(rows) >= 2:
            for row in rows[1:]:
                if len(row) > 1 and row[1] == toilet_name:
                    address = (row[2] if len(row) > 2 else "") or "未知地址"
                    break

        if address == "未知地址":
            return render_template("toilet_feedback.html", toilet_name=toilet_name,
                                   summary="請改用座標版入口（卡片上的『查詢回饋（座標）』）。")

        # 舊邏輯：以地址聚合
        try:
            rows_f, idx = load_feedback_rows()
            if not rows_f or not idx or idx.get("address") is None:
                return render_template("toilet_feedback.html", toilet_name=toilet_name, summary="讀取錯誤")
            data = rows_f[1:]
            matched = [r for r in data if len(r) > idx["address"] and str(r[idx["address"]]).strip() == address.strip()]
            if not matched:
                return render_template("toilet_feedback.html", toilet_name=toilet_name, summary="尚無回饋資料")

            paper_counts = {"有": 0, "沒有": 0}
            access_counts = {"有": 0, "沒有": 0}
            score_sum = 0.0
            valid = 0
            comments = []

            for r in matched:
                if idx.get("predicted") is not None and len(r) > idx["predicted"]:
                    try:
                        score_sum += float(r[idx["predicted"]]); valid += 1
                    except:
                        pass
                if idx.get("toilet_paper") is not None and len(r) > idx["toilet_paper"]:
                    p = (r[idx["toilet_paper"]] or "").strip()
                    if p in paper_counts: paper_counts[p] += 1
                if idx.get("accessibility") is not None and len(r) > idx["accessibility"]:
                    a = (r[idx["accessibility"]] or "").strip()
                    if a in access_counts: access_counts[a] += 1
                if idx.get("comment") is not None and len(r) > idx["comment"]:
                    c = (r[idx["comment"]] or "").strip()
                    if c: comments.append(c)

            avg = round(score_sum/valid, 2) if valid else "未預測"
            summary = f"🔍 筆數：{len(matched)}\n🧼 平均清潔分數：{avg}\n🧻 衛生紙：{'有' if paper_counts['有']>=paper_counts['沒有'] else '沒有'}\n♿ 無障礙：{'有' if access_counts['有']>=access_counts['沒有'] else '沒有'}\n"
            if comments: summary += f"💬 最新留言：{comments[-1]}"
            return render_template("toilet_feedback.html", toilet_name=toilet_name, summary=summary)
        except Exception:
            return render_template("toilet_feedback.html", toilet_name=toilet_name, summary="讀取錯誤")
    except Exception as e:
        logging.error(f"❌ 渲染回饋頁面錯誤: {e}")
        return "查詢失敗", 500

# === 新路由：以座標顯示（推薦） ===
@app.route("/toilet_feedback_by_coord/<lat>/<lon>")
def toilet_feedback_by_coord(lat, lon):
    try:
        name = f"廁所（{lat}, {lon}）"
        summary = get_feedback_summary_by_coord(lat, lon)
        return render_template("toilet_feedback.html", toilet_name=name, summary=summary)
    except Exception as e:
        logging.error(f"❌ 渲染回饋頁面（座標）錯誤: {e}")
        return "查詢失敗", 500

# === 趨勢 API（名稱版保留） ===
@app.route("/get_clean_trend/<toilet_name>")
def get_clean_trend(toilet_name):
    try:
        if toilet_name == "無名稱":
            return {"success": False, "data": []}, 404

        rows = worksheet.get_all_values()
        address = None
        if rows and len(rows) >= 2:
            for row in rows[1:]:
                if len(row) > 1 and row[1] == toilet_name:
                    address = (row[2] if len(row) > 2 else "") or None
                    break
        if not address:
            return {"success": False, "data": []}, 404

        rows_f, idx = load_feedback_rows()
        if not rows_f or not idx or idx.get("address") is None or idx.get("predicted") is None:
            return {"success": False, "data": []}, 503

        data = []
        for r in rows_f[1:]:
            if len(r) > max(idx["address"], idx["predicted"]) and str(r[idx["address"]]).strip() == address.strip():
                try:
                    data.append({"score": float(r[idx["predicted"]])})
                except:
                    pass

        return {"success": True, "data": data}
    except Exception as e:
        logging.error(f"❌ 清潔度趨勢 API 錯誤: {e}")
        return {"success": False, "data": []}, 500

# === 趨勢 API（座標版，推薦） ===
@app.route("/get_clean_trend_by_coord/<lat>/<lon>")
def get_clean_trend_by_coord(lat, lon):
    try:
        rows, idx = load_feedback_rows()
        if not rows or not idx or idx.get("lat") is None or idx.get("lon") is None or idx.get("predicted") is None:
            return {"success": False, "data": []}, 503

        def close(a, b, tol=1e-6):
            try: return abs(float(a) - float(b)) <= tol
            except: return False

        out = []
        for r in rows[1:]:
            if len(r) <= max(idx["lat"], idx["lon"], idx["predicted"]):
                continue
            if close(r[idx["lat"]], lat) and close(r[idx["lon"]], lon):
                try:
                    out.append({"score": float(r[idx["predicted"]])})
                except:
                    pass

        return {"success": True, "data": out}
    except Exception as e:
        logging.error(f"❌ 趨勢 API（座標）錯誤: {e}")
        return {"success": False, "data": []}, 500

# === Flex Message（全面帶座標；地址可空） ===
def create_toilet_flex_messages(toilets, show_delete=False, uid=None):
    bubbles = []
    for toilet in toilets[:5]:
        actions = []

        lat_s = norm_coord(toilet['lat'])
        lon_s = norm_coord(toilet['lon'])
        addr_text = toilet.get('address') or "（無地址，使用座標）"

        # 導航
        actions.append({
            "type": "uri",
            "label": "導航",
            "uri": f"https://www.google.com/maps/search/?api=1&query={lat_s},{lon_s}"
        })

        # 查詢回饋（座標）
        actions.append({
            "type": "uri",
            "label": "查詢回饋（座標）",
            "uri": f"https://school-i9co.onrender.com/toilet_feedback_by_coord/{lat_s}/{lon_s}"
        })

        # 回饋表單（座標帶在 querystring）
        addr_param = quote(toilet.get('address') or "")
        actions.append({
            "type": "uri",
            "label": "廁所回饋",
            "uri": (
                "https://school-i9co.onrender.com/feedback_form/"
                f"{quote(toilet['name'])}/{addr_param}"
                f"?lat={lat_s}&lon={lon_s}"
            )
        })

        # 最愛
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

        # 刪除（目前僅移除最愛）
        if show_delete and toilet.get("type") == "user" and uid:
            actions.append({
                "type": "postback",
                "label": "刪除廁所",
                "data": f"confirm_delete:{quote(toilet['name'])}:{addr_param}:{lat_s}:{lon_s}"
            })

        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {"type": "text", "text": toilet['name'], "weight": "bold", "size": "lg", "wrap": True},
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

# === 使用者位置 ===
user_locations = {}
pending_delete_confirm = {}

# === TextMessage ===
@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    text = event.message.text.strip().lower()
    uid = event.source.user_id
    reply_messages = []

    if uid in pending_delete_confirm:
        info = pending_delete_confirm[uid]
        if text == "確認刪除":
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
            toilets = query_sheet_toilets(lat, lon) + query_overpass_toilets(lat, lon)
            if not toilets:
                reply_messages.append(TextSendMessage(text="附近沒有廁所，可能要原地解放了 💦"))
            else:
                msg = create_toilet_flex_messages(toilets, show_delete=True, uid=uid)
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

    elif text == "新增廁所":
        reply_messages.append(TextSendMessage(text="請前往此頁新增廁所：\nhttps://school-i9co.onrender.com/add"))

    elif text == "回饋":
        form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
        reply_messages.append(TextSendMessage(text=f"💡 請透過下列連結回報問題或提供意見：\n{form_url}"))

    if reply_messages:
        try:
            line_bot_api.reply_message(event.reply_token, reply_messages)
        except Exception as e:
            logging.error(f"❌ 回覆訊息失敗（TextMessage）: {e}")

# === LocationMessage ===
@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
    uid = event.source.user_id
    lat = event.message.latitude
    lon = event.message.longitude
    user_locations[uid] = (lat, lon)
    try:
        line_bot_api.reply_message(event.reply_token, TextSendMessage(text="✅ 位置已更新"))
    except Exception as e:
        logging.error(f"❌ 回覆位置訊息失敗: {e}")

# === Postback ===
@handler.add(PostbackEvent)
def handle_postback(event):
    uid = event.source.user_id
    data = event.postback.data

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
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=f"✅ 已收藏 {name}"))

        elif data.startswith("remove_fav:"):
            _, qname, lat, lon = data.split(":", 3)
            name = unquote(qname)
            success = remove_from_favorites(uid, name, lat, lon)
            msg = "✅ 已移除最愛" if success else "❌ 移除失敗"
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=msg))

        elif data.startswith("confirm_delete:"):
            _, qname, qaddr, lat, lon = data.split(":", 4)
            name = unquote(qname)
            address = unquote(qaddr)
            pending_delete_confirm[uid] = {
                "name": name,
                "address": address,
                "lat": norm_coord(lat),
                "lon": norm_coord(lon)
            }
            line_bot_api.reply_message(event.reply_token, [
                TextSendMessage(text=f"⚠️ 確定要刪除 {name} 嗎？（目前刪除為移除最愛）"),
                TextSendMessage(text="請輸入『確認刪除』或『取消』")
            ])
    except Exception as e:
        logging.error(f"❌ 處理 postback 失敗: {e}")

# === 新增廁所頁面 ===
@app.route("/add", methods=["GET"])
def render_add_page():
    return render_template("submit_toilet.html")

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
