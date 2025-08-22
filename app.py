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
import pandas as pd  # 用於消除 sklearn feature name 警告

# === 初始化 ===
load_dotenv()
logging.basicConfig(level=logging.INFO)
app = Flask(__name__)
CORS(app)

line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

# 檔案路徑（僅保留 favorites.txt；CSV 不再做查詢來源）
DATA_DIR = os.path.join(os.getcwd(), "data")
TOILETS_FILE_PATH = os.path.join(DATA_DIR, "public_toilets.csv")  # 仍保留備份用途（非查詢）
FAVORITES_FILE_PATH = os.path.join(DATA_DIR, "favorites.txt")

# 確保資料夾與 favorites 檔存在
os.makedirs(DATA_DIR, exist_ok=True)
if not os.path.exists(FAVORITES_FILE_PATH):
    open(FAVORITES_FILE_PATH, "a", encoding="utf-8").close()

# === Google Sheets 設定 ===
GSHEET_SCOPE = ['https://spreadsheets.google.com/feeds', 'https://www.googleapis.com/auth/drive']
GSHEET_CREDENTIALS_JSON = os.getenv("GSHEET_CREDENTIALS_JSON")
TOILET_SPREADSHEET_ID = "1Vg3tiqlXcXjcic2cAWCG-xTXfNzcI7wegEnZx8Ak7ys"  # 廁所主資料（唯一來源）
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

# === 公用：座標標準化，避免浮點誤差（作為字串鍵）===
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
        worksheet = gc.open_by_key(TOILET_SPREADSHEET_ID).sheet1      # 主資料（使用者新增）
        feedback_sheet = gc.open_by_key(FEEDBACK_SPREADSHEET_ID).sheet1  # 回饋/預測
        logging.info("✅ Sheets 初始化完成")
    except Exception as e:
        logging.critical(f"❌ Sheets 初始化失敗: {e}")
        raise  # 直接中止，因為我們以 Sheets 為唯一資料來源

init_gsheet()

# === 回饋表固定欄位表頭（避免 get_all_records() 因空白/重複欄名報錯） ===
FEEDBACK_HEADERS = [
    "name", "地址", "rating", "是否有衛生紙", "是否有無障礙設施",
    "使用時間", "留言", "預測分數", "lat", "lon", "created_at"
]

# === 計算距離 ===
def haversine(lat1, lon1, lat2, lon2):
    try:
        lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
        dlat = lat2 - lat1
        dlon = lon2 - lon1
        a = sin(dlat / 2)**2 + cos(lat1) * cos(lat2) * sin(dlon / 2)**2
        return 2 * asin(sqrt(a)) * 6371000  # 地球半徑為 6371000 公尺
    except Exception as e:
        logging.error(f"計算距離失敗: {e}")
        return 0

# === 從 Google Sheets 查使用者新增廁所（唯一來源，取代本地 CSV） ===
def query_sheet_toilets(user_lat, user_lon, radius=500):
    toilets = []
    try:
        rows = worksheet.get_all_values()  # 第一列多半是標題
        header, data = rows[0], rows[1:]
        # 假設欄位順序：[uid, name, address, lat, lon, created_at]
        for row in data:
            if len(row) < 5:
                continue
            name = (row[1] if len(row) > 1 else "").strip()
            address = (row[2] if len(row) > 2 else "").strip()
            try:
                t_lat = float(row[3]); t_lon = float(row[4])
            except:
                continue
            dist = haversine(user_lat, user_lon, t_lat, t_lon)
            if dist <= radius:
                toilets.append({
                    "name": name or "無名稱",
                    "lat": float(norm_coord(t_lat)),
                    "lon": float(norm_coord(t_lon)),
                    "address": address or "",
                    "distance": dist,
                    "type": "sheet"
                })
    except Exception as e:
        logging.error(f"讀取 Google Sheets 廁所主資料錯誤: {e}")
    return sorted(toilets, key=lambda x: x["distance"])

# === 查 OpenStreetMap 廁所資料 ===
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
        # OSM 常常沒有地址，這裡允許空
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

# === 最愛管理（lat/lon 一律用標準化字串，避免精度誤差） ===
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

# === 地址轉經緯度（新增廁所時用；回饋不強制地址） ===
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

# === 附近廁所 API（來源：OSM + Google Sheets） ===
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

# === 使用者新增廁所（寫 Google Sheets；CSV 僅備份可選） ===
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

        # 寫入 Google Sheets（唯一來源）
        worksheet.append_row([
            uid, name, address,
            float(norm_coord(lat)), float(norm_coord(lon)),
            datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")
        ])
        logging.info(f"✅ 廁所資料已寫入 Google Sheets: {name}")

        # （可選）備份到本地 CSV（不做查詢來源）
        try:
            if not os.path.exists(TOILETS_FILE_PATH):
                open(TOILETS_FILE_PATH, "a", encoding="utf-8").close()
            with open(TOILETS_FILE_PATH, "a", encoding="utf-8", newline="") as f:
                writer = csv.writer(f)
                writer.writerow([
                    "00000","0000000","未知里","USERADD", name, address, "使用者補充",
                    norm_coord(lat), norm_coord(lon),
                    "普通級","公共場所","未知","使用者","0",""
                ])
        except Exception as e:
            logging.warning(f"備份至本地 CSV 失敗：{e}")

        return {"success": True, "message": f"✅ 已新增廁所 {name}"}

    except Exception as e:
        logging.error(f"❌ 新增廁所錯誤:\n{traceback.format_exc()}")
        return {"success": False, "message": "伺服器錯誤"}, 500

# === 顯示自建回饋表單 HTML（地址可空，座標從 querystring 帶） ===
@app.route("/feedback_form/<toilet_name>/<address>")
def feedback_form(toilet_name, address):
    return render_template("feedback_form.html", toilet_name=toilet_name, address=address)

# === 提交回饋表單（必須帶 lat/lon；地址可空；寫 Google Sheets） ===
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
        features = [r, paper_map.get(toilet_paper, 0), access_map.get(accessibility, 0)]

        predicted_score = predict_cleanliness(features)

        feedback_sheet.append_row([
            name, address, rating, toilet_paper, accessibility, time_of_use,
            comment, predicted_score, lat, lon, datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")
        ])

        return redirect(url_for("feedback_form", toilet_name=name, address=address or ""))

    except Exception as e:
        logging.error(f"❌ 提交回饋表單錯誤: {e}")
        return "提交失敗", 500

# === 清潔度預測函式（用 DataFrame 包裝以消警告） ===
def predict_cleanliness(features):
    try:
        if cleanliness_model is None or label_encoder is None:
            return "未預測"
        X = pd.DataFrame([features], columns=["rating", "paper", "access"])
        probs = cleanliness_model.predict_proba(X)[0]
        try:
            classes_enc = cleanliness_model.classes_
            labels = label_encoder.inverse_transform(classes_enc.astype(int))
        except Exception:
            labels = cleanliness_model.classes_
        expected = round(sum(float(p) * float(l) for p, l in zip(probs, labels)), 2)
        return expected
    except Exception as e:
        logging.error(f"❌ 清潔度預測錯誤: {e}")
        return "未預測"

# === 以座標聚合的統計 ===
def get_feedback_summary_by_coord(lat, lon, tol=1e-6):
    try:
        records = feedback_sheet.get_all_records(expected_headers=FEEDBACK_HEADERS)
        def close(a, b):
            try: return abs(float(a) - float(b)) <= tol
            except: return False
        matched = [r for r in records if close(r.get("lat"), lat) and close(r.get("lon"), lon)]
        if not matched:
            return "尚無回饋資料"

        paper_counts = {"有": 0, "沒有": 0}
        access_counts = {"有": 0, "沒有": 0}
        score_sum = 0
        valid_score_count = 0
        comments = []

        for r in matched:
            s = r.get("預測分數") or r.get("cleanliness_score")
            try:
                score_sum += float(s)
                valid_score_count += 1
            except:
                pass
            p = str(r.get("是否有衛生紙", "")).strip()
            if p in paper_counts:
                paper_counts[p] += 1
            a = str(r.get("是否有無障礙設施", "")).strip()
            if a in access_counts:
                access_counts[a] += 1
            c = str(r.get("留言", "")).strip()
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

# === 舊路由（以名稱找地址）仍保留，但不再依賴 CSV：改用主資料表找第一筆同名地址 ===
@app.route("/toilet_feedback/<toilet_name>")
def toilet_feedback(toilet_name):
    try:
        address = "未知地址"
        # 從主資料表找第一筆同名（若無地址，顯示提示）
        rows = worksheet.get_all_values()
        header, data = rows[0], rows[1:]
        for row in data:
            if len(row) > 1 and row[1] == toilet_name:
                address = (row[2] if len(row) > 2 else "") or "未知地址"
                break
        # 若地址為未知，提示改用座標版
        if address == "未知地址":
            return render_template("toilet_feedback.html", toilet_name=toilet_name, summary="請改用座標版入口（卡片上的『查詢回饋（座標）』）。")

        # 名稱版相容：以地址聚合
        try:
            records = feedback_sheet.get_all_records(expected_headers=FEEDBACK_HEADERS)
            matched = [r for r in records if str(r.get("地址", "")).strip() == address.strip()]
            if not matched:
                return render_template("toilet_feedback.html", toilet_name=toilet_name, summary="尚無回饋資料")

            paper_counts = {"有": 0, "沒有": 0}
            access_counts = {"有": 0, "沒有": 0}
            score_sum = 0; valid = 0; comments = []
            for r in matched:
                s = r.get("預測分數") or r.get("cleanliness_score")
                try: score_sum += float(s); valid += 1
                except: pass
                p = str(r.get("是否有衛生紙", "")).strip()
                if p in paper_counts: paper_counts[p] += 1
                a = str(r.get("是否有無障礙設施", "")).strip()
                if a in access_counts: access_counts[a] += 1
                c = str(r.get("留言", "")).strip()
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

# === 新路由：以座標顯示回饋摘要（推薦使用） ===
@app.route("/toilet_feedback_by_coord/<lat>/<lon>")
def toilet_feedback_by_coord(lat, lon):
    try:
        name = f"廁所（{lat}, {lon}）"
        summary = get_feedback_summary_by_coord(lat, lon)
        return render_template("toilet_feedback.html", toilet_name=name, summary=summary)
    except Exception as e:
        logging.error(f"❌ 渲染回饋頁面（座標）錯誤: {e}")
        return "查詢失敗", 500

# === 清潔度趨勢 API（名稱版相容 + 座標版） ===
@app.route("/get_clean_trend/<toilet_name>")
def get_clean_trend(toilet_name):
    try:
        if toilet_name == "無名稱":
            return {"success": False, "data": []}, 404

        # 改用主資料表找地址；若無則回空
        rows = worksheet.get_all_values()
        header, data = rows[0], rows[1:]
        address = None
        for row in data:
            if len(row) > 1 and row[1] == toilet_name:
                address = (row[2] if len(row) > 2 else "") or None
                break
        if not address:
            return {"success": False, "data": []}, 404

        if not feedback_sheet:
            return {"success": False, "data": []}, 503

        records = feedback_sheet.get_all_records(expected_headers=FEEDBACK_HEADERS)
        matched = [r for r in records if str(r.get("地址", "")).strip() == address.strip()]

        data_out = []
        for r in matched:
            s = r.get("預測分數") or r.get("cleanliness_score")
            try:
                data_out.append({"score": float(s)})
            except:
                continue

        return {"success": True, "data": data_out}
    except Exception as e:
        logging.error(f"❌ 清潔度趨勢 API 錯誤: {e}")
        return {"success": False, "data": []}, 500

@app.route("/get_clean_trend_by_coord/<lat>/<lon>")
def get_clean_trend_by_coord(lat, lon):
    try:
        if not feedback_sheet:
            return {"success": False, "data": []}, 503
        records = feedback_sheet.get_all_records(expected_headers=FEEDBACK_HEADERS)
        def close(a, b, tol=1e-6):
            try: return abs(float(a) - float(b)) <= tol
            except: return False
        matched = [r for r in records if close(r.get("lat"), lat) and close(r.get("lon"), lon)]
        data = []
        for r in matched:
            s = r.get("預測分數") or r.get("cleanliness_score")
            try:
                data.append({"score": float(s)})
            except:
                continue
        return {"success": True, "data": data}
    except Exception as e:
        logging.error(f"❌ 趨勢 API（座標）錯誤: {e}")
        return {"success": False, "data": []}, 500

# === 建立 Flex Message（全面帶座標；地址可空；postback 安全編碼） ===
def create_toilet_flex_messages(toilets, show_delete=False, uid=None):
    bubbles = []
    for toilet in toilets[:5]:
        actions = []

        lat_s = norm_coord(toilet['lat'])
        lon_s = norm_coord(toilet['lon'])
        addr_text = toilet.get('address') or "（無地址，使用座標）"

        # ✅ 導航
        actions.append({
            "type": "uri",
            "label": "導航",
            "uri": f"https://www.google.com/maps/search/?api=1&query={lat_s},{lon_s}"
        })

        # ✅ 查詢回饋（座標版）
        actions.append({
            "type": "uri",
            "label": "查詢回饋（座標）",
            "uri": f"https://school-i9co.onrender.com/toilet_feedback_by_coord/{lat_s}/{lon_s}"
        })

        # ✅ 廁所回饋（帶座標；地址可空）
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

        # 加入最愛 / 移除最愛（名稱 quote，座標標準化）
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

        # 刪除（若未實作真的刪主資料，建議更名為「移除最愛」）
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
                    {
                        "type": "button",
                        "style": "primary",
                        "height": "sm",
                        "action": actions[0]
                    }
                ] + [
                    {
                        "type": "button",
                        "style": "secondary",
                        "height": "sm",
                        "action": a
                    } for a in actions[1:]
                ]
            }
        }
        bubbles.append(bubble)

    return {"type": "carousel", "contents": bubbles}

# === Webhook 設定 ===
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

# === 處理 TextMessage（回饋一定會回覆；附近廁所改讀 Sheets） ===
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

    # ✅ 最後統一回覆一次
    if reply_messages:
        try:
            line_bot_api.reply_message(event.reply_token, reply_messages)
        except Exception as e:
            logging.error(f"❌ 回覆訊息失敗（TextMessage）: {e}")

# === 處理 LocationMessage ===
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

# === 處理 Postback（名稱 quote/解析；座標字串標準化） ===
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

# === 背景排程：預留（僅示意） ===
def auto_predict_cleanliness_background():
    while True:
        try:
            logging.info("🌀 背景排程啟動中（未來可加入自動統計）")
        except Exception as e:
            logging.error(f"❌ 背景任務出錯：{e}")
        time.sleep(1800)  # 每半時執行一次

# === 啟動應用程式 ===
if __name__ == "__main__":
    # 只在主行程啟動背景執行緒（避免多進程重複）
    threading.Thread(target=auto_predict_cleanliness_background, daemon=True).start()
    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
