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
from urllib.parse import quote
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

# === 初始化 ===
load_dotenv()
logging.basicConfig(level=logging.INFO)
app = Flask(__name__)
CORS(app)

line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

TOILETS_FILE_PATH = os.path.join(os.getcwd(), "data", "public_toilets.csv")
FAVORITES_FILE_PATH = os.path.join(os.getcwd(), "data", "favorites.txt")

# === Google Sheets 設定 ===
GSHEET_SCOPE = ['https://spreadsheets.google.com/feeds', 'https://www.googleapis.com/auth/drive']
GSHEET_CREDENTIALS_JSON = os.getenv("GSHEET_CREDENTIALS_JSON")
TOILET_SPREADSHEET_ID = os.getenv("TOILET_SPREADSHEET_ID")  # 廁所主資料
FEEDBACK_SPREADSHEET_ID = os.getenv("TOILET_FEEDBACK_SHEET_ID")  # 新回饋表單 Sheet

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

# === 初始化 Google Sheets ===
def init_gsheet():
    global gc, worksheet, feedback_sheet
    try:
        if not GSHEET_CREDENTIALS_JSON:
            logging.error("❌ 缺少憑證設定")
            return
        creds_dict = json.loads(GSHEET_CREDENTIALS_JSON)
        creds = ServiceAccountCredentials.from_json_keyfile_dict(creds_dict, GSHEET_SCOPE)
        gc = gspread.authorize(creds)
        worksheet = gc.open_by_key(TOILET_SPREADSHEET_ID).sheet1
        feedback_sheet = gc.open_by_key(FEEDBACK_SPREADSHEET_ID).sheet1
        logging.info("✅ Sheets 初始化完成")
        
        # 測試是否可以成功讀取資料
        worksheet_data = worksheet.get_all_records()
        feedback_data = feedback_sheet.get_all_records()
        logging.info(f"工作表數據：{worksheet_data}")
        logging.info(f"回饋表數據：{feedback_data}")
        
    except Exception as e:
        logging.error(f"❌ Sheets 初始化失敗: {e}")


init_gsheet()
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

# === 查本地廁所資料 ===
def query_local_toilets(lat, lon, radius=500):
    toilets = []
    try:
        with open(TOILETS_FILE_PATH, 'r', encoding='utf-8') as file:
            reader = csv.reader(file)
            next(reader, None)  # skip header
            for row in reader:
                if len(row) != 15:
                    continue
                _, _, _, _, name, address, _, t_lat, t_lon, *_ = row
                try:
                    t_lat, t_lon = float(t_lat), float(t_lon)
                    dist = haversine(lat, lon, t_lat, t_lon)
                    if dist <= radius:
                        toilets.append({
                            "name": name or "無名稱",
                            "lat": t_lat,
                            "lon": t_lon,
                            "address": address or "無地址",
                            "distance": dist,
                            "type": "local"
                        })
                except Exception as e:
                    logging.warning(f"無法處理資料列: {e}")
    except Exception as e:
        logging.error(f"讀取本地 CSV 錯誤: {e}")
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
        resp = requests.post("https://overpass-api.de/api/interpreter", data=query, headers={"User-Agent": "ToiletBot/1.0"}, timeout=10)
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
        address = elem.get("tags", {}).get("name", f"{t_lat},{t_lon}")
        toilets.append({
            "name": name,
            "lat": t_lat,
            "lon": t_lon,
            "address": address,
            "distance": haversine(lat, lon, t_lat, t_lon),
            "type": "osm"
        })
    return sorted(toilets, key=lambda x: x["distance"])

# === 最愛管理 ===
def add_to_favorites(uid, toilet):
    try:
        with open(FAVORITES_FILE_PATH, "a", encoding="utf-8") as f:
            f.write(f"{uid},{toilet['name']},{toilet['lat']},{toilet['lon']},{toilet['address']}\n")
    except Exception as e:
        logging.error(f"加入最愛失敗: {e}")

def remove_from_favorites(uid, name, lat, lon):
    try:
        with open(FAVORITES_FILE_PATH, "r", encoding="utf-8") as f:
            lines = f.readlines()
        with open(FAVORITES_FILE_PATH, "w", encoding="utf-8") as f:
            for line in lines:
                data = line.strip().split(',')
                if not (data[0] == uid and data[1] == name and data[2] == str(lat) and data[3] == str(lon)):
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
        headers = { "User-Agent": "ToiletBot/1.0" }
        resp = requests.get(url, headers=headers)
        data = resp.json()
        if resp.status_code == 200 and data:
            return float(data[0]['lat']), float(data[0]['lon'])
    except Exception as e:
        logging.error(f"地址轉經緯度失敗: {e}")
    return None, None

# === 寫入本地 CSV 廁所資料 ===
def add_to_toilets_file(name, address, lat, lon):
    try:
        new_row = f"00000,0000000,未知里,USERADD,{name},{address},使用者補充,{lat},{lon},普通級,公共場所,未知,使用者,0,\n"
        with open(TOILETS_FILE_PATH, "a", encoding="utf-8") as f:
            f.write(new_row)
        logging.info(f"✅ 新增至本地 CSV：{name} @ {address}")
    except Exception as e:
        logging.error(f"寫入本地 CSV 失敗: {e}")
# === 顯示自建回饋表單 HTML ===
@app.route("/feedback_form/<toilet_name>/<address>")
def feedback_form(toilet_name, address):
    return render_template("feedback_form.html", toilet_name=toilet_name, address=address)

# === 提交回饋表單，寫入 Google Sheets ===
@app.route("/submit_feedback", methods=["POST"])
def submit_feedback():
    try:
        data = request.form
        name = data.get("name", "").strip()
        address = data.get("address", "").strip()
        rating = data.get("rating", "").strip()
        toilet_paper = data.get("toilet_paper", "").strip()
        accessibility = data.get("accessibility", "").strip()
        time_of_use = data.get("time_of_use", "").strip()
        comment = data.get("comment", "").strip()

        if not all([name, address, rating]):
            return "缺少必要欄位", 400

        # 清潔度轉數值
        rating_map = {"乾淨": 5, "普通": 3, "髒亂": 1}
        paper_map = {"有": 1, "沒有": 0}
        access_map = {"有": 1, "沒有": 0}
        r = rating_map.get(rating)
        p = paper_map.get(toilet_paper, 0)
        a = access_map.get(accessibility, 0)
        features = [r, p, a]

        predicted_score = predict_cleanliness(features)

        row = [name, address, rating, toilet_paper, accessibility, time_of_use, comment, predicted_score]
        feedback_sheet.append_row(row)
        return redirect(url_for("feedback_form", toilet_name=name, address=address))
    except Exception as e:
        logging.error(f"❌ 提交回饋表單錯誤: {e}")
        return "提交失敗", 500

# === 清潔度預測函式 ===
def predict_cleanliness(features):
    try:
        if cleanliness_model is None or label_encoder is None:
            return "未預測"
        probs = cleanliness_model.predict_proba([features])[0]
        labels = label_encoder.inverse_transform(range(len(probs)))
        expected = round(sum(p * l for p, l in zip(probs, labels)), 2)
        return expected
    except Exception as e:
        logging.error(f"❌ 清潔度預測錯誤: {e}")
        return "未預測"
# === 查詢某地址的所有回饋統計（從 Google Sheet） ===
def get_feedback_summary_by_address(address):
    try:
        records = feedback_sheet.get_all_records()
        matched = [r for r in records if str(r.get("地址", "")).strip() == address.strip()]
        if not matched:
            return "尚無回饋資料"

        total = len(matched)
        rating_map = {"乾淨": 5, "普通": 3, "髒亂": 1}
        paper_counts = {"有": 0, "沒有": 0}
        access_counts = {"有": 0, "沒有": 0}
        score_sum = 0
        valid_score_count = 0
        comments = []

        for r in matched:
            # 清潔度預測分數
            score = r.get("預測分數") or r.get("cleanliness_score")
            try:
                score_sum += float(score)
                valid_score_count += 1
            except:
                pass

            # 衛生紙
            p = r.get("是否有衛生紙", "").strip()
            if p in paper_counts:
                paper_counts[p] += 1

            # 無障礙
            a = r.get("是否有無障礙設施", "").strip()
            if a in access_counts:
                access_counts[a] += 1

            # 留言
            c = r.get("留言", "").strip()
            if c:
                comments.append(c)

        avg_score = round(score_sum / valid_score_count, 2) if valid_score_count else "未預測"

        summary = f"🔍 統計筆數：{total} 筆\n"
        summary += f"🧼 平均清潔分數：{avg_score}\n"
        summary += f"🧻 衛生紙：{'有' if paper_counts['有'] >= paper_counts['沒有'] else '沒有'}\n"
        summary += f"♿ 無障礙：{'有' if access_counts['有'] >= access_counts['沒有'] else '沒有'}\n"
        if comments:
            summary += f"💬 最新留言：{comments[-1]}"
        return summary

    except Exception as e:
        logging.error(f"❌ 查詢回饋統計錯誤: {e}")
        return "讀取錯誤"

# === 查詢回饋頁面（HTML 渲染） ===
@app.route("/toilet_feedback/<toilet_name>")
def toilet_feedback(toilet_name):
    try:
        # 從本地 CSV 找到該廁所對應的地址
        address = "未知地址"
        with open(TOILETS_FILE_PATH, "r", encoding="utf-8") as f:
            for line in f.readlines()[1:]:
                parts = line.strip().split(",")
                if len(parts) >= 6 and parts[4] == toilet_name:
                    address = parts[5]
                    break

        records = feedback_sheet.get_all_records()
        feedbacks = []
        for r in records:
            if str(r.get("地址", "")).strip() == address.strip():
                feedbacks.append({
                    "rating": r.get("評分", r.get("rating", "")),
                    "toilet_paper": r.get("是否有衛生紙", r.get("toilet_paper", "")),
                    "accessibility": r.get("是否有無障礙設施", r.get("accessibility", "")),
                    "time_of_use": r.get("使用時間", r.get("time_of_use", "")),
                    "comment": r.get("留言", r.get("comment", "")),
                    "cleanliness_score": r.get("預測分數", r.get("cleanliness_score", ""))
                })

        return render_template("feedback_page.html", toilet_name=toilet_name, address=address, feedbacks=feedbacks)
    except Exception as e:
        logging.error(f"❌ 渲染 feedback_page.html 錯誤: {e}")
        return "查詢失敗", 500

# === 建立 Flex Message ===
def create_toilet_flex_messages(toilets, show_delete=False, uid=None):
    bubbles = []
    for toilet in toilets[:5]:
        actions = []

        # ✅ 導航按鈕
        actions.append({
            "type": "uri",
            "label": "導航",
            "uri": f"https://www.google.com/maps/search/?api=1&query={toilet['lat']},{toilet['lon']}"
        })

        # ✅ 查詢回饋按鈕（跳轉至 Flex 概覽頁）
        actions.append({
            "type": "uri",
            "label": "查詢回饋",
            "uri": f"https://school-i9co.onrender.com/toilet_feedback/{quote(toilet['name'])}"
        })

        # ✅ 廁所回饋按鈕（跳轉至自建表單）
        addr_param = quote(toilet['address'] or f"{toilet['lat']},{toilet['lon']}")
        actions.append({
            "type": "uri",
            "label": "廁所回饋",
            "uri": f"https://school-i9co.onrender.com/feedback_form/{quote(toilet['name'])}/{addr_param}"
        })

        # 加入最愛 / 移除最愛
        if toilet.get("type") == "favorite" and uid:
            actions.append({
                "type": "postback",
                "label": "移除最愛",
                "data": f"remove_fav:{toilet['name']}:{toilet['lat']}:{toilet['lon']}"
            })
        elif toilet.get("type") not in ["user", "favorite"] and uid:
            actions.append({
                "type": "postback",
                "label": "加入最愛",
                "data": f"add:{toilet['name']}:{toilet['lat']}:{toilet['lon']}"
            })

        # 刪除（限 user 新增）
        if show_delete and toilet.get("type") == "user" and uid:
            actions.append({
                "type": "postback",
                "label": "刪除廁所",
                "data": f"confirm_delete:{toilet['name']}:{toilet['address']}:{toilet['lat']}:{toilet['lon']}"
            })

        # Bubble 格式
        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {"type": "text", "text": toilet['name'], "weight": "bold", "size": "lg", "wrap": True},
                    {"type": "text", "text": toilet['address'] or "無地址", "size": "sm", "color": "#666666", "wrap": True},
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

# === 處理 TextMessage ===
@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    text = event.message.text.strip().lower()
    uid = event.source.user_id
    reply_messages = []

    if uid in pending_delete_confirm:
        info = pending_delete_confirm[uid]
        if text == "確認刪除":
            # 刪除本地 CSV
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
            toilets = query_local_toilets(lat, lon) + query_overpass_toilets(lat, lon)
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
        reply_messages.append(TextSendMessage(text="請前往此頁新增廁所：\nhttps://your-domain.com/add"))

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

# === 處理 Postback ===
@handler.add(PostbackEvent)
def handle_postback(event):
    uid = event.source.user_id
    data = event.postback.data

    try:
        if data.startswith("add:"):
            _, name, lat, lon = data.split(":")
            toilet = {
                "name": name,
                "lat": float(lat),
                "lon": float(lon),
                "address": f"{lat},{lon}",
                "distance": 0,
                "type": "local"
            }
            add_to_favorites(uid, toilet)
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=f"✅ 已收藏 {name}"))
        elif data.startswith("remove_fav:"):
            _, name, lat, lon = data.split(":")
            success = remove_from_favorites(uid, name, lat, lon)
            msg = "✅ 已移除最愛" if success else "❌ 移除失敗"
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=msg))
        elif data.startswith("confirm_delete:"):
            _, name, address, lat, lon = data.split(":")
            pending_delete_confirm[uid] = {
                "name": name,
                "address": address,
                "lat": lat,
                "lon": lon
            }
            line_bot_api.reply_message(event.reply_token, [
                TextSendMessage(text=f"⚠️ 確定要刪除 {name} 嗎？"),
                TextSendMessage(text="請輸入『確認刪除』或『取消』")
            ])
    except Exception as e:
        logging.error(f"❌ 處理 postback 失敗: {e}")
# === 新增廁所頁面 ===
@app.route("/add", methods=["GET"])
def render_add_page():
    return render_template("submit_toilet.html")

# === 接收新增廁所表單 POST ===
@app.route("/submit_toilet", methods=["POST"])
def submit_toilet():
    try:
        data = request.get_json()
        uid = data.get("user_id")
        name = data.get("name")
        address = data.get("address")

        if not all([uid, name, address]):
            return {"success": False, "message": "缺少參數"}, 400

        lat, lon = geocode_address(address)
        if lat is None or lon is None:
            return {"success": False, "message": "地址轉換失敗"}, 400

        add_to_toilets_file(name, address, lat, lon)

        # 寫入主資料表
        if worksheet:
            try:
                worksheet.append_row([
                    uid, name, address, lat, lon,
                    datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")
                ])
            except Exception as e:
                logging.error(f"⚠️ 寫入 Google Sheets 失敗: {e}")
        return {"success": True, "message": f"✅ 已新增廁所 {name}"}

    except Exception as e:
        logging.error(f"❌ 新增廁所錯誤: {e}")
        return {"success": False, "message": "伺服器錯誤"}, 500
# === 背景排程：每小時自動預測未來清潔度（可擴充）===
import threading
import time

def auto_predict_cleanliness_background():
    while True:
        try:
            logging.info("🌀 背景排程啟動中（未來可加入自動統計）")
            # 預留未來功能，例如每小時做整體趨勢整理
        except Exception as e:
            logging.error(f"❌ 背景任務出錯：{e}")
        time.sleep(1800)  # 每半時執行一次

# === 清潔度趨勢 API ===
@app.route("/get_clean_trend/<toilet_name>")
def get_clean_trend(toilet_name):
    try:
        with open(TOILETS_FILE_PATH, "r", encoding="utf-8") as f:
            for line in f.readlines()[1:]:
                parts = line.strip().split(",")
                if len(parts) >= 6 and parts[4] == toilet_name:
                    address = parts[5]
                    break
            else:
                return {"success": False, "data": []}, 404

        records = feedback_sheet.get_all_records()
        matched = [r for r in records if str(r.get("地址", "")).strip() == address.strip()]

        data = []
        for r in matched:
            score = r.get("預測分數") or r.get("cleanliness_score")
            try:
                score_val = float(score)
                data.append({"score": score_val})
            except:
                continue

        return {"success": True, "data": data}
    except Exception as e:
        logging.error(f"❌ 清潔度趨勢 API 錯誤: {e}")
        return {"success": False, "data": []}, 500


# 啟動背景執行緒
threading.Thread(target=auto_predict_cleanliness_background, daemon=True).start()

# === 啟動應用程式 ===
if __name__ == "__main__":
    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
