import os
import csv
import json
import logging
import requests
import traceback
from math import radians, cos, sin, asin, sqrt
from flask_cors import CORS
from flask import Flask, request, abort, render_template
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
GSHEET_CREDENTIALS_JSON = os.getenv("GSHEET_CREDENTIALS_JSON")  # 放在環境變數中
GSHEET_SPREADSHEET_ID = "1Vg3tiqlXcXjcic2cAWCG-xTXfNzcI7wegEnZx8Ak7ys"

gc = sh = worksheet = None

def init_gsheet():
    global gc, sh, worksheet
    try:
        if not GSHEET_CREDENTIALS_JSON:
            logging.error("❌ GSHEET_CREDENTIALS_JSON 環境變數未設定")
            return
        credentials_dict = json.loads(GSHEET_CREDENTIALS_JSON)
        creds = ServiceAccountCredentials.from_json_keyfile_dict(credentials_dict, GSHEET_SCOPE)
        gc = gspread.authorize(creds)
        sh = gc.open_by_key(GSHEET_SPREADSHEET_ID)
        worksheet = sh.sheet1
        logging.info("✅ Google Sheets 初始化成功")
    except Exception as e:
        logging.error(f"❌ Google Sheets 初始化失敗: {e}")
        worksheet = None

def restore_csv_from_gsheet():
    if worksheet is None:
        logging.warning("🛑 無法從 Sheets 回復資料，因為 worksheet 尚未初始化")
        return
    try:
        records = worksheet.get_all_records()
        if not records:
            logging.info("📭 Google Sheets 沒有任何資料可回復")
            return

        os.makedirs(os.path.dirname(TOILETS_FILE_PATH), exist_ok=True)
        with open(TOILETS_FILE_PATH, "w", encoding="utf-8") as f:
            f.write("code,villagecode,village,source,name,address,note,lat,lon,level,category,open,provider,count,\n")
            for row in records:
                name = row['name']
                address = row['address']
                lat = row['lat']
                lon = row['lon']
                new_row = f"00000,0000000,未知里,USERADD,{name},{address},使用者補充,{lat},{lon},普通級,公共場所,未知,使用者,0,\n"
                f.write(new_row)
        logging.info("✅ 已從 Google Sheets 回復 public_toilets.csv")
    except Exception as e:
        logging.error(f"❌ 回復 CSV 失敗: {e}")

init_gsheet()
restore_csv_from_gsheet()


# === 本地檔案確認 ===
if not os.path.exists(TOILETS_FILE_PATH):
    logging.error(f"{TOILETS_FILE_PATH} 不存在")
else:
    logging.info(f"{TOILETS_FILE_PATH} 檔案存在")

def ensure_favorites_file():
    try:
        os.makedirs(os.path.dirname(FAVORITES_FILE_PATH), exist_ok=True)
        if not os.path.exists(FAVORITES_FILE_PATH):
            with open(FAVORITES_FILE_PATH, "w", encoding="utf-8"):
                pass
    except Exception as e:
        logging.error(f"建立 favorites.txt 時出錯: {e}")
        raise

ensure_favorites_file()

# === 全域資料 ===
user_locations = {}
MAX_DISTANCE = 500
MAX_TOILETS_REPLY = 5
pending_delete_confirm = {}

# === 計算距離 ===
def haversine(lat1, lon1, lat2, lon2):
    try:
        lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
        dlat = lat2 - lat1
        dlon = lon2 - lon1
        a = sin(dlat/2)**2 + cos(lat1) * cos(lat2) * sin(dlon/2)**2
        return 2 * asin(sqrt(a)) * 6371000
    except Exception as e:
        logging.error(f"計算距離錯誤: {e}")
        return 0

# === 查本地廁所資料 ===
def query_local_toilets(lat, lon):
    toilets = []
    try:
        with open(TOILETS_FILE_PATH, 'r', encoding='utf-8') as file:
            reader = csv.reader(file)
            next(reader, None)
            for row in reader:
                if len(row) != 15:
                    continue
                _, _, _, _, name, address, _, latitude, longitude, _, _, type_, _, _, _ = row
                try:
                    t_lat, t_lon = float(latitude), float(longitude)
                    dist = haversine(lat, lon, t_lat, t_lon)
                    if dist <= MAX_DISTANCE:
                        toilets.append({
                            "name": name or "無名稱",
                            "lat": t_lat,
                            "lon": t_lon,
                            "address": address or "",
                            "distance": dist,
                            "type": type_
                        })
                except Exception as e:
                    logging.error(f"處理 row 錯誤: {e}")
    except Exception as e:
        logging.error(f"讀取 CSV 錯誤: {e}")
    return sorted(toilets, key=lambda x: x['distance'])

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
        logging.error(f"Overpass 查詢失敗: {e}")
        return []

    toilets = []
    for elem in data.get("elements", []):
        if elem["type"] == "node":
            t_lat, t_lon = elem["lat"], elem["lon"]
        elif "center" in elem:
            t_lat, t_lon = elem["center"]["lat"], elem["center"]["lon"]
        else:
            continue
        toilets.append({
            "name": elem.get("tags", {}).get("name", "無名稱"),
            "lat": t_lat,
            "lon": t_lon,
            "address": "",
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
def geocode_address(address, user_name):
    try:
        url = f"https://nominatim.openstreetmap.org/search?format=json&q={requests.utils.quote(address)}"
        headers = { "User-Agent": "ToiletBot/1.0" }
        logging.info(f"📡 查詢地址：{address} → {url}")  # 加這行

        resp = requests.get(url, headers=headers)
        if resp.status_code != 200:
            logging.error(f"❌ Geocode API 回應碼: {resp.status_code}")
            return None, None, None
        data = resp.json()
        logging.info(f"📦 查詢結果：{data}")  # 加這行

        if resp.status_code == 200 and data:
            return user_name, float(data[0]['lat']), float(data[0]['lon'])
    except Exception as e:
        logging.error(f"地址解析失敗: {e}")
    return None, None, None


# === 寫入廁所 CSV 與 Sheets ===
def add_to_toilets_file(name, address, lat, lon):
    try:
        new_row = f"00000,0000000,未知里,USERADD,{name},{address},使用者補充,{lat},{lon},普通級,公共場所,未知,使用者,0,\n"
        with open(TOILETS_FILE_PATH, "a", encoding="utf-8") as f:
            f.write(new_row)
        logging.info(f"✅ 成功寫入本地 CSV：{name} @ {address}")
    except Exception as e:
        logging.error(f"寫入廁所資料失敗: {e}")
        raise


def add_to_gsheet(uid, name, address, lat, lon):
    if worksheet is None:
        logging.error("Sheets 未初始化")
        return False
    try:
        worksheet.append_row([uid, name, address, lat, lon, datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")])
        return True
    except Exception as e:
        logging.error(f"寫入 Sheets 失敗: {e}")
        return False

def delete_from_gsheet(uid, name, address, lat, lon):
    if worksheet is None:
        logging.error("Sheets 未初始化")
        return False
    try:
        records = worksheet.get_all_records()
        for idx, row in enumerate(records, start=2):
            if (str(row.get('user_id', '')) == uid and
                row.get('name', '') == name and
                row.get('address', '') == address and
                str(row.get('lat', '')) == str(lat) and
                str(row.get('lon', '')) == str(lon)):
                worksheet.delete_rows(idx)
                return True
        return False
    except Exception as e:
        logging.error(f"刪除 Sheets 失敗: {e}")
        return False

def get_recent_added(uid, limit=5):
    if worksheet is None:
        logging.error("Sheets 未初始化")
        return []
    try:
        records = worksheet.get_all_records()
        user_records = [r for r in records if str(r.get('user_id', '')) == uid]
        # 按 timestamp 倒序
        sorted_records = sorted(user_records, key=lambda r: r.get("timestamp", ""), reverse=True)
        recent = []
        for r in sorted_records[:limit]:
            recent.append({
                "name": r["name"],
                "address": r["address"],
                "lat": float(r["lat"]),
                "lon": float(r["lon"]),
                "distance": 0,
                "type": "user"  # 表示是用戶新增
            })
        return recent
    except Exception as e:
        logging.error(f"讀取最近新增失敗: {e}")
        return []

def delete_from_toilets_file(name, address, lat, lon):
    try:
        with open(TOILETS_FILE_PATH, "r", encoding="utf-8") as f:
            lines = f.readlines()
        with open(TOILETS_FILE_PATH, "w", encoding="utf-8") as f:
            f.write(lines[0])  # header
            for line in lines[1:]:
                parts = line.strip().split(',')
                if len(parts) < 15:
                    continue
                line_name = parts[4]
                line_address = parts[5]
                try:
                    line_lat = float(parts[7])
                    line_lon = float(parts[8])
                except:
                    continue
                if not (line_name == name and line_address == address and abs(line_lat - float(lat)) < 1e-6 and abs(line_lon - float(lon)) < 1e-6):
                    f.write(line)
    except Exception as e:
        logging.error(f"刪除 CSV 失敗: {e}")
        return False
    return True
def get_feedback_for_toilet(toilet_name):
    feedbacks = []
    try:
        records = worksheet.get_all_records()
        for row in records:
            if row.get("廁所名稱(請輸入或貼上廁所名稱；或留空將以地圖標記)") == toilet_name:
                feedback = {
                    "rating": row.get("清潔度評分", "無"),
                    "toilet_paper": row.get("是否有衛生紙？", "無資料"),
                    "accessibility": row.get("無障礙設施情況", "無資料"),
                    "time_of_use": row.get("您使用廁所的時間", "未填寫"),
                    "comment": row.get("使用者留言(建議根據實際經驗填寫)", "無留言")
                }
                feedbacks.append(feedback)
    except Exception as e:
        logging.error(f"❌ 讀取回饋資料失敗: {e}")
    return feedbacks

def save_feedback_to_gsheet(toilet_name, rating, toilet_paper, accessibility, comment):
    try:
        # 假設您已經初始化了 worksheet
        worksheet.append_row([toilet_name, rating, toilet_paper, accessibility, comment, datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")])
        return True
    except Exception as e:
        logging.error(f"寫入 Google Sheets 失敗: {e}")
        return False

# === 建立 Flex Message ===
def create_toilet_flex_messages(toilets, show_delete=False, uid=None):
    bubbles = []
    for toilet in toilets[:MAX_TOILETS_REPLY]:
        actions = []

        # 導航按鈕
        actions.append({
            "type": "uri",
            "label": "導航",
            "uri": f"https://www.google.com/maps/search/?api=1&query={toilet['lat']},{toilet['lon']}"
        })

        # 查看回饋按鈕（跳轉到回饋頁面）
        actions.append({
            "type": "uri",
            "label": "查看回饋",
            "uri": f"https://school-i9co.onrender.com/toilet_feedback/{quote(toilet['name'])}"
        })

        # 加入 / 移除 最愛
        if toilet.get("type") == "user":
            pass
        elif toilet.get("type") == "favorite" and uid is not None:
            actions.append({
                "type": "postback",
                "label": "移除最愛",
                "data": f"remove_fav:{toilet['name']}:{toilet['lat']}:{toilet['lon']}"
            })
        else:
            actions.append({
                "type": "postback",
                "label": "加入最愛",
                "data": f"add:{toilet['name']}:{toilet['lat']}:{toilet['lon']}"
            })

        # 刪除按鈕（僅限 user 新增）
        if show_delete and toilet.get("type") == "user" and uid is not None:
            actions.append({
                "type": "postback",
                "label": "刪除廁所",
                "data": f"confirm_delete:{toilet['name']}:{toilet['address']}:{toilet['lat']}:{toilet['lon']}"
            })

        # 回饋按鈕（所有類型都加）
        name_for_feedback = toilet['name'] or f"無名稱@{toilet['lat']:.5f},{toilet['lon']:.5f}"
        addr_for_feedback = toilet['address'] or "無地址"
        feedback_url = (
            "https://docs.google.com/forms/d/e/1FAIpQLSdx33f9m2GnI2PNRKr-frsskw8lLG6L4gEnew-Ornes4sWquA/viewform?usp=pp_url"
            f"&entry.1461963858={quote(name_for_feedback)}"
            f"&entry.1048755567={quote(addr_for_feedback)}"
        )
        actions.append({
            "type": "uri",
            "label": "廁所回饋",
            "uri": feedback_url
        })

        # 組合 Bubble（footer 改為垂直排版）
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

@app.route("/toilet_feedback/<toilet_name>", methods=["GET"])
def toilet_feedback(toilet_name):
    feedbacks = get_feedback_for_toilet(toilet_name)
    # 從資料庫獲取廁所的詳細地址
    address = "某個地址"  # 這裡需要從資料庫或其他資料來源獲取廁所地址
    return render_template("toilet_feedback.html", name=toilet_name, address=address, comments=feedbacks)

@app.route("/submit_feedback/<toilet_name>", methods=["POST"])
def submit_feedback(toilet_name):
    try:
        # 獲取表單資料
        rating = request.form.get("rating")
        toilet_paper = request.form.get("toilet_paper")
        accessibility = request.form.get("accessibility")
        time_of_use = request.form.get("time_of_use")  # 使用廁所時間
        comment = request.form.get("comment")  # 使用者留言
        
        # 確保所有必填欄位都有填寫
        if not all([rating, toilet_paper, accessibility]):
            flash("請填寫所有必填欄位！", "warning")
            return redirect(url_for("toilet_feedback", toilet_name=toilet_name))
        
        # 儲存回饋資料到 Google Sheets 或資料庫
        save_feedback_to_gsheet(toilet_name, rating, toilet_paper, accessibility, time_of_use, comment)
        
        flash("感謝您的回饋！", "success")
        return redirect(url_for("toilet_feedback", toilet_name=toilet_name))  # 返回廁所回饋頁面
    
    except Exception as e:
        logging.error(f"回饋提交錯誤: {e}")
        flash("提交失敗，請稍後再試！", "danger")
        return redirect(url_for("toilet_feedback", toilet_name=toilet_name))

def save_feedback_to_gsheet(toilet_name, rating, toilet_paper, accessibility, time_of_use, comment):
    try:
        # 假設您已經初始化了 worksheet
        worksheet.append_row([toilet_name, rating, toilet_paper, accessibility, time_of_use, comment, datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")])
        return True
    except Exception as e:
        logging.error(f"寫入 Google Sheets 失敗: {e}")
        return False

@app.route("/add")
def render_add_page():
    return render_template("submit_toilet.html")

@app.route("/submit_toilet", methods=["POST"])
def submit_toilet():
    try:
        data = request.get_json()
        logging.info(f"📥 收到表單資料: {data}")  # 加這行
        
        uid = data.get("user_id")
        name = data.get("name")
        address = data.get("address")
        
        logging.info(f"🔎 使用者ID: {uid}, 名稱: {name}, 地址: {address}")  # 加這行

        if not all([uid, name, address]):
            logging.warning("⚠️ 缺少參數")  # 加這行
            return {"success": False, "message": "缺少參數"}, 400

        _, lat, lon = geocode_address(address, name)
        logging.info(f"📍 地址轉換結果: lat={lat}, lon={lon}")  # 加這行

        if lat is None or lon is None:
            return {"success": False, "message": "無法解析地址"}, 400

        add_to_toilets_file(name, address, lat, lon)
        ok = add_to_gsheet(uid, name, address, lat, lon)
        if not ok:
            return {"success": False, "message": "寫入 Google Sheets 失敗"}, 500

        return {"success": True, "message": f"✅ 已新增廁所 {name}"}
    except Exception as e:
        logging.error(f"❌ 表單提交錯誤:\n{traceback.format_exc()}")
        return {"success": False, "message": "❌ 伺服器錯誤"}, 500

@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    text = event.message.text.strip().lower()
    uid = event.source.user_id
    reply_messages = []

    # === 刪除確認流程 ===
    if uid in pending_delete_confirm:
        info = pending_delete_confirm[uid]
        if text == "確認刪除":
            deleted_sheet = delete_from_gsheet(uid, info["name"], info["address"], info["lat"], info["lon"])
            deleted_csv = delete_from_toilets_file(info["name"], info["address"], info["lat"], info["lon"])
            msg = "✅ 已刪除該廁所"
            if not deleted_sheet:
                msg += "（但 Google Sheets 刪除失敗）"
            if not deleted_csv:
                msg += "（但 CSV 刪除失敗）"
            del pending_delete_confirm[uid]
            reply_messages.append(TextSendMessage(text=msg))
        elif text == "取消":
            del pending_delete_confirm[uid]
            reply_messages.append(TextSendMessage(text="❌ 已取消刪除操作"))
        else:
            reply_messages.append(TextSendMessage(text="⚠️ 請輸入『確認刪除』或『取消』"))

    elif text == "新增廁所":
        reply_messages.append(TextSendMessage(
            text="請點擊以下連結新增廁所：\nhttps://school-i9co.onrender.com/add"
        ))
    elif text == "回饋":
        form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
        reply_messages.append(TextSendMessage(text=f"💡 請透過下列連結回報問題或提供意見：\n{form_url}"))

    elif text == "附近廁所":
        if uid not in user_locations:
            reply_messages.append(TextSendMessage(text="請先傳送位置"))
        else:
            lat, lon = user_locations[uid]
            toilets = query_local_toilets(lat, lon) + query_overpass_toilets(lat, lon, radius=MAX_DISTANCE)
            if not toilets:
                reply_messages.append(TextSendMessage(text="附近找不到廁所，看來只能原地解放了"))
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
                for fav in favs:
                    fav["distance"] = int(haversine(lat, lon, fav["lat"], fav["lon"]))
            msg = create_toilet_flex_messages(favs, show_delete=True, uid=uid)
            reply_messages.append(FlexSendMessage("我的最愛", msg))

    elif text == "最近新增":
        recent_toilets = get_recent_added(uid)
        if not recent_toilets:
            reply_messages.append(TextSendMessage(text="❌ 找不到您最近新增的廁所"))
        else:
            if uid in user_locations:
                lat, lon = user_locations[uid]
                for toilet in recent_toilets:
                    toilet["distance"] = int(haversine(lat, lon, toilet["lat"], toilet["lon"]))
            msg = create_toilet_flex_messages(recent_toilets, show_delete=True, uid=uid)
            reply_messages.append(FlexSendMessage("最近新增的廁所", msg))

    # ✅ 統一回覆
    if reply_messages:
        try:
            line_bot_api.reply_message(event.reply_token, reply_messages)
        except Exception as e:
            logging.error(f"❌ 回覆訊息失敗（TextMessage）: {e}")


@handler.add(PostbackEvent)
def handle_postback(event):
    uid = event.source.user_id
    data = event.postback.data

    # 分三種狀況：加入收藏、移除收藏、刪除廁所確認流程
    if data.startswith("add:"):
        added = False
        try:
            _, name, lat, lon = data.split(":")
        except ValueError:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 格式錯誤，請重新操作"))
            return

        reply_messages = []
        if uid not in user_locations:
            reply_messages.append(TextSendMessage(text="請先傳送位置"))
        else:
            for toilet in query_local_toilets(*user_locations[uid]) + query_overpass_toilets(*user_locations[uid]):
                if toilet['name'] == name and str(toilet['lat']) == lat and str(toilet['lon']) == lon:
                    add_to_favorites(uid, toilet)
                    added = True
                    break
        if added:
            reply_messages.append(TextSendMessage(text=f"✅ 已收藏 {name}"))
        else:
            reply_messages.append(TextSendMessage(text="找不到該廁所，收藏失敗"))
        if reply_messages:
            try:
                line_bot_api.reply_message(event.reply_token, reply_messages)
            except Exception as e:
                logging.error(f"❌ 回覆訊息失敗（Postback add）: {e}")
    elif data.startswith("remove_fav:"):
        try:
            _, name, lat, lon = data.split(":")
            removed = remove_from_favorites(uid, name, lat, lon)
            msg = f"✅ 已從最愛移除 {name}" if removed else "❌ 移除失敗，請稍後再試"
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=msg))
        except:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 移除最愛失敗，格式錯誤"))

    elif data.startswith("confirm_delete:"):
        try:
            _, name, address, lat, lon = data.split(":")
            pending_delete_confirm[uid] = {
                "name": name,
                "address": address,
                "lat": lat,
                "lon": lon
            }
            line_bot_api.reply_message(event.reply_token, [
                TextSendMessage(text=f"⚠️ 確定要刪除廁所 {name} 嗎？"),
                TextSendMessage(text="請輸入『確認刪除』或『取消』")
            ])
        except:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 格式錯誤，請重新操作"))


@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
    uid = event.source.user_id
    lat, lon = event.message.latitude, event.message.longitude
    user_locations[uid] = (lat, lon)
    line_bot_api.reply_message(event.reply_token, TextSendMessage(text="✅ 位置已更新，請點選『附近廁所』查詢"))

if __name__ == "__main__":
    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
