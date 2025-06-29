import os
import csv
import json
import logging
import requests
from math import radians, cos, sin, asin, sqrt
from flask import Flask, request, abort
from dotenv import load_dotenv
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
            # 寫入 header（跟原來 CSV 一樣，因為你讀檔時跳過了 header）
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
pending_additions = {}
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

# === 收藏管理 ===
def add_to_favorites(uid, toilet):
    try:
        with open(FAVORITES_FILE_PATH, "a", encoding="utf-8") as f:
            f.write(f"{uid},{toilet['name']},{toilet['lat']},{toilet['lon']},{toilet['address']}\n")
    except Exception as e:
        logging.error(f"收藏失敗: {e}")

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
        logging.error(f"移除收藏失敗: {e}")
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
        logging.error(f"讀取收藏失敗: {e}")
    return favs

# === 地址轉經緯度 ===
def geocode_address(address, user_name):
    try:
        url = f"https://nominatim.openstreetmap.org/search?format=json&q={requests.utils.quote(address)}"
        headers = { "User-Agent": "ToiletBot/1.0" }
        resp = requests.get(url, headers=headers)
        if resp.status_code == 200 and resp.json():
            data = resp.json()[0]
            return user_name, float(data['lat']), float(data['lon'])
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

# === 建立 Flex Message ===
def create_toilet_flex_messages(toilets, show_delete=False, uid=None):
    bubbles = []
    for toilet in toilets[:MAX_TOILETS_REPLY]:
        actions = []
        # 第一個按鈕：導航（所有都要）
        actions.append({
            "type": "uri",
            "label": "導航",
            "uri": f"https://www.google.com/maps/search/?api=1&query={toilet['lat']},{toilet['lon']}"
        })

        # 第二個按鈕：
        if toilet.get("type") == "user":
            # user新增廁所沒有加入收藏按鈕，改成第三個刪除按鈕
            pass
        else:
            # 非user新增，顯示加入收藏按鈕
            actions.append({
                "type": "postback",
                "label": "加入收藏",
                "data": f"add:{toilet['name']}:{toilet['lat']}:{toilet['lon']}"
            })

        # 第三個按鈕：
        if show_delete and toilet.get("type") == "user" and uid is not None:
            actions.append({
                "type": "postback",
                "label": "刪除廁所",
                "data": f"confirm_delete:{toilet['name']}:{toilet['address']}:{toilet['lat']}:{toilet['lon']}"
            })

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
                "layout": "horizontal",
                "spacing": "sm",
                "contents": [
                    {"type": "button", "style": "primary", "action": actions[0]},
                ] + [
                    {"type": "button", "style": "secondary", "action": a} for a in actions[1:]
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

@app.route("/")
def index():
    return "ToiletBot is running!"

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
            line_bot_api.reply_message(event.reply_token, reply_messages)
            return
        elif text == "取消":
            del pending_delete_confirm[uid]
            reply_messages.append(TextSendMessage(text="❌ 已取消刪除操作"))
            line_bot_api.reply_message(event.reply_token, reply_messages)
            return
        else:
            reply_messages.append(TextSendMessage(text="⚠️ 請輸入『確認刪除』或『取消』"))
            line_bot_api.reply_message(event.reply_token, reply_messages)
            return

    # === 新增廁所流程 ===
    if text.startswith("新增廁所"):
        pending_additions[uid] = {'step': 1}
        reply_messages.append(TextSendMessage(text="🔧 請提供廁所名稱："))

    elif uid in pending_additions:
        step = pending_additions[uid]['step']
        if text == "取消":
            del pending_additions[uid]
            reply_messages.append(TextSendMessage(text="❌ 新增廁所操作已取消，您可以繼續其他操作。"))
        else:
            if step == 1:
                pending_additions[uid]['name'] = text
                pending_additions[uid]['step'] = 2
                reply_messages.append(TextSendMessage(text="📍 請提供地址 例如：新北市 三重區 五華街 282號(用空格隔開)："))
            elif step == 2:
                name = pending_additions[uid]['name']
                address = text
                city, lat, lon = geocode_address(address, name)
                if lat is None or lon is None:
                    reply_messages.append(TextSendMessage(text="❌ 地址無法解析，請確認地址格式正確並重新輸入。\n若不想繼續新增廁所，請輸入「取消」來取消操作。"))
                else:
                    try:
                        add_to_toilets_file(name, address, lat, lon)
                        success = add_to_gsheet(uid, name, address, lat, lon)
                        if success:
                            reply_messages.append(TextSendMessage(text=f"✅ 已成功新增廁所：{name} 並同步至 Google Sheets"))
                        else:
                            reply_messages.append(TextSendMessage(text=f"✅ 已成功新增廁所：{name}，但同步 Google Sheets 失敗"))
                            del pending_additions[uid]  # <--- 這行是關鍵
                    except Exception as e:
                        logging.error(f"寫入檔案失敗：{e}")
                        line_bot_api.push_message(uid, TextSendMessage(text="❌ 寫入檔案失敗，請稍後再試或聯絡管理員。"))
                        return  # 🔥 加這一行，避免出現 Invalid reply token 錯誤

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
                # 傳入 show_delete=True 並帶入 uid，這樣才會在附近廁所的Flex Message中，對user新增的廁所加上刪除按鈕
                msg = create_toilet_flex_messages(toilets, show_delete=True, uid=uid)
                reply_messages.append(FlexSendMessage("附近廁所", msg))

    elif text == "我的最愛":
        favs = get_user_favorites(uid)
        if not favs:
            reply_messages.append(TextSendMessage(text="你尚未收藏任何廁所"))
        else:
            msg = create_toilet_flex_messages(favs, show_delete=True)
            reply_messages.append(FlexSendMessage("我的最愛", msg))
    elif text == "最近新增":
        recent_toilets = get_recent_added(uid)
        if not recent_toilets:
            reply_messages.append(TextSendMessage(text="❌ 找不到您最近新增的廁所"))
        else:
            msg = create_toilet_flex_messages(recent_toilets, show_delete=True, uid=uid)
            reply_messages.append(FlexSendMessage("最近新增的廁所", msg))

    if reply_messages:
        try:
            line_bot_api.reply_message(event.reply_token, reply_messages)
        except Exception as e:
            logging.error(f"❌ 回覆訊息時失敗: {e}")


@handler.add(PostbackEvent)
def handle_postback(event):
    uid = event.source.user_id
    data = event.postback.data
    # 分三種狀況：加入收藏、移除收藏、刪除廁所確認流程
    if data.startswith("add:"):
        try:
            _, name, lat, lon = data.split(":")
        except ValueError:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 格式錯誤，請重新操作"))
            return

        reply_messages = []
        if uid not in user_locations:
            reply_messages.append(TextSendMessage(text="請先傳送位置"))
        else:
            added = False
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
            line_bot_api.reply_message(event.reply_token, reply_messages)

    if data.startswith("confirm_delete:"):
        try:
            _, name, address, lat, lon = data.split(":")
            pending_delete_confirm[uid] = {"name": name, "address": address, "lat": lat, "lon": lon}
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