import os
import csv
import logging
import requests
from math import radians, cos, sin, asin, sqrt
from flask import Flask, request, abort
from dotenv import load_dotenv
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError
from linebot.models import (
    MessageEvent, TextMessage, LocationMessage,
    FlexSendMessage, PostbackEvent, TextSendMessage,
    URIAction
)
from datetime import timedelta

# 載入 .env
load_dotenv()

# 設定 logging
logging.basicConfig(level=logging.INFO)

# 初始化 Flask 與 LINE Bot
app = Flask(__name__)
line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

TOILETS_FILE_PATH = '/opt/render/project/src/toilets.txt'
FAVORITES_FILE_PATH = os.path.join(os.getcwd(), 'favorites.txt')  # 使用相對路徑

# 建立 favorites.txt 如不存在
def ensure_favorites_file():
    try:
        # 確保目錄存在
        os.makedirs(os.path.dirname(FAVORITES_FILE_PATH), exist_ok=True)
        
        if not os.path.exists(FAVORITES_FILE_PATH):
            with open(FAVORITES_FILE_PATH, "w", encoding="utf-8"):
                pass
    except Exception as e:
        logging.error(f"Error creating favorites.txt: {e}")
        raise

ensure_favorites_file()

user_locations = {}
MAX_TOILETS_REPLY = 5
MAX_DISTANCE = 500  # 限制搜尋距離（公尺）
used_reply_tokens = set()
reply_token_expiry = timedelta(minutes=1)

# 存儲正在進行新增廁所的使用者狀態
pending_additions = {}

# 計算 Haversine 距離
def haversine(lat1, lon1, lat2, lon2):
    try:
        lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
        dlat = lat2 - lat1
        dlon = lon2 - lon1
        a = sin(dlat / 2) ** 2 + cos(lat1) * cos(lat2) * sin(dlon / 2) ** 2
        return 2 * asin(sqrt(a)) * 6371000
    except Exception as e:
        logging.error(f"Error calculating distance: {e}")
        return 0

# 查詢本地廁所（限500m內）
def query_local_toilets(lat, lon):
    toilets = []
    try:
        if not os.path.exists(TOILETS_FILE_PATH):
            logging.error(f"{TOILETS_FILE_PATH} 不存在，請確認檔案是否存在於指定路徑")
            return []
        
        with open(TOILETS_FILE_PATH, 'r', encoding='utf-8') as file:
            reader = csv.reader(file)
            next(reader, None)  # skip header

            for row in reader:
                if len(row) != 14:
                    continue
                row = [col.strip() for col in row]
                _, _, _, _, name, address, _, latitude, longitude, _, _, type_, _, _ = row
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
                    logging.error(f"Error processing row: {e}")
                    continue
    except Exception as e:
        logging.error(f"Error reading {TOILETS_FILE_PATH}: {e}")
        return []

    return sorted(toilets, key=lambda x: x['distance'])

# 查詢 OSM API
def query_overpass_toilets(lat, lon, radius=500):
    url = "https://overpass-api.de/api/interpreter"
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
        resp = requests.post(url, data=query, headers={"User-Agent": "LineBotToiletFinder/1.0"}, timeout=10)
        resp.raise_for_status()
        data = resp.json()
    except Exception as e:
        logging.error(f"Overpass API 查詢失敗：{e}")
        return []

    toilets = []
    for elem in data.get("elements", []):
        if elem["type"] == "node":
            t_lat, t_lon = elem["lat"], elem["lon"]
        elif "center" in elem:
            t_lat, t_lon = elem["center"]["lat"], elem["center"]["lon"]
        else:
            continue
        dist = haversine(lat, lon, t_lat, t_lon)
        name = elem.get("tags", {}).get("name", "無名稱")
        toilets.append({
            "name": name,
            "lat": t_lat,
            "lon": t_lon,
            "address": "",
            "distance": dist,
            "type": "osm"
        })
    return sorted(toilets, key=lambda x: x["distance"])

# 加入最愛
def add_to_favorites(user_id, toilet):
    try:
        with open(FAVORITES_FILE_PATH, "a", encoding="utf-8") as file:
            file.write(f"{user_id},{toilet['name']},{toilet['lat']},{toilet['lon']},{toilet['address']}\n")
    except Exception as e:
        logging.error(f"Error adding to favorites: {e}")

# 移除最愛
def remove_from_favorites(user_id, name, lat, lon):
    try:
        with open(FAVORITES_FILE_PATH, "r", encoding="utf-8") as file:
            lines = file.readlines()
        with open(FAVORITES_FILE_PATH, "w", encoding="utf-8") as file:
            for line in lines:
                data = line.strip().split(',')
                if not (data[0] == user_id and data[1] == name and data[2] == str(lat) and data[3] == str(lon)):
                    file.write(line)
        return True
    except Exception as e:
        logging.error(f"Error removing favorite: {e}")
        return False

# 取得我的最愛
def get_user_favorites(user_id):
    favorites = []
    try:
        with open(FAVORITES_FILE_PATH, "r", encoding="utf-8") as file:
            for line in file:
                data = line.strip().split(',')
                if data[0] == user_id:
                    favorites.append({
                        "name": data[1],
                        "lat": float(data[2]),
                        "lon": float(data[3]),
                        "address": data[4],
                        "type": "favorite",
                        "distance": 0
                    })
    except Exception as e:
        logging.error(f"Error reading {FAVORITES_FILE_PATH}: {e}")
    return favorites

# geocode 地址轉換為經緯度（使用 OpenStreetMap Nominatim）
def geocode_address(address, user_name):
    try:
        formatted_address = ' '.join(address.split())  # 去除多餘空格並確保每部分有一個空格
        address_encoded = requests.utils.quote(formatted_address)  # URL 編碼
        url = f"https://nominatim.openstreetmap.org/search?format=json&q={address_encoded}"

        headers = {
            "User-Agent": "YourAppName/1.0 (http://yourwebsite.com/contact)"
        }

        response = requests.get(url, headers=headers)

        if response.status_code == 200:
            logging.info(f"Nominatim API 回應：{response.text}")
            data = response.json()
            if data:
                lat = float(data[0]['lat'])
                lon = float(data[0]['lon'])
                name = data[0].get('name', '')  # 如果name為空，保持空白

                # 如果name為空，使用輸入的廁所名稱
                if not name:
                    name = user_name

                logging.info(f"Geocoded address: {formatted_address} -> lat: {lat}, lon: {lon}, name: {name}")
                return name, lat, lon
            else:
                logging.error(f"無法解析地址: {formatted_address}")
                return None, None, None
        else:
            logging.error(f"API 請求失敗，狀態碼：{response.status_code}")
            logging.error(f"回應內容：{response.text}")
            return None, None, None
    except Exception as e:
        logging.error(f"解析地址出錯：{e}")
        return None, None, None

# 寫入 toilets.txt，將新廁所資料放在檔案的第一筆
def add_to_toilets_file(name, address, lat, lon):
    try:
        if not os.path.exists(TOILETS_FILE_PATH):
            logging.error(f"{TOILETS_FILE_PATH} 不存在，請確認檔案是否存在於指定路徑")
            return

        with open(TOILETS_FILE_PATH, "r", encoding="utf-8", errors='ignore') as f:
            lines = f.readlines()

        # 新增的廁所資料
        new_row = f"00000,0000000,未知里,USERADD,{name},{address},使用者補充,{lat},{lon},普通級,公共場所,未知,使用者,0\n"

        with open(TOILETS_FILE_PATH, "w", encoding="utf-8", errors='ignore') as f:
            f.write(new_row)  # 寫入新的廁所資料
            f.writelines(lines)  # 寫入原檔案中的其他內容

        logging.info(f"成功將廁所 {name} 新增至檔案並放置於第一筆")
    except Exception as e:
        logging.error(f"寫入檔案失敗：{e}")

# 建立 Flex Message（使用 Google Map）
def create_toilet_flex_messages(toilets, user_lat, user_lon, show_delete=False):
    bubbles = []
    for t in toilets[:MAX_TOILETS_REPLY]:
        dist = haversine(user_lat, user_lon, t['lat'], t['lon'])
        map_url = f"https://staticmap.openstreetmap.de/staticmap.php?center={t['lat']},{t['lon']}&zoom=15&size=600x300&markers={t['lat']},{t['lon']}&format=png"
        google_map = f"https://www.google.com/maps/search/?api=1&query={t['lat']},{t['lon']}"
        bubble = {
            "type": "bubble",
            "hero": {
                "type": "image",
                "url": map_url,
                "size": "full",
                "aspectMode": "cover",
                "aspectRatio": "20:13"
            },
            "body": {
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {"type": "text", "text": t['name'], "weight": "bold", "size": "lg"},
                    {"type": "text", "text": f"距離：{dist:.1f} 公尺", "size": "sm", "color": "#555555"},
                    {"type": "text", "text": f"地址：{t['address']}", "size": "sm", "wrap": True, "color": "#aaaaaa"},
                    {"type": "text", "text": f"類型：{t['type']}", "size": "sm", "color": "#aaaaaa"}
                ]
            },
            "footer": {
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {
                        "type": "button",
                        "style": "primary",
                        "color": "#00BFFF",
                        "action": URIAction(label="導航至最近廁所", uri=google_map)
                    },
                    {
                        "type": "button",
                        "style": "primary",
                        "color": "#FFA07A",
                        "action": {
                            "type": "postback",
                            "label": "刪除最愛" if show_delete else "加入最愛",
                            "data": f"{'remove' if show_delete else 'add'}:{t['name']}:{t['lat']}:{t['lon']}"
                        }
                    }
                ]
            }
        }
        bubbles.append(bubble)
    return {"type": "carousel", "contents": bubbles}

# Webhook callback
@app.route("/callback", methods=["POST"])
def callback():
    signature = request.headers.get("X-Line-Signature")
    body = request.get_data(as_text=True)
    try:
        handler.handle(body, signature)
    except InvalidSignatureError:
        abort(400)
    return 'OK'

@app.route("/")
def index():
    return "Line Bot API is running!"

# 文字訊息處理
@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    text = event.message.text.lower()
    uid = event.source.user_id

    # 1. 新增廁所流程
    if text.startswith("新增廁所"):
        pending_additions[uid] = {'step': 1}  # 記錄正在進行新增廁所的流程
        line_bot_api.reply_message(event.reply_token, TextSendMessage(text="🔧 請提供廁所名稱："))
        return

    # 2. 如果使用者在新增廁所過程中
    if uid in pending_additions:
        step = pending_additions[uid]['step']

        if step == 1:  # 收集廁所名稱
            if text == "取消":
                del pending_additions[uid]  # 清除正在進行的新增廁所流程
                line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 新增廁所操作已取消，您可以繼續其他操作。"))
                return
            pending_additions[uid]['name'] = text
            pending_additions[uid]['step'] = 2
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="📍 請提供地址（格式：市區、區域、街道名、門牌號，例如：新北市三重區五華街282號）："))

        elif step == 2:  # 收集地址
            if text == "取消":
                del pending_additions[uid]  # 清除正在進行的新增廁所流程
                line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 新增廁所操作已取消，您可以繼續其他操作。"))
                return

            name = pending_additions[uid]['name']
            address = text
            # 使用用戶名稱作為name
            city, lat, lon = geocode_address(address, name)

            if lat is None or lon is None:
                # 地址無法解析，讓用戶選擇是否重新輸入
                line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 地址無法解析，請確認地址格式正確並重新輸入。\n若不想繼續新增廁所，請輸入「取消」來取消操作。"))
                return

            # 寫入 toilets.txt 並將新資料放在第一筆
            try:
                add_to_toilets_file(name, address, lat, lon)  # 確保經緯度資料被加入
                line_bot_api.reply_message(event.reply_token, TextSendMessage(text=f"✅ 已成功新增廁所：{name}"))
            except Exception as e:
                line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 寫入檔案失敗"))

            # 清除使用者狀態
            del pending_additions[uid]

    # 回饋功能
    elif text == "回饋":
        form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
        line_bot_api.reply_message(event.reply_token, TextSendMessage(text=f"💡 請透過下列連結回報問題或提供意見：\n{form_url}"))

    # 其他功能：查詢附近廁所、我的最愛等...
    elif text == "附近廁所":
        if uid not in user_locations:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="請先傳送位置"))
            return
        lat, lon = user_locations[uid]
        toilets = query_local_toilets(lat, lon) + query_overpass_toilets(lat, lon, radius=MAX_DISTANCE)
        if not toilets:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="附近找不到廁所，看來只能原地解放了"))
            return
        msg = create_toilet_flex_messages(toilets, lat, lon)
        line_bot_api.reply_message(event.reply_token, FlexSendMessage("附近廁所", msg))

    elif text == "我的最愛":
        favs = get_user_favorites(uid)
        if not favs:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="你尚未收藏任何廁所"))
            return
        lat, lon = user_locations.get(uid, (0, 0))
        msg = create_toilet_flex_messages(favs, lat, lon, show_delete=True)
        line_bot_api.reply_message(event.reply_token, FlexSendMessage("我的最愛", msg))

# Postback 處理
@handler.add(PostbackEvent)
def handle_postback(event):
    uid = event.source.user_id
    data = event.postback.data
    action, name, lat, lon = data.split(":")
    if action == "add":
        for toilet in query_local_toilets(*user_locations[uid]) + query_overpass_toilets(*user_locations[uid]):
            if toilet['name'] == name and str(toilet['lat']) == lat and str(toilet['lon']) == lon:
                add_to_favorites(uid, toilet)
                break
        line_bot_api.reply_message(event.reply_token, TextSendMessage(text=f"✅ 已收藏 {name}"))
    elif action == "remove":
        if remove_from_favorites(uid, name, lat, lon):
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=f"❌ 已移除 {name}"))
        else:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="找不到該收藏"))

# 位置處理
@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
    uid = event.source.user_id
    lat, lon = event.message.latitude, event.message.longitude
    user_locations[uid] = (lat, lon)
    line_bot_api.reply_message(event.reply_token, TextSendMessage(text="✅ 位置已更新，請點選『附近廁所』查詢"))

if __name__ == "__main__":
    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
