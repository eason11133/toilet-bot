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

load_dotenv()
logging.basicConfig(level=logging.INFO)

app = Flask(__name__)
line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

TOILETS_FILE_PATH = os.path.join(os.getcwd(), 'public_toilets.csv')
FAVORITES_FILE_PATH = os.path.join(os.getcwd(), 'favorites.txt')

if not os.path.exists(TOILETS_FILE_PATH):
    logging.error(f"{TOILETS_FILE_PATH} 不存在，請確認檔案是否存在於指定路徑")
else:
    logging.info(f"{TOILETS_FILE_PATH} 檔案存在")

def ensure_favorites_file():
    try:
        os.makedirs(os.path.dirname(FAVORITES_FILE_PATH), exist_ok=True)
        if not os.path.exists(FAVORITES_FILE_PATH):
            with open(FAVORITES_FILE_PATH, "w", encoding="utf-8"):
                pass
    except Exception as e:
        logging.error(f"Error creating favorites.txt: {e}")
        raise

ensure_favorites_file()

user_locations = {}
MAX_DISTANCE = 500
MAX_TOILETS_REPLY = 5  # 加入這行
pending_additions = {}

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

def query_local_toilets(lat, lon):
    toilets = []
    try:
        if not os.path.exists(TOILETS_FILE_PATH):
            logging.error(f"{TOILETS_FILE_PATH} 不存在，請確認檔案是否存在於指定路徑")
            return []
        with open(TOILETS_FILE_PATH, 'r', encoding='utf-8') as file:
            reader = csv.reader(file)
            header = next(reader, None)
            for row in reader:
                if len(row) != 15:
                    continue
                row = [col.strip() for col in row]
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
                    logging.error(f"Error processing row: {e}")
                    continue
    except Exception as e:
        logging.error(f"Error reading {TOILETS_FILE_PATH}: {e}")
        return []
    return sorted(toilets, key=lambda x: x['distance'])

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

def add_to_favorites(user_id, toilet):
    try:
        with open(FAVORITES_FILE_PATH, "a", encoding="utf-8") as file:
            file.write(f"{user_id},{toilet['name']},{toilet['lat']},{toilet['lon']},{toilet['address']}\n")
    except Exception as e:
        logging.error(f"Error adding to favorites: {e}")

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

def geocode_address(address, user_name):
    try:
        formatted_address = ' '.join(address.split())
        address_encoded = requests.utils.quote(formatted_address)
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
                name = data[0].get('name', '')
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

def add_to_toilets_file(name, address, lat, lon):
    try:
        if not os.path.exists(TOILETS_FILE_PATH):
            logging.error(f"{TOILETS_FILE_PATH} 不存在，請確認檔案是否存在於指定路徑")
            return

        with open(TOILETS_FILE_PATH, "r", encoding="utf-8", errors='ignore') as f:
            lines = f.readlines()

        new_row = f"00000,0000000,未知里,USERADD,{name},{address},使用者補充,{lat},{lon},普通級,公共場所,未知,使用者,0,\n"

        with open(TOILETS_FILE_PATH, "w", encoding="utf-8", errors='ignore') as f:
            if lines:
                f.write(lines[0])  # 標題列
            f.write(new_row)       # 新增資料
            if len(lines) > 1:
                f.writelines(lines[1:])  # 原資料

        logging.info(f"成功將廁所 {name} 新增至檔案並放置於第一筆")
    except Exception as e:
        logging.error(f"寫入檔案失敗：{e}")

def create_toilet_flex_messages(toilets, user_lat, user_lon, show_delete=False):
    bubbles = []
    for toilet in toilets[:MAX_TOILETS_REPLY]:
        distance_m = int(toilet['distance'])
        distance_text = f"{distance_m}公尺" if distance_m < 1000 else f"{distance_m/1000:.2f}公里"
        actions = []
        if show_delete:
            data_remove = f"remove:{toilet['name']}:{toilet['lat']}:{toilet['lon']}"
            actions.append({
                "type": "postback",
                "label": "移除收藏",
                "data": data_remove
            })
        else:
            data_add = f"add:{toilet['name']}:{toilet['lat']}:{toilet['lon']}"
            actions.append({
                "type": "postback",
                "label": "加入收藏",
                "data": data_add
            })
        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {"type": "text", "text": toilet['name'], "weight": "bold", "size": "lg", "wrap": True},
                    {"type": "text", "text": toilet['address'], "size": "sm", "color": "#666666", "wrap": True},
                    {"type": "text", "text": distance_text, "size": "sm", "color": "#999999"},
                ]
            },
            "footer": {
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {
                        "type": "button",
                        "style": "primary",
                        "action": {
                            "type": "uri",
                            "label": "導航",
                            "uri": f"https://www.google.com/maps/search/?api=1&query={toilet['lat']},{toilet['lon']}"
                        }
                    },
                    {
                        "type": "button",
                        "style": "secondary",
                        "action": actions[0]
                    }
                ]
            }
        }
        bubbles.append(bubble)

    flex_message = {
        "type": "carousel",
        "contents": bubbles
    }
    return flex_message

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

@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    text = event.message.text.lower()
    uid = event.source.user_id

    if text.startswith("新增廁所"):
        pending_additions[uid] = {'step': 1}
        line_bot_api.reply_message(event.reply_token, TextSendMessage(text="🔧 請提供廁所名稱："))
        return

    if uid in pending_additions:
        step = pending_additions[uid]['step']

        if step == 1:
            if text == "取消":
                del pending_additions[uid]
                line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 新增廁所操作已取消，您可以繼續其他操作。"))
                return
            pending_additions[uid]['name'] = text
            pending_additions[uid]['step'] = 2
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="📍 請提供地址 例如：新北市 三重區 五華街 282號(用空格隔開)："))

        elif step == 2:
            if text == "取消":
                del pending_additions[uid]
                line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 新增廁所操作已取消，您可以繼續其他操作。"))
                return

            name = pending_additions[uid]['name']
            address = text
            city, lat, lon = geocode_address(address, name)

            if lat is None or lon is None:
                line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 地址無法解析，請確認地址格式正確並重新輸入。\n若不想繼續新增廁所，請輸入「取消」來取消操作。"))
                return

            try:
                add_to_toilets_file(name, address, lat, lon)
                line_bot_api.reply_message(event.reply_token, TextSendMessage(text=f"✅ 已成功新增廁所：{name}"))
            except Exception as e:
                line_bot_api.reply_message(event.reply_token, TextSendMessage(text="❌ 寫入檔案失敗"))

            del pending_additions[uid]

    elif text == "回饋":
        form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
        line_bot_api.reply_message(event.reply_token, TextSendMessage(text=f"💡 請透過下列連結回報問題或提供意見：\n{form_url}"))

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

@handler.add(PostbackEvent)
def handle_postback(event):
    uid = event.source.user_id
    data = event.postback.data
    action, name, lat, lon = data.split(":")

    if uid not in user_locations:
        line_bot_api.reply_message(event.reply_token, TextSendMessage(text="請先傳送位置"))
        return

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

@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
    uid = event.source.user_id
    lat, lon = event.message.latitude, event.message.longitude
    user_locations[uid] = (lat, lon)
    line_bot_api.reply_message(event.reply_token, TextSendMessage(text="✅ 位置已更新，請點選『附近廁所』查詢"))

if __name__ == "__main__":
    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
