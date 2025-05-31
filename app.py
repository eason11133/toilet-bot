import os 
import hmac
import hashlib
import base64
from math import radians, cos, sin, asin, sqrt
import sqlite3
import requests
from flask import Flask, request, abort
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError, LineBotApiError
from linebot.models import (
    MessageEvent, TextMessage, TextSendMessage,
    LocationMessage, FlexSendMessage
)
from dotenv import load_dotenv

load_dotenv()

if not os.getenv("LINE_CHANNEL_ACCESS_TOKEN") or not os.getenv("LINE_CHANNEL_SECRET"):
    raise ValueError("❌ 請確認 LINE_CHANNEL_ACCESS_TOKEN 和 LINE_CHANNEL_SECRET 已設置在環境變數中")

app = Flask(__name__)
line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

user_locations = {}

def create_db():
    conn = sqlite3.connect('toilets.db')
    c = conn.cursor()
    c.execute('''CREATE TABLE IF NOT EXISTS toilets
                 (name TEXT, type TEXT, latitude REAL, longitude REAL, address TEXT)''')
    conn.commit()
    conn.close()

def haversine(lat1, lon1, lat2, lon2):
    lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
    dlat = lat2 - lat1
    dlon = lon2 - lon1
    a = sin(dlat/2)**2 + cos(lat1)*cos(lat2)*sin(dlon/2)**2
    c = 2*asin(sqrt(a))
    r = 6371000
    return c * r

def get_nearest_toilets(lat, lon, radius=500, min_results=3, max_results=5):
    # 查本地資料庫
    conn = sqlite3.connect("toilets.db")
    cursor = conn.cursor()
    cursor.execute("SELECT name, address, latitude, longitude FROM toilets")
    rows = cursor.fetchall()
    conn.close()

    local_results = []
    for name, address, toilet_lat, toilet_lon in rows:
        if toilet_lat is None or toilet_lon is None:
            continue
        distance = haversine(lat, lon, toilet_lat, toilet_lon)
        if distance <= radius:
            local_results.append({
                "source": "local",
                "name": name,
                "address": address,
                "latitude": toilet_lat,
                "longitude": toilet_lon,
                "distance": distance
            })

    # 如果本地資料不夠，再查 OSM
    if len(local_results) < min_results:
        try:
            response = requests.post("https://overpass-api.de/api/interpreter", data=f"""
            [out:json];
            (
              node["amenity"="toilets"](around:{radius},{lat},{lon});
              way["amenity"="toilets"](around:{radius},{lat},{lon});
              relation["amenity"="toilets"](around:{radius},{lat},{lon});
            );
            out center;
            """)
            data = response.json().get("elements", [])
            for el in data:
                if el.get('type') == 'node':
                    toilet_lat = el.get('lat')
                    toilet_lon = el.get('lon')
                else:
                    center = el.get('center')
                    if not center: continue
                    toilet_lat = center.get('lat')
                    toilet_lon = center.get('lon')

                if toilet_lat is None or toilet_lon is None:
                    continue

                distance = haversine(lat, lon, toilet_lat, toilet_lon)
                name = el.get('tags', {}).get('name', '無名稱')

                local_results.append({
                    "source": "overpass",
                    "name": name,
                    "address": "來自 OpenStreetMap",
                    "latitude": toilet_lat,
                    "longitude": toilet_lon,
                    "distance": distance
                })
        except Exception as e:
            print(f"⚠️ Overpass API 錯誤: {e}")

    local_results.sort(key=lambda x: x["distance"])
    return local_results[:max_results]

@app.route("/")
def home():
    return "✅ LINE Bot is running!"

@app.route("/callback", methods=["POST"])
def callback():
    signature = request.headers.get("X-Line-Signature", "")
    body = request.get_data(as_text=True)

    secret = os.getenv("LINE_CHANNEL_SECRET")
    hash = hmac.new(secret.encode(), body.encode(), hashlib.sha256).digest()
    calculated_signature = base64.b64encode(hash).decode()

    if calculated_signature != signature:
        print("❌ Invalid signature")
        abort(400)

    try:
        handler.handle(body, signature)
    except InvalidSignatureError:
        abort(400)
    except LineBotApiError as e:
        print(f"❌ LineBot API error: {e}")
        abort(500)

    return "OK"

@handler.add(MessageEvent, message=TextMessage)
def handle_text_message(event):
    user_text = event.message.text.strip()
    user_id = event.source.user_id

    if "廁所" in user_text:
        if user_id in user_locations:
            lat, lon = user_locations[user_id]
            toilets = get_nearest_toilets(lat, lon)

            if not toilets:
                reply_text = "🚽 很抱歉，未能找到附近的廁所。"
                line_bot_api.reply_message(
                    event.reply_token, TextSendMessage(text=reply_text)
                )
                return

            best = toilets[0]
            map_url = f"https://www.google.com/maps/search/?api=1&query={best['latitude']},{best['longitude']}"
            flex_message = {
                "type": "bubble",
                "hero": {
                    "type": "image",
                    "url": "https://i.imgur.com/BRO9ZQw.png",
                    "size": "full",
                    "aspectRatio": "20:13",
                    "aspectMode": "cover"
                },
                "body": {
                    "type": "box",
                    "layout": "vertical",
                    "contents": [
                        {"type": "text", "text": best['name'], "weight": "bold", "size": "lg"},
                        {"type": "text", "text": f"來源：{best['source']}", "size": "sm", "color": "#AAAAAA"},
                        {"type": "text", "text": f"距離你 {best['distance']:.0f} 公尺", "size": "sm"}
                    ]
                },
                "footer": {
                    "type": "box",
                    "layout": "vertical",
                    "contents": [
                        {"type": "button", "style": "link", "action": {
                            "type": "uri", "label": "🗺 開啟地圖導航", "uri": map_url}}
                    ]
                }
            }
            line_bot_api.reply_message(
                event.reply_token, FlexSendMessage(alt_text="最近的廁所資訊", contents=flex_message)
            )
        else:
            line_bot_api.reply_message(
                event.reply_token,
                TextSendMessage(text="請先傳送您目前的位置，讓我幫您找附近的廁所喔！")
            )
    else:
        line_bot_api.reply_message(
            event.reply_token,
            TextSendMessage(text="請輸入「廁所」來查詢附近廁所，或先傳送您目前的位置。")
        )

@handler.add(MessageEvent, message=LocationMessage)
def handle_location_message(event):
    user_id = event.source.user_id
    lat = event.message.latitude
    lon = event.message.longitude
    user_locations[user_id] = (lat, lon)

    line_bot_api.reply_message(
        event.reply_token,
        TextSendMessage(text=f"📍 位置已更新，緯度：{lat}\n經度：{lon}\n請輸入「廁所」查詢附近廁所。")
    )

if __name__ == "__main__":
    create_db()
    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
