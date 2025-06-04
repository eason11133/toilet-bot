import os
import logging
from math import radians, cos, sin, asin, sqrt
import sqlite3
import requests
from flask import Flask, request, abort
from dotenv import load_dotenv
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError
from linebot.models import (
    MessageEvent, TextMessage, LocationMessage,
    FlexSendMessage, PostbackEvent, TextSendMessage, PostbackAction
)

# Load environment variables
load_dotenv()

app = Flask(__name__)
line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

user_locations = {}
last_toilet_by_user = {}
MAX_TOILETS_REPLY = 5

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")

# Initialize favorites table
with sqlite3.connect("toilets.db") as conn:
    cursor = conn.cursor()
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS favorites (
            user_id TEXT,
            name TEXT,
            lat REAL,
            lon REAL,
            address TEXT,
            added_time TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    conn.commit()

def haversine(lat1, lon1, lat2, lon2):
    lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
    dlat, dlon = lat2 - lat1, lon2 - lon1
    a = sin(dlat / 2) ** 2 + cos(lat1) * cos(lat2) * sin(dlon / 2) ** 2
    return 2 * asin(sqrt(a)) * 6371000

def add_to_favorites(user_id, toilet):
    with sqlite3.connect("toilets.db") as conn:
        cursor = conn.cursor()
        cursor.execute("""
            INSERT INTO favorites (user_id, name, lat, lon, address)
            VALUES (?, ?, ?, ?, ?)
        """, (user_id, toilet['name'], toilet['lat'], toilet['lon'], toilet.get('address', '')))
        conn.commit()

def remove_from_favorites(user_id, name):
    with sqlite3.connect("toilets.db") as conn:
        cursor = conn.cursor()
        cursor.execute("DELETE FROM favorites WHERE user_id = ? AND name = ?", (user_id, name))
        conn.commit()
        return cursor.rowcount > 0

def get_user_favorites(user_id):
    with sqlite3.connect("toilets.db") as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT name, lat, lon, address FROM favorites WHERE user_id = ?", (user_id,))
        return [{"name": name, "lat": lat, "lon": lon, "address": addr, "type": "favorite", "distance": 0}
                for name, lat, lon, addr in cursor.fetchall()]

def query_local_toilets(lat, lon):
    conn = sqlite3.connect("toilets.db")
    cursor = conn.cursor()
    cursor.execute("SELECT 設施名稱, 類別, 緯度, 經度, 位置 FROM toilets")
    toilets = []
    for name, type_, t_lat, t_lon, addr in cursor.fetchall():
        if not t_lat or not t_lon:
            continue
        try:
            t_lat, t_lon = float(t_lat), float(t_lon)
        except ValueError:
            continue
        dist = haversine(lat, lon, t_lat, t_lon)
        toilets.append({"name": name or "無名稱", "lat": t_lat, "lon": t_lon,
                        "address": addr or "", "distance": dist, "type": "local"})
    conn.close()
    return sorted(toilets, key=lambda x: x['distance'])

def create_toilet_flex_messages(toilets, show_delete=False):
    bubbles = []
    for t in toilets[:MAX_TOILETS_REPLY]:
        action_button = {
            "type": "button",
            "style": "primary",
            "color": "#FFA07A",
            "action": {
                "type": "postback",
                "label": "刪除最愛" if show_delete else "加入最愛",
                "data": f"{'remove' if show_delete else 'add'}:{t['name']}"
            }
        }
        bubble = {
            "type": "bubble",
            "hero": {
                "type": "image",
                "url": "https://i.imgur.com/BRO9ZQw.png",
                "size": "full",
                "aspectMode": "cover",
                "aspectRatio": "20:13"
            },
            "body": {
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {"type": "text", "text": t['name'], "weight": "bold", "size": "lg"},
                    {"type": "text", "text": f"距離：{t['distance']:.1f} 公尺" if t['distance'] else "", "size": "sm", "color": "#555555", "margin": "md"},
                    {"type": "text", "text": f"地址：{t['address']}", "size": "sm", "color": "#aaaaaa", "wrap": True, "margin": "md"}
                ]
            },
            "footer": {
                "type": "box",
                "layout": "vertical",
                "contents": [action_button],
                "spacing": "sm",
                "flex": 0
            }
        }
        bubbles.append(bubble)
    return {"type": "carousel", "contents": bubbles}

@app.route("/callback", methods=["POST"])
def callback():
    signature = request.headers.get("X-Line-Signature")
    body = request.get_data(as_text=True)
    try:
        handler.handle(body, signature)
    except InvalidSignatureError:
        abort(400)
    return 'OK'

@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    text = event.message.text.lower()
    uid = event.source.user_id

    if text == "廁所":
        if uid not in user_locations:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="請先傳送位置"))
            return
        lat, lon = user_locations[uid]
        toilets = query_local_toilets(lat, lon)
        last_toilet_by_user[uid] = toilets[0] if toilets else None
        msg = create_toilet_flex_messages(toilets)
        line_bot_api.reply_message(event.reply_token, FlexSendMessage("附近廁所", msg))

    elif text == "我的最愛":
        favs = get_user_favorites(uid)
        if not favs:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="你尚未收藏任何廁所"))
            return
        msg = create_toilet_flex_messages(favs, show_delete=True)
        line_bot_api.reply_message(event.reply_token, FlexSendMessage("我的最愛", msg))

@handler.add(PostbackEvent)
def handle_postback(event):
    data = event.postback.data
    uid = event.source.user_id
    if data.startswith("add:"):
        name = data[4:]
        toilet = last_toilet_by_user.get(uid)
        if toilet and toilet['name'] == name:
            add_to_favorites(uid, toilet)
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=f"✅ 已收藏 {name}"))
    elif data.startswith("remove:"):
        name = data[7:]
        if remove_from_favorites(uid, name):
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=f"❌ 已移除 {name}"))
        else:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="找不到該收藏"))

@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
    uid = event.source.user_id
    lat, lon = event.message.latitude, event.message.longitude
    user_locations[uid] = (lat, lon)
    line_bot_api.reply_message(event.reply_token, TextSendMessage(text="✅ 位置已更新，輸入 '廁所' 查詢"))

if __name__ == '__main__':
    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
