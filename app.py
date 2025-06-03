import os
import hmac
import hashlib
import base64
import sqlite3
import requests
from math import radians, cos, sin, asin, sqrt
from flask import Flask, request, abort
from dotenv import load_dotenv
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError, LineBotApiError
from linebot.models import (
    MessageEvent, TextMessage, TextSendMessage, LocationMessage,
    FlexSendMessage, BubbleContainer, BoxComponent, ImageComponent,
    TextComponent, ButtonComponent, MessageAction, LocationAction
)

load_dotenv()
app = Flask(__name__)
line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

user_locations = {}

def haversine(lat1, lon1, lat2, lon2):
    r = 6371000
    dlat, dlon = radians(lat2 - lat1), radians(lon2 - lon1)
    a = sin(dlat/2)**2 + cos(radians(lat1)) * cos(radians(lat2)) * sin(dlon/2)**2
    return 2 * r * asin(sqrt(a))

def query_local_toilets(lat, lon, radius=1000):
    conn = sqlite3.connect("toilets.db")
    cur = conn.cursor()
    result = []
    try:
        for name, type_, t_lat, t_lon, addr in cur.execute("SELECT 設施名稱, 類別, 緯度, 經度, 位置 FROM toilets"):
            try:
                t_lat, t_lon = float(t_lat), float(t_lon)
            except:
                continue
            d = haversine(lat, lon, t_lat, t_lon)
            if d <= radius:
                result.append({"name": name or "無名稱", "type": "local", "lat": t_lat, "lon": t_lon, "address": addr or "", "distance": d})
        return sorted(result, key=lambda x: x["distance"])
    except Exception as e:
        print("本地查詢錯誤：", e)
        return []
    finally:
        conn.close()

def query_overpass_toilets(lat, lon, radius=1000):
    url = "https://overpass-api.de/api/interpreter"
    query = f"""
    [out:json];
    (node["amenity"="toilets"](around:{radius},{lat},{lon});
     way["amenity"="toilets"](around:{radius},{lat},{lon});
     relation["amenity"="toilets"](around:{radius},{lat},{lon}););
    out center;
    """
    try:
        data = requests.post(url, data=query, timeout=10).json()
    except Exception as e:
        print("Overpass 查詢錯誤：", e)
        return []

    result = []
    for i in data.get("elements", []):
        if i["type"] == "node":
            t_lat, t_lon = i["lat"], i["lon"]
        elif "center" in i:
            t_lat, t_lon = i["center"]["lat"], i["center"]["lon"]
        else:
            continue
        d = haversine(lat, lon, t_lat, t_lon)
        result.append({"name": i.get("tags", {}).get("name", "無名稱"), "type": "osm", "lat": t_lat, "lon": t_lon, "distance": d})
    return sorted(result, key=lambda x: x["distance"])

def send_flex_buttons(reply_token):
    message = FlexSendMessage(
        alt_text="傳送位置或查詢附近廁所",
        contents=BubbleContainer(
            hero=ImageComponent(
                url="https://i.imgur.com/RStA3pp.png",
                size="full", aspectMode="cover", aspectRatio="1.51:1"
            ),
            body=BoxComponent(
                layout="vertical",
                contents=[
                    TextComponent(text="🚽 廁所小幫手", weight="bold", size="lg"),
                    BoxComponent(
                        layout="horizontal",
                        contents=[
                            ButtonComponent(action=LocationAction(label="傳送位置"), style="secondary", height="sm", color="#A7D6FF"),
                            ButtonComponent(action=MessageAction(label="查附近廁所", text="廁所"), style="primary", height="sm", color="#55C9A6")
                        ]
                    )
                ]
            )
        )
    )
    try:
        line_bot_api.reply_message(reply_token, message)
    except LineBotApiError as e:
        print("Flex Message 錯誤：", e)

@app.route("/")
def home():
    return "Bot is running!"

@app.route("/callback", methods=["POST"])
def callback():
    sig = request.headers.get("X-Line-Signature", "")
    body = request.get_data(as_text=True)
    hash = hmac.new(os.getenv("LINE_CHANNEL_SECRET").encode(), body.encode(), hashlib.sha256).digest()
    if base64.b64encode(hash).decode() != sig:
        abort(400)
    try:
        handler.handle(body, sig)
    except:
        abort(500)
    return "OK"

@handler.add(MessageEvent, message=TextMessage)
def handle_text(event):
    text = event.message.text.strip().lower()
    uid = event.source.user_id

    if text in ["開始", "menu", "start", "選單"]:
        send_flex_buttons(event.reply_token)
        return

    if "廁所" in text:
        if uid not in user_locations:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="請先傳送你的位置"))
            return

        lat, lon = user_locations[uid]
        toilets = query_local_toilets(lat, lon) or query_overpass_toilets(lat, lon)
        if not toilets:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="找不到附近的廁所"))
            return

        t = toilets[0]
        source = "本地" if t["type"] == "local" else "OSM"
        map_url = f"https://www.google.com/maps/search/?api=1&query={t['lat']},{t['lon']}"

        flex = {
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
                    {"type": "text", "text": t["name"], "weight": "bold", "size": "lg"},
                    {"type": "text", "text": f"距離 {t['distance']:.1f} 公尺", "size": "sm", "color": "#666", "margin": "md"},
                    {"type": "text", "text": f"來源：{source}", "size": "sm", "color": "#aaa", "margin": "md"}
                ]
            },
            "footer": {
                "type": "box",
                "layout": "vertical",
                "contents": [{
                    "type": "button",
                    "style": "link",
                    "action": {"type": "uri", "label": "🗺 地圖導航", "uri": map_url}
                }]
            }
        }
        line_bot_api.reply_message(event.reply_token, FlexSendMessage(alt_text="最近廁所", contents=flex))
    else:
        line_bot_api.reply_message(event.reply_token, TextSendMessage(text="輸入「廁所」或傳送位置"))

@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
    uid = event.source.user_id
    user_locations[uid] = (event.message.latitude, event.message.longitude)
    line_bot_api.reply_message(event.reply_token, TextSendMessage(text="位置已更新，輸入「廁所」查詢"))

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.getenv("PORT", 10000)))
