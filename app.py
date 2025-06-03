import os
import logging
from math import radians, cos, sin, asin, sqrt
import sqlite3
import requests
from flask import Flask, request, abort
from dotenv import load_dotenv
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError, LineBotApiError
from linebot.models import (
    MessageEvent, TextMessage, TextSendMessage, LocationMessage,
    FlexSendMessage, BubbleContainer, BoxComponent, ImageComponent,
    TextComponent, ButtonComponent, MessageAction, URIAction
)

# 載入環境變數
load_dotenv()

# 初始化 Flask 與 LINE API
app = Flask(__name__)
line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

# 使用者位置暫存字典
user_locations = {}

# 常數設定
BTN_COLOR_LOCATION = "#A7D6FF"
BTN_COLOR_SEARCH = "#55C9A6"
MAX_TOILETS_REPLY = 5

# 設定 logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")

def haversine(lat1, lon1, lat2, lon2):
    """計算兩經緯度間距離(公尺)"""
    lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
    dlat = lat2 - lat1
    dlon = lon2 - lon1
    a = sin(dlat / 2) ** 2 + cos(lat1) * cos(lat2) * sin(dlon / 2) ** 2
    c = 2 * asin(sqrt(a))
    r = 6371000
    return c * r

def query_local_toilets(lat, lon, radius=1000):
    """查本地SQLite廁所資料"""
    try:
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
            if dist <= radius:
                toilets.append({
                    "name": name or "無名稱",
                    "type": "local",
                    "lat": t_lat,
                    "lon": t_lon,
                    "address": addr or "",
                    "distance": dist
                })
        toilets.sort(key=lambda x: x["distance"])
        return toilets
    except Exception as e:
        logging.error(f"資料庫查詢錯誤：{e}")
        return []
    finally:
        conn.close()

def query_overpass_toilets(lat, lon, radius=1000):
    """透過Overpass API查詢OSM廁所資料"""
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
    headers = {"User-Agent": "LineBotToiletFinder/1.0"}
    try:
        resp = requests.post(url, data=query, headers=headers, timeout=10)
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
            "type": "osm",
            "lat": t_lat,
            "lon": t_lon,
            "distance": dist
        })
    toilets.sort(key=lambda x: x["distance"])
    return toilets

def send_flex_buttons(reply_token):
    """傳送主選單 Flex Message"""
    bubble = BubbleContainer(
        hero=ImageComponent(
            url="https://i.imgur.com/RStA3pp.png",
            size="full",
            aspectMode="cover",
            aspectRatio="1.51:1"
        ),
        body=BoxComponent(
            layout="vertical",
            spacing="md",
            contents=[
                TextComponent(text="🚽 廁所小幫手", weight="bold", size="lg"),
                BoxComponent(
                    layout="horizontal",
                    spacing="md",
                    contents=[
                        ButtonComponent(
                            action=LocationAction(label="傳送位置"),
                            style="secondary",
                            height="sm",
                            color=BTN_COLOR_LOCATION,
                            flex=1
                        ),
                        ButtonComponent(
                            action=MessageAction(label="查附近廁所", text="廁所"),
                            style="primary",
                            height="sm",
                            color=BTN_COLOR_SEARCH,
                            flex=1
                        )
                    ]
                )
            ]
        )
    )
    try:
        line_bot_api.reply_message(reply_token, FlexSendMessage(alt_text="請傳送您目前的位置或查詢附近廁所", contents=bubble))
    except LineBotApiError as e:
        logging.error(f"Flex Message 發送失敗：{e}")

def create_toilet_flex_messages(toilets):
    """建立多筆廁所的 Flex Message 清單"""
    bubbles = []
    for t in toilets[:MAX_TOILETS_REPLY]:
        map_url = f"https://www.google.com/maps/search/?api=1&query={t['lat']},{t['lon']}"
        source = "本地資料庫" if t["type"] == "local" else "OpenStreetMap"
        dist_str = f"{t['distance']:.1f} 公尺"
        bubble = {
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
                    {"type": "text", "text": f"距離：{dist_str}", "size": "sm", "color": "#666666", "margin": "md"},
                    {"type": "text", "text": f"來源：{source}", "size": "sm", "color": "#aaaaaa", "margin": "md"}
                ]
            },
            "footer": {
                "type": "box",
                "layout": "vertical",
                "contents": [{
                    "type": "button",
                    "style": "link",
                    "height": "sm",
                    "action": {
                        "type": "uri",
                        "label": "🗺 開啟地圖導航",
                        "uri": map_url
                    }
                }],
                "flex": 0
            }
        }
        bubbles.append(bubble)

    return {
        "type": "carousel",
        "contents": bubbles
    }

@app.route("/")
def home():
    return "✅ LINE Bot is running!"

@app.route("/callback", methods=["POST"])
def callback():
    signature = request.headers.get("X-Line-Signature", "")
    body = request.get_data(as_text=True)
    try:
        handler.handle(body, signature)
    except InvalidSignatureError:
        abort(400)
    except Exception as e:
        logging.error(f"Webhook 處理錯誤: {e}")
        abort(500)
    return "OK"

@handler.add(MessageEvent, message=TextMessage)
def handle_text_message(event):
    user_text = event.message.text.strip().lower()
    user_id = event.source.user_id

    if user_text in ["開始", "menu", "start", "選單"]:
        send_flex_buttons(event.reply_token)
        return

    if "廁所" in user_text:
        if user_id not in user_locations:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="請先傳送您目前的位置，讓我幫您找附近的廁所喔！"))
            return

        lat, lon = user_locations[user_id]
        toilets = query_local_toilets(lat, lon)
        if not toilets:
            toilets = query_overpass_toilets(lat, lon)
        if not toilets:
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="🚽 很抱歉，未能找到附近的廁所。"))
            return

        flex_carousel = create_toilet_flex_messages(toilets)
        try:
            line_bot_api.reply_message(event.reply_token, FlexSendMessage(alt_text="附近廁所列表", contents=flex_carousel))
        except LineBotApiError as e:
            logging.error(f"Flex Message 發送錯誤：{e}")
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text="發生錯誤，請稍後再試。"))
    else:
        line_bot_api.reply_message(event.reply_token, TextSendMessage(text="請輸入「廁所」或傳送位置來查詢附近廁所 🗺️"))

@handler.add(MessageEvent, message=LocationMessage)
def handle_location_message(event):
    user_id = event.source.user_id
    lat, lon = event.message.latitude, event.message.longitude
    user_locations[user_id] = (lat, lon)
    reply = f"📍 位置已更新！\n緯度：{lat}\n經度：{lon}\n請輸入「廁所」查詢附近的廁所。"
    line_bot_api.reply_message(event.reply_token, TextSendMessage(text=reply))

if __name__ == "__main__":
    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
