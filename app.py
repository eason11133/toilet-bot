from flask import Flask, request, abort
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError
from linebot.models import MessageEvent, TextMessage, LocationMessage, TextSendMessage
from dotenv import load_dotenv
import os
import requests
import math
import sqlite3

load_dotenv()

app = Flask(__name__)

line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

# Haversine 公式計算距離
def haversine(lon1, lat1, lon2, lat2):
    R = 6371000  # 地球半徑（公尺）
    phi1 = math.radians(lat1)
    phi2 = math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlambda = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(dlambda / 2) ** 2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))

# 從本地資料庫查詢
def get_local_toilets(lat, lon, radius=500):
    conn = sqlite3.connect("toilets.db")
    cursor = conn.cursor()
    cursor.execute("SELECT name, lat, lon FROM toilets")
    results = []
    for name, t_lat, t_lon in cursor.fetchall():
        distance = haversine(lon, lat, t_lon, t_lat)
        if distance <= radius:
            results.append({
                "name": name,
                "lat": t_lat,
                "lon": t_lon,
                "distance": round(distance, 1)
            })
    conn.close()
    return results

# 查詢 OSM 的公共廁所
def get_overpass_toilets(lat, lon, radius=500):
    overpass_url = "http://overpass-api.de/api/interpreter"
    query = f"""
    [out:json];
    (
      node["amenity"="toilets"](around:{radius},{lat},{lon});
      way["amenity"="toilets"](around:{radius},{lat},{lon});
      relation["amenity"="toilets"](around:{radius},{lat},{lon});
    );
    out center;
    """
    response = requests.post(overpass_url, data=query)
    data = response.json()

    toilets = []
    for element in data["elements"]:
        if "lat" in element and "lon" in element:
            t_lat, t_lon = element["lat"], element["lon"]
        elif "center" in element:
            t_lat, t_lon = element["center"]["lat"], element["center"]["lon"]
        else:
            continue

        name = element["tags"].get("name", "未命名廁所")
        distance = round(haversine(lon, lat, t_lon, t_lat), 1)
        toilets.append({
            "name": name,
            "lat": t_lat,
            "lon": t_lon,
            "distance": distance
        })
    return toilets

# 判斷是否重複
def is_duplicate(toilet, existing_list, threshold=30):
    for t in existing_list:
        d = haversine(toilet["lon"], toilet["lat"], t["lon"], t["lat"])
        if d < threshold:
            return True
    return False

# 整合查詢本地與 OSM
def get_nearest_toilets_combined(lat, lon, radius=500):
    local = get_local_toilets(lat, lon, radius)
    if len(local) >= 3:
        return sorted(local, key=lambda x: x["distance"])[:5]

    osm = get_overpass_toilets(lat, lon, radius)
    merged = local + [t for t in osm if not is_duplicate(t, local)]
    return sorted(merged, key=lambda x: x["distance"])[:5]

# LINE Webhook
@app.route("/callback", methods=["POST"])
def callback():
    signature = request.headers["X-Line-Signature"]
    body = request.get_data(as_text=True)

    try:
        handler.handle(body, signature)
    except InvalidSignatureError:
        abort(400)
    return "OK"

# 處理文字與位置訊息
@handler.add(MessageEvent, message=TextMessage)
def handle_text_message(event):
    if event.message.text.lower() == "hi":
        reply = "哈囉！請傳送您的定位，我會幫您找附近的廁所 🚻"
        line_bot_api.reply_message(event.reply_token, TextSendMessage(text=reply))

@handler.add(MessageEvent, message=LocationMessage)
def handle_location_message(event):
    lat, lon = event.message.latitude, event.message.longitude
    toilets = get_nearest_toilets_combined(lat, lon)

    if not toilets:
        reply = "抱歉，500 公尺內找不到廁所 😢"
    else:
        reply = "最近的廁所有：\n"
        for t in toilets:
            reply += f"{t['name']}（約 {t['distance']} 公尺）\n"

    line_bot_api.reply_message(event.reply_token, TextSendMessage(text=reply))

if __name__ == "__main__":
    app.run()
