import os
import csv
import json
import logging
import requests
import traceback
from math import radians, cos, sin, asin, sqrt
from flask_cors import CORS
from flask import Flask, request, abort, render_template, redirect, url_for, flash
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
import joblib  # 用於載入與保存模型
from sklearn.linear_model import LinearRegression  # 若需要使用回歸模型進行預測


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
TOILET_SPREADSHEET_ID = "1Vg3tiqlXcXjcic2cAWCG-xTXfNzcI7wegEnZx8Ak7ys"  # 廁所主資料（含經緯度）
FEEDBACK_SPREADSHEET_ID = "1vEdk4IV1aaLUjvYSdQsM5SVl0eqn5WosY5ZB3y7GTbg"  # 回饋表單回應

gc = sh = worksheet = None

# 假設模型保存在 'cleanliness_model.pkl'
BASE_DIR = os.path.abspath(os.path.dirname(__file__))

def load_cleanliness_model():
    try:
        model_path = os.path.join(BASE_DIR, 'models', 'clean_model.pkl')
        model = joblib.load(model_path)
        logging.info("✅ 清潔度預測模型已載入")
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

# 載入模型
cleanliness_model = load_cleanliness_model()

def init_gsheet():
    global gc, worksheet, feedback_worksheet
    try:
        if not GSHEET_CREDENTIALS_JSON:
            logging.error("❌ GSHEET_CREDENTIALS_JSON 環境變數未設定")
            return
        credentials_dict = json.loads(GSHEET_CREDENTIALS_JSON)
        creds = ServiceAccountCredentials.from_json_keyfile_dict(credentials_dict, GSHEET_SCOPE)
        gc = gspread.authorize(creds)

        # ✅ 廁所主表單（for 新增、回復 CSV）
        toilet_sh = gc.open_by_key(TOILET_SPREADSHEET_ID)
        worksheet = toilet_sh.sheet1
        logging.info("✅ 廁所主表單 worksheet 初始化成功")

        # ✅ 回饋表單（for 查詢回饋）
        feedback_sh = gc.open_by_key(FEEDBACK_SPREADSHEET_ID)
        feedback_worksheet = feedback_sh.worksheet("表單回應 1")  # 表單名稱要正確
        logging.info("✅ 回饋表單 worksheet 初始化成功")

    except Exception as e:
        logging.error(f"❌ Google Sheets 初始化失敗: {e}")
        worksheet = None
        feedback_worksheet = None

def restore_csv_from_gsheet():
    if worksheet is None:
        logging.warning("🛑 無法從 Sheets 回復資料，因為 worksheet 尚未初始化")
        return
    try:
        records = worksheet.get_all_records()
        if not records:
            logging.info("📭 Google Sheets 沒有任何資料可回復")
            return

        logging.info(f"欄位名稱為：{records[0].keys()}")  # Debug 用

        os.makedirs(os.path.dirname(TOILETS_FILE_PATH), exist_ok=True)
        with open(TOILETS_FILE_PATH, "w", encoding="utf-8") as f:
            f.write("code,villagecode,village,source,name,address,note,lat,lon,level,category,open,provider,count,\n")
            for row in records:
                name = row.get('name', '').strip()
                address = row.get('address', '').strip()
                lat = str(row.get('lat', '')).strip()
                lon = str(row.get('lon', '')).strip()
                
                if not name or not lat or not lon:
                    logging.warning(f"⚠️ 跳過缺欄位資料：{row}")
                    continue  # 若有缺欄位則跳過

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
    if feedback_worksheet is None:
        logging.error("🛑 回饋 worksheet 尚未初始化")
        return []

    try:
        records = feedback_worksheet.get_all_records()
        for row in records:
            name_field = next((k for k in row if "廁所名稱" in k), None)
            rating_field = next((k for k in row if "清潔度" in k), None)
            paper_field = next((k for k in row if "衛生紙" in k), None)
            access_field = next((k for k in row if "無障礙" in k), None)
            time_field = next((k for k in row if "使用廁所的時間" in k), None)
            comment_field = next((k for k in row if "使用者留言" in k), None)
            score_field = next((k for k in row if "清潔度預測" in k or "cleanliness_score" in k), None)  # ✅ 新增這行

            if not name_field or row.get(name_field, "").strip() != toilet_name.strip():
                continue

            feedback = {
                "rating": row.get(rating_field, "無"),
                "toilet_paper": row.get(paper_field, "無資料"),
                "accessibility": row.get(access_field, "無資料"),
                "time_of_use": row.get(time_field, "未填寫"),
                "comment": row.get(comment_field, "無留言"),
                "cleanliness_score": row.get(score_field, "未預測")  # ✅ 新增這行
            }
            feedbacks.append(feedback)
        logging.info(f"🔍 共取得 {len(feedbacks)} 筆回饋 for {toilet_name}")
    except Exception as e:
        logging.error(f"❌ 讀取回饋資料失敗: {e}")
    return feedbacks

def predict_cleanliness(features):
    try:
        if cleanliness_model is None:
            logging.error("❌ 無法預測，模型尚未載入")
            return None

        # 載入 label encoder（用來還原數值）
        encoder_path = os.path.join(BASE_DIR, 'models', 'label_encoder.pkl')
        label_encoder = joblib.load(encoder_path)

        # 取得分類的機率分布
        probs = cleanliness_model.predict_proba([features])[0]
        labels = label_encoder.inverse_transform(range(len(probs)))
        expected_score = round(sum(p * l for p, l in zip(probs, labels)), 2)

        logging.info(f"預測期望清潔度: {expected_score}")
        return expected_score

    except Exception as e:
        logging.error(f"預測清潔度失敗: {e}")
        return None

def save_feedback_to_gsheet(toilet_name, rating, toilet_paper, accessibility, time_of_use, comment, cleanliness_score):
    try:
        if feedback_worksheet is None:
            logging.error("🛑 回饋 worksheet 尚未初始化")
            return False

        # 🟨 正確的填寫順序，共 11 欄，其中第 10 欄為清潔度預測
        row_data = [
            datetime.utcnow().strftime("%Y/%m/%d %p %I:%M:%S"),  # 第 1 欄：時間戳記
            toilet_name,       # 第 2 欄：廁所名稱
            "",                # 第 3 欄：廁所地址（由 Bot 自動填，暫空）
            rating,            # 第 4 欄：清潔度評分
            toilet_paper,      # 第 5 欄：是否有衛生紙
            accessibility,     # 第 6 欄：無障礙設施
            time_of_use,       # 第 7 欄：使用廁所的時間
            comment,           # 第 8 欄：使用者留言
            "",                # 第 9 欄：電子郵件地址（留空）
            cleanliness_score, # ✅ 第 10 欄：清潔度預測
            ""                 # 第 11 欄：使用者 ID（可日後補上）
        ]

        feedback_worksheet.append_row(row_data)
        logging.info("✅ 清潔度預測結果已正確寫入第 10 欄")
        return True

    except Exception as e:
        logging.error(f"❌ 寫入 Google Sheets 失敗: {e}")
        return False

# === 建立 Flex Message ===
def create_toilet_flex_messages(toilets, expanded_names=set(), show_delete=False, uid=None):
    from urllib.parse import quote
    bubbles = []

    for toilet in toilets[:MAX_TOILETS_REPLY]:
        is_expanded = toilet["name"] in expanded_names
        actions = []

        # 基本按鈕：導航 + 查看回饋
        actions.append({
            "type": "uri",
            "label": "導航",
            "uri": f"https://www.google.com/maps/search/?api=1&query={toilet['lat']},{toilet['lon']}"
        })
        actions.append({
            "type": "uri",
            "label": "查看回饋",
            "uri": f"https://school-i9co.onrender.com/toilet_feedback/{quote(toilet['name'])}"
        })

        # 展開狀態下：加入其他操作按鈕
        if is_expanded:
            # 收藏邏輯
            if toilet.get("type") == "favorite" and uid is not None:
                actions.append({
                    "type": "postback",
                    "label": "移除最愛",
                    "data": f"remove_fav:{toilet['name']}:{toilet['lat']}:{toilet['lon']}"
                })
            elif uid is not None:
                actions.append({
                    "type": "postback",
                    "label": "加入最愛",
                    "data": f"add:{toilet['name']}:{toilet['lat']}:{toilet['lon']}"
                })

            # 刪除廁所（只限 user 新增）
            if show_delete and toilet.get("type") == "user" and uid is not None:
                actions.append({
                    "type": "postback",
                    "label": "刪除廁所",
                    "data": f"confirm_delete:{toilet['name']}:{toilet['address']}:{toilet['lat']}:{toilet['lon']}"
                })

            # 廁所回饋表單
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

            # 收起按鈕
            actions.append({
                "type": "postback",
                "label": "▲ 收起",
                "data": f"collapse:{toilet['name']}"
            })
        else:
            # 預設折疊狀態下加上「展開」按鈕
            actions.append({
                "type": "postback",
                "label": "▼ 更多",
                "data": f"expand:{toilet['name']}"
            })

        # 組合 Bubble
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
                        "style": "primary" if i == 0 else "secondary",
                        "height": "sm",
                        "action": a
                    } for i, a in enumerate(actions)
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
    address = "某個地址"

    if feedback_worksheet is None:
        logging.error("🛑 回饋 worksheet 尚未初始化")
        return render_template("toilet_feedback.html", name=toilet_name, address=address, comments=[],
                               cleanliness_score="未預測", toilet_paper_summary="無", accessibility_summary="無", comment_count=0)

    try:
        records = feedback_worksheet.get_all_records()
        for row in records:
            name_field = next((k for k in row if "廁所名稱" in k), None)
            address_field = next((k for k in row if "廁所地址" in k), None)

            if not name_field or row.get(name_field, "").strip() != toilet_name.strip():
                continue

            if address == "某個地址" and address_field:
                address = row.get(address_field, "無地址")
    except Exception as e:
        logging.error(f"❌ 讀取回饋資料時抓取地址失敗: {e}")

    # === 新增：布林欄位統計
    def summarize_boolean_field(feedbacks, key):
        """'有' 視為 1，其餘為 0，回傳 '有' 或 '無'"""
        has_count = sum(1 for fb in feedbacks if fb.get(key, '').strip() == "有")
        return "有" if has_count >= len(feedbacks) / 2 else "無"

    toilet_paper_summary = summarize_boolean_field(feedbacks, "toilet_paper")
    accessibility_summary = summarize_boolean_field(feedbacks, "accessibility")

    # === 新增：清潔度預測摘要（取第一筆）
    first_cleanliness_score = None
    if feedbacks and "cleanliness_score" in feedbacks[0]:
        first_cleanliness_score = feedbacks[0]["cleanliness_score"]

    comment_count = len(feedbacks)

    return render_template(
        "toilet_feedback.html",
        name=toilet_name,
        address=address,
        comments=feedbacks,
        cleanliness_score=first_cleanliness_score,
        toilet_paper_summary=toilet_paper_summary,
        accessibility_summary=accessibility_summary,
        comment_count=comment_count
    )

@app.route("/submit_feedback/<toilet_name>", methods=["POST"])
def submit_feedback(toilet_name):
    try:
        # 獲取表單資料
        rating = request.form.get("rating")
        toilet_paper = request.form.get("toilet_paper")
        accessibility = request.form.get("accessibility")
        time_of_use = request.form.get("time_of_use")  # 使用廁所時間
        comment = request.form.get("comment")  # 使用者留言

        # 必填欄位檢查
        if not all([rating, toilet_paper, accessibility]):
            flash("請填寫所有必填欄位！", "warning")
            return redirect(url_for("toilet_feedback", toilet_name=toilet_name))

        # ✅ 中文選項轉換成數值
        mapping = {
            "有": 1,
            "沒有": 0,
            "不確定/沒注意": 0.5,
            "": 0
        }

        try:
            rating_val = float(rating)
            tp = mapping.get(toilet_paper.strip(), 0)
            acc = mapping.get(accessibility.strip(), 0)
            features = [rating_val, tp, acc]
        except Exception as e:
            logging.error(f"特徵轉換失敗: {e}")
            flash("預測清潔度時發生錯誤，請確認欄位填寫是否正確", "danger")
            return redirect(url_for("toilet_feedback", toilet_name=toilet_name))

        # ✅ 模型預測
        cleanliness_score = predict_cleanliness(features)

        # ✅ 儲存至 Google Sheets
        save_feedback_to_gsheet(toilet_name, rating, toilet_paper, accessibility, time_of_use, comment, cleanliness_score)

        flash(f"感謝您的回饋！預測的清潔度分數為：{cleanliness_score}", "success")
        return redirect(url_for("toilet_feedback", toilet_name=toilet_name))  # 返回廁所回饋頁面

    except Exception as e:
        logging.error(f"回饋提交錯誤: {e}")
        flash("提交失敗，請稍後再試！", "danger")
        return redirect(url_for("toilet_feedback", toilet_name=toilet_name))

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

    # --- 展開更多 ---
    if data.startswith("expand:"):
        name = data.split(":")[1]
        if uid not in user_locations:
            line_bot_api.reply_message(event.reply_token, TextSendMessage("請先傳送位置"))
            return
        lat, lon = user_locations[uid]
        toilets = query_local_toilets(lat, lon) + query_overpass_toilets(lat, lon)
        flex = create_toilet_flex_messages(toilets, expanded_names={name}, uid=uid)
        line_bot_api.reply_message(event.reply_token, FlexSendMessage("廁所資訊", flex))
        return

    # --- 收起 ---
    elif data.startswith("collapse:"):
        name = data.split(":")[1]
        if uid not in user_locations:
            line_bot_api.reply_message(event.reply_token, TextSendMessage("請先傳送位置"))
            return
        lat, lon = user_locations[uid]
        toilets = query_local_toilets(lat, lon) + query_overpass_toilets(lat, lon)
        flex = create_toilet_flex_messages(toilets, expanded_names=set(), uid=uid)
        line_bot_api.reply_message(event.reply_token, FlexSendMessage("廁所資訊", flex))
        return

    # --- 加入收藏 ---
    elif data.startswith("add:"):
        try:
            _, name, lat, lon = data.split(":")
        except ValueError:
            line_bot_api.reply_message(event.reply_token, TextSendMessage("❌ 格式錯誤，請重新操作"))
            return

        if uid not in user_locations:
            line_bot_api.reply_message(event.reply_token, TextSendMessage("請先傳送位置"))
            return

        found = False
        lat_user, lon_user = user_locations[uid]
        all_toilets = query_local_toilets(lat_user, lon_user) + query_overpass_toilets(lat_user, lon_user)
        for toilet in all_toilets:
            if toilet['name'] == name and str(toilet['lat']) == lat and str(toilet['lon']) == lon:
                add_to_favorites(uid, toilet)
                found = True
                break
        msg = f"✅ 已收藏 {name}" if found else "找不到該廁所，收藏失敗"
        line_bot_api.reply_message(event.reply_token, TextSendMessage(msg))
        return

    # --- 移除收藏 ---
    elif data.startswith("remove_fav:"):
        try:
            _, name, lat, lon = data.split(":")
            removed = remove_from_favorites(uid, name, lat, lon)
            msg = f"✅ 已從最愛移除 {name}" if removed else "❌ 移除失敗，請稍後再試"
            line_bot_api.reply_message(event.reply_token, TextSendMessage(msg))
        except:
            line_bot_api.reply_message(event.reply_token, TextSendMessage("❌ 移除最愛失敗，格式錯誤"))
        return

    # --- 確認刪除 ---
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
            line_bot_api.reply_message(event.reply_token, TextSendMessage("❌ 格式錯誤，請重新操作"))
        return

@handler.add(MessageEvent, message=LocationMessage)
def handle_location(event):
    uid = event.source.user_id
    lat, lon = event.message.latitude, event.message.longitude
    user_locations[uid] = (lat, lon)
    line_bot_api.reply_message(event.reply_token, TextSendMessage(text="✅ 位置已更新，請點選『附近廁所』查詢"))

if __name__ == "__main__":
    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
