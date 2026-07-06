import os
import json
import logging
import sqlite3
import threading
import time
import urllib.parse
from urllib.parse import quote, unquote, parse_qs
from datetime import datetime

from flask import request, abort
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError, LineBotApiError
from linebot.models import (
    MessageEvent, TextMessage, LocationMessage,
    TextSendMessage, FlexSendMessage,
    QuickReply, QuickReplyButton, LocationAction, MessageAction,
    PostbackEvent, PostbackAction,
)

from config import TW_TZ, LOC_MAX_CONCURRENCY
from core.database import POSTGRES_ENABLED, _pg_connect, ANALYTICS_DB_PATH, _get_db, psycopg2
from core.cache import _CACHE
from core.i18n import (
    set_user_lang, get_user_lang, T, L, _localize_outgoing_messages,
)
from core.utils import norm_coord, haversine
from linebot_app.reply_tokens import CHANNEL_ACCESS_TOKEN, show_loading
from linebot_app.dedupe import is_duplicate_and_mark_event
from linebot_app.replies import (
    make_location_quick_reply,
    make_retry_location_text,
    make_no_toilet_quick_reply,
)
from linebot_app.consent import ensure_consent_or_prompt
from toilet.favorites import add_to_favorites, remove_from_favorites, get_user_favorites
from toilet.feedback import build_feedback_index
from toilet.status import build_status_index
from toilet.identity import make_query_id, _make_toilet_id
from toilet.search import build_nearby_toilets
from toilet.recommendation_logs import (
    log_recommendation_results,
    log_shadow_recommendation_results,
    log_user_action,
)
from features.usage import build_usage_review_text, build_ai_nearby_recommendation

line_bot_api = LineBotApi(os.getenv("LINE_CHANNEL_ACCESS_TOKEN"))
handler = WebhookHandler(os.getenv("LINE_CHANNEL_SECRET"))

_LOC_SEM = threading.Semaphore(LOC_MAX_CONCURRENCY)

PUBLIC_URL = (os.getenv("PUBLIC_URL") or "").rstrip("/")
LIFF_STATUS_ID = os.getenv("LIFF_STATUS_ID", "")

LINE_REPLY_MAX = 5

# push fallback 去重（避免重送 / 重試造成重複推播）
_PUSH_DEDUPE = getattr(globals(), "_PUSH_DEDUPE", {})
_PUSH_LOCK = threading.Lock()
PUSH_FALLBACK_DEDUPE_WINDOW = int(os.getenv("PUSH_FALLBACK_DEDUPE_WINDOW", "180"))

# === 共用狀態 ===
user_locations = {}
pending_delete_confirm = {}
user_search_count = {}
user_loc_mode = {}  # 新增：記錄使用者目前查廁所模式（"normal" or "ai"）

# 建議：高併發時避免競態
_dict_lock = threading.Lock()

# === 座標 → 區域名稱推斷 ===
# Research dashboard V3:
# 1) First use local bounding boxes for landmark / district / county-level naming.
# 2) If nothing matches, do NOT collapse everything into "其他區域".
#    Return a stable 0.02-degree grid label so unknown points remain separable in reports.
# 3) _backfill_area_names_async() writes inferred names back to analytics_events, so old rows
#    stop being re-inferred on every dashboard render.
_AREA_NAME_CACHE = {}
_AREA_RULES = [
    # Micro-locations first: these are better for a demand-cluster report than broad districts.
    # Order matters. Smaller, more human-readable places should come before larger areas.
    ("中山雙連周邊", 25.0520, 25.0618, 121.5160, 121.5255),
    ("中山站周邊",   25.0490, 25.0556, 121.5160, 121.5248),
    ("雙連站周邊",   25.0550, 25.0625, 121.5160, 121.5258),
    ("北門／台北車站西側", 25.0460, 25.0535, 121.5060, 121.5148),
    ("台北車站核心", 25.0430, 25.0505, 121.5140, 121.5235),
    ("京站／華陰街", 25.0485, 25.0552, 121.5128, 121.5208),
    ("西門町",   25.0390, 25.0508, 121.4980, 121.5115),
    ("龍山寺／艋舺", 25.0320, 25.0408, 121.4950, 121.5065),
    ("東門／永康街", 25.0290, 25.0378, 121.5260, 121.5355),
    ("公館商圈",     25.0090, 25.0248, 121.5250, 121.5455),
    ("信義商圈", 25.0280, 25.0415, 121.5580, 121.5755),
    ("松山車站／饒河", 25.0460, 25.0555, 121.5700, 121.5835),
    ("南港車站", 25.0490, 25.0570, 121.6030, 121.6155),
    ("板橋車站", 25.0090, 25.0208, 121.4550, 121.4705),
    ("府中／板橋舊站", 25.0065, 25.0148, 121.4555, 121.4645),
    ("台中車站", 24.1320, 24.1425, 120.6800, 120.6920),
    ("台南車站", 22.9910, 23.0025, 120.2050, 120.2180),
    ("高雄車站", 22.6330, 22.6440, 120.2960, 120.3120),

    # Taipei districts, intentionally rough but less important than micro-locations above.
    ("中正區", 24.985, 25.055, 121.500, 121.545),
    ("萬華區", 25.015, 25.055, 121.470, 121.515),
    ("大同區", 25.045, 25.075, 121.500, 121.525),
    ("中山區", 25.045, 25.085, 121.515, 121.555),
    ("松山區", 25.035, 25.070, 121.545, 121.585),
    ("大安區", 25.000, 25.045, 121.520, 121.565),
    ("信義區", 25.015, 25.050, 121.555, 121.595),
    ("士林區", 25.075, 25.165, 121.500, 121.590),
    ("北投區", 25.105, 25.215, 121.455, 121.570),
    ("內湖區", 25.045, 25.100, 121.565, 121.650),
    ("南港區", 25.025, 25.075, 121.585, 121.690),
    ("文山區", 24.955, 25.015, 121.530, 121.610),

    # New Taipei / surrounding common areas
    ("板橋區", 24.990, 25.040, 121.430, 121.500),
    ("新莊區", 25.015, 25.065, 121.420, 121.470),
    ("三重區", 25.045, 25.085, 121.465, 121.510),
    ("蘆洲區", 25.070, 25.105, 121.450, 121.490),
    ("中和區", 24.985, 25.020, 121.480, 121.535),
    ("永和區", 25.000, 25.025, 121.500, 121.530),
    ("新店區", 24.930, 25.000, 121.500, 121.585),
    ("汐止區", 25.045, 25.095, 121.620, 121.710),
    ("土城區", 24.950, 25.005, 121.410, 121.480),
    ("樹林區", 24.940, 25.010, 121.360, 121.430),
    ("林口區", 25.055, 25.105, 121.340, 121.405),
    ("淡水區", 25.145, 25.235, 121.420, 121.520),
    ("基隆市區", 25.105, 25.170, 121.690, 121.805),
    ("桃園區", 24.965, 25.035, 121.250, 121.345),

    # County / city-level fallback rules for government-facing reports.
    ("台北市", 24.955, 25.220, 121.450, 121.700),
    ("新北市", 24.780, 25.320, 121.280, 122.030),
    ("基隆市", 25.080, 25.180, 121.650, 121.820),
    ("桃園市", 24.800, 25.130, 121.000, 121.500),
    ("新竹縣市", 24.660, 24.950, 120.850, 121.250),
    ("苗栗縣", 24.250, 24.750, 120.600, 121.050),
    ("台中市", 24.000, 24.450, 120.450, 121.450),
    ("彰化縣", 23.780, 24.180, 120.250, 120.650),
    ("南投縣", 23.450, 24.250, 120.600, 121.350),
    ("雲林縣", 23.450, 23.850, 120.050, 120.650),
    ("嘉義縣市", 23.180, 23.650, 120.050, 120.850),
    ("台南市", 22.880, 23.420, 120.000, 120.700),
    ("高雄市", 22.450, 23.300, 120.000, 121.050),
    ("屏東縣", 21.880, 22.880, 120.350, 121.050),
    ("宜蘭縣", 24.300, 25.050, 121.550, 122.100),
    ("花蓮縣", 23.000, 24.500, 121.100, 121.850),
    ("台東縣", 21.900, 23.500, 120.700, 121.650),
    ("澎湖縣", 23.150, 23.850, 119.250, 119.850),
    ("金門縣", 24.300, 24.550, 118.150, 118.550),
    ("連江縣", 25.900, 26.400, 119.850, 120.200),
]

def _try_acquire_loc_slot() -> bool:
    try:
        return _LOC_SEM.acquire(blocking=False)
    except Exception:
        return False

def _release_loc_slot():
    try:
        _LOC_SEM.release()
    except Exception:
        pass

def _base_url():
    # PUBLIC_URL 優先，沒設定就用 request.url_root
    try:
        if PUBLIC_URL:
            return PUBLIC_URL.rstrip("/")
        return request.url_root.rstrip("/")
    except Exception:
        # 保底：至少不要噴錯
        return (PUBLIC_URL or "").rstrip("/")

def _append_uid_lang(url: str, uid: str, lang: str = None, extra: dict = None) -> str:
    """把 uid/lang 安全地加到 URL querystring（避免 LIFF 頁面拿不到語言）"""
    try:
        if not uid and not lang and not extra:
            return url
        parsed = urllib.parse.urlparse(url)
        qs = dict(urllib.parse.parse_qsl(parsed.query, keep_blank_values=True))
        if uid:
            qs.setdefault("uid", uid)
        if lang:
            qs.setdefault("lang", "en" if (lang or '').lower().startswith('en') else "zh")
        if extra:
            for k, v in extra.items():
                if v is None:
                    continue
                qs.setdefault(str(k), str(v))
        new_q = urllib.parse.urlencode(qs)
        return urllib.parse.urlunparse(parsed._replace(query=new_q))
    except Exception:
        return url

def _user_lang_q(uid: str) -> str:
    try:
        return "en" if get_user_lang(uid) == "en" else "zh"
    except Exception:
        return "zh"

def _status_liff_url(lat=None, lon=None, uid=None):
    """回傳狀態回報 LIFF 頁面網址。

    ✅ 重要：LIFF 網頁本身不會自動知道你在 LINE 裡切到哪個語言，所以我們在 URL 上帶：
      - uid：讓後端可以查 get_user_lang(uid)
      - lang：讓前端（或後端 redirect）可以直接用 ?lang=en 切語言
    若沒帶座標，讓 LIFF 自己取定位。
    """
    if not PUBLIC_URL:
        return None

    base = f"{PUBLIC_URL}/status_liff"

    params = {}
    # 讓 LIFF 能知道是誰（也方便後端做預設語言）
    if uid:
        params["uid"] = uid
        try:
            params["lang"] = "en" if get_user_lang(uid) == "en" else "zh"
        except Exception:
            params["lang"] = "zh"

    if lat is not None and lon is not None:
        params["lat"] = norm_coord(lat)
        params["lon"] = norm_coord(lon)

    if not params:
        return base
    return base + "?" + urllib.parse.urlencode(params)

def safe_reply(event, messages):
    """
    ✅ 安全回覆（零 push 版本）：
    - 只使用 reply_message 回覆（不做 push fallback），避免額外消耗月額度與避免 429 洗版
    - 若 reply_token 無效/過期/不存在：直接略過（只記錄 log）
    - 保留最多 5 則訊息限制，避免 LINE API 拒絕
    """
    if messages is None:
        return
    if not isinstance(messages, list):
        messages = [messages]
    messages = [m for m in messages if m is not None]
    if not messages:
        return

    # LINE 規則：一次 reply 最多 5 則
    if len(messages) > LINE_REPLY_MAX:
        logging.warning(f"[safe_reply] messages too many ({len(messages)}), truncating to {LINE_REPLY_MAX}.")
        messages = messages[:LINE_REPLY_MAX]

    # 根據使用者語言做最後一層在地化，盡量避免漏網之魚
    uid = getattr(getattr(event, "source", None), "user_id", None)
    messages = _localize_outgoing_messages(messages, uid=uid)

    # 沒有 reply_token（或事件不支援 reply）就不送，避免用 push
    reply_token = getattr(event, "reply_token", None)
    if not reply_token:
        logging.warning("[safe_reply] no reply_token; skip (push disabled).")
        return

    try:
        line_bot_api.reply_message(reply_token, messages)
        return
    except LineBotApiError as e:
        # 解析錯誤訊息
        try:
            msg_txt = getattr(getattr(e, "error", None), "message", "") or str(e)
        except Exception:
            msg_txt = str(e)

        # reply_token 無效/過期：不做 push，直接跳過
        if "Invalid reply token" in msg_txt:
            logging.warning(f"[safe_reply] invalid reply token; skip (push disabled). err={msg_txt}")
            return

        # 月額度/限流/其他：只記錄，不重試、不 fallback
        logging.warning(f"[safe_reply] reply_message failed; skip (push disabled). err={msg_txt}")
        return
    except Exception as ex:
        logging.error(f"[safe_reply] unexpected error: {ex}", exc_info=True)
        return

def _too_old_to_reply(event, limit_seconds=None):
    try:
        if limit_seconds is None:
            limit_seconds = int(os.getenv("MAX_EVENT_AGE_SEC", "1800"))

        evt_ms = int(getattr(event, "timestamp", 0))
        if evt_ms <= 0:
            return False

        now_ms = int(time.time() * 1000)
        return (now_ms - evt_ms) > (limit_seconds * 1000)
    except Exception:
        return False

def reply_only(event, messages):
    try:
        uid = getattr(getattr(event, "source", None), "user_id", None)
        messages = _localize_outgoing_messages(messages, uid=uid)
        line_bot_api.reply_message(event.reply_token, messages)
    except LineBotApiError as e:
        msg_txt = ""
        try:
            msg_txt = getattr(getattr(e, "error", None), "message", "") or str(e)
        except Exception:
            msg_txt = str(e)
        logging.warning(f"reply_message 失敗（不做 push）：{msg_txt}")
    except Exception as ex:
        logging.error(f"reply_only 執行錯誤：{ex}")

def log_analytics_event(
    user_id=None,
    event_type="query",
    result_count=0,
    success=1,
    response_time_ms=None,
    lat=None,
    lon=None,
    area_name=None,
    query_text=None,
    created_at=None
):
    try:
        rt_ms = int(response_time_ms) if response_time_ms is not None else None
        if event_type == "location_query" and (rt_ms is None or rt_ms <= 0):
            return
        if POSTGRES_ENABLED:
            conn = _pg_connect()
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO analytics_events
                (user_id, event_type, result_count, success, response_time_ms, lat, lon, area_name, query_text, created_at)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            """, (
                user_id,
                event_type,
                int(result_count or 0),
                int(1 if success else 0),
                rt_ms,
                float(lat) if lat is not None else None,
                float(lon) if lon is not None else None,
                area_name,
                query_text,
                created_at or datetime.now(TW_TZ)
            ))
            conn.commit()
            conn.close()
            return

        conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO analytics_events
            (user_id, event_type, result_count, success, response_time_ms, lat, lon, area_name, query_text, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            user_id,
            event_type,
            int(result_count or 0),
            int(1 if success else 0),
            rt_ms,
            float(lat) if lat is not None else None,
            float(lon) if lon is not None else None,
            area_name,
            query_text,
            created_at or datetime.now(TW_TZ).isoformat()
        ))
        conn.commit()
        conn.close()
    except Exception as e:
        logging.warning(f"log_analytics_event failed: {e}")

def _unknown_area_grid_label(lat, lon):
    try:
        # 0.02 degree is roughly 2km. It separates unknown clusters without leaking exact coordinates.
        return f"待分類格網 {round(float(lat), 2):.2f},{round(float(lon), 2):.2f}"
    except Exception:
        return "待分類區域"

def get_area_name(lat, lon):
    try:
        lat = float(lat)
        lon = float(lon)
    except Exception:
        return "待分類區域"

    key = f"{round(lat, 3):.3f},{round(lon, 3):.3f}"
    cached = _AREA_NAME_CACHE.get(key)
    if cached:
        return cached

    for name, min_lat, max_lat, min_lon, max_lon in _AREA_RULES:
        if min_lat <= lat <= max_lat and min_lon <= lon <= max_lon:
            _AREA_NAME_CACHE[key] = name
            return name

    inferred = _unknown_area_grid_label(lat, lon)
    _AREA_NAME_CACHE[key] = inferred
    return inferred

def _short_txt(s, n=60):
    try:
        s = (s or "").strip()
        return s if len(s) <= n else (s[:n-1] + "…")
    except Exception:
        return s

def create_toilet_flex_messages(toilets, uid=None, query_id=None):
    indicators = build_feedback_index()
    status_map = build_status_index()

    def _nearby_indicator(lat_s, lon_s, default=None):
        default = default or {"paper": "?", "access": "?", "avg": None}

        # 先 exact match
        hit = indicators.get((lat_s, lon_s))
        if hit:
            return hit

        # 再容許約 15 公尺內的回饋座標
        try:
            lat_f = float(lat_s)
            lon_f = float(lon_s)
            best = None
            best_d = 999999

            for (ilat, ilon), val in indicators.items():
                try:
                    d = haversine(lat_f, lon_f, float(ilat), float(ilon))
                except Exception:
                    continue

                if d <= 15 and d < best_d:
                    best = val
                    best_d = d

            return best or default

        except Exception:
            return default

    # === 資料來源顯示對照（中/英）===
    SOURCE_LABEL = {
        "public_csv": ("政府開放資料", "Government Open Data"),
        "sheet": ("使用者新增", "User Added"),
        "osm": ("OpenStreetMap", "OpenStreetMap"),
        "user": ("使用者新增", "User Added"),
        "favorite": ("我的最愛", "My Favorites"),
    }

    # === 狀態（中/英）===
    STATUS_EN = {
        "恢復正常": "Back to normal",
        "有人排隊": "Queue present",
        "缺衛生紙": "No toilet paper",
        "暫停使用": "Out of service",
    }

    bubbles = []
    for toilet in toilets[:5]:
        actions = []

        lat_s = norm_coord(toilet['lat'])
        lon_s = norm_coord(toilet['lon'])
        addr_text = toilet.get('address') or L(uid, "（無地址，使用座標）", "(No address, using coordinates)")

        toilet_id = _make_toilet_id(toilet)
        # -------------------------
        # ✅ title（修正：不要先拼中文再 L）
        # -------------------------
        title = (toilet.get('name') or "").strip()
        if (not title) or title == "無名稱":
            ph = (toilet.get("place_hint") or "").strip()

            zh_title = f"{ph}（附近）廁所" if ph else "（未命名）廁所"
            en_title = f"Toilet near {ph}" if ph else "(Unnamed) Toilet"
            title = L(uid, zh_title, en_title)

        # === 來源文字（小小顯示）===
        source_type = toilet.get("type", "")
        src_zh_en = SOURCE_LABEL.get(source_type, ("其他來源", "Other source"))
        source_text = L(uid, src_zh_en[0], src_zh_en[1])

        # 只讀三個欄位（可能為空）
        lvl   = (toilet.get("level") or "").strip()
        pos   = (toilet.get("floor_hint") or "").strip()
        hours = (toilet.get("open_hours") or "").strip()

        # 額外顯示行
        extra_lines = []
        st_obj = status_map.get((lat_s, lon_s))
        if st_obj and st_obj.get("status"):
            st = st_obj["status"]
            emoji = "🟡" if st == "有人排隊" else ("🧻" if st == "缺衛生紙" else ("⛔" if st == "暫停使用" else "✅"))
            st_en = STATUS_EN.get(st, st)

            extra_lines.append({
                "type": "text",
                "text": _short_txt(L(uid, f"{emoji} 狀態：{st}", f"{emoji} Status: {st_en}")),
                "size": "sm", "color": "#666666", "wrap": True
            })

        if lvl or pos:
            if lvl and pos and (lvl.strip().lower() != pos.strip().lower()):
                extra_lines.append({
                    "type": "text",
                    "text": _short_txt(L(uid, f"🏷 樓層：{lvl}", f"🏷 Floor: {lvl}")),
                    "size": "sm", "color": "#666666", "wrap": True
                })
                extra_lines.append({
                    "type": "text",
                    "text": _short_txt(L(uid, f"🧭 位置：{pos}", f"🧭 Location: {pos}")),
                    "size": "sm", "color": "#666666", "wrap": True
                })
            else:
                val = pos or lvl
                extra_lines.append({
                    "type": "text",
                    "text": _short_txt(L(uid, f"🧭 位置/樓層：{val}", f"🧭 Location/Floor: {val}")),
                    "size": "sm", "color": "#666666", "wrap": True
                })

        if hours:
            extra_lines.append({
                "type": "text",
                "text": _short_txt(L(uid, f"🕒 開放：{hours}", f"🕒 Hours: {hours}")),
                "size": "sm", "color": "#666666", "wrap": True
            })

        # 指示燈文字（paper/access/avg）
                ind = _nearby_indicator(lat_s, lon_s, {"paper": "?", "access": "?", "avg": None})

        # ⭐ 評分顯示不分語言
        star_text = f"⭐{ind['avg']}" if ind.get("avg") is not None else "⭐—"

        # 🧻 paper 顯示
        if ind.get("paper") == "有":
            paper_text = L(uid, "🧻有", "🧻Yes")
        elif ind.get("paper") == "沒有":
            paper_text = L(uid, "🧻無", "🧻No")
        else:
            paper_text = "🧻—"

        # ♿ access 顯示
        if ind.get("access") == "有":
            access_text = L(uid, "♿有", "♿Yes")
        elif ind.get("access") == "沒有":
            access_text = L(uid, "♿無", "♿No")
        else:
            access_text = "♿—"

        # 按鈕
        base = _base_url()

        nav_url = (
            f"{base}/go_to_toilet"
            f"?qid={quote(query_id or '')}"
            f"&uid={quote(uid or '')}"
            f"&tid={quote(toilet_id)}"
            f"&lat={quote(lat_s)}"
            f"&lon={quote(lon_s)}"
            f"&name={quote(title)}"
        )

        actions.append({
            "type": "uri",
            "label": L(uid, "導航", "Navigate"),
            "uri": nav_url
        })

        actions.append({
            "type": "uri",
            "label": L(uid, "查詢回饋", "View feedback"),
            "uri": _append_uid_lang(f"{base}/toilet_feedback_by_coord/{lat_s}/{lon_s}", uid, _user_lang_q(uid))
        })

        addr_raw = toilet.get('address') or ""
        addr_param = quote(addr_raw or "-")
        actions.append({
            "type": "uri",
            "label": L(uid, "廁所回饋", "Leave feedback"),
            "uri": (
                f"{base}/feedback_form/"
                f"{quote(title)}/{addr_param}"
                f"?lat={lat_s}&lon={lon_s}&address={quote(addr_raw)}"
            )
        })

        ai_uri = f"{base}/ai_feedback_summary_page/{lat_s}/{lon_s}" + (f"?uid={quote(uid)}" if uid else "")
        actions.append({
            "type": "uri",
            "label": L(uid, "AI 回饋摘要", "AI summary"),
            "uri": ai_uri
        })

        if toilet.get("type") == "favorite" and uid:
            actions.append({
                "type": "postback",
                "label": L(uid, "移除最愛", "Remove favorite"),
                "data": f"remove_fav:{quote(title)}:{lat_s}:{lon_s}"
            })
        elif toilet.get("type") not in ["user", "favorite"] and uid:
            actions.append({
                "type": "postback",
                "label": L(uid, "加入最愛", "Add favorite"),
                "data": f"add:{quote(title)}:{lat_s}:{lon_s}"
            })

        # === 主體內容（加上資料來源）===
        dist = int(toilet.get('distance', 0) or 0)
        dist_text = L(uid, f"{dist} 公尺", f"{dist} m")

        body_contents = [
            {"type": "text", "text": title, "weight": "bold", "size": "lg", "wrap": True},
            {"type": "text", "text": f"{paper_text}  {access_text}  {star_text}", "size": "sm", "color": "#555555", "wrap": True},
            {"type": "text", "text": addr_text, "size": "sm", "color": "#666666", "wrap": True},
        ] + extra_lines + [
            {"type": "text", "text": dist_text, "size": "sm", "color": "#999999"},
            {
                "type": "text",
                "text": L(uid, f"資料來源：{source_text}", f"Source: {source_text}"),
                "size": "xs",
                "color": "#AAAAAA",
                "wrap": True
            }
        ]

        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "contents": body_contents
            },
            "footer": {
                "type": "box",
                "layout": "vertical",
                "spacing": "sm",
                "contents": [
                    {"type": "button", "style": "primary", "height": "sm", "action": actions[0]}
                ] + [
                    {"type": "button", "style": "secondary", "height": "sm", "action": a}
                    for a in actions[1:]
                ]
            }
        }

        bubbles.append(bubble)

    return {"type": "carousel", "contents": bubbles}

def get_user_contributions(uid):
    """List current user's submitted toilets from Neon."""
    items = []
    if not uid or not POSTGRES_ENABLED:
        return items
    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT id, name, address, lat, lon, created_at, verification_status
            FROM user_toilets
            WHERE user_id = %s
            ORDER BY created_at DESC
            LIMIT 20
        """, (uid,))
        rows = cur.fetchall()
        conn.close()
        for r in rows:
            ts = r.get("created_at")
            status = r.get("verification_status") or "pending"
            items.append({
                "id": r.get("id"),
                "name": r.get("name") or "無名稱",
                "address": r.get("address") or "",
                "lat": float(norm_coord(r.get("lat"))),
                "lon": float(norm_coord(r.get("lon"))),
                "created": ts.isoformat() if hasattr(ts, "isoformat") else str(ts or ""),
                "verification_status": status,
            })
        return items
    except Exception as e:
        logging.error(f"讀取 Neon 我的貢獻失敗：{e}", exc_info=True)
        return items

def create_my_contrib_flex(uid):
    contribs = get_user_contributions(uid)
    if not contribs:
        return None
    status_label = {
        "pending": L(uid, "待審核", "Pending"),
        "approved": L(uid, "已通過", "Approved"),
        "rejected": L(uid, "未通過", "Rejected"),
        "likely": L(uid, "待確認", "Likely"),
    }
    bubbles = []
    for it in contribs[:10]:
        lat_s = norm_coord(it["lat"])
        lon_s = norm_coord(it["lon"])
        st = it.get("verification_status") or "pending"
        actions = [
            {"type": "uri", "label": L(uid, "導航", "Navigate"), "uri": f"https://www.google.com/maps/search/?api=1&query={lat_s},{lon_s}"},
            {"type": "postback", "label": L(uid, "刪除此貢獻", "Delete this contribution"), "data": f"confirm_delete_my_toilet:{it['id']}"}
        ]
        bubble = {
            "type": "bubble",
            "body": {"type": "box", "layout": "vertical", "contents": [
                {"type": "text", "text": it["name"], "size": "lg", "weight": "bold", "wrap": True},
                {"type": "text", "text": it.get("address") or L(uid, "（無地址）", "(No address)"), "size": "sm", "color": "#666666", "wrap": True},
                {"type": "text", "text": L(uid, f"狀態：{status_label.get(st, st)}", f"Status: {status_label.get(st, st)}"), "size": "xs", "color": "#999999", "wrap": True},
                {"type": "text", "text": it.get("created", ""), "size": "xs", "color": "#999999", "wrap": True}
            ]},
            "footer": {"type": "box", "layout": "vertical", "spacing": "sm", "contents": [
                {"type": "button", "style": "primary", "height": "sm", "action": actions[0]},
                {"type": "button", "style": "secondary", "height": "sm", "action": actions[1]},
            ]}
        }
        bubbles.append(bubble)
    return {"type": "carousel", "contents": bubbles}

def delete_my_contribution(uid, toilet_id):
    """Delete current user's submitted toilet from Neon."""
    if not uid or not toilet_id or not POSTGRES_ENABLED:
        return False, "missing_or_postgres_disabled"
    try:
        toilet_id = int(toilet_id)
    except Exception:
        return False, "invalid_id"
    try:
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            DELETE FROM user_toilets
            WHERE id = %s AND user_id = %s
            RETURNING id
        """, (toilet_id, uid))
        row = cur.fetchone()
        conn.commit()
        conn.close()
        try: _CACHE.clear()
        except Exception: pass
        if row:
            return True, "deleted"
        return False, "not_found_or_permission_denied"
    except Exception as e:
        logging.error(f"delete_my_contribution failed: {e}", exc_info=True)
        return False, "exception"

def callback():
    signature = request.headers.get("X-Line-Signature")
    body = request.get_data(as_text=True)
    try:
        handler.handle(body, signature)
    except InvalidSignatureError:
        abort(400)
    return "OK"

def home():
    return "Toilet bot is running!", 200

def set_user_location(uid, latlon):
    with _dict_lock:
        user_locations[uid] = latlon

def get_user_location(uid):
    with _dict_lock:
        return user_locations.get(uid)

def set_user_loc_mode(uid, mode):
    with _dict_lock:
        user_loc_mode[uid] = mode

def get_user_loc_mode(uid):
    with _dict_lock:
        return user_loc_mode.get(uid, "normal")

def handle_text(event):
    if _too_old_to_reply(event):
        logging.warning("[handle_text] event too old; skip reply.")
        return

    uid = event.source.user_id
    text_raw = event.message.text or ""

    # =========================
    # 🔧 強化文字正規化
    # =========================
    text_norm = text_raw.strip()
    text = text_norm.lower()
    text_key = " ".join(text.split())  # 壓掉 \n / \t / 多空白

    # =========================
    # 🔥 英文 Nearby Toilets 最優先容錯（不靠完全比對）
    # =========================
    if ("nearby" in text_key) and (("toilet" in text_key) or ("restroom" in text_key)):
        set_user_loc_mode(uid, "normal")
        try:
            safe_reply(
                event,
                make_location_quick_reply(
                    L(
                        uid,
                        "📍 請點下方『發送我的位置』，我會幫你找最近的廁所",
                        "📍 Please share your location and I will find nearby toilets for you"
                    ),
                    mode="normal"
                )
            )
        except Exception as e:
            logging.error(f"[nearby] quick reply failed: {e}", exc_info=True)
            safe_reply(
                event,
                TextSendMessage(
                    text=L(uid, "❌ 系統錯誤，請稍後再試", "❌ System error. Please try again later.")
                )
            )
        return

    # =========================
    # 🚫 重複事件 / 同意條款 gate
    # =========================
    if is_duplicate_and_mark_event(event):
        return

    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg)
        return

    reply_messages = []

    # =========================
    # ✅ 中英文文字指令 → cmd
    # =========================
    TEXT_TO_CMD = {
        # 附近廁所
        "附近廁所": "nearby",
        "nearby toilets": "nearby",
        "nearby": "nearby",
        "toilets nearby": "nearby",

        # AI 推薦
        "ai推薦附近廁所": "nearby_ai",
        "ai nearby toilets": "nearby_ai",
        "ai recommend": "nearby_ai",
        "ai recommendation": "nearby_ai",

        # 切換回一般模式
        "切換回一般模式": "mode_normal",
        "switch to normal": "mode_normal",
        "normal mode": "mode_normal",

        # 我的最愛
        "我的最愛": "favs",
        "my favorites": "favs",
        "favorites": "favs",

        # 我的貢獻
        "我的貢獻": "contrib",
        "my contributions": "contrib",
        "contributions": "contrib",

        # 新增廁所
        "新增廁所": "add",
        "add toilet": "add",
        "add a toilet": "add",

        # 意見回饋
        "意見回饋": "feedback",
        "feedback": "feedback",

        # 合作信箱
        "合作信箱": "contact",
        "contact": "contact",

        # 狀態回報
        "狀態回報": "status",
        "status report": "status",
        "report status": "status",

        # 成就
        "成就": "ach",
        "achievements": "ach",

        # 徽章
        "徽章": "badges",
        "badges": "badges",

        # 使用回顧
        "使用回顧": "review",
        "usage summary": "review",
        "review": "review",

        # 使用說明
        "使用說明": "help",
        "help": "help",
    }

    # 三段式 lookup（最穩）
    cmd = TEXT_TO_CMD.get(text_norm)
    if cmd is None:
        cmd = TEXT_TO_CMD.get(text)
    if cmd is None:
        cmd = TEXT_TO_CMD.get(text_key)

    # =========================
    # ✅ cmd 分派（原本邏輯全部保留）
    # =========================
    if cmd == "nearby":
        start_ts = time.time()
        set_user_loc_mode(uid, "normal")
        safe_reply(
            event,
            make_location_quick_reply(
                L(uid,
                  "📍 請點下方『發送我的位置』，我會幫你找最近的廁所",
                  "📍 Please share your location and I will find nearby toilets for you"),
                mode="normal"
            )
        )
        return

    elif cmd == "nearby_ai":
        start_ts = time.time()
        set_user_loc_mode(uid, "ai")
        safe_reply(
            event,
            make_location_quick_reply(
                L(uid,
                  "📍 請傳送你現在的位置，我會用 AI 幫你挑附近最適合的廁所",
                  "📍 Please share your location. I will use AI to pick the best nearby toilets."),
                mode="ai"
            )
        )
        return

    elif cmd == "mode_normal":
        set_user_loc_mode(uid, "normal")
        safe_reply(
            event,
            make_location_quick_reply(
                L(uid,
                  "✅ 已切換回一般模式，請點『發送我的位置』我會幫你找最近的廁所",
                  "✅ Switched to normal mode. Please share your location to find nearby toilets."),
                mode="normal"
            )
        )
        return

    elif cmd == "favs":
        favs = get_user_favorites(uid)
        if not favs:
            reply_messages.append(TextSendMessage(text=L(uid, "你尚未收藏任何廁所", "You have no favorites yet.")))
        else:
            loc = get_user_location(uid)
            if loc:
                lat, lon = loc
                for f in favs:
                    f["distance"] = haversine(lat, lon, f["lat"], f["lon"])
            msg = create_toilet_flex_messages(favs, uid=uid)
            reply_messages.append(FlexSendMessage(L(uid, "我的最愛", "My Favorites"), msg))

    elif cmd == "contrib":
        msg = create_my_contrib_flex(uid)
        if msg:
            reply_messages.append(FlexSendMessage(L(uid, "我新增的廁所", "My Contributions"), msg))
        else:
            reply_messages.append(TextSendMessage(text=L(uid, "你還沒有新增過廁所喔。", "You haven't added any toilets yet.")))

    elif cmd == "add":
        base = f"{_base_url()}/add"
        loc = get_user_location(uid)
        if loc:
            la, lo = loc
            url = f"{base}?uid={quote(uid)}&lat={la}&lon={lo}#openExternalBrowser=1"
        else:
            url = f"{base}?uid={quote(uid)}#openExternalBrowser=1"
        reply_messages.append(TextSendMessage(text=L(uid, f"請前往此頁新增廁所：\n{url}", f"Please add a toilet here:\n{url}")))

    elif cmd == "feedback":
        form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
        reply_messages.append(TextSendMessage(text=L(
            uid,
            f"💡 請透過下列連結回報問題或提供意見：\n{form_url}",
            f"💡 Please send feedback via:\n{form_url}"
        )))

    elif cmd == "contact":
        email = os.getenv("FEEDBACK_EMAIL", "hello@example.com")
        ig_url = "https://www.instagram.com/toiletmvp?igsh=MWRvMnV2MTNyN2RkMw=="
        reply_messages.append(TextSendMessage(text=L(
            uid,
            f"📬 合作信箱：{email}\n\n📸 官方IG: {ig_url}",
            f"📬 Contact: {email}\n\n📸 IG: {ig_url}"
        )))

    elif cmd == "status":
        url = _status_liff_url(uid=uid)
        safe_reply(event, TextSendMessage(text=L(uid, f"⚡ 開啟狀態回報：\n{url}", f"⚡ Open status report:\n{url}")))
        return

    elif cmd == "ach":
        reply_url = f"{PUBLIC_URL}/achievements_liff?uid={uid}&lang={get_user_lang(uid)}"
        safe_reply(event, TextSendMessage(text=L(uid, f"查看成就 👉 {reply_url}", f"View achievements 👉 {reply_url}")))
        return

    elif cmd == "badges":
        reply_url = f"{PUBLIC_URL}/badges_liff?uid={uid}&lang={get_user_lang(uid)}"
        safe_reply(event, TextSendMessage(text=L(uid, f"查看徽章 👉 {reply_url}", f"View badges 👉 {reply_url}")))
        return

    elif cmd == "review":
        summary = build_usage_review_text(uid)
        reply_messages.append(TextSendMessage(text=summary))

    elif cmd == "help":
        return 

    # =========================
    # ✅ 永遠不沉默
    # =========================
    if reply_messages:
        safe_reply(event, reply_messages)
    else:
        safe_reply(
            event,
            TextSendMessage(text=L(
                uid,
                "我沒有看懂你的指令 🙏\n你可以試試：附近廁所 / 使用說明",
                "I didn’t understand 🙏\nTry: Nearby Toilets / Help"
            ))
        )

def handle_location(event):
    if _too_old_to_reply(event):
        logging.warning("[handle_location] event too old; skip reply.")
        return
    uid = event.source.user_id
    show_loading(uid, seconds=15)
    lat = event.message.latitude
    lon = event.message.longitude

    # 記錄查詢次數（寫 DB）
    try:
        conn = _get_db()
        cur = conn.cursor()
        cur.execute(
            "INSERT INTO search_log (user_id, lat, lon, ts) VALUES (?,?,?,?)",
            (uid, norm_coord(lat), norm_coord(lon),
             datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S"))
        )
        conn.commit()
        conn.close()
    except Exception as e:
        logging.warning(f"記錄查詢次數失敗: {e}")

    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg)
        return

    if is_duplicate_and_mark_event(event):
        return

    # 記下使用者最近一次的位置
    set_user_location(uid, (lat, lon))

    if not _try_acquire_loc_slot():
        safe_reply(event, make_retry_location_text())
        return

    start_ts = time.time()
    area_name = get_area_name(lat, lon)

    try:
        query_id = make_query_id()

        toilets = build_nearby_toilets(uid, lat, lon)
        elapsed_ms = int((time.time() - start_ts) * 1000)

        if toilets:
            log_recommendation_results(
                query_id=query_id,
                uid=uid,
                user_lat=lat,
                user_lon=lon,
                toilets=toilets,
                limit=5
            )
            log_shadow_recommendation_results(
                query_id=query_id,
                uid=uid,
                user_lat=lat,
                user_lon=lon,
                toilets=toilets,
                limit=5
            )

        elapsed_ms = int((time.time() - start_ts) * 1000)

        if elapsed_ms > 0:
            log_analytics_event(
                user_id=uid,
                event_type="location_query",
                result_count=len(toilets or []),
                success=1,
                response_time_ms=elapsed_ms,
                lat=lat,
                lon=lon,
                area_name=area_name
            )

        if toilets:
            # 產出廁所 carousel，並帶入 query_id，讓導航點擊可回連到本次推薦紀錄
            msg = create_toilet_flex_messages(toilets, uid=uid, query_id=query_id)

            # 看目前是一般模式還是 AI 模式
            mode = get_user_loc_mode(uid)

            if mode == "ai":
                # 🧠 AI 模式：把 AI 推薦文字塞成「第一個 bubble」
                ai_text = build_ai_nearby_recommendation(uid, toilets)

                if ai_text:
                    ai_bubble = {
                        "type": "bubble",
                        "body": {
                            "type": "box",
                            "layout": "vertical",
                            "contents": [
                                {
                                    "type": "text",
                                    "text": L(uid, "🤖 AI 推薦分析", "🤖 AI Recommendation"),
                                    "weight": "bold",
                                    "size": "lg",
                                    "wrap": True,
                                },
                                {
                                    "type": "text",
                                    "text": ai_text,
                                    "size": "sm",
                                    "color": "#444444",
                                    "wrap": True,
                                },
                            ]
                        }
                    }
                    try:
                        # 安全插入到 carousel 最前面
                        if isinstance(msg, dict) and msg.get("type") == "carousel":
                            msg.setdefault("contents", [])
                            contents = msg.get("contents")
                            if isinstance(contents, list):
                                contents.insert(0, ai_bubble)
                    except Exception as e:
                        logging.warning(f"插入 AI bubble 失敗: {e}")

                # 👉 訊息數量：1 則 Flex + 1 則 quick-reply 文字
                messages = [
                    FlexSendMessage(L(uid, "附近廁所（AI 模式）", "Nearby Toilets (AI Mode)"), msg),
                    make_location_quick_reply(L(uid, "想用 AI 再分析其他位置嗎？", "Want AI to analyze another location?")),
                ]

            else:
                # ⚡ 一般模式：原本行為不變
                messages = [
                    FlexSendMessage(L(uid, "附近廁所", "Nearby Toilets"), msg),
                    make_location_quick_reply(
                        L(uid, "想換個地點再找嗎？", "Want to search another location?")
                    ),
                ]

            safe_reply(event, messages)
        else:
            safe_reply(event, make_no_toilet_quick_reply(uid, lat, lon))

    except Exception as e:
        elapsed_ms = int((time.time() - start_ts) * 1000)
        log_analytics_event(
            user_id=uid,
            event_type="error",
            result_count=0,
            success=0,
            response_time_ms=elapsed_ms,
            lat=lat,
            lon=lon,
            area_name=area_name,
            query_text=str(e)[:200]
        )
        logging.error(f"nearby error: {e}", exc_info=True)
        safe_reply(event, TextSendMessage(text=L(uid, "系統忙線中，請稍後再試 🙏", "System is busy. Please try again later 🙏")))
    finally:
        _release_loc_slot()

def handle_postback(event):
    uid = event.source.user_id
    data_raw = (event.postback.data or "").strip()

    # =========================
    # 0️⃣ 解析 postback 參數（支援任何順序 / URL encode）
    #    支援：
    #      switch=more&lang=en
    #      switch=main&lang=zh
    #      cmd=nearby&lang=en
    # =========================
    decoded = data_raw
    qs = {}
    _lang = _cmd = _switch = None

    try:
        decoded = unquote(data_raw)
        qs = parse_qs(decoded, keep_blank_values=True)

        _lang   = (qs.get("lang")   or [None])[0]
        _cmd    = (qs.get("cmd")    or [None])[0]
        _switch = (qs.get("switch") or [None])[0]
    except Exception:
        # 解析失敗就走 fallback（保留原字串）
        qs = {}
    # ✅ 只在『切換語言/切換選單』時更新語言；避免一般功能 postback 夾帶 lang 把語言又切回去

    # ✅ richmenuswitch：只做「切換確認」，不要走 gate/不要觸發其它功能
    #    （避免你覺得「沒切成功」其實只是 LINE UI 快取/後端沒回覆）
    if _switch in ("more", "main"):
        # 若切換選單時有帶 lang，才更新使用者語言（切換 menu 才允許改語言，避免一般 cmd 夾帶 lang 造成誤切）
        if _lang in ("en", "zh"):
            try:
                set_user_lang(uid, _lang)
            except Exception as e:
                logging.error(f"set_user_lang failed (switch): uid={uid} lang={_lang} err={e}", exc_info=True)

        # 讀回目前語言（確保真的寫進 DB）
        lang_now = get_user_lang(uid)
        if _lang in ("en", "zh") and lang_now != _lang:
            logging.warning(f"language mismatch after switch: uid={uid} expect={_lang} got={lang_now}")

        safe_reply(
            event,
            TextSendMessage(text=("✅ Menu switched" if lang_now == "en" else "✅ 已切換選單"))
        )
        return

    # ✅ 如果有 cmd，統一收斂成 cmd=xxx（讓你下面原本 cmd 分派能命中）
    if _cmd:
        data = f"cmd={_cmd}"
    else:
        data = decoded  # 保留原字串（例如 lang=en / set_lang:en 這種）

    # =========================
    # 1️⃣ 語言切換（最優先）
    # =========================
    if data in ("lang=en", "lang=zh"):
        try:
            lang = "en" if data == "lang=en" else "zh"
            set_user_lang(uid, lang)
            safe_reply(
                event,
                TextSendMessage(
                    text=("✅ Language switched to English" if lang == "en" else "✅ 已切換為中文")
                )
            )
        except Exception as e:
            logging.error(f"切換語言失敗: {e}", exc_info=True)
            safe_reply(event, TextSendMessage(text=T("lang_switch_fail", uid=uid)))
        return

    if data == "set_lang:en":
        set_user_lang(uid, "en")
        safe_reply(event, TextSendMessage(text=T("lang_switched_en", lang="en")))
        return

    if data == "set_lang:zh":
        set_user_lang(uid, "zh")
        safe_reply(event, TextSendMessage(text=T("lang_switched_zh", lang="zh")))
        return

    # =========================
    # 2️⃣ 重複事件擋掉
    # =========================
    if is_duplicate_and_mark_event(event):
        return

    # =========================
    # 3️⃣ 同意條款 gate
    # =========================
    gate_msg = ensure_consent_or_prompt(uid)
    if gate_msg:
        safe_reply(event, gate_msg)
        return

    # =========================
    # 🗑️ 我的貢獻：確認 / 刪除 / 取消
    # =========================
    if data.startswith("confirm_delete_my_toilet:"):
        toilet_id = data.split(":", 1)[1].strip()
        safe_reply(event, TextSendMessage(
            text=L(uid, "⚠️ 確定要刪除這筆你新增的廁所嗎？", "⚠️ Delete this submitted toilet?"),
            quick_reply=QuickReply(items=[
                QuickReplyButton(action=PostbackAction(label=L(uid, "確認刪除", "Confirm delete"), data=f"delete_my_toilet:{toilet_id}", display_text=L(uid, "確認刪除", "Confirm delete"))),
                QuickReplyButton(action=PostbackAction(label=L(uid, "取消", "Cancel"), data="cancel_delete_my_toilet", display_text=L(uid, "取消", "Cancel"))),
            ])
        ))
        return

    if data.startswith("delete_my_toilet:"):
        toilet_id = data.split(":", 1)[1].strip()
        ok, reason = delete_my_contribution(uid, toilet_id)
        if ok:
            safe_reply(event, TextSendMessage(text=L(uid, "✅ 已刪除你新增的廁所", "✅ Deleted.")))
        else:
            logging.warning(f"delete_my_toilet failed: uid={uid} id={toilet_id} reason={reason}")
            safe_reply(event, TextSendMessage(text=L(uid, "❌ 刪除失敗，資料可能不存在或不是你新增的", "❌ Delete failed.")))
        return

    if data == "cancel_delete_my_toilet":
        safe_reply(event, TextSendMessage(text=L(uid, "已取消刪除", "Delete cancelled.")))
        return

    # =========================
    # ⭐ 我的最愛：加入 / 移除
    # data format from Flex:
    #   add:{quoted_name}:{lat}:{lon}
    #   remove_fav:{quoted_name}:{lat}:{lon}
    # =========================
    if data.startswith("add:"):
        try:
            _, name_q, lat_s, lon_s = data.split(":", 3)
            name = unquote(name_q).strip()
            ok = add_to_favorites(uid, {
                "name": name,
                "lat": lat_s,
                "lon": lon_s,
                "address": ""
            })
            if ok:
                safe_reply(event, TextSendMessage(text=L(uid, "✅ 已加入最愛", "✅ Added to favorites")))
                log_user_action(
                    query_id="",
                    uid=uid,
                    toilet_id=f"{name}|{lat_s}|{lon_s}",
                    action_type="add_favorite",
                    extra_info=json.dumps({"name": name, "lat": lat_s, "lon": lon_s}, ensure_ascii=False)
                )
            else:
                safe_reply(event, TextSendMessage(text=L(uid, "❌ 加入最愛失敗", "❌ Failed to add favorite")))
        except Exception as e:
            logging.error(f"add favorite postback failed: {e}", exc_info=True)
            safe_reply(event, TextSendMessage(text=L(uid, "❌ 加入最愛失敗", "❌ Failed to add favorite")))
        return

    if data.startswith("remove_fav:"):
        try:
            _, name_q, lat_s, lon_s = data.split(":", 3)
            name = unquote(name_q).strip()
            ok = remove_from_favorites(uid, name, lat_s, lon_s)
            if ok:
                safe_reply(event, TextSendMessage(text=L(uid, "✅ 已移除最愛", "✅ Removed from favorites")))
            else:
                safe_reply(event, TextSendMessage(text=L(uid, "❌ 移除失敗，可能已不在最愛中", "❌ Remove failed or already removed")))
        except Exception as e:
            logging.error(f"remove favorite postback failed: {e}", exc_info=True)
            safe_reply(event, TextSendMessage(text=L(uid, "❌ 移除最愛失敗", "❌ Failed to remove favorite")))
        return
    
    try:
        # ==========================================================
        # 3.5️⃣ Rich Menu 統一指令：cmd=xxxx
        # ==========================================================
        if data.startswith("cmd="):
            cmd = data.split("=", 1)[1].strip().split("&", 1)[0]
            if cmd in ("noop_main", "noop_more"):
                return

            # =========================
            # ✅ 新增：附近廁所（重點）
            # =========================
            if cmd == "nearby":
                mode = get_user_loc_mode(uid)
                safe_reply(
                    event,
                    make_location_quick_reply(
                        L(uid,
                          "📍 請點下方『傳送我的位置』，我立刻幫你找廁所",
                          "📍 Please share your location and I’ll find nearby toilets for you"),
                        mode=mode,
                        uid=uid
                    )
                )
                return

            # 我的最愛
            if cmd == "favs":
                favs = get_user_favorites(uid)
                if not favs:
                    safe_reply(event, TextSendMessage(text=L(uid, "你尚未收藏任何廁所", "You have no favorites yet.")))
                    return

                loc = get_user_location(uid)
                if loc:
                    lat, lon = loc
                    for f in favs:
                        f["distance"] = haversine(lat, lon, f["lat"], f["lon"])

                msg = create_toilet_flex_messages(favs, uid=uid)
                safe_reply(event, FlexSendMessage(L(uid, "我的最愛", "My Favorites"), msg))
                return

            # 使用說明
            if cmd == "help":
                return

            # 新增廁所
            if cmd == "add":
                base = f"{_base_url()}/add"
                loc = get_user_location(uid)
                if loc:
                    la, lo = loc
                    url = f"{base}?uid={quote(uid)}&lat={la}&lon={lo}#openExternalBrowser=1"
                else:
                    url = f"{base}?uid={quote(uid)}#openExternalBrowser=1"

                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    f"請前往此頁新增廁所：\n{url}",
                    f"Please add a toilet here:\n{url}"
                )))
                return

            # 我的貢獻
            if cmd == "contrib":
                msg = create_my_contrib_flex(uid)
                if msg:
                    safe_reply(event, FlexSendMessage(L(uid, "我新增的廁所", "My Contributions"), msg))
                else:
                    safe_reply(event, TextSendMessage(text=L(uid, "你還沒有新增過廁所喔。", "You haven't added any toilets yet.")))
                return

            # 意見回饋
            if cmd == "feedback":
                form_url = "https://docs.google.com/forms/d/e/1FAIpQLSdsibz15enmZ3hJsQ9s3BiTXV_vFXLy0llLKlpc65vAoGo_hg/viewform?usp=sf_link"
                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    f"💡 請透過下列連結回報問題或提供意見：\n{form_url}",
                    f"💡 Please send feedback via:\n{form_url}"
                )))
                return

            # 狀態回報
            if cmd == "status":
                url = _status_liff_url(uid=uid)
                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    f"⚡ 開啟狀態回報：\n{url}",
                    f"⚡ Open status report:\n{url}"
                )))
                return

            # 成就
            if cmd == "ach":
                reply_url = f"{PUBLIC_URL}/achievements_liff?uid={uid}&lang={get_user_lang(uid)}"
                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    f"查看成就 👉 {reply_url}",
                    f"View achievements 👉 {reply_url}"
                )))
                return

            # 徽章
            if cmd == "badges":
                reply_url = f"{PUBLIC_URL}/badges_liff?uid={uid}&lang={get_user_lang(uid)}"
                safe_reply(event, TextSendMessage(text=L(
                    uid,
                    f"查看徽章 👉 {reply_url}",
                    f"View badges 👉 {reply_url}"
                )))
                return

            # 使用回顧
            if cmd == "review":
                summary = build_usage_review_text(uid)
                safe_reply(event, TextSendMessage(text=summary))
                return

            return

        # =========================
        # 4️⃣ Quick Reply：一般位置
        # =========================
        if data == "ask_location":
            mode = get_user_loc_mode(uid)
            safe_reply(
                event,
                make_location_quick_reply(
                    L(uid,
                      "📍 請點下方『傳送我的位置』，我立刻幫你找廁所",
                      "📍 Please share your location and I’ll find nearby toilets for you"),
                    mode=mode,
                    uid=uid
                )
            )
            return

        # =========================
        # 5️⃣ Quick Reply：AI 位置
        # =========================
        if data == "ask_ai_location":
            set_user_loc_mode(uid, "ai")
            safe_reply(
                event,
                make_location_quick_reply(
                    L(uid,
                      "📍 請傳送你的位置，我會用 AI 幫你挑附近最適合的廁所",
                      "📍 Please share your location. I will use AI to pick the best nearby toilets."),
                    mode="ai",
                    uid=uid
                )
            )
            return

    except Exception as e:
        logging.error(f"❌ 處理 postback 失敗: {e}", exc_info=True)


def register_linebot_routes(app):
    app.add_url_rule("/callback", "callback", callback, methods=["POST"])
    app.add_url_rule("/", "home", home, methods=["GET"])
    handler.add(MessageEvent, message=TextMessage)(handle_text)
    handler.add(MessageEvent, message=LocationMessage)(handle_location)
    handler.add(PostbackEvent)(handle_postback)
