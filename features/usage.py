import os
import json
import logging
import threading
import urllib.parse
from datetime import datetime

from flask import request, redirect, render_template
from openai import OpenAI

from config import TW_TZ

_get_db = None
_read_status_rows = None
get_user_contributions = None
get_user_favorites = None
get_user_lang = None
build_feedback_index = None
build_status_index = None
norm_coord = None
L = None
PUBLIC_URL = ""
LIFF_ID_STATUS = ""
_get_liff_status_id = None
_base_url = None


def configure_usage(
    get_db_func,
    read_status_rows_func,
    get_user_contributions_func,
    get_user_favorites_func,
    get_user_lang_func,
    build_feedback_index_func,
    build_status_index_func,
    norm_coord_func,
    L_func,
    public_url,
    liff_id_status,
    base_url_func,
    get_liff_status_id_func=None,
):
    global _get_db, _read_status_rows, get_user_contributions, get_user_favorites, get_user_lang
    global build_feedback_index, build_status_index, norm_coord, L, PUBLIC_URL, LIFF_ID_STATUS, _base_url, _get_liff_status_id
    _get_db = get_db_func
    _read_status_rows = read_status_rows_func
    get_user_contributions = get_user_contributions_func
    get_user_favorites = get_user_favorites_func
    get_user_lang = get_user_lang_func
    build_feedback_index = build_feedback_index_func
    build_status_index = build_status_index_func
    norm_coord = norm_coord_func
    L = L_func
    PUBLIC_URL = public_url
    LIFF_ID_STATUS = liff_id_status
    _base_url = base_url_func
    _get_liff_status_id = get_liff_status_id_func



def _current_liff_status_id():
    try:
        if _get_liff_status_id:
            return _get_liff_status_id()
    except Exception:
        pass
    return LIFF_ID_STATUS

AI_MODEL = os.getenv("AI_MODEL", "gpt-4o-mini")

AI_KEY   = os.getenv("OPENAI_API_KEY", "")

client   = OpenAI(api_key=AI_KEY) if AI_KEY else None

AI_DAILY_LIMIT = int(os.getenv("AI_DAILY_LIMIT", "3"))  # 預設 3 次/人/天

_ai_quota_lock = threading.Lock()

_ai_quota = {}  # key: (usage_key, date_str) -> count


def achievements_liff_page():
    uid = (request.args.get("uid") or "").strip()
    lang = (request.args.get("lang") or "").strip().lower()
    if uid and not lang:
        try:
            lang = "en" if get_user_lang(uid) == "en" else "zh"
        except Exception:
            lang = "zh"
        qs = request.args.to_dict(flat=True)
        qs["lang"] = lang
        return redirect(request.path + "?" + urllib.parse.urlencode(qs), code=302)

    return render_template(
        "achievements_liff.html",
        liff_id=_current_liff_status_id(),
        public_url=PUBLIC_URL,
        uid=uid,
        lang=(lang if lang in ["en","zh"] else "zh")
    )

def badges_liff_page():
    uid = (request.args.get("uid") or "").strip()
    lang = (request.args.get("lang") or "").strip().lower()
    if uid and not lang:
        try:
            lang = "en" if get_user_lang(uid) == "en" else "zh"
        except Exception:
            lang = "zh"
        qs = request.args.to_dict(flat=True)
        qs["lang"] = lang
        return redirect(request.path + "?" + urllib.parse.urlencode(qs), code=302)

    return render_template(
        "badges_liff.html",
        liff_id=_current_liff_status_id(),
        public_url=PUBLIC_URL,
        uid=uid,
        lang=(lang if lang in ["en","zh"] else "zh")
    )

def _parse_ts(ts: str):
    try:
        s = (ts or "").strip()
        if not s:
            return None

        # ISO Z → +00:00
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"

        try:
            return datetime.fromisoformat(s)
        except Exception:
            pass

        for fmt in (
            "%Y-%m-%d %H:%M:%S",
            "%Y/%m/%d %H:%M:%S",
            "%Y-%m-%d %H:%M",
            "%Y/%m/%d %H:%M",
        ):
            try:
                return datetime.strptime(s, fmt)
            except Exception:
                continue

        return None
    except Exception:
        return None

def _stats_for_user(uid: str):
    rows = _read_status_rows()
    total = 0
    by_status = {}
    last_ts = None

    for r in rows:
        if uid and r.get("user_id") != uid:
            continue

        total += 1
        s = r.get("status") or ""
        by_status[s] = by_status.get(s, 0) + 1

        ts = r.get("timestamp")
        if ts:
            t = _parse_ts(ts)
            if t is not None:
                if last_ts is None or t > last_ts:
                    last_ts = t

    return {
        "total": total,
        "by_status": by_status,
        "last_ts": last_ts.isoformat() if last_ts else None
    }

def get_search_count(uid: str) -> int:
    try:
        conn = _get_db()
        cur = conn.cursor()
        cur.execute("SELECT COUNT(*) FROM search_log WHERE user_id = ?", (uid,))
        row = cur.fetchone()
        conn.close()
        return int(row[0]) if row and row[0] is not None else 0
    except Exception as e:
        logging.warning(f"查詢 search_log 失敗: {e}")
        return 0


ACHIEVEMENT_RULES = {
    "first": {
        "goal": 1,
        "counter": "total",
        "desc": {
            "zh": "完成第一次狀態回報",
            "en": "Complete your first status report"
        }
    },
    "helper10": {
        "goal": 10,
        "counter": "total",
        "desc": {
            "zh": "累積回報 10 次",
            "en": "Report status 10 times"
        }
    },
    "pro_reporter": {
        "goal": 20,
        "counter": "total",
        "desc": {
            "zh": "累積回報 20 次",
            "en": "Report status 20 times"
        }
    },
    "helper50": {
        "goal": 50,
        "counter": "total",
        "desc": {
            "zh": "累積回報 50 次",
            "en": "Report status 50 times"
        }
    },
    "tissue_guard": {
        "goal": 3,
        "counter": "缺衛生紙",
        "desc": {
            "zh": "回報『缺衛生紙』滿 3 次",
            "en": "Report of 'toilet paper' shortage 3 time"
        }
    },
    "tissue_master": {
        "goal": 10,
        "counter": "缺衛生紙",
        "desc": {
            "zh": "回報『缺衛生紙』滿 10 次",
            "en": "Report of 'toilet paper' shortage 10 time"
        }
    },
    "queue_scout": {
    "goal": 3,
    "counter": "有人排隊",
    "desc": {
        "zh": "回報『有人排隊』滿 3 次",
        "en": "Report 'Queue present' status 3 times"
    }
    },
    "queue_commander": {
        "goal": 10,
        "counter": "有人排隊",
        "desc": {
            "zh": "回報『有人排隊』滿 10 次",
            "en": "Report 'Queue present' status 10 times"
        }
    },
    "maintenance_watcher": {
        "goal": 3,
        "counter": "暫停使用",
        "desc": {
            "zh": "回報『暫停使用』滿 3 次",
            "en": "Report 'Out of service' status 3 times"
        }
    },
    "good_news": {
        "goal": 5,
        "counter": "恢復正常",
        "desc": {
            "zh": "回報『恢復正常』滿 5 次",
            "en": "Report 'Back to normal' status 5 times"
        }
    },
}


def api_achievements():
    uid = request.args.get("user_id", "").strip()
    lang = resolve_lang(uid=uid, lang=request.args.get("lang"))

    stats = _stats_for_user(uid)
    total = int(stats.get("total", 0) or 0)
    by = stats.get("by_status", {}) or {}

    out = []
    for cfg in BADGE_CONFIG:
        key = cfg["key"]
        rule = ACHIEVEMENT_RULES.get(key)
        if not rule:
            # 如果有在 BADGE_CONFIG 增加新 key 但還沒在 ACHIEVEMENT_RULES 定義，就先跳過
            continue

        counter_type = rule["counter"]
        if counter_type == "total":
            progress = total
        else:
            # counter_type 對應到 by_status 裡的中文 key，例如「缺衛生紙」「有人排隊」等
            progress = int(by.get(counter_type, 0) or 0)

        goal = int(rule["goal"] or 0)

        # ✅ title 也做 i18n（避免只有 UI 變、內容還是中文）
        name = cfg.get("name") or {}
        if isinstance(name, dict):
            title = name.get(lang) or name.get("zh") or ""
        else:
            title = str(name)

        out.append({
            "key": key,
            "title": title,
            "desc": (rule["desc"]["en"] if lang == "en" else rule["desc"]["zh"]),
            "goal": goal,
            "progress": progress,
            # ✅ 成就解鎖應該用成就自己的規則（progress >= goal）
            "unlocked": (progress >= goal),
            "icon": cfg.get("icon", ""),
        })

    return {"ok": True, "achievements": out}, 200

def build_usage_review_text(uid: str) -> str:
    # 改成用 DB 裡的 search_log 統計查詢次數
    search_times = get_search_count(uid)

    stats = _stats_for_user(uid)
    total = int(stats.get("total", 0) or 0)
    by = stats.get("by_status", {}) or {}
    last_ts = stats.get("last_ts") or L(uid, "尚無紀錄", "No record")

    try:
        contribs = get_user_contributions(uid) or []
        num_contribs = len(contribs)
    except Exception:
        num_contribs = 0

    try:
        favs = get_user_favorites(uid) or []
        num_favs = len(favs)
    except Exception:
        num_favs = 0

    unlocked_badges = 0
    try:
        rules = _badge_rules(uid)
        unlocked_badges = sum(1 for v in rules.values() if v)
    except Exception:
        pass

    lines = []

    # === 查詢次數 ===
    lines.append(L(
        uid,
        f"・你總共查詢過附近廁所：{search_times} 次",
        f"• You searched nearby toilets {search_times} times"
    ))

    lines.append("")
    lines.append(L(uid, "📊 使用回顧", "📊 Usage Summary"))
    lines.append("")

    # === 狀態回報 ===
    if total > 0:
        lines.append(L(
            uid,
            f"・狀態回報次數：{total} 次",
            f"• Status reports: {total} times"
        ))

        parts = []

        mapping = {
            "恢復正常": ("✅", "Back to normal"),
            "有人排隊": ("🟡", "Queue"),
            "缺衛生紙": ("🧻", "No toilet paper"),
            "暫停使用": ("⛔", "Out of service"),
        }

        for zh_key, (emo, en_label) in mapping.items():
            c = int(by.get(zh_key, 0) or 0)
            if c > 0:
                parts.append(
                    L(
                        uid,
                        f"{emo}{zh_key} {c} 次",
                        f"{emo}{en_label} {c}"
                    )
                )

        if parts:
            lines.append(L(
                uid,
                "  └ 狀態類型：" + "｜".join(parts),
                "  └ Status types: " + " | ".join(parts)
            ))

        lines.append(L(
            uid,
            f"・最近一次回報時間：{last_ts}",
            f"• Last report time: {last_ts}"
        ))
    else:
        lines.append(L(
            uid,
            "・目前還沒有任何狀態回報紀錄",
            "• No status reports yet"
        ))

    lines.append("")

    # === 新增廁所 & 最愛 ===
    lines.append(L(
        uid,
        f"・你新增的廁所：{num_contribs} 間",
        f"• Toilets you added: {num_contribs}"
    ))
    lines.append(L(
        uid,
        f"・你收藏的最愛廁所：{num_favs} 間",
        f"• Favorite toilets: {num_favs}"
    ))

    # === 徽章 ===
    lines.append("")
    if unlocked_badges > 0:
        lines.append(L(
            uid,
            f"🏅 已解鎖徽章數：{unlocked_badges} 個（可輸入「徽章」查看詳細）",
            f"🏅 Badges unlocked: {unlocked_badges} (type 'Badges' to view)"
        ))
    else:
        lines.append(L(
            uid,
            "🏅 還沒解鎖徽章，試著多回報幾次狀態就會慢慢解鎖囉！",
            "🏅 No badges unlocked yet. Try reporting more status updates!"
        ))

    lines.append("")
    lines.append(L(
        uid,
        "🔁 小提醒：可以輸入「附近廁所」或傳送位置，我會幫你找最近的廁所 🚽",
        "🔁 Tip: Type 'Nearby toilets' or share your location to find toilets 🚽"
    ))

    lines.append("")
    lines.append(L(
        uid,
        "🤖 查看 AI 為你生成的個人化使用分析：",
        "🤖 View your AI-generated personal usage summary:"
    ))
    base = _base_url()
    lines.append(f"👉 {base}/ai_usage_summary_page/{uid}")

    return "\n".join(lines)

def build_ai_usage_summary(uid: str) -> str:
    """
    用 AI 幫使用者做『個人使用回顧』總結。
    - 有資料時：呼叫 OpenAI 產生精簡的 Wrapped 風格文字
    - 資料太少時：直接回固定提示，不浪費 AI 流量
    - 沒有 AI client 時：退回原本的文字版使用回顧
    """
    # 先拿你原本的資料來源
    search_times = get_search_count(uid)  # 資料表 search_log
    stats = _stats_for_user(uid)          # 狀態回報統計

    total = int(stats.get("total", 0) or 0)
    by = stats.get("by_status", {}) or {}
    last_ts = stats.get("last_ts") or L(uid, "尚無紀錄", "No record")

    try:
        contribs = get_user_contributions(uid) or []
        num_contribs = len(contribs)
    except Exception:
        num_contribs = 0

    try:
        favs = get_user_favorites(uid) or []
        num_favs = len(favs)
    except Exception:
        num_favs = 0

    # 徽章數
    unlocked_badges = 0
    try:
        rules = _badge_rules(uid)
        unlocked_badges = sum(1 for v in rules.values() if v)
    except Exception:
        pass

    # 🔹 如果幾乎沒有任何紀錄，就不要浪費 AI，直接回固定文字
    if (search_times == 0 and total == 0 and
        num_contribs == 0 and num_favs == 0 and
        unlocked_badges == 0):
        return L(
            uid,
            "目前還沒有足夠的使用紀錄可以產生 AI 使用回顧喔～\n"
            "可以多多使用「附近廁所」「狀態回報」「新增廁所」「收藏最愛」，\n"
            "之後我會幫你做一份專屬的使用報告 🙌",
            "Not enough usage data yet to generate an AI usage summary.\n"
            "Try using Nearby Toilets, Status Report, Add Toilet, and Favorites more often.\n"
            "I’ll prepare a personalized report for you soon 🙌"
        )

    # 🔸 client 防呆（避免 client 尚未初始化就被呼叫）
    _client = globals().get("client", None)
    if _client is None:
        return build_usage_review_text(uid)

    # 🔹 每個使用者「AI 使用回顧」每天最多觸發 AI_DAILY_LIMIT 次
    ok, used = _ai_quota_check_and_inc(f"usage:{uid or 'anonymous'}")
    if not ok:
        base = build_usage_review_text(uid)
        return base + "\n\n（今日 AI 使用回顧次數已達上限，明天再來看看新的分析吧 🙏）"

    # ✅ 依使用者語言決定 AI 回覆語言（加防呆）
    try:
        lang = get_user_lang(uid)
    except Exception:
        lang = "zh"

    payload = {
        "search_times": search_times,
        "status_total": total,
        "status_by_type": by,
        "last_status_time": last_ts,
        "contributions": num_contribs,
        "favorites": num_favs,
        "unlocked_badges": unlocked_badges,
    }

    try:
        import json
        payload_json = json.dumps(payload, ensure_ascii=False)

        # ✅ 中英 prompt 分離（避免模型語言混亂）
        prompt_zh = f"""
你是一個溫暖的生活小助手，要幫使用者總結他使用「智慧廁所助手」的情況。

下面是一位使用者的使用統計資料（JSON）：
{payload_json}

請根據這些數據，幫他產生一段「個人使用回顧」，要求如下：
- 使用繁體中文
- 整體篇幅控制在 4～7 行以內
- 第 1 行：Wrapped 風格的一句開場總結
- 接著列出 3～5 點重點（用條列）
  - 查詢附近廁所次數
  - 狀態回報次數、最常見的狀態類型
  - 新增廁所數
  - 收藏最愛數
  - 解鎖徽章數（若有）
- 最後 1 行：一句鼓勵或小建議

請直接輸出給使用者看的內容，不要再出現 JSON 或技術描述。
        """.strip()

        prompt_en = f"""
You are a warm, friendly assistant summarizing a user's usage of the "Smart Toilet Assistant".

Here is the user's usage stats (JSON):
{payload_json}

Write a short "usage recap" with:
- English only
- 4–7 lines total
- Line 1: a Wrapped-style headline
- Then 3–5 bullet highlights (searches, status reports + most common types, contributions, favorites, badges)
- Final line: a short encouragement or tip

Output user-facing text only. Do NOT include JSON or technical descriptions.
        """.strip()

        prompt = prompt_en if lang == "en" else prompt_zh
        system_msg = (
            "You are a friendly assistant that writes a short usage recap in English."
            if lang == "en"
            else "你是一個幫忙做使用回顧的生活小助手，說話親切、簡潔，用繁體中文。"
        )

        resp = _client.chat.completions.create(
            model=AI_MODEL,
            messages=[
                {"role": "system", "content": system_msg},
                {"role": "user", "content": prompt}
            ],
        )

        summary = (resp.choices[0].message.content or "").strip()
        return summary or build_usage_review_text(uid)

    except Exception as e:
        logging.error(f"AI usage summary error: {e}", exc_info=True)
        return build_usage_review_text(uid)

def build_ai_nearby_recommendation(uid: str, toilets):
    """
    依據附近廁所清單，呼叫 OpenAI 幫忙產生一段推薦說明文字。
    - 如果沒有 AI 金鑰 / 沒有廁所資料，就直接回空字串，不影響原本流程
    - 每位使用者每天 AI 推薦次數有限，超過就回提示文字
    """
    if client is None:
        return ""
    if not toilets:
        return ""

    # 🔹 每個使用者「AI 推薦附近廁所」每天最多觸發 AI_DAILY_LIMIT 次
    try:
        quota_key = uid or "anonymous"
        ok, used = _ai_quota_check_and_inc(f"nearby:{quota_key}")
    except Exception as e:
        logging.warning(f"AI nearby quota check failed: {e}")
        ok = True  # quota 壞掉時當作不限制

    if not ok:
        return L(
            uid,
            "今天 AI 推薦附近廁所的次數已達每日上限喔～\n"
            "如果還需要查詢，建議先切換回一般模式 👍",
            "You have reached today's AI nearby recommendation limit.\n"
            "Please switch back to normal mode to continue 👍"
        )

    # ✅ 3-3：依使用者語言決定 AI 回覆語言
    lang = get_user_lang(uid)
    lang_rule = "請使用繁體中文回答。" if lang != "en" else "Please answer in English."

    try:
        import json

        # 最多拿前 5 間，避免 token 太大
        indicators = build_feedback_index()
        status_map = build_status_index()

        items = []
        for t in toilets[:5]:
            try:
                lat_s = norm_coord(t["lat"])
                lon_s = norm_coord(t["lon"])
            except Exception:
                continue

            key = (lat_s, lon_s)
            ind = indicators.get(key, {})
            st = status_map.get(key, {})

            items.append({
                "name": t.get("name") or t.get("place_hint") or "未命名廁所",
                "distance_m": int(t.get("distance", 0) or 0),
                "paper": ind.get("paper"),          # "有" / "沒有" / "?"
                "access": ind.get("access"),        # "有" / "沒有" / "?"
                "avg_score": ind.get("avg"),        # 清潔分數平均
                "status": (st.get("status") or ""), # 例如：有人排隊、暫停使用、恢復正常
            })

        if not items:
            return ""

        payload = {
            "uid": uid,
            "nearby_toilets": items
        }

        prompt = f"""
你是一個「智慧廁所助手」的推薦小幫手，使用者剛剛傳了他的位置，我們幫他找到幾間附近的廁所。

下面是整理好的附近廁所資料（JSON）：
{json.dumps(payload, ensure_ascii=False)}

請你根據：
- 距離（distance_m，越小越近）
- 清潔分數 avg_score（數字越高代表越乾淨，如果是 null 代表目前沒有評分）
- 衛生紙狀態 paper（"有"/"沒有"/"?"）
- 無障礙設施 access（"有"/"沒有"/"?"）
- 即時狀態 status（例如：有人排隊、暫停使用、恢復正常）

幫使用者做一段簡短的「推薦說明」，要求：
{lang_rule}
- Keep the total length within 3–5 lines.
- First line: a quick overall summary.
- Then recommend 1–2 toilets (up to 3 max) with brief reasons.
- Final line: a short tip.

Please output user-facing text only. Do NOT include JSON or technical descriptions.
        """.strip()

        resp = client.chat.completions.create(
            model=AI_MODEL,
            messages=[
                {
                    "role": "system",
                    "content": f"You are a friendly assistant that recommends nearby toilets. {lang_rule}"
                },
                {"role": "user", "content": prompt}
            ],
        )

        text = (resp.choices[0].message.content or "").strip()
        return text

    except Exception as e:
        logging.error(f"AI nearby recommendation error: {e}", exc_info=True)
        return ""

def _badge_rules(uid: str):
    s = _stats_for_user(uid)
    by = s.get("by_status", {}) or {}
    total = int(s.get("total", 0) or 0)

    def c(k):
        return int(by.get(k, 0) or 0)

    return {
        "first": total >= 1,
        "helper10": total >= 10,
        "pro_reporter": total >= 20,
        "helper50": total >= 50,
        "tissue_guard": c("缺衛生紙") >= 3,
        "tissue_master": c("缺衛生紙") >= 10,
        "queue_scout": c("有人排隊") >= 3,
        "queue_commander": c("有人排隊") >= 10,
        "maintenance_watcher": c("暫停使用") >= 3,
        "good_news": c("恢復正常") >= 5,
    }


BADGE_CONFIG = [
    {"key":"first",               "name":{"zh":"新手報到",     "en":"First Report"},          "icon":"/static/badges/first.png"},
    {"key":"helper10",            "name":{"zh":"勤勞小幫手",   "en":"Helpful Reporter"},      "icon":"/static/badges/helper10.png"},
    {"key":"pro_reporter",        "name":{"zh":"資深回報員",   "en":"Pro Reporter"},          "icon":"/static/badges/pro_reporter.png"},
    {"key":"helper50",            "name":{"zh":"超級幫手",     "en":"Super Helper"},          "icon":"/static/badges/helper50.png"},
    {"key":"tissue_guard",        "name":{"zh":"紙巾守護者",   "en":"Tissue Guardian"},       "icon":"/static/badges/tissue_guard.png"},
    {"key":"tissue_master",       "name":{"zh":"紙巾總管",     "en":"Tissue Manager"},        "icon":"/static/badges/tissue_master.png"},
    {"key":"queue_scout",         "name":{"zh":"排隊偵查員",   "en":"Queue Scout"},           "icon":"/static/badges/queue_scout.png"},
    {"key":"queue_commander",     "name":{"zh":"排隊指揮官",   "en":"Queue Commander"},       "icon":"/static/badges/queue_commander.png"},
    {"key":"maintenance_watcher", "name":{"zh":"維運守護者",   "en":"Maintenance Watcher"},   "icon":"/static/badges/maintenance_watcher.png"},
    {"key":"good_news",           "name":{"zh":"好消息分享員", "en":"Good News Messenger"},   "icon":"/static/badges/good_news.png"},
]


def api_badges():
    uid = request.args.get("user_id", "").strip()
    lang = resolve_lang(uid=uid, lang=request.args.get("lang"))

    unlocked_map = _badge_rules(uid)
    items = []
    for b in BADGE_CONFIG:
        name = b.get("name") or {}
        if isinstance(name, dict):
            display_name = name.get(lang) or name.get("zh") or ""
        else:
            display_name = str(name)

        items.append({
            "key": b["key"],
            "name": display_name,
            "icon": b["icon"],
            "unlocked": bool(unlocked_map.get(b["key"], False)),
        })
    return {"ok": True, "badges": items}, 200

def ai_usage_summary_page(uid):
    text = build_ai_usage_summary(uid)
    return render_template(
        "ai_usage_summary.html",
        uid=uid,
        summary=text
    )

def _ai_quota_check_and_inc(key: str):
    today = datetime.now(TW_TZ).strftime("%Y-%m-%d")

    conn = _get_db()
    cur = conn.cursor()

    cur.execute("SELECT count FROM ai_quota WHERE key=? AND date=?", (key, today))
    row = cur.fetchone()
    cnt = row[0] if row else 0

    if cnt >= AI_DAILY_LIMIT:
        conn.close()
        return False, cnt

    if row:
        cur.execute("UPDATE ai_quota SET count=? WHERE key=? AND date=?", (cnt+1, key, today))
    else:
        cur.execute("INSERT INTO ai_quota (key, date, count) VALUES (?, ?, ?)", (key, today, 1))

    conn.commit()
    conn.close()

    return True, cnt+1



def register_usage_routes(app):
    app.add_url_rule('/achievements_liff', endpoint='achievements_liff_page', view_func=achievements_liff_page)
    app.add_url_rule('/badges_liff', endpoint='badges_liff_page', view_func=badges_liff_page)
    app.add_url_rule('/api/achievements', endpoint='api_achievements', view_func=api_achievements)
    app.add_url_rule('/api/badges', endpoint='api_badges', view_func=api_badges)
    app.add_url_rule('/ai_usage_summary_page/<uid>', endpoint='ai_usage_summary_page', view_func=ai_usage_summary_page)
