import os
import json
import logging
from flask import request

# _get_db is injected by app.py after the SQLite helper is defined.
_get_db = None

def configure_i18n(get_db_func):
    global _get_db
    _get_db = get_db_func

# 使用者語言（記憶體版，之後可換 DB）
user_lang = {}

def set_user_lang(uid: str, lang: str):
    try:
        if not uid:
            return
        lang = "en" if (lang or "").lower() == "en" else "zh"
        conn = _get_db()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO user_lang (user_id, lang)
            VALUES (?, ?)
            ON CONFLICT(user_id) DO UPDATE SET lang=excluded.lang
        """, (uid, lang))
        conn.commit()
        conn.close()
    except Exception as e:
        logging.warning(f"set_user_lang failed: {e}")


def get_user_lang(uid: str) -> str:
    try:
        if not uid:
            return "zh"
        conn = _get_db()
        cur = conn.cursor()
        cur.execute("SELECT lang FROM user_lang WHERE user_id=?", (uid,))
        row = cur.fetchone()
        conn.close()
        if row and row[0] == "en":
            return "en"
        return "zh"
    except Exception as e:
        logging.warning(f"get_user_lang failed: {e}")
        return "zh"


TEXTS = {
    "nearby_toilet": {
        "zh": "附近廁所",
        "en": "Nearby toilets"
    },
    "ask_location": {
        "zh": "請傳送你的位置",
        "en": "Please share your location"
    },
    "no_result": {
        "zh": "附近沒有找到廁所",
        "en": "No toilets found nearby"
    },
    "loading": {
        "zh": "查詢中，請稍候…",
        "en": "Searching, please wait…"
    },
    "added_favorite": {
        "zh": "已加入最愛 ⭐",
        "en": "Added to favorites ⭐"
    },
    "removed_favorite": {
        "zh": "已移除最愛",
        "en": "Removed from favorites"
    },
    "ask_location_normal": {
        "zh": "📍 請點『傳送我的位置』，我立刻幫你找廁所",
        "en": "📍 Please share your location and I’ll find nearby toilets for you"
    },
    "ask_location_ai": {
        "zh": "📍 請點『傳送我的位置』，我會用 AI 幫你挑附近的廁所",
        "en": "📍 Please share your location and I’ll use AI to recommend nearby toilets"
    },
    "added_fav_ok": {
        "zh": "✅ 已收藏 {name}",
        "en": "✅ Added {name} to favorites"
    },
    "removed_fav_ok": {
        "zh": "✅ 已移除最愛",
        "en": "✅ Removed from favorites"
    },
    "removed_fav_fail": {
        "zh": "❌ 移除失敗",
        "en": "❌ Failed to remove"
    },
    "confirm_delete": {
        "zh": "⚠️ 確定要刪除 {name} 嗎？（目前刪除為移除最愛）",
        "en": "⚠️ Are you sure you want to remove {name} from favorites?"
    },
    "confirm_hint": {
        "zh": "請輸入『確認刪除』或『取消』",
        "en": "Please type “Confirm delete” or “Cancel”"
    },
    "busy_try_later": {
        "zh": "系統忙線中，請稍後再試 🙏",
        "en": "System is busy. Please try again later 🙏"
    },
    "lang_switch_fail": {
        "zh": "❌ 切換語言失敗，請稍後再試",
        "en": "❌ Failed to switch language. Please try again later."
    },
    # Used by ensure_consent_or_prompt() — must include {url} placeholder.
    # Previously missing after Google Sheets removal, causing the bot to
    # send the literal string "consent_required" instead of real text.
    "consent_required": {
        "zh": "📋 使用「智慧廁所助手」前，請先閱讀並同意個資使用條款：\n{url}",
        "en": "📋 Before using the Smart Toilet Assistant, please read and agree to our privacy policy:\n{url}"
    },
}

# === 外部語言包（lang/zh.json, lang/en.json）===
LANG_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)), "lang")

def _load_lang_pack(lang_code: str):
    try:
        path = os.path.join(LANG_DIR, f"{lang_code}.json")
        if not os.path.exists(path):
            return {"texts": {}, "literals": {}}
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return {"texts": {}, "literals": {}}
        return {
            "texts": data.get("texts", {}) or {},
            "literals": data.get("literals", {}) or {}
        }
    except Exception as e:
        logging.warning(f"load lang pack failed ({lang_code}): {e}")
        return {"texts": {}, "literals": {}}

_LANG_PACKS = {
    "zh": _load_lang_pack("zh"),
    "en": _load_lang_pack("en"),
}

def _lang_text(key: str, lang: str):
    pack = _LANG_PACKS.get(lang, {})
    texts = pack.get("texts", {}) if isinstance(pack, dict) else {}
    if key in texts:
        return texts.get(key)
    return None

def _translate_literal_runtime(text: str, lang: str):
    if not isinstance(text, str) or not text:
        return text
    pack = _LANG_PACKS.get(lang, {})
    literals = pack.get("literals", {}) if isinstance(pack, dict) else {}
    if not literals:
        return text

    # 先 exact match，再做長字串優先的子字串替換
    if text in literals:
        return literals[text]

    out = text
    try:
        for src, dst in sorted(literals.items(), key=lambda kv: len(kv[0]), reverse=True):
            if src and src in out:
                out = out.replace(src, dst)
    except Exception:
        return text
    return out

def _localize_line_message_object(obj, lang: str):
    """
    針對 LINE message object 做遞迴在地化。
    - 會翻譯 TextSendMessage / FlexSendMessage / QuickReply label 等顯示文字
    - 不翻譯 postback data / URI / MessageAction.text，避免功能被翻壞
    """
    if obj is None:
        return obj

    def walk(node):
        if node is None:
            return
        if isinstance(node, list):
            for item in node:
                walk(item)
            return
        if isinstance(node, tuple):
            for item in node:
                walk(item)
            return
        if isinstance(node, dict):
            for k, v in list(node.items()):
                if isinstance(v, str):
                    # 避免翻掉功能欄位
                    if k in ("data", "uri"):
                        continue
                    node[k] = _translate_literal_runtime(v, lang)
                else:
                    walk(v)
            return

        if hasattr(node, "__dict__"):
            cls_name = node.__class__.__name__
            for attr, value in vars(node).items():
                if attr.startswith("_"):
                    continue

                if isinstance(value, str):
                    # 避免翻壞功能用文字
                    if attr in ("data", "uri"):
                        continue
                    if cls_name == "MessageAction" and attr == "text":
                        continue
                    # 顯示文字可翻
                    if attr in ("text", "alt_text", "label", "title", "placeholder", "display_text"):
                        try:
                            setattr(node, attr, _translate_literal_runtime(value, lang))
                        except Exception:
                            pass
                else:
                    walk(value)

    walk(obj)
    return obj

def _localize_outgoing_messages(messages, uid=None, lang=None):
    target_lang = resolve_lang(uid=uid, lang=lang)
    if target_lang == "zh":
        return messages

    if messages is None:
        return messages
    if not isinstance(messages, list):
        messages = [messages]

    out = []
    for msg in messages:
        try:
            out.append(_localize_line_message_object(msg, target_lang))
        except Exception:
            out.append(msg)
    return out


# =========================
# ✅ 統一語言/翻譯入口（唯一入口）
# - LINE：用 uid 決定語言（get_user_lang）
# - API：用 ?lang=en 決定語言（request.args）
# - 舊函式 t/L/_api_L/_api_T 仍保留，但全部改走這裡
# =========================

def _api_lang():
    # API 沒有 LINE uid 時，用 querystring 控制語言：?lang=en
    lang = (request.args.get("lang") or "").strip().lower()
    return "en" if lang == "en" else "zh"

def resolve_lang(uid=None, lang=None):
    # 1) 明確指定 lang（最優先）
    if (lang or "").lower() == "en":
        return "en"
    if (lang or "").lower() == "zh":
        return "zh"

    # 2) 有 uid → 走使用者語言
    if uid:
        try:
            return "en" if get_user_lang(uid) == "en" else "zh"
        except Exception:
            return "zh"

    # 3) 無 uid → 視為 API → 走 querystring
    return _api_lang()

def T(key_or_zh, uid=None, en=None, lang=None, **fmt):
    """
    ✅ 統一翻譯函式（全案唯一入口）
    用法：
    1) key 模式（推薦）：T("no_result", uid=uid)  → 從外部語言包 / TEXTS 抓 zh/en
    2) zh/en 模式（相容舊碼）：T("附近沒有廁所", uid=uid, en="No toilets nearby")
    3) API 模式：T("missing_params", lang=_api_lang())
    4) 支援 format：T("added_fav_ok", uid=uid, name="xxx")
    """
    l = resolve_lang(uid=uid, lang=lang)

    # key 模式：先查外部語言包，再 fallback 到內建 TEXTS
    if en is None and isinstance(key_or_zh, str):
        from_pack = _lang_text(key_or_zh, l)
        if from_pack is not None:
            s = from_pack
        elif key_or_zh in TEXTS:
            s = TEXTS[key_or_zh].get(l, TEXTS[key_or_zh].get("zh", "")) or ""
        else:
            s = key_or_zh or ""
    else:
        # zh/en 模式（相容）
        s = (en if l == "en" else key_or_zh) if en is not None else (key_or_zh or "")

    # 最後做一次 literal runtime 替換，補齊未完全 key 化的字串
    s = _translate_literal_runtime(s, l)

    try:
        return s.format(**fmt)
    except Exception:
        return s

def t(key, uid):

    return T(key, uid=uid)

def L(uid, zh_or_key, en=None):
    # 舊 L(uid, "key") 或 L(uid, "中文", "English") 都能用
    return T(zh_or_key, uid=uid, en=en)

def _api_L(zh, en):
    # 舊 API 翻譯（相容）
    return T(zh, lang=_api_lang(), en=en)

# ✅ 把 API_TEXTS 併入 TEXTS（避免再多一套字典）
API_TEXTS = {
    "missing_params": ("缺少參數", "Missing parameters"),
    "invalid_params": ("參數錯誤", "Invalid parameters"),
    "not_found": ("找不到資料", "Data not found"),
    "write_failed": ("寫入失敗", "Write failed"),
    "server_error": ("伺服器錯誤", "Server error"),
}
for k, (zh, en) in API_TEXTS.items():
    if k not in TEXTS:
        TEXTS[k] = {"zh": zh, "en": en}

def _api_T(key: str):
    # 舊 _api_T（相容）
    return T(key, lang=_api_lang())


