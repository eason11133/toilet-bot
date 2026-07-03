import logging
import os
import urllib.parse

from flask import request, render_template, redirect

build_nearby_toilets = None
norm_coord = None
submit_status_update = None
_api_L = None
_get_liff_status_id = None
get_user_lang = None


def configure_status_routes(
    build_nearby_toilets_func,
    norm_coord_func,
    submit_status_update_func,
    api_L_func,
    get_liff_status_id_func,
    get_user_lang_func,
):
    global build_nearby_toilets, norm_coord, submit_status_update, _api_L, _get_liff_status_id, get_user_lang
    build_nearby_toilets = build_nearby_toilets_func
    norm_coord = norm_coord_func
    submit_status_update = submit_status_update_func
    _api_L = api_L_func
    _get_liff_status_id = get_liff_status_id_func
    get_user_lang = get_user_lang_func

def api_status_candidates():
    try:
        lat = float(request.args.get("lat"))
        lon = float(request.args.get("lon"))
    except Exception:
        return {"ok": False, "message": "缺少或錯誤的座標"}, 400

    try:
        # 半徑放寬一點，提高命中率；已內建快取/去重/排序
        items = build_nearby_toilets("status", lat, lon, radius=700) or []
        out = []
        for t in items[:3]:
            out.append({
                "title": t.get("name") or t.get("place_hint") or "（未命名）廁所",
                "address": t.get("address") or "",
                # 用 norm_coord（字串）讓之後比對座標更穩定
                "lat": norm_coord(t["lat"]),
                "lon": norm_coord(t["lon"]),
                "distance": int(t.get("distance", 0))
            })
        return {"ok": True, "candidates": out}, 200
    except Exception as e:
        logging.error(f"/api/status_candidates 失敗: {e}")
        return {"ok": False, "message": "server error"}, 500


def api_status_report():
    try:
        payload = request.get_json(force=True)
        lat = float(payload["lat"])
        lon = float(payload["lon"])
        status_text = (payload.get("status") or "").strip()
        user_id = (payload.get("user_id") or "").strip()
        display_name = (payload.get("display_name") or "").strip()
        note = (payload.get("note") or "").strip()
    except Exception:
        return {"ok": False, "message": _api_L("參數錯誤", "Invalid parameters")}, 400

    allowed = {"有人排隊", "缺衛生紙", "暫停使用", "恢復正常"}
    if status_text not in allowed:
        return {"ok": False, "message": _api_L("不支援的狀態", "Unsupported status")}, 400

    try:
        ok = submit_status_update(lat, lon, status_text, user_id, display_name, note)
        return ({"ok": True}, 200) if ok else ({"ok": False, "message": _api_L("寫入失敗", "Write failed")}, 500)
    except Exception as e:
        logging.error(f"/api/status_report 寫入失敗: {e}")
        return {"ok": False, "message": "server error"}, 500


def status_liff():
    liff_id = _get_liff_status_id()
    public_url = os.getenv("PUBLIC_URL", "").rstrip("/")

    # ✅ 語言：LIFF 沒辦法自動知道你在聊天裡切的語言，所以用 querystring 帶 uid/lang
    uid = (request.args.get("uid") or "").strip()
    lang = (request.args.get("lang") or "").strip().lower()

    # 如果有 uid 但沒帶 lang，就依資料庫記錄自動補上 lang，避免前端還要自己算
    if uid and not lang:
        try:
            lang = "en" if get_user_lang(uid) == "en" else "zh"
        except Exception:
            lang = "zh"
        # 保留原本的其他 querystring（如 lat/lon）
        qs = request.args.to_dict(flat=True)
        qs["lang"] = lang
        return redirect(request.path + "?" + urllib.parse.urlencode(qs), code=302)

    if not liff_id:
        logging.error("LIFF_STATUS_ID / LIFF_ID_STATUS / LIFF_ID not set")
        return "LIFF ID not set", 500

    if not public_url:
        logging.error("PUBLIC_URL not set")
        return "PUBLIC_URL not set", 500

    return render_template(
        "status_liff.html",
        liff_id=liff_id,
        public_url=public_url,
        uid=uid,
        lang=(lang if lang in ["en","zh"] else "zh")
    )



def register_status_routes(app):
    app.add_url_rule('/api/status_candidates', endpoint='api_status_candidates', view_func=api_status_candidates)
    app.add_url_rule('/api/status_report', endpoint='api_status_report', view_func=api_status_report, methods=['POST'])
    app.add_url_rule('/status_liff', endpoint='status_liff', view_func=status_liff)
