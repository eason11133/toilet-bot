import os
import json
import logging
import requests
import traceback
from flask import request, render_template

POSTGRES_ENABLED = False
_pg_connect = None
_CACHE = None
_floor_from_name = None
_parse_lat_lon = None
geocode_address = None
norm_coord = None
auto_verify_user_toilet = None

def configure_submission(
    postgres_enabled,
    pg_connect,
    cache,
    floor_from_name_func,
    parse_lat_lon_func,
    geocode_address_func,
    norm_coord_func,
    auto_verify_user_toilet_func,
):
    global POSTGRES_ENABLED, _pg_connect, _CACHE, _floor_from_name, _parse_lat_lon, geocode_address, norm_coord, auto_verify_user_toilet
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    _CACHE = cache
    _floor_from_name = floor_from_name_func
    _parse_lat_lon = parse_lat_lon_func
    geocode_address = geocode_address_func
    norm_coord = norm_coord_func
    auto_verify_user_toilet = auto_verify_user_toilet_func

def register_submission_routes(app):
    app.add_url_rule("/add", endpoint="render_add_page", view_func=render_add_page, methods=["GET"])
    app.add_url_rule("/submit_toilet", endpoint="submit_toilet", view_func=submit_toilet, methods=["POST"])

def render_add_page():
    uid = request.args.get("uid", "")
    lat = request.args.get("lat", "")
    lon = request.args.get("lon", "")
    preset_address = ""

    if lat and lon:
        try:
            ua_email = os.getenv("CONTACT_EMAIL", "you@example.com")
            url = f"https://nominatim.openstreetmap.org/reverse?format=jsonv2&lat={lat}&lon={lon}&addressdetails=1"
            headers = {"User-Agent": f"ToiletBot/1.0 (+{ua_email})"}
            resp = requests.get(url, headers=headers, timeout=10)
            if resp.status_code == 200:
                data = resp.json()
                a = data.get("address", {})
                pretty = " ".join(filter(None, [
                    a.get("country", ""),
                    a.get("state", a.get("region", "")),
                    a.get("city", a.get("town", a.get("village", a.get("county", "")))),
                    a.get("suburb", a.get("neighbourhood", "")),
                    a.get("road", ""),
                    a.get("house_number", ""),
                    a.get("postcode", "")
                ])).strip()
                preset_address = pretty or data.get("display_name", "")
        except Exception as e:
            logging.warning(f"reverse geocode 失敗: {e}")

    return render_template(
        "submit_toilet.html",
        preset_address=preset_address,
        preset_lat=lat,
        preset_lon=lon
    )


def submit_toilet():
    if not POSTGRES_ENABLED:
        return {"success": False, "message": "資料庫尚未啟用，無法新增廁所"}, 503
    try:
        data = request.get_json(force=True, silent=False) or {}

        uid   = (data.get("user_id") or "web").strip()
        name  = (data.get("name") or "").strip()
        addr  = (data.get("address") or "").strip()

        level          = (data.get("level") or "").strip()
        floor_hint     = (data.get("floor_hint") or "").strip()
        entrance_hint  = (data.get("entrance_hint") or "").strip()
        access_note    = (data.get("access_note") or "").strip()
        open_hours     = (data.get("open_hours") or "").strip()

        lat_in = (data.get("lat") or "").strip()
        lon_in = (data.get("lon") or "").strip()
        logging.info(f"📥 收到新增廁所表單: name={name!r}, lat={lat_in!r}, lon={lon_in!r}")

        # 必填檢查
        if not name or not addr:
            return {"success": False, "message": "請提供『廁所名稱』與『地址』"}, 400

        # 位置描述基本檢查
        if floor_hint and len(floor_hint) < 4:
            return {"success": False, "message": "『位置描述』太短，請至少 4 個字"}, 400

        # 未提供位置描述則嘗試由名稱推斷
        if not floor_hint:
            inferred = _floor_from_name(name)
            if inferred:
                floor_hint = inferred

        # 座標解析與地理編碼
        lat_f, lon_f = (None, None)
        if lat_in and lon_in:
            lat_f, lon_f = _parse_lat_lon(lat_in, lon_in)
        if lat_f is None or lon_f is None:
            lat_f, lon_f = geocode_address(addr)
        if lat_f is None or lon_f is None:
            return {"success": False, "message": "地址轉換失敗，請修正地址或提供座標"}, 400

        lat_s, lon_s = norm_coord(lat_f), norm_coord(lon_f)

        # Auto Verification 1.0：表單送出後自動判定 approved / pending / rejected
        candidate = {
            "user_id": uid,
            "name": name,
            "address": addr,
            "lat": float(lat_s),
            "lon": float(lon_s),
            "level": level,
            "floor_hint": floor_hint,
            "entrance_hint": entrance_hint,
            "access_note": access_note,
            "open_hours": open_hours,
        }
        av = auto_verify_user_toilet(candidate)
        verification_status = av["verification_status"]
        verification_score = int(av["auto_verification_score"])
        verification_reason = av["auto_verification_reason"]
        risk_flags_json = json.dumps(av.get("risk_flags") or [], ensure_ascii=False)
        similar_json = json.dumps(av.get("similar_toilets") or [], ensure_ascii=False)

        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO user_toilets (
                user_id, name, address, lat, lon,
                level, floor_hint, entrance_hint,
                access_note, open_hours,
                verification_status, verification_score, verification_reason,
                auto_verification_score, auto_verification_result,
                auto_verification_reason, risk_flags, similar_toilets_json,
                created_at, updated_at, source
            )
            VALUES (
                %s, %s, %s, %s, %s,
                %s, %s, %s,
                %s, %s,
                %s, %s, %s,
                %s, %s,
                %s, %s, %s,
                NOW(), NOW(), 'neon'
            )
            ON CONFLICT (user_id, name, lat, lon)
            DO UPDATE SET
                address = EXCLUDED.address,
                level = EXCLUDED.level,
                floor_hint = EXCLUDED.floor_hint,
                entrance_hint = EXCLUDED.entrance_hint,
                access_note = EXCLUDED.access_note,
                open_hours = EXCLUDED.open_hours,
                verification_status = EXCLUDED.verification_status,
                verification_score = EXCLUDED.verification_score,
                verification_reason = EXCLUDED.verification_reason,
                auto_verification_score = EXCLUDED.auto_verification_score,
                auto_verification_result = EXCLUDED.auto_verification_result,
                auto_verification_reason = EXCLUDED.auto_verification_reason,
                risk_flags = EXCLUDED.risk_flags,
                similar_toilets_json = EXCLUDED.similar_toilets_json,
                updated_at = NOW()
            RETURNING id
        """, (
            uid, name, addr, float(lat_s), float(lon_s),
            level, floor_hint, entrance_hint,
            access_note, open_hours,
            verification_status, verification_score, verification_reason,
            verification_score, verification_status,
            verification_reason, risk_flags_json, similar_json,
        ))
        new_id = cur.fetchone()[0]
        conn.commit()
        conn.close()
        try: _CACHE.clear()
        except Exception: pass

        if verification_status == "approved":
            msg = f"✅ 已收到 {name}，系統自動驗證為低風險，已加入推薦資料。"
        elif verification_status == "rejected":
            msg = f"⚠️ 已收到 {name}，但系統判定資料風險較高，暫不加入推薦。原因：{verification_reason}"
        else:
            msg = f"✅ 已收到 {name}，目前列為待確認資料。原因：{verification_reason}"

        logging.info(f"📝 submit_toilet 已寫入 Neon id={new_id} name={name} status={verification_status} score={verification_score}")
        return {
            "success": True,
            "message": msg,
            "id": new_id,
            "verification_status": verification_status,
            "auto_verification_score": verification_score,
            "auto_verification_result": verification_status,
            "risk_flags": av.get("risk_flags") or [],
            "similar_toilets": av.get("similar_toilets") or [],
            "facility_type": av.get("facility_type")
        }

    except Exception as e:
        logging.error(f"❌ 新增廁所錯誤:\n{traceback.format_exc()}")
        return {"success": False, "message": "伺服器錯誤"}, 500

