import logging
import os
import time
from datetime import datetime

from flask import request, render_template

from config import TW_TZ
from linebot_app.consent import (
    _consent_q,
    _consent_lock,
    _last_consent_ts,
    CONSENT_MIN_INTERVAL,
    upsert_consent,
)

def _get_liff_consent_id() -> str:
    return (os.getenv("LIFF_CONSENT_ID") or "").strip()


def render_consent_page():
    liff_id = (os.getenv("LIFF_ID") or "").strip()   # 改成讀 consent 專用 ID

    if not liff_id:
        logging.error("LIFF_CONSENT_ID not set")
        return "LIFF_CONSENT_ID not set on server", 500

    return render_template(
        "consent.html",
        liff_id=liff_id
    )


def render_privacy_page():
    return render_template("privacy_policy.html")


def api_consent():
    try:
        payload = request.get_json(force=True, silent=False) or {}
        agreed = bool(payload.get("agree"))
        user_id = (payload.get("userId") or "").strip()
        display_name = payload.get("displayName") or ""
        source_type = payload.get("sourceType") or ""
        ua = payload.get("ua") or request.headers.get("User-Agent","")
        ts = payload.get("ts") or datetime.now(TW_TZ).isoformat()

        if not user_id:
            logging.warning(f"/api/consent missing userId. payload={payload}")
            return {"ok": False, "message": "缺少 userId"}, 400

        now = time.time()
        last = _last_consent_ts.get(user_id, 0.0)
        if now - last < CONSENT_MIN_INTERVAL:
            return {"ok": True, "message": "accepted"}, 200
        _last_consent_ts[user_id] = now

        ok = upsert_consent(user_id, agreed, display_name, source_type, ua, ts)
        if not ok:
            def job():
                try:
                    upsert_consent(user_id, agreed, display_name, source_type, ua, ts)
                except Exception:
                    pass
            with _consent_lock:
                if len(_consent_q) < 1000:
                    _consent_q.append(job)
            return {"ok": True, "message": "queued"}, 200

        return {"ok": True}, 200
    except Exception as e:
        logging.error(f"/api/consent 失敗: {e}")
        return {"ok": False}, 500



def register_consent_routes(app):
    app.add_url_rule('/consent', endpoint='render_consent_page', view_func=render_consent_page, methods=['GET'])
    app.add_url_rule('/privacy', endpoint='render_privacy_page', view_func=render_privacy_page, methods=['GET'])
    app.add_url_rule('/api/consent', endpoint='api_consent', view_func=api_consent, methods=['POST'])
