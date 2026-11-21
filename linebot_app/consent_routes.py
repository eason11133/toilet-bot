import logging
import os
import time
from datetime import datetime

import requests
from flask import request, render_template

from config import TW_TZ
from linebot_app.consent import (
    _consent_q,
    _consent_lock,
    _last_consent_ts,
    _booly,
    record_consent_attempt,
    upsert_consent,
)

def _get_liff_consent_id() -> str:
    # Prefer the dedicated consent LIFF app, while keeping the old shared LIFF
    # variable as a backwards-compatible fallback for existing deployments.
    return (
        os.getenv("LIFF_CONSENT_ID")
        or os.getenv("LIFF_ID_CONSENT")
        or os.getenv("LIFF_ID")
        or ""
    ).strip()


def _get_liff_channel_id() -> str:
    configured = (
        os.getenv("LIFF_CONSENT_CHANNEL_ID")
        or os.getenv("LINE_LOGIN_CHANNEL_ID")
        or ""
    ).strip()
    if configured:
        return configured
    liff_id = _get_liff_consent_id()
    return liff_id.split("-", 1)[0].strip() if "-" in liff_id else ""


def _verify_line_id_token(id_token):
    """Verify a LIFF ID token with LINE and return its trusted payload."""
    if not id_token:
        return None, "缺少 LINE 身分憑證", 401
    channel_id = _get_liff_channel_id()
    if not channel_id:
        logging.error("LIFF consent channel ID is not configured")
        return None, "伺服器缺少 LINE Login Channel ID", 500
    try:
        response = requests.post(
            "https://api.line.me/oauth2/v2.1/verify",
            data={"id_token": id_token, "client_id": channel_id},
            headers={"Content-Type": "application/x-www-form-urlencoded"},
            timeout=float(os.getenv("LINE_ID_TOKEN_VERIFY_TIMEOUT_SEC", "5")),
        )
    except requests.RequestException as exc:
        logging.warning("LINE ID token verification unavailable: %s", type(exc).__name__)
        return None, "LINE 身分驗證暫時無法使用，請稍後再試", 503
    try:
        payload = response.json()
    except Exception:
        payload = {}
    if response.status_code != 200:
        logging.warning("LINE ID token verification rejected status=%s", response.status_code)
        return None, "LINE 身分驗證失敗，請重新開啟同意頁", 401
    user_id = str(payload.get("sub") or "").strip()
    if not user_id:
        logging.warning("LINE ID token verification returned no subject")
        return None, "LINE 身分資料不完整，請重新登入", 401
    return payload, "", 200


def render_consent_page():
    liff_id = _get_liff_consent_id()

    if not liff_id:
        logging.error("LIFF_CONSENT_ID / LIFF_ID not set")
        return "LIFF consent ID not set on server", 500

    return render_template(
        "consent.html",
        liff_id=liff_id
    )


def render_privacy_page():
    return render_template("privacy_policy.html")


def api_consent():
    try:
        if request.content_length and request.content_length > 16384:
            return {"ok": False, "message": "請求內容過大"}, 413
        payload = request.get_json(silent=True)
        if payload is None:
            return {"ok": False, "message": "請求格式錯誤"}, 400
        if not isinstance(payload, dict):
            return {"ok": False, "message": "請求格式錯誤"}, 400
        if "agree" not in payload:
            return {"ok": False, "message": "缺少同意狀態"}, 400
        agreed = _booly(payload.get("agree"))
        claimed_user_id = str(payload.get("userId") or "").strip()[:128]
        id_token = str(payload.get("idToken") or "").strip()
        if len(id_token) > 8192:
            return {"ok": False, "message": "LINE 身分憑證格式錯誤"}, 400
        verified, verify_error, verify_status = _verify_line_id_token(
            id_token
        )
        if not verified:
            return {"ok": False, "message": verify_error, "retryable": verify_status >= 500}, verify_status
        user_id = (verified.get("sub") or "").strip()
        if claimed_user_id and claimed_user_id != user_id:
            logging.warning("/api/consent LINE user mismatch")
            return {"ok": False, "message": "LINE 帳號驗證不一致，請重新開啟同意頁"}, 401
        display_name = str(verified.get("name") or "")[:200]
        source_type = str(payload.get("sourceType") or "")[:50]
        ua = str(request.headers.get("User-Agent", ""))[:500]
        ts = datetime.now(TW_TZ).isoformat()

        ok = upsert_consent(user_id, agreed, display_name, source_type, ua, ts)
        if not ok:
            def job():
                try:
                    upsert_consent(user_id, agreed, display_name, source_type, ua, ts)
                except Exception:
                    pass
            with _consent_lock:
                if _consent_q.maxlen is None or len(_consent_q) < _consent_q.maxlen:
                    _consent_q.append(job)
            # Never tell the LIFF page that consent succeeded before it was
            # durably stored.  The page stays open and lets the user retry.
            return {
                "ok": False,
                "message": "同意狀態暫時無法儲存，請稍後再試",
                "retryable": True,
            }, 503

        record_consent_attempt(user_id, time.time())
        return {"ok": True}, 200
    except Exception as e:
        logging.error(f"/api/consent 失敗: {e}")
        return {"ok": False}, 500



def register_consent_routes(app):
    app.add_url_rule('/consent', endpoint='render_consent_page', view_func=render_consent_page, methods=['GET'])
    app.add_url_rule('/privacy', endpoint='render_privacy_page', view_func=render_privacy_page, methods=['GET'])
    app.add_url_rule('/api/consent', endpoint='api_consent', view_func=api_consent, methods=['POST'])
