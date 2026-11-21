import logging
import os
import time
from datetime import datetime

import requests
from flask import request, render_template, make_response

from config import TW_TZ
from linebot_app.consent import (
    _consent_q,
    _consent_lock,
    _last_consent_ts,
    _booly,
    record_consent_attempt,
    upsert_consent,
    consent_storage_health,
    CONSENT_FLOW_VERSION,
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
    # The ID token audience belongs to the channel that owns this LIFF app.
    # A generic LINE_LOGIN_CHANNEL_ID may point to another Login channel and
    # would make LINE reject an otherwise valid token as invalid_id_token.
    dedicated = (os.getenv("LIFF_CONSENT_CHANNEL_ID") or "").strip()
    if dedicated:
        return dedicated
    liff_id = _get_liff_consent_id()
    derived = liff_id.split("-", 1)[0].strip() if "-" in liff_id else ""
    if derived:
        return derived
    # Backwards compatibility only for legacy LIFF IDs that do not contain a
    # channel prefix. New deployments should set LIFF_CONSENT_CHANNEL_ID.
    return (os.getenv("LINE_LOGIN_CHANNEL_ID") or "").strip()


def _verify_line_id_token(id_token):
    """Verify a LIFF ID token with LINE and return its trusted payload."""
    if not id_token:
        return None, "缺少 LINE 身分憑證，請關閉後重新開啟同意頁", 401, "missing_id_token"
    channel_id = _get_liff_channel_id()
    if not channel_id:
        logging.error("LIFF consent channel ID is not configured")
        return None, "伺服器缺少 LINE Login Channel ID", 500, "channel_config_missing"
    try:
        response = requests.post(
            "https://api.line.me/oauth2/v2.1/verify",
            data={"id_token": id_token, "client_id": channel_id},
            headers={"Content-Type": "application/x-www-form-urlencoded"},
            timeout=float(os.getenv("LINE_ID_TOKEN_VERIFY_TIMEOUT_SEC", "5")),
        )
    except requests.RequestException as exc:
        logging.warning("LINE ID token verification unavailable: %s", type(exc).__name__)
        return None, "LINE 身分驗證暫時無法使用，請稍後再試", 503, "line_verify_unavailable"
    try:
        payload = response.json()
    except Exception:
        payload = {}
    if response.status_code != 200:
        logging.warning("LINE ID token verification rejected status=%s", response.status_code)
        return None, "LINE 身分驗證失敗，請重新開啟同意頁", 401, "invalid_id_token"
    user_id = str(payload.get("sub") or "").strip()
    if not user_id:
        logging.warning("LINE ID token verification returned no subject")
        return None, "LINE 身分資料不完整，請重新登入", 401, "missing_subject"
    return payload, "", 200, "ok"


def _verify_line_access_token(access_token):
    """Validate a LIFF access token and load its LINE-owned profile."""
    if not access_token:
        return None, "缺少 LINE 存取憑證，請關閉後重新開啟同意頁", 401, "missing_access_token"
    channel_id = _get_liff_channel_id()
    if not channel_id:
        logging.error("LIFF consent channel ID is not configured")
        return None, "伺服器缺少 LINE Login Channel ID", 500, "channel_config_missing"
    timeout = float(os.getenv("LINE_ID_TOKEN_VERIFY_TIMEOUT_SEC", "5"))
    try:
        verification = requests.get(
            "https://api.line.me/oauth2/v2.1/verify",
            params={"access_token": access_token},
            timeout=timeout,
        )
    except requests.RequestException as exc:
        logging.warning("LINE access token verification unavailable: %s", type(exc).__name__)
        return None, "LINE 身分驗證暫時無法使用，請稍後再試", 503, "line_verify_unavailable"
    try:
        verification_payload = verification.json()
    except Exception:
        verification_payload = {}
    if verification.status_code != 200:
        logging.warning("LINE access token verification rejected status=%s", verification.status_code)
        return None, "LINE 身分驗證失敗，請重新開啟同意頁", 401, "invalid_access_token"
    token_channel_id = str(verification_payload.get("client_id") or "").strip()
    if token_channel_id != channel_id:
        logging.warning("LINE access token channel mismatch")
        return None, "LINE 應用程式設定不一致，請聯絡管理者", 500, "channel_mismatch"
    try:
        profile = requests.get(
            "https://api.line.me/v2/profile",
            headers={"Authorization": f"Bearer {access_token}"},
            timeout=timeout,
        )
    except requests.RequestException as exc:
        logging.warning("LINE profile lookup unavailable: %s", type(exc).__name__)
        return None, "LINE 身分資料暫時無法取得，請稍後再試", 503, "line_profile_unavailable"
    try:
        profile_payload = profile.json()
    except Exception:
        profile_payload = {}
    user_id = str(profile_payload.get("userId") or "").strip()
    if profile.status_code != 200 or not user_id:
        logging.warning("LINE profile lookup rejected status=%s", profile.status_code)
        return None, "LINE 身分資料無法取得，請重新開啟同意頁", 401, "invalid_profile"
    return {
        "sub": user_id,
        "name": str(profile_payload.get("displayName") or ""),
    }, "", 200, "ok"


def render_consent_page():
    liff_id = _get_liff_consent_id()

    if not liff_id:
        logging.error("LIFF_CONSENT_ID / LIFF_ID not set")
        return "LIFF consent ID not set on server", 500

    response = make_response(render_template(
        "consent.html",
        liff_id=liff_id,
        consent_flow_version=CONSENT_FLOW_VERSION,
    ))
    response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    response.headers["Pragma"] = "no-cache"
    response.headers["Expires"] = "0"
    return response


def render_privacy_page():
    return render_template(
        "privacy_policy.html",
        contact_url="https://www.instagram.com/toiletmvp?jplx=MWRvMnV2MTNyN2RkMw==",
    )


def api_consent_health():
    storage_ok, storage_status = consent_storage_health()
    status = 200 if storage_ok and _get_liff_consent_id() and _get_liff_channel_id() else 503
    return {
        "ok": status == 200,
        "flow_version": CONSENT_FLOW_VERSION,
        "liff_configured": bool(_get_liff_consent_id()),
        "channel_configured": bool(_get_liff_channel_id()),
        "storage_ok": storage_ok,
        "storage_status": storage_status,
    }, status


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
        access_token = str(payload.get("accessToken") or "").strip()
        id_token = str(payload.get("idToken") or "").strip()
        if len(access_token) > 4096:
            return {"ok": False, "message": "LINE 存取憑證格式錯誤"}, 400
        if len(id_token) > 8192:
            return {"ok": False, "message": "LINE 身分憑證格式錯誤"}, 400
        if access_token:
            verified, verify_error, verify_status, verify_code = _verify_line_access_token(
                access_token
            )
        else:
            verified, verify_error, verify_status, verify_code = _verify_line_id_token(
                id_token
            )
        if not verified:
            return {
                "ok": False,
                "code": verify_code,
                "message": verify_error,
                "retryable": verify_status >= 500,
            }, verify_status
        user_id = (verified.get("sub") or "").strip()
        if claimed_user_id and claimed_user_id != user_id:
            logging.warning("/api/consent LINE user mismatch")
            return {
                "ok": False,
                "code": "identity_mismatch",
                "message": "LINE 帳號驗證不一致，請重新開啟同意頁",
            }, 401
        display_name = str(verified.get("name") or "")[:200]
        source_type = str(payload.get("sourceType") or "")[:50]
        ua = str(request.headers.get("User-Agent", ""))[:500]
        ts = datetime.now(TW_TZ).isoformat()

        ok = upsert_consent(
            user_id,
            agreed,
            display_name,
            source_type,
            ua,
            ts,
            access_token=access_token,
        )
        if not ok:
            def job():
                try:
                    upsert_consent(
                        user_id,
                        agreed,
                        display_name,
                        source_type,
                        ua,
                        ts,
                        access_token=access_token,
                    )
                except Exception:
                    pass
            with _consent_lock:
                if _consent_q.maxlen is None or len(_consent_q) < _consent_q.maxlen:
                    _consent_q.append(job)
            # Never tell the LIFF page that consent succeeded before it was
            # durably stored.  The page stays open and lets the user retry.
            return {
                "ok": False,
                "code": "storage_unavailable",
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
    app.add_url_rule('/api/consent/health', endpoint='api_consent_health', view_func=api_consent_health, methods=['GET'])
