import os
import json
import logging
import requests
import random
import time
from flask import request, Response, redirect

POSTGRES_ENABLED = False
log_user_action = None


def configure_app_support(postgres_enabled=False, log_user_action_func=None):
    global POSTGRES_ENABLED, log_user_action
    POSTGRES_ENABLED = postgres_enabled
    log_user_action = log_user_action_func


class _NoHealthzFilter(logging.Filter):
    def filter(self, record):
        try:
            msg = record.getMessage()
        except Exception:
            return True
        return "/healthz" not in msg


def add_security_headers(resp):
    """安全標頭與快取策略
    - 一般頁面：禁止被 iframe（XFO=DENY + frame-ancestors 'none'）
    - LIFF/同意/回饋等頁面：需要在 LINE/LIFF WebView 裡開啟，必須放寬 frame-ancestors 與 script/connect 白名單
    """
    try:
        resp.headers.setdefault("Cache-Control", "no-store")
        resp.headers.setdefault("Pragma", "no-cache")
        resp.headers.setdefault("X-Content-Type-Options", "nosniff")
        resp.headers.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")

        path = (request.path or "").lower()

        # 需要在 LIFF WebView / LINE 內嵌開啟的頁面（請依你的實際路由再增減）
        is_liff_page = (
            path.startswith("/status_liff")
            or path.startswith("/toilet_feedback_by_coord")
            or path.startswith("/feedback_form")
            or path.startswith("/add")
            or path.startswith("/consent")
        )

        if is_liff_page:
            # ✅ LIFF 需要允許被 LINE/LIFF 內嵌
            # X-Frame-Options 建議不要用 DENY（會擋 iframe / webview），改成 SAMEORIGIN（或乾脆不設）
            resp.headers["X-Frame-Options"] = "SAMEORIGIN"

            # ✅ CSP：允許 LIFF SDK、Chart.js、以及 LIFF 可能用到的 API/連線
            csp = [
                "default-src 'self'",
                "img-src 'self' data: https:",
                "script-src 'self' 'unsafe-inline' 'unsafe-eval' https://static.line-scdn.net https://cdn.jsdelivr.net https://cdnjs.cloudflare.com https://unpkg.com",
                "style-src 'self' 'unsafe-inline'",
                "connect-src 'self' https: https://api.line.me https://access.line.me",
                "font-src 'self' data: https:",
                # 允許 LINE/LIFF 內嵌（如需也可加上特定 domain）
                "frame-ancestors 'self' https://access.line.me https://liff.line.me",
            ]
            resp.headers["Content-Security-Policy"] = "; ".join(csp) + ";"
        else:
            # ✅ 非 LIFF 頁面：更嚴格
            resp.headers.setdefault("X-Frame-Options", "DENY")
            csp = [
                "default-src 'self'",
                "img-src 'self' data: https:",
                "script-src 'self' 'unsafe-inline' https://cdn.jsdelivr.net https://cdnjs.cloudflare.com https://unpkg.com",
                "style-src 'self' 'unsafe-inline'",
                "connect-src 'self' https:",
                "font-src 'self' data: https:",
                "frame-ancestors 'none'",
            ]
            resp.headers["Content-Security-Policy"] = "; ".join(csp) + ";"
    except Exception as e:
        logging.debug(f"add_security_headers skipped: {e}")
    return resp


def readyz():
    """Readiness check: Neon/Postgres is the primary store now."""
    ok = POSTGRES_ENABLED
    status = 200 if ok else 503
    msg = "ready" if ok else "not-ready: postgres disabled"
    headers = {"Content-Type": "text/plain; charset=utf-8", "Cache-Control": "no-store", "X-Robots-Tag": "noindex"}
    if request.method == "HEAD":
        return Response(status=204 if ok else 503, headers=headers)
    return Response(msg, status=status, headers=headers)


def healthz():
    headers = {
        "Content-Type": "text/plain; charset=utf-8",
        "Cache-Control": "no-store",
        "X-Robots-Tag": "noindex",
    }
    if request.method == "HEAD":
        return Response(status=204, headers=headers)
    return Response("ok", status=200, headers=headers)


def go_to_toilet():
    query_id = request.args.get("qid", "")
    uid = request.args.get("uid", "")
    toilet_id = request.args.get("tid", "")
    lat = request.args.get("lat", "")
    lon = request.args.get("lon", "")
    name = request.args.get("name", "")

    try:
        log_user_action(
            query_id=query_id,
            uid=uid,
            toilet_id=toilet_id,
            action_type="click_navigation",
            extra_info=json.dumps({
                "lat": lat,
                "lon": lon,
                "name": name
            }, ensure_ascii=False)
        )
    except Exception as e:
        logging.warning(f"go_to_toilet log failed: {e}")

    return redirect(f"https://www.google.com/maps/search/?api=1&query={lat},{lon}")


# === 自我激活設定 ===
KEEPALIVE_URL = (
    os.getenv("KEEPALIVE_URL")
    or (os.getenv("PUBLIC_URL") and os.getenv("PUBLIC_URL").rstrip("/") + "/healthz")
    or (os.getenv("RENDER_EXTERNAL_URL") and os.getenv("RENDER_EXTERNAL_URL").rstrip("/") + "/healthz")
)
KEEPALIVE_ENABLE = os.getenv("KEEPALIVE_ENABLE", "1") == "1"
KEEPALIVE_INTERVAL_SECONDS = int(os.getenv("KEEPALIVE_INTERVAL_SECONDS", "600"))
KEEPALIVE_JITTER_SECONDS   = int(os.getenv("KEEPALIVE_JITTER_SECONDS", "60"))


def _self_keepalive_background():
    if not KEEPALIVE_ENABLE or not KEEPALIVE_URL:
        logging.info("⏭️ keepalive disabled (no URL or disabled by env).")
        return
    headers = {"User-Agent": f"SelfKeepalive/1.0 (+{os.getenv('CONTACT_EMAIL','you@example.com')})"}
    while True:
        try:
            requests.head(KEEPALIVE_URL, timeout=8, headers=headers)
            logging.debug("✅ keepalive ok")
        except Exception as e:
            logging.debug(f"⚠️ keepalive failed: {e}")
        sleep_for = KEEPALIVE_INTERVAL_SECONDS + random.randint(0, KEEPALIVE_JITTER_SECONDS)
        time.sleep(sleep_for)


def register_app_support_routes(app):
    app.after_request(add_security_headers)
    app.add_url_rule("/readyz", view_func=readyz, methods=["GET", "HEAD"])
    logging.getLogger("werkzeug").addFilter(_NoHealthzFilter())
    app.add_url_rule("/healthz", view_func=healthz, methods=["GET", "HEAD"])
    app.add_url_rule("/go_to_toilet", view_func=go_to_toilet)
