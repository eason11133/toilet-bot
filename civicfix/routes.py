import hashlib
import hmac
import json
import os
import tempfile
import time
from datetime import datetime, timezone
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit

from flask import jsonify, make_response, redirect, render_template, request, url_for
from werkzeug.utils import secure_filename

from civicfix.facilities import configure_facilities, get_civicfix_overview, get_recent_sync_logs
from civicfix.gate import evaluate_submission
from civicfix.publish import approve_submission, reject_submission, mark_need_review, configure_publish
from civicfix.rescue import (
    configure_rescue,
    create_ticket,
    create_tickets_from_gap_summary,
    create_ticket_from_sync_status,
    create_tickets_from_negative_feedback,
    get_ticket,
    list_tickets,
)
from civicfix.sync import configure_sync, sync_moenv_toilets_from_csv

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None
UPLOAD_DIR = None
DATA_DIR = None
_maintenance_auth_ok = None

_CIVICFIX_COOKIE = "civicfix_admin_session"
_CIVICFIX_COOKIE_MAX_AGE = 12 * 60 * 60


def configure_civicfix(postgres_enabled, pg_connect, psycopg2_module, upload_dir=None, maintenance_auth_ok_func=None):
    global POSTGRES_ENABLED, _pg_connect, psycopg2, UPLOAD_DIR, DATA_DIR, _maintenance_auth_ok
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module
    UPLOAD_DIR = os.path.abspath(upload_dir or os.path.join(os.getcwd(), "data", "civicfix_uploads"))
    DATA_DIR = os.path.abspath(os.path.dirname(UPLOAD_DIR))
    _maintenance_auth_ok = maintenance_auth_ok_func
    os.makedirs(UPLOAD_DIR, exist_ok=True)
    configure_sync(postgres_enabled, pg_connect, psycopg2_module)
    configure_facilities(postgres_enabled, pg_connect, psycopg2_module)
    configure_rescue(postgres_enabled, pg_connect, psycopg2_module)
    configure_publish(postgres_enabled, pg_connect, psycopg2_module)


def _admin_secret():
    return (os.getenv("ADMIN_TOKEN") or "").strip()


def _cookie_signature(expires_at: str) -> str:
    secret = _admin_secret()
    if not secret:
        return ""
    return hmac.new(secret.encode("utf-8"), str(expires_at).encode("utf-8"), hashlib.sha256).hexdigest()


def _make_cookie_value() -> str:
    expires_at = str(int(time.time()) + _CIVICFIX_COOKIE_MAX_AGE)
    return f"{expires_at}:{_cookie_signature(expires_at)}"


def _cookie_auth_ok() -> bool:
    raw = request.cookies.get(_CIVICFIX_COOKIE) or ""
    try:
        expires_at, sig = raw.split(":", 1)
        if int(expires_at) < int(time.time()):
            return False
        expected = _cookie_signature(expires_at)
        return bool(expected) and hmac.compare_digest(sig, expected)
    except Exception:
        return False


def _request_token_ok() -> bool:
    return bool(_maintenance_auth_ok and _maintenance_auth_ok())


def _auth_ok() -> bool:
    # Compatibility: direct ?token= / X-Admin-Token still works.
    # Safer admin UX: after /dashboard/civicfix/login, a signed HttpOnly cookie is used.
    return _cookie_auth_ok() or _request_token_ok()


def _safe_next_path(next_path: str) -> str:
    default = "/dashboard/civicfix/tickets"
    if not next_path:
        return default
    raw = str(next_path).strip()
    if not raw.startswith("/") or raw.startswith("//"):
        return default

    parts = urlsplit(raw)
    if parts.scheme or parts.netloc:
        return default

    query = urlencode([(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True) if k != "token"])
    path = parts.path or default
    return urlunsplit(("", "", path, query, parts.fragment))


def _require_auth():
    if not _auth_ok():
        if request.method == "GET":
            return render_template(
                "civicfix_auth.html",
                next_path=_safe_next_path(request.full_path if request.query_string else request.path),
                message="請輸入 ADMIN_TOKEN 後再進入 CivicFix 後台。",
            ), 401
        return "Unauthorized", 401
    return None


def _token_kwargs(extra=None):
    # Kept so older call sites still work, but do not propagate ADMIN_TOKEN in URLs anymore.
    return dict(extra or {})


def civicfix_login_page():
    if _auth_ok():
        return redirect(_safe_next_path(request.args.get("next") or "/dashboard/civicfix/tickets"))
    return render_template(
        "civicfix_auth.html",
        next_path=_safe_next_path(request.args.get("next") or "/dashboard/civicfix/tickets"),
        message="請輸入 ADMIN_TOKEN。",
    )


def civicfix_login():
    if not _request_token_ok():
        return render_template(
            "civicfix_auth.html",
            next_path=_safe_next_path(request.form.get("next_path") or "/dashboard/civicfix/tickets"),
            message="密碼錯誤，請重新輸入 ADMIN_TOKEN。",
        ), 401

    next_path = _safe_next_path(request.form.get("next_path") or "/dashboard/civicfix/tickets")
    resp = make_response(redirect(next_path))
    resp.set_cookie(
        _CIVICFIX_COOKIE,
        _make_cookie_value(),
        max_age=_CIVICFIX_COOKIE_MAX_AGE,
        httponly=True,
        secure=bool(request.is_secure),
        samesite="Lax",
        path="/",
    )
    return resp


def civicfix_logout():
    resp = make_response(redirect(url_for("civicfix_login_page")))
    resp.delete_cookie(_CIVICFIX_COOKIE, path="/")
    return resp


def _safe_data_path(local_path: str) -> str:
    root = os.path.abspath(DATA_DIR or os.getcwd())
    if not local_path:
        return os.path.join(root, "public_toilets.csv")

    raw = str(local_path).strip().replace("\\", "/")
    if raw.startswith("data/"):
        raw = raw[len("data/"):]
    if os.path.isabs(raw):
        candidate = os.path.abspath(raw)
    else:
        candidate = os.path.abspath(os.path.join(root, raw))
    if candidate != root and not candidate.startswith(root + os.sep):
        raise ValueError("invalid local_path: only files under the data directory are allowed")
    return candidate


def _validate_csv_filename(filename: str) -> str:
    raw = (filename or "").strip()
    if not raw:
        raise ValueError("missing CSV filename")
    if not raw.lower().endswith(".csv"):
        raise ValueError("only .csv uploads are allowed")

    safe = secure_filename(raw)
    # secure_filename("全國公廁建檔資料.csv") may become "csv" on some environments.
    # Accept the original .csv extension, then fall back to a stable ASCII filename.
    if not safe or "." not in safe:
        return "public_toilets.csv"
    if not safe.lower().endswith(".csv"):
        safe = os.path.splitext(safe)[0] + ".csv"
    return safe


def _db_required_response():
    if POSTGRES_ENABLED:
        return None
    return render_template("civicfix_help.html", message="CivicFix 需要 DATABASE_URL/Postgres 才能使用同步與急救單功能。")


def civicfix_dashboard():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    return redirect(url_for("civicfix_tickets_page"))


def civicfix_help():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    return render_template("civicfix_help.html", message=request.args.get("message", ""))


def civicfix_sync_page():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    logs = get_recent_sync_logs(20)
    return render_template("civicfix_sync.html", logs=logs, result=None)


def civicfix_sync_toilets():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    upload = request.files.get("file")
    local_path = (request.form.get("local_path") or "").strip()
    try:
        if upload and upload.filename:
            filename = _validate_csv_filename(upload.filename)
            safe_name = f"{datetime.now().strftime('%Y%m%d_%H%M%S')}_{filename}"
            path = os.path.abspath(os.path.join(UPLOAD_DIR, safe_name))
            if not path.startswith(os.path.abspath(UPLOAD_DIR) + os.sep):
                raise ValueError("invalid upload path")
            upload.save(path)
        elif local_path:
            path = _safe_data_path(local_path)
            filename = os.path.relpath(path, DATA_DIR or os.getcwd())
        else:
            path = _safe_data_path("public_toilets.csv")
            filename = "data/public_toilets.csv"
        result = sync_moenv_toilets_from_csv(path, file_name=filename)
        logs = get_recent_sync_logs(20)
        return render_template("civicfix_sync.html", logs=logs, result=result)
    except Exception as e:
        logs = get_recent_sync_logs(20)
        return render_template("civicfix_sync.html", logs=logs, result={"ok": False, "error": str(e)}), 400


def _parse_ticket_evidence(ticket):
    raw = ticket.get("evidence_json") if isinstance(ticket, dict) else None
    if isinstance(raw, dict):
        return raw
    try:
        return json.loads(raw or "{}")
    except Exception:
        return {"raw": raw or ""}


def _decorate_ticket(ticket):
    t = dict(ticket or {})
    evidence = _parse_ticket_evidence(t)
    t["evidence"] = evidence
    source = evidence.get("source") or "manual"
    t["source"] = source
    t["source_label"] = {
        "gap_dashboard": "Gap 缺口",
        "toilet_feedbacks": "使用者回報",
        "source_sync_logs": "同步狀態",
        "manual": "手動備用",
    }.get(source, source)
    t["problem_label"] = {
        "no_result": "查無結果",
        "low_coverage": "低覆蓋",
        "unavailable_reported": "回報不存在/不可用",
        "missing_point": "疑似缺點位",
        "low_trust_point": "低可信點位",
        "outdated_official_data": "官方資料過期",
        "biggis_hotspot": "BigGIS 熱區",
    }.get(t.get("problem_type"), t.get("problem_type") or "未知")

    summary_bits = []
    for key, label in (
        ("effective_queries", "有效查詢"),
        ("no_result_count", "查無"),
        ("low_result_count", "低覆蓋"),
        ("unique_users", "使用者"),
        ("active_days", "天數"),
        ("gap_score", "缺口分數"),
    ):
        val = evidence.get(key)
        if val not in (None, ""):
            summary_bits.append(f"{label} {val}")
    if evidence.get("comment"):
        summary_bits.append(str(evidence.get("comment"))[:60])
    if evidence.get("days_old") is not None:
        summary_bits.append(f"距上次同步 {evidence.get('days_old')} 天")
    t["evidence_summary"] = " / ".join(summary_bits) or "—"
    return t


def civicfix_tickets_page():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    tickets = [_decorate_ticket(t) for t in list_tickets(limit=200)]
    counts = {"gap_dashboard": 0, "toilet_feedbacks": 0, "source_sync_logs": 0, "manual": 0}
    for t in tickets:
        counts[t.get("source") or "manual"] = counts.get(t.get("source") or "manual", 0) + 1
    return render_template(
        "civicfix_tickets.html",
        tickets=tickets,
        counts=counts,
        message=request.args.get("message", ""),
    )


def civicfix_ticket_detail(ticket_id):
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    ticket = get_ticket(ticket_id)
    if not ticket:
        return "Ticket not found", 404
    return render_template("civicfix_ticket_detail.html", ticket=_decorate_ticket(ticket))


def civicfix_new_ticket_page():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    return render_template("civicfix_ticket_new.html")


def civicfix_new_ticket():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    data = request.form
    ticket = create_ticket({
        "facility_type": data.get("facility_type") or "toilet",
        "area_name": data.get("area_name") or "",
        "lat": data.get("lat") or None,
        "lon": data.get("lon") or None,
        "problem_type": data.get("problem_type") or "no_result",
        "evidence": {"source": "manual", "manual_note": data.get("evidence") or ""},
        "suspected_reason": data.get("suspected_reason") or "",
        "suggested_action": data.get("suggested_action") or "",
        "priority_level": data.get("priority_level") or "medium",
    })
    return redirect(url_for("civicfix_ticket_detail", ticket_id=ticket["id"]))


def civicfix_convert_feedback():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    result = create_tickets_from_negative_feedback(limit=int(request.form.get("limit") or 300))
    return redirect(url_for("civicfix_tickets_page", message=f"已掃描 {result['scanned']} 筆回饋，建立 {result['created']} 張急救單"))


def civicfix_convert_gap():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    result = create_tickets_from_gap_summary(
        range_key=request.form.get("range") or "30d",
        limit=int(request.form.get("limit") or 10),
    )
    return redirect(url_for("civicfix_tickets_page", message=f"已從 Gap Dashboard 掃描 {result['scanned']} 個缺口群，建立 {result['created']} 張急救單，略過重複 {result.get('skipped_duplicate', 0)} 張"))


def civicfix_convert_sync_issues():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    result = create_ticket_from_sync_status(stale_days=int(request.form.get("stale_days") or 30))
    return redirect(url_for("civicfix_tickets_page", message=f"同步狀態檢查完成：建立 {result.get('created', 0)} 張急救單（{result.get('reason', '')}）"))


def civicfix_submit_page():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    ticket_id = request.args.get("ticket_id") or ""
    related_facility_id = request.args.get("facility_id") or ""
    return render_template("civicfix_submit.html", ticket_id=ticket_id, related_facility_id=related_facility_id, result=None)


def _none_if_blank(v):
    if v is None:
        return None
    s = str(v).strip()
    return s if s else None


def civicfix_submit():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    form = request.form
    payload = {
        "ticket_id": _none_if_blank(form.get("ticket_id")),
        "facility_type": form.get("facility_type") or "toilet",
        "submission_type": form.get("submission_type") or "field_info_update",
        "related_facility_id": _none_if_blank(form.get("related_facility_id")),
        "name": _none_if_blank(form.get("name")),
        "address": _none_if_blank(form.get("address")),
        "lat": _none_if_blank(form.get("lat")),
        "lon": _none_if_blank(form.get("lon")),
        "opening_hours": _none_if_blank(form.get("opening_hours")),
        "photo_url": _none_if_blank(form.get("photo_url")),
        "placement_note": _none_if_blank(form.get("placement_note")),
        "access_note": _none_if_blank(form.get("access_note")),
        "status_note": _none_if_blank(form.get("status_note")),
        "submitter_type": form.get("submitter_type") or "admin",
    }
    gate = evaluate_submission(payload)
    conn = _pg_connect()
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            INSERT INTO facility_submissions (
                ticket_id, facility_type, submission_type, related_facility_id,
                name, address, lat, lon, opening_hours, photo_url, placement_note,
                access_note, status_note, submitter_type, verification_score,
                trust_level, field_info_level, risk_flags, verification_status,
                created_at, updated_at
            ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, NOW(), NOW())
            RETURNING *
        """, (
            payload["ticket_id"], payload["facility_type"], payload["submission_type"], payload["related_facility_id"],
            payload["name"], payload["address"], payload["lat"], payload["lon"], payload["opening_hours"],
            payload["photo_url"], payload["placement_note"], payload["access_note"], payload["status_note"],
            payload["submitter_type"], gate["score"], gate["trust_level"], gate["field_info_level"],
            json.dumps(gate["risk_flags"], ensure_ascii=False), gate["suggested_action"],
        ))
        submission = dict(cur.fetchone())
        cur.execute("""
            INSERT INTO verification_logs (
                submission_id, facility_type, score, trust_level, field_info_level,
                risk_flags, suggested_action, reason, created_at
            ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, NOW())
        """, (
            submission["id"], payload["facility_type"], gate["score"], gate["trust_level"], gate["field_info_level"],
            json.dumps(gate["risk_flags"], ensure_ascii=False), gate["suggested_action"], gate["reason"],
        ))
        conn.commit()
        return render_template("civicfix_submit.html", ticket_id=payload.get("ticket_id") or "", related_facility_id=payload.get("related_facility_id") or "", result={"submission": submission, "gate": gate})
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def _decode_risk_flags(raw):
    if isinstance(raw, list):
        return raw
    try:
        data = json.loads(raw or "[]")
        return data if isinstance(data, list) else [str(data)]
    except Exception:
        if not raw:
            return []
        return [str(raw)]


def _decorate_submission(row):
    s = dict(row or {})
    flags = _decode_risk_flags(s.get("risk_flags"))
    s["risk_flag_list"] = flags
    s["risk_flag_labels"] = [{
        "missing_name": "缺名稱",
        "invalid_coordinate": "座標異常",
        "missing_coordinate": "缺座標",
        "missing_photo": "缺照片",
        "missing_placement_note": "缺位置描述",
        "missing_access_note": "缺到達說明",
        "looks_like_test_data": "疑似測試資料",
        "low_info": "資訊不足",
    }.get(f, f) for f in flags]
    s["action_label"] = {
        "approve": "建議通過",
        "need_review": "建議人工查核",
        "reject": "建議拒絕",
        "approved": "已通過",
        "rejected": "已拒絕",
    }.get(s.get("verification_status"), s.get("verification_status") or "待處理")
    return s


def civicfix_gate_page():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    conn = _pg_connect()
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT * FROM facility_submissions
            WHERE verification_status IN ('approve', 'need_review', 'pending')
               OR verification_status IS NULL
            ORDER BY created_at DESC
            LIMIT 200
        """)
        submissions = [_decorate_submission(dict(r)) for r in (cur.fetchall() or [])]
        return render_template("civicfix_gate.html", submissions=submissions, message=request.args.get("message", ""))
    finally:
        conn.close()


def civicfix_gate_approve(submission_id):
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    approve_submission(int(submission_id))
    return redirect(url_for("civicfix_gate_page", message=f"已通過 submission #{submission_id}"))


def civicfix_gate_reject(submission_id):
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    reason = request.form.get("reason") or ""
    reject_submission(int(submission_id), reason=reason)
    return redirect(url_for("civicfix_gate_page", message=f"已拒絕 submission #{submission_id}"))


def civicfix_gate_need_review(submission_id):
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    mark_need_review(int(submission_id))
    return redirect(url_for("civicfix_gate_page", message=f"已標記待查核 submission #{submission_id}"))


def api_civicfix_overview():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    return jsonify(get_civicfix_overview())


def register_civicfix_routes(app):
    app.add_url_rule("/dashboard/civicfix", endpoint="civicfix_dashboard", view_func=civicfix_dashboard, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/login", endpoint="civicfix_login_page", view_func=civicfix_login_page, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/login", endpoint="civicfix_login", view_func=civicfix_login, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/logout", endpoint="civicfix_logout", view_func=civicfix_logout, methods=["GET", "POST"])
    app.add_url_rule("/dashboard/civicfix/help", endpoint="civicfix_help", view_func=civicfix_help, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/sync", endpoint="civicfix_sync_page", view_func=civicfix_sync_page, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/sync/toilets", endpoint="civicfix_sync_toilets", view_func=civicfix_sync_toilets, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/tickets", endpoint="civicfix_tickets_page", view_func=civicfix_tickets_page, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/tickets/<int:ticket_id>", endpoint="civicfix_ticket_detail", view_func=civicfix_ticket_detail, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/tickets/new", endpoint="civicfix_new_ticket_page", view_func=civicfix_new_ticket_page, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/tickets/new", endpoint="civicfix_new_ticket", view_func=civicfix_new_ticket, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/tickets/from-feedback", endpoint="civicfix_convert_feedback", view_func=civicfix_convert_feedback, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/tickets/from-gap", endpoint="civicfix_convert_gap", view_func=civicfix_convert_gap, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/tickets/from-sync", endpoint="civicfix_convert_sync_issues", view_func=civicfix_convert_sync_issues, methods=["POST"])
    app.add_url_rule("/civicfix/submit", endpoint="civicfix_submit_page", view_func=civicfix_submit_page, methods=["GET"])
    app.add_url_rule("/civicfix/submit", endpoint="civicfix_submit", view_func=civicfix_submit, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/gate", endpoint="civicfix_gate_page", view_func=civicfix_gate_page, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/gate/<int:submission_id>/approve", endpoint="civicfix_gate_approve", view_func=civicfix_gate_approve, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/gate/<int:submission_id>/reject", endpoint="civicfix_gate_reject", view_func=civicfix_gate_reject, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/gate/<int:submission_id>/need-review", endpoint="civicfix_gate_need_review", view_func=civicfix_gate_need_review, methods=["POST"])
    app.add_url_rule("/api/civicfix/overview", endpoint="api_civicfix_overview", view_func=api_civicfix_overview, methods=["GET"])
