import json
import os
import tempfile
from datetime import datetime, timezone

from flask import jsonify, redirect, render_template, request, url_for
from werkzeug.utils import secure_filename

from civicfix.facilities import configure_facilities, get_civicfix_overview, get_recent_sync_logs
from civicfix.gate import evaluate_submission
from civicfix.publish import approve_submission, reject_submission, mark_need_review, configure_publish
from civicfix.rescue import (
    configure_rescue,
    create_ticket,
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


def _require_auth():
    # CivicFix is an admin/development surface for now. Public citizen-facing
    # endpoints can be reopened later after a separate abuse-control design.
    if _maintenance_auth_ok and not _maintenance_auth_ok():
        return "Unauthorized", 401
    return None


def _safe_data_path(local_path: str) -> str:
    root = os.path.abspath(DATA_DIR or os.getcwd())
    if not local_path:
        return os.path.join(root, "public_toilets.csv")

    raw = str(local_path).strip().replace("\\", "/")
    # Accept both "public_toilets.csv" and the common UI wording
    # "data/public_toilets.csv", while still pinning reads to DATA_DIR.
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
    safe = secure_filename(filename or "")
    if not safe:
        raise ValueError("missing CSV filename")
    if not safe.lower().endswith(".csv"):
        raise ValueError("only .csv uploads are allowed")
    return safe


def _db_required_response():
    if POSTGRES_ENABLED:
        return None
    return render_template("civicfix_dashboard.html", overview={"postgres_enabled": False}, logs=[], message="CivicFix 需要 DATABASE_URL/Postgres 才能使用同步與急救單功能。")


def civicfix_dashboard():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    overview = get_civicfix_overview()
    logs = get_recent_sync_logs(8)
    return render_template("civicfix_dashboard.html", overview=overview, logs=logs, message=request.args.get("message", ""))


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
        return render_template("civicfix_sync.html", logs=logs, result={"ok": False, "error": str(e)}), 500


def civicfix_tickets_page():
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    tickets = list_tickets(limit=200)
    return render_template("civicfix_tickets.html", tickets=tickets, message=request.args.get("message", ""))


def civicfix_ticket_detail(ticket_id):
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    if not POSTGRES_ENABLED:
        return _db_required_response()
    ticket = get_ticket(ticket_id)
    if not ticket:
        return "Ticket not found", 404
    return render_template("civicfix_ticket_detail.html", ticket=ticket)


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
        "evidence": {"manual_note": data.get("evidence") or ""},
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
        submissions = [dict(r) for r in (cur.fetchall() or [])]
        return render_template("civicfix_gate.html", submissions=submissions, message=request.args.get("message", ""))
    finally:
        conn.close()


def civicfix_gate_approve(submission_id):
    auth_error = _require_auth()
    if auth_error:
        return auth_error
    result = approve_submission(int(submission_id))
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
    app.add_url_rule("/dashboard/civicfix/sync", endpoint="civicfix_sync_page", view_func=civicfix_sync_page, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/sync/toilets", endpoint="civicfix_sync_toilets", view_func=civicfix_sync_toilets, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/tickets", endpoint="civicfix_tickets_page", view_func=civicfix_tickets_page, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/tickets/<int:ticket_id>", endpoint="civicfix_ticket_detail", view_func=civicfix_ticket_detail, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/tickets/new", endpoint="civicfix_new_ticket_page", view_func=civicfix_new_ticket_page, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/tickets/new", endpoint="civicfix_new_ticket", view_func=civicfix_new_ticket, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/tickets/from-feedback", endpoint="civicfix_convert_feedback", view_func=civicfix_convert_feedback, methods=["POST"])
    app.add_url_rule("/civicfix/submit", endpoint="civicfix_submit_page", view_func=civicfix_submit_page, methods=["GET"])
    app.add_url_rule("/civicfix/submit", endpoint="civicfix_submit", view_func=civicfix_submit, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/gate", endpoint="civicfix_gate_page", view_func=civicfix_gate_page, methods=["GET"])
    app.add_url_rule("/dashboard/civicfix/gate/<int:submission_id>/approve", endpoint="civicfix_gate_approve", view_func=civicfix_gate_approve, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/gate/<int:submission_id>/reject", endpoint="civicfix_gate_reject", view_func=civicfix_gate_reject, methods=["POST"])
    app.add_url_rule("/dashboard/civicfix/gate/<int:submission_id>/need-review", endpoint="civicfix_gate_need_review", view_func=civicfix_gate_need_review, methods=["POST"])
    app.add_url_rule("/api/civicfix/overview", endpoint="api_civicfix_overview", view_func=api_civicfix_overview, methods=["GET"])
