import json
import logging
from flask import request, jsonify, render_template

ADMIN_TOKEN = ""
POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None
_CACHE = None
_build_auto_verify_context = None
auto_verify_user_toilet = None

def configure_admin_routes(
    admin_token,
    postgres_enabled,
    pg_connect,
    psycopg2_module,
    cache,
    build_auto_verify_context_func,
    auto_verify_user_toilet_func,
):
    global ADMIN_TOKEN, POSTGRES_ENABLED, _pg_connect, psycopg2, _CACHE, _build_auto_verify_context, auto_verify_user_toilet
    ADMIN_TOKEN = admin_token
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module
    _CACHE = cache
    _build_auto_verify_context = build_auto_verify_context_func
    auto_verify_user_toilet = auto_verify_user_toilet_func

def register_admin_routes(app):
    app.add_url_rule("/admin/reverify-user-toilets", endpoint="admin_reverify_user_toilets", view_func=admin_reverify_user_toilets, methods=["POST", "GET"])
    app.add_url_rule("/api/maintenance-summary", endpoint="api_maintenance_summary", view_func=api_maintenance_summary, methods=["GET"])
    app.add_url_rule("/api/user-toilets-admin", endpoint="api_user_toilets_admin", view_func=api_user_toilets_admin, methods=["GET"])
    app.add_url_rule("/api/user-toilet-review", endpoint="api_user_toilet_review", view_func=api_user_toilet_review, methods=["POST"])
    app.add_url_rule("/dashboard/maintenance", endpoint="dashboard_maintenance", view_func=dashboard_maintenance, methods=["GET"])

def admin_reverify_user_toilets():
    if not _maintenance_auth_ok():
        return jsonify({"ok": False, "message": "unauthorized"}), 401
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "message": "postgres disabled"}), 503

    apply_update = (request.args.get("apply") or "0").strip() != "0"
    limit = int(request.args.get("limit") or "500")
    updated = 0
    preview = []
    counts = {"approved": 0, "pending": 0, "rejected": 0}

    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT id, user_id, name, address, lat, lon, level, floor_hint,
                   entrance_hint, access_note, open_hours, verification_status
            FROM user_toilets
            ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST
            LIMIT %s
        """, (limit,))
        rows = cur.fetchall()

        verify_context = _build_auto_verify_context()

        for r in rows:
            av = auto_verify_user_toilet(r, context=verify_context, exclude_id=r.get("id"))
            st = av["verification_status"]
            counts[st] = counts.get(st, 0) + 1
            preview.append({
                "id": r.get("id"),
                "name": r.get("name"),
                "old_status": r.get("verification_status") or "pending",
                "new_status": st,
                "score": av["auto_verification_score"],
                "facility_type": av.get("facility_type"),
                "reason": av["auto_verification_reason"],
                "risk_flags": av.get("risk_flags") or [],
                "verification_version": av.get("verification_version"),
                "soft_flags": av.get("soft_flags") or [],
                "address_coordinate_distance_m": av.get("address_coordinate_distance_m"),
                "spatial_context": av.get("spatial_context") or {}
            })
            if apply_update:
                cur.execute("""
                    UPDATE user_toilets
                    SET verification_status = %s,
                        verification_score = %s,
                        verification_reason = %s,
                        auto_verification_score = %s,
                        auto_verification_result = %s,
                        auto_verification_reason = %s,
                        risk_flags = %s,
                        similar_toilets_json = %s,
                        updated_at = NOW()
                    WHERE id = %s
                """, (
                    st,
                    int(av["auto_verification_score"]),
                    av["auto_verification_reason"],
                    int(av["auto_verification_score"]),
                    st,
                    av["auto_verification_reason"],
                    json.dumps(av.get("risk_flags") or [], ensure_ascii=False),
                    json.dumps(av.get("similar_toilets") or [], ensure_ascii=False),
                    r.get("id")
                ))
                updated += 1

        if apply_update:
            conn.commit()
        conn.close()
        try: _CACHE.clear()
        except Exception: pass
        return jsonify({
            "ok": True,
            "apply": apply_update,
            "scanned": len(rows),
            "updated": updated,
            "counts": counts,
            "preview": preview[:30]
        })
    except Exception as e:
        logging.error(f"admin_reverify_user_toilets failed: {e}", exc_info=True)
        return jsonify({"ok": False, "message": str(e)}), 500


def _parse_risk_flags_value(value):
    """Parse risk_flags stored as JSON text/list into a safe list[str]."""
    if value is None:
        return []
    if isinstance(value, list):
        return [str(x) for x in value if x not in (None, "")]
    if isinstance(value, (dict, tuple)):
        return [str(x) for x in value]
    raw = str(value).strip()
    if not raw:
        return []
    try:
        data = json.loads(raw)
        if isinstance(data, list):
            return [str(x) for x in data if x not in (None, "")]
        if isinstance(data, dict):
            return [str(k) for k, v in data.items() if v]
    except Exception:
        pass
    # fallback: support comma separated or python-list-like text
    raw = raw.strip("[]")
    parts = [x.strip().strip("'\"") for x in raw.split(',')]
    return [x for x in parts if x]


def _parse_similar_toilets_value(value):
    if value is None:
        return []
    if isinstance(value, list):
        return value
    raw = str(value).strip()
    if not raw:
        return []
    try:
        data = json.loads(raw)
        return data if isinstance(data, list) else []
    except Exception:
        return []


def _maintenance_auth_ok():
    if not ADMIN_TOKEN:
        logging.critical("ADMIN_TOKEN not set; rejecting admin request")
        return False

    json_token = ""
    try:
        data = request.get_json(silent=True) if request.is_json else None
        if isinstance(data, dict):
            json_token = data.get("token") or ""
    except Exception:
        json_token = ""

    token = (
        request.headers.get("X-Admin-Token")
        or request.args.get("token")
        or json_token
        or ""
    ).strip()
    return token == ADMIN_TOKEN


def api_maintenance_summary():
    """Auto Verification / maintenance queue summary.
    Used by /dashboard/maintenance. Requires ADMIN_TOKEN when configured.
    """
    if not _maintenance_auth_ok():
        return jsonify({"ok": False, "message": "unauthorized"}), 401
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "message": "postgres disabled"}), 503

    try:
        limit = max(1, min(int(request.args.get("limit") or "500"), 3000))
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT
                id, name, address, lat, lon,
                verification_status, verification_score, verification_reason,
                auto_verification_score, auto_verification_result, auto_verification_reason,
                risk_flags, similar_toilets_json,
                created_at, updated_at
            FROM user_toilets
            ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST
            LIMIT %s
        """, (limit,))
        rows = cur.fetchall()

        recent_review_logs = []
        try:
            cur.execute("""
                SELECT
                    id, toilet_id, toilet_name,
                    old_status, new_status,
                    old_score, new_score, auto_verification_score,
                    reviewer, action_reason, reject_reason,
                    risk_flags, created_at
                FROM user_toilet_review_logs
                ORDER BY created_at DESC
                LIMIT 30
            """)
            recent_review_logs = cur.fetchall()
        except Exception as log_err:
            logging.warning(f"maintenance review logs skipped: {log_err}")
            recent_review_logs = []

        conn.close()

        status_counts = {"approved": 0, "pending": 0, "rejected": 0, "unknown": 0}
        score_values = []
        flag_counts = {}
        queues = {
            "pending": [],
            "possible_duplicate": [],
            "possible_duplicate_high": [],
            "possible_duplicate_medium": [],
            "possible_duplicate_low": [],
            "strict_duplicate": [],
            "duplicate_high": [],
            "duplicate_medium": [],
            "duplicate_low": [],
            "shop_access_unclear": [],
            "generic_name": [],
            "address_coordinate_mismatch": [],
            "spatial_outlier": [],
            "outside_primary_region": [],
            "rejected": [],
            "low_score": []
        }

        def row_item(r, flags=None, similar=None):
            flags = flags if flags is not None else _parse_risk_flags_value(r.get("risk_flags"))
            similar = similar if similar is not None else _parse_similar_toilets_value(r.get("similar_toilets_json"))
            return {
                "id": r.get("id"),
                "name": r.get("name") or "",
                "address": r.get("address") or "",
                "status": r.get("verification_status") or "unknown",
                "score": r.get("auto_verification_score") if r.get("auto_verification_score") is not None else r.get("verification_score"),
                "reason": r.get("auto_verification_reason") or r.get("verification_reason") or "",
                "risk_flags": flags,
                "similar_count": len(similar),
                "similar_toilets": similar[:3],
                "updated_at": r.get("updated_at").isoformat() if hasattr(r.get("updated_at"), "isoformat") else str(r.get("updated_at") or "")
            }

        for r in rows:
            status = (r.get("verification_status") or "unknown").lower()
            if status not in status_counts:
                status_counts["unknown"] += 1
            else:
                status_counts[status] += 1

            try:
                sc = r.get("auto_verification_score")
                if sc is None:
                    sc = r.get("verification_score")
                if sc is not None:
                    score_values.append(float(sc))
            except Exception:
                pass

            flags = _parse_risk_flags_value(r.get("risk_flags"))
            similar = _parse_similar_toilets_value(r.get("similar_toilets_json"))
            for f in flags:
                flag_counts[f] = flag_counts.get(f, 0) + 1

            item = row_item(r, flags, similar)
            if status == "pending" and len(queues["pending"]) < 80:
                queues["pending"].append(item)
            if status == "rejected" and len(queues["rejected"]) < 80:
                queues["rejected"].append(item)
            if any(f.startswith("possible_duplicate") for f in flags) and len(queues["possible_duplicate"]) < 80:
                queues["possible_duplicate"].append(item)
            if "possible_duplicate_high" in flags:
                if len(queues["possible_duplicate_high"]) < 80:
                    queues["possible_duplicate_high"].append(item)
                if len(queues["duplicate_high"]) < 80:
                    queues["duplicate_high"].append(item)
            if "possible_duplicate_medium" in flags:
                if len(queues["possible_duplicate_medium"]) < 80:
                    queues["possible_duplicate_medium"].append(item)
                if len(queues["duplicate_medium"]) < 80:
                    queues["duplicate_medium"].append(item)
            if "possible_duplicate_low" in flags:
                if len(queues["possible_duplicate_low"]) < 80:
                    queues["possible_duplicate_low"].append(item)
                if len(queues["duplicate_low"]) < 80:
                    queues["duplicate_low"].append(item)
            if "strict_duplicate" in flags and len(queues["strict_duplicate"]) < 80:
                queues["strict_duplicate"].append(item)
            if any(f.startswith("address_coordinate_mismatch") for f in flags) and len(queues["address_coordinate_mismatch"]) < 80:
                queues["address_coordinate_mismatch"].append(item)
            if "spatial_outlier_candidate" in flags and len(queues["spatial_outlier"]) < 80:
                queues["spatial_outlier"].append(item)
            if "shop_access_unclear" in flags and len(queues["shop_access_unclear"]) < 80:
                queues["shop_access_unclear"].append(item)
            if "name_too_generic" in flags and len(queues["generic_name"]) < 80:
                queues["generic_name"].append(item)
            if "outside_primary_region" in flags and len(queues["outside_primary_region"]) < 80:
                queues["outside_primary_region"].append(item)
            try:
                item_score = float(item.get("score") or 0)
                if item_score < 70 and len(queues["low_score"]) < 80:
                    queues["low_score"].append(item)
            except Exception:
                pass

        total = len(rows)
        avg_score = round(sum(score_values) / len(score_values), 2) if score_values else 0
        top_flags = [
            {"flag": k, "count": v}
            for k, v in sorted(flag_counts.items(), key=lambda kv: kv[1], reverse=True)
        ]

        review_logs_out = []
        for log_row in recent_review_logs or []:
            review_logs_out.append({
                "id": log_row.get("id"),
                "toilet_id": log_row.get("toilet_id"),
                "toilet_name": log_row.get("toilet_name") or "",
                "old_status": log_row.get("old_status") or "",
                "new_status": log_row.get("new_status") or "",
                "old_score": log_row.get("old_score"),
                "new_score": log_row.get("new_score"),
                "auto_verification_score": log_row.get("auto_verification_score"),
                "reviewer": log_row.get("reviewer") or "",
                "action_reason": log_row.get("action_reason") or "",
                "reject_reason": log_row.get("reject_reason") or "",
                "risk_flags": _parse_risk_flags_value(log_row.get("risk_flags")),
                "created_at": log_row.get("created_at").isoformat() if hasattr(log_row.get("created_at"), "isoformat") else str(log_row.get("created_at") or "")
            })

        return jsonify({
            "ok": True,
            "scanned": total,
            "summary": {
                "total": total,
                "approved": status_counts.get("approved", 0),
                "pending": status_counts.get("pending", 0),
                "rejected": status_counts.get("rejected", 0),
                "unknown": status_counts.get("unknown", 0),
                "avg_auto_score": avg_score,
                "risk_flag_types": len(flag_counts),
                "risk_flag_total": sum(flag_counts.values()),
                "pending_rate": round((status_counts.get("pending", 0) / total * 100), 2) if total else 0,
                "verification_version": "auto_verify_1_5_4"
            },
            "flag_counts": top_flags,
            "queues": queues,
            "review_logs": review_logs_out
        })
    except Exception as e:
        logging.error(f"/api/maintenance-summary failed: {e}", exc_info=True)
        return jsonify({"ok": False, "message": str(e)}), 500


def api_user_toilets_admin():
    """List user-added toilets for manual review / full data inspection.

    Query params:
      token: ADMIN_TOKEN
      status: all | approved | pending | rejected
      flag: optional risk flag substring/exact tag
      q: optional keyword for name/address/reason
      limit: 1..500
      offset: >=0
    """
    if not _maintenance_auth_ok():
        return jsonify({"ok": False, "message": "unauthorized"}), 401
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "message": "postgres disabled"}), 503

    try:
        status = (request.args.get("status") or "all").strip().lower()
        flag = (request.args.get("flag") or "").strip()
        q = (request.args.get("q") or "").strip()
        limit = max(1, min(int(request.args.get("limit") or "100"), 500))
        offset = max(0, int(request.args.get("offset") or "0"))

        where = []
        params = []
        if status in ("approved", "pending", "rejected"):
            where.append("LOWER(COALESCE(verification_status,'')) = %s")
            params.append(status)
        if q:
            like = f"%{q}%"
            where.append("""
                (
                    name ILIKE %s OR address ILIKE %s OR
                    COALESCE(auto_verification_reason,'') ILIKE %s OR
                    COALESCE(verification_reason,'') ILIKE %s OR
                    COALESCE(risk_flags,'') ILIKE %s
                )
            """)
            params.extend([like, like, like, like, like])
        if flag:
            like_flag = f"%{flag}%"
            where.append("COALESCE(risk_flags,'') ILIKE %s")
            params.append(like_flag)

        where_sql = "WHERE " + " AND ".join(where) if where else ""

        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute(f"SELECT COUNT(*) AS c FROM user_toilets {where_sql}", tuple(params))
        total = int((cur.fetchone() or {}).get("c") or 0)

        cur.execute(f"""
            SELECT
                id, user_id, name, address, lat, lon,
                level, floor_hint, entrance_hint, access_note, open_hours,
                source,
                verification_status, verification_score, verification_reason,
                auto_verification_score, auto_verification_result, auto_verification_reason,
                risk_flags, similar_toilets_json,
                verified_at, verified_by, reject_reason,
                created_at, updated_at
            FROM user_toilets
            {where_sql}
            ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST, id DESC
            LIMIT %s OFFSET %s
        """, tuple(params + [limit, offset]))
        rows = cur.fetchall()
        conn.close()

        items = []
        for r in rows:
            flags = _parse_risk_flags_value(r.get("risk_flags"))
            similar = _parse_similar_toilets_value(r.get("similar_toilets_json"))
            items.append({
                "id": r.get("id"),
                "name": r.get("name") or "",
                "address": r.get("address") or "",
                "lat": r.get("lat"),
                "lon": r.get("lon"),
                "level": r.get("level") or "",
                "floor_hint": r.get("floor_hint") or "",
                "entrance_hint": r.get("entrance_hint") or "",
                "access_note": r.get("access_note") or "",
                "open_hours": r.get("open_hours") or "",
                "source": r.get("source") or "",
                "status": r.get("verification_status") or "unknown",
                "verification_score": r.get("verification_score"),
                "auto_verification_score": r.get("auto_verification_score"),
                "score": r.get("auto_verification_score") if r.get("auto_verification_score") is not None else r.get("verification_score"),
                "verification_reason": r.get("verification_reason") or "",
                "auto_verification_reason": r.get("auto_verification_reason") or "",
                "reason": r.get("auto_verification_reason") or r.get("verification_reason") or "",
                "risk_flags": flags,
                "similar_count": len(similar),
                "similar_toilets": similar[:5],
                "verified_at": r.get("verified_at").isoformat() if hasattr(r.get("verified_at"), "isoformat") else str(r.get("verified_at") or ""),
                "verified_by": r.get("verified_by") or "",
                "reject_reason": r.get("reject_reason") or "",
                "created_at": r.get("created_at").isoformat() if hasattr(r.get("created_at"), "isoformat") else str(r.get("created_at") or ""),
                "updated_at": r.get("updated_at").isoformat() if hasattr(r.get("updated_at"), "isoformat") else str(r.get("updated_at") or "")
            })

        return jsonify({
            "ok": True,
            "total": total,
            "limit": limit,
            "offset": offset,
            "items": items
        })
    except Exception as e:
        logging.error(f"/api/user-toilets-admin failed: {e}", exc_info=True)
        return jsonify({"ok": False, "message": str(e)}), 500


def api_user_toilet_review():
    """Manually review a user-added toilet from the maintenance dashboard.

    Expected JSON:
    {
      "token": "ADMIN_TOKEN",
      "id": 123,
      "status": "approved" | "rejected",
      "reason": "optional note",
      "verified_by": "admin_dashboard"
    }
    """
    try:
        data = request.get_json(silent=True) or {}
        if not _maintenance_auth_ok():
            return jsonify({"ok": False, "message": "unauthorized"}), 401
        if not POSTGRES_ENABLED:
            return jsonify({"ok": False, "message": "postgres disabled"}), 503

        toilet_id = data.get("id") or data.get("toilet_id")
        try:
            toilet_id = int(toilet_id)
        except Exception:
            return jsonify({"ok": False, "message": "invalid toilet id"}), 400

        status = str(data.get("status") or "").strip().lower()
        allowed = {"approved", "pending", "rejected"}
        if status not in allowed:
            return jsonify({"ok": False, "message": "invalid status"}), 400

        reason = str(data.get("reason") or "").strip()
        verified_by = str(data.get("verified_by") or "admin_dashboard").strip()[:80]

        if status == "approved":
            default_reason = "人工審核通過"
            reject_reason = None
        elif status == "rejected":
            default_reason = "人工審核不通過"
            reject_reason = reason or default_reason
        else:
            default_reason = "人工保留待審"
            reject_reason = None

        final_reason = default_reason if not reason else f"{default_reason}：{reason}"

        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT
                id, name,
                verification_status,
                verification_score,
                verification_reason,
                auto_verification_score,
                auto_verification_result,
                auto_verification_reason,
                risk_flags,
                reject_reason
            FROM user_toilets
            WHERE id = %s
        """, (toilet_id,))
        exists = cur.fetchone()
        if not exists:
            conn.close()
            return jsonify({"ok": False, "message": "toilet not found"}), 404

        # Manual review should not overwrite the scoring model with fixed 100/50/0.
        # Keep the original automatic score as the verification_score so the score
        # continues to represent Auto Verification quality rather than the button clicked.
        try:
            original_score = exists.get("auto_verification_score")
            if original_score is None:
                original_score = exists.get("verification_score")
            score = int(original_score or 0)
        except Exception:
            score = 0

        cur.execute("""
            UPDATE user_toilets
            SET verification_status = %s,
                verification_score = %s,
                verification_reason = %s,
                verified_at = NOW(),
                verified_by = %s,
                reject_reason = %s,
                updated_at = NOW()
            WHERE id = %s
            RETURNING
                id, name, address, lat, lon,
                verification_status, verification_score, verification_reason,
                auto_verification_score, auto_verification_result, auto_verification_reason,
                risk_flags, similar_toilets_json,
                verified_at, verified_by, reject_reason, updated_at
        """, (status, score, final_reason, verified_by, reject_reason, toilet_id))
        row = cur.fetchone()

        # 寫入人工審核紀錄：保留前後狀態，方便追蹤誰在何時做了什麼。
        try:
            cur.execute("""
                INSERT INTO user_toilet_review_logs (
                    toilet_id, toilet_name,
                    old_status, new_status,
                    old_score, new_score,
                    auto_verification_score,
                    reviewer, action_reason, reject_reason,
                    risk_flags
                ) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
            """, (
                toilet_id,
                exists.get("name") or "",
                exists.get("verification_status") or "",
                status,
                exists.get("verification_score"),
                score,
                exists.get("auto_verification_score"),
                verified_by,
                final_reason,
                reject_reason,
                exists.get("risk_flags") or ""
            ))
        except Exception as log_err:
            logging.warning(f"insert user_toilet_review_logs failed: {log_err}")

        conn.commit()
        conn.close()

        try:
            _CACHE.clear()
        except Exception:
            pass

        return jsonify({
            "ok": True,
            "message": "updated",
            "item": {
                "id": row.get("id"),
                "name": row.get("name"),
                "status": row.get("verification_status"),
                "verification_score": row.get("verification_score"),
                "verification_reason": row.get("verification_reason"),
                "verified_at": row.get("verified_at").isoformat() if hasattr(row.get("verified_at"), "isoformat") else str(row.get("verified_at") or ""),
                "verified_by": row.get("verified_by") or "",
                "reject_reason": row.get("reject_reason") or ""
            }
        })
    except Exception as e:
        logging.error(f"/api/user-toilet-review failed: {e}", exc_info=True)
        return jsonify({"ok": False, "message": str(e)}), 500


def dashboard_maintenance():
    return render_template("maintenance.html")

