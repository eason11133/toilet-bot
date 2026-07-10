import json

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None


def configure_publish(postgres_enabled, pg_connect, psycopg2_module):
    global POSTGRES_ENABLED, _pg_connect, psycopg2
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module


def approve_submission(submission_id: int, reviewer: str = "admin"):
    if not POSTGRES_ENABLED:
        raise RuntimeError("CivicFix publish requires Postgres/DATABASE_URL")
    conn = _pg_connect()
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("SELECT * FROM facility_submissions WHERE id = %s FOR UPDATE", (int(submission_id),))
        submission = cur.fetchone()
        if not submission:
            raise ValueError(f"submission not found: {submission_id}")
        s = dict(submission)
        submission_type = s.get("submission_type")

        # Idempotency guard: browser double-clicks or retrying the same POST must
        # not create duplicate facilities for one approved submission.
        if s.get("verification_status") == "approved":
            return {
                "ok": True,
                "already_approved": True,
                "facility_id": s.get("related_facility_id"),
                "submission_id": int(submission_id),
            }

        if submission_type == "new_facility":
            cur.execute("""
                INSERT INTO facilities (
                    facility_type, source, source_id, name, address, lat, lon,
                    opening_hours, photo_url, placement_note, access_note, status_note,
                    field_info_level, trust_level, verification_status, publish_status,
                    civicfix_status, official_status, created_at, updated_at
                ) VALUES (%s, 'civicfix_user', %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, 'approved', 'published', 'active', 'active', NOW(), NOW())
                RETURNING id
            """, (
                s.get("facility_type"),
                f"submission_{s.get('id')}",
                s.get("name"),
                s.get("address"),
                s.get("lat"),
                s.get("lon"),
                s.get("opening_hours"),
                s.get("photo_url"),
                s.get("placement_note"),
                s.get("access_note"),
                s.get("status_note"),
                s.get("field_info_level") or "medium",
                s.get("trust_level") or "L3",
            ))
            facility_id = cur.fetchone()["id"]
        else:
            facility_id = s.get("related_facility_id")
            if not facility_id:
                raise ValueError("non-new submission requires related_facility_id")

            assignments = []
            params = []
            if submission_type in {"field_info_update", "photo_update"}:
                for col in ("photo_url", "placement_note", "access_note"):
                    if s.get(col):
                        assignments.append(f"{col} = %s")
                        params.append(s.get(col))
                assignments.append("field_info_level = %s")
                params.append(s.get("field_info_level") or "medium")
                assignments.append("last_field_verified_at = NOW()")
            if submission_type == "status_update" and s.get("status_note"):
                assignments.append("status_note = %s")
                params.append(s.get("status_note"))
            if submission_type == "opening_hours_fix" and s.get("opening_hours"):
                assignments.append("opening_hours = %s")
                params.append(s.get("opening_hours"))
            if submission_type == "location_fix" and s.get("lat") is not None and s.get("lon") is not None:
                assignments.append("lat = %s")
                params.append(s.get("lat"))
                assignments.append("lon = %s")
                params.append(s.get("lon"))

            if assignments:
                assignments.append("updated_at = NOW()")
                params.append(int(facility_id))
                cur.execute(f"""
                    UPDATE facilities
                    SET {', '.join(assignments)}
                    WHERE id = %s
                """, params)

        cur.execute("""
            UPDATE facility_submissions
            SET verification_status = 'approved',
                related_facility_id = COALESCE(related_facility_id, %s),
                verified_at = NOW(), verified_by = %s, updated_at = NOW()
            WHERE id = %s
        """, (facility_id, reviewer, int(submission_id)))
        if s.get("ticket_id"):
            cur.execute("""
                UPDATE rescue_tickets
                SET status = 'resolved', related_submission_id = %s, updated_at = NOW()
                WHERE id = %s
            """, (int(submission_id), s.get("ticket_id")))
        conn.commit()
        return {"ok": True, "facility_id": facility_id, "submission_id": int(submission_id)}
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def reject_submission(submission_id: int, reviewer: str = "admin", reason: str = ""):
    if not POSTGRES_ENABLED:
        raise RuntimeError("CivicFix publish requires Postgres/DATABASE_URL")
    conn = _pg_connect()
    try:
        cur = conn.cursor()
        cur.execute("""
            UPDATE facility_submissions
            SET verification_status = 'rejected', verified_at = NOW(), verified_by = %s,
                reject_reason = %s, updated_at = NOW()
            WHERE id = %s
        """, (reviewer, reason or "", int(submission_id)))
        conn.commit()
        return {"ok": True, "submission_id": int(submission_id), "status": "rejected"}
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def mark_need_review(submission_id: int):
    if not POSTGRES_ENABLED:
        raise RuntimeError("CivicFix publish requires Postgres/DATABASE_URL")
    conn = _pg_connect()
    try:
        cur = conn.cursor()
        cur.execute("""
            UPDATE facility_submissions
            SET verification_status = 'need_review', updated_at = NOW()
            WHERE id = %s
        """, (int(submission_id),))
        conn.commit()
        return {"ok": True, "submission_id": int(submission_id), "status": "need_review"}
    finally:
        conn.close()
