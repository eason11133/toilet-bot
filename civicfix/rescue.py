import json
from datetime import datetime

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None

_NEGATIVE_COMMENT_KEYWORDS = [
    "不存在", "已關閉", "關閉", "停用", "不能用", "不可用", "無法使用",
    "找不到", "沒有這間", "拆除", "封閉", "施工", "不開放",
]


def configure_rescue(postgres_enabled, pg_connect, psycopg2_module):
    global POSTGRES_ENABLED, _pg_connect, psycopg2
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module


def create_ticket(ticket):
    if not POSTGRES_ENABLED:
        raise RuntimeError("CivicFix rescue tickets require Postgres/DATABASE_URL")
    conn = _pg_connect()
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            INSERT INTO rescue_tickets (
                ticket_code, facility_type, area_name, lat, lon, problem_type,
                evidence_json, suspected_reason, suggested_action, priority_level,
                status, related_facility_id, related_submission_id, created_at, updated_at
            ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, COALESCE(%s, 'open'), %s, %s, NOW(), NOW())
            RETURNING *
        """, (
            ticket.get("ticket_code") or _make_ticket_code(),
            ticket.get("facility_type") or "toilet",
            ticket.get("area_name") or "",
            ticket.get("lat"),
            ticket.get("lon"),
            ticket.get("problem_type") or "no_result",
            json.dumps(ticket.get("evidence") or ticket.get("evidence_json") or {}, ensure_ascii=False),
            ticket.get("suspected_reason") or "",
            ticket.get("suggested_action") or "",
            ticket.get("priority_level") or "medium",
            ticket.get("status") or "open",
            ticket.get("related_facility_id"),
            ticket.get("related_submission_id"),
        ))
        row = dict(cur.fetchone())
        conn.commit()
        return row
    finally:
        conn.close()


def list_tickets(limit=100, status=None):
    if not POSTGRES_ENABLED:
        return []
    conn = _pg_connect()
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        if status:
            cur.execute("""
                SELECT * FROM rescue_tickets
                WHERE status = %s
                ORDER BY created_at DESC
                LIMIT %s
            """, (status, int(limit)))
        else:
            cur.execute("""
                SELECT * FROM rescue_tickets
                ORDER BY created_at DESC
                LIMIT %s
            """, (int(limit),))
        return [dict(r) for r in (cur.fetchall() or [])]
    finally:
        conn.close()


def get_ticket(ticket_id):
    if not POSTGRES_ENABLED:
        return None
    conn = _pg_connect()
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("SELECT * FROM rescue_tickets WHERE id = %s", (int(ticket_id),))
        row = cur.fetchone()
        return dict(row) if row else None
    finally:
        conn.close()


def _make_ticket_code():
    return "CF-" + datetime.utcnow().strftime("%Y%m%d%H%M%S%f")[:-3]


def _is_negative_comment(text):
    text = (text or "").strip()
    return bool(text and any(k in text for k in _NEGATIVE_COMMENT_KEYWORDS))


def create_tickets_from_negative_feedback(limit=300):
    """Convert recent negative toilet feedback into rescue tickets.

    This is intentionally conservative and creates at most one open ticket per
    rounded coordinate/problem type.
    """
    if not POSTGRES_ENABLED:
        raise RuntimeError("CivicFix feedback conversion requires Postgres/DATABASE_URL")
    conn = _pg_connect()
    created = 0
    scanned = 0
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT name, address, comment, lat, lon, created_at
            FROM toilet_feedbacks
            WHERE comment IS NOT NULL AND comment <> ''
            ORDER BY created_at DESC
            LIMIT %s
        """, (int(limit),))
        rows = [dict(r) for r in (cur.fetchall() or [])]
        for r in rows:
            scanned += 1
            comment = r.get("comment") or ""
            if not _is_negative_comment(comment):
                continue
            lat = r.get("lat")
            lon = r.get("lon")
            try:
                lat_f = float(lat)
                lon_f = float(lon)
            except Exception:
                # Some old feedback rows may not have coordinates.  Do not let
                # one malformed feedback record abort the whole conversion job.
                continue
            cur.execute("""
                SELECT id FROM rescue_tickets
                WHERE facility_type = 'toilet'
                  AND problem_type = 'unavailable_reported'
                  AND status IN ('open', 'processing')
                  AND ABS(COALESCE(lat, 0) - %s) < 0.00002
                  AND ABS(COALESCE(lon, 0) - %s) < 0.00002
                LIMIT 1
            """, (lat_f, lon_f))
            if cur.fetchone():
                continue
            evidence = {
                "source": "toilet_feedbacks",
                "name": r.get("name"),
                "address": r.get("address"),
                "comment": comment,
                "reported_at": str(r.get("created_at")),
            }
            cur.execute("""
                INSERT INTO rescue_tickets (
                    ticket_code, facility_type, area_name, lat, lon, problem_type,
                    evidence_json, suspected_reason, suggested_action, priority_level,
                    status, created_at, updated_at
                ) VALUES (%s, 'toilet', %s, %s, %s, 'unavailable_reported', %s, %s, %s, 'high', 'open', NOW(), NOW())
            """, (
                _make_ticket_code(),
                r.get("name") or r.get("address") or "使用者回報公廁異常",
                lat_f,
                lon_f,
                json.dumps(evidence, ensure_ascii=False),
                "使用者回報該公廁不存在、關閉、找不到或不可用。",
                "請管理者查核；若確認異常，標記為 needs_review 或 hidden，避免繼續推薦。",
            ))
            created += 1
        conn.commit()
        return {"ok": True, "scanned": scanned, "created": created}
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()
