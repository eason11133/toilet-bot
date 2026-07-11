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



def _ticket_exists_near(cur, facility_type, problem_type, lat, lon, radius_deg=0.00035):
    """Return True if an open/processing ticket already exists near the same point.

    radius_deg ~= 35m near Taiwan for lat/lon. It is only used as a safe duplicate guard,
    not as a GIS distance calculation.
    """
    try:
        cur.execute("""
            SELECT id FROM rescue_tickets
            WHERE facility_type = %s
              AND problem_type = %s
              AND status IN ('open', 'processing')
              AND ABS(COALESCE(lat, 0) - %s) < %s
              AND ABS(COALESCE(lon, 0) - %s) < %s
            LIMIT 1
        """, (facility_type, problem_type, float(lat), radius_deg, float(lon), radius_deg))
        return cur.fetchone() is not None
    except Exception:
        return False


def create_tickets_from_gap_summary(range_key="30d", limit=10, force=False):
    """Create rescue tickets from the existing Gap Dashboard backend summary.

    This is the important CivicFix bridge:
    Gap Dashboard detects demand gaps -> CivicFix turns them into processable rescue tickets.

    It intentionally imports dashboard.gap_analysis lazily to avoid adding a hard startup
    dependency from the original bot runtime into CivicFix.
    """
    if not POSTGRES_ENABLED:
        raise RuntimeError("CivicFix gap-ticket generation requires Postgres/DATABASE_URL")

    range_key = (range_key or "30d").strip()
    if range_key not in ("all", "1h", "1d", "7d", "30d", "1y"):
        range_key = "30d"
    limit = max(1, min(int(limit or 10), 50))

    try:
        from dashboard.gap_analysis import _build_gap_summary
    except Exception as e:
        raise RuntimeError(f"Gap summary is not available: {e}")

    summary = _build_gap_summary(range_key=range_key)
    clusters = summary.get("recommended_sites") or summary.get("demand_clusters") or []

    conn = _pg_connect()
    created = 0
    scanned = 0
    skipped_duplicate = 0
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        for row in clusters[:limit]:
            scanned += 1
            lat = row.get("lat")
            lon = row.get("lon")
            try:
                lat_f = float(lat)
                lon_f = float(lon)
            except Exception:
                continue

            no_result = int(row.get("no_result_count") or 0)
            low_result = int(row.get("low_result_count") or 0)
            slow_count = int(row.get("slow_query_count") or 0)
            total = int(row.get("effective_queries") or row.get("total_queries") or 0)
            gap_score = float(row.get("gap_score") or 0)

            if no_result >= 3 or (total >= 5 and no_result / max(total, 1) >= 0.35):
                problem_type = "no_result"
                suspected_reason = "Gap Dashboard 偵測到此需求圈有多次查無結果，可能是官方資料漏收、座標錯誤，或實際服務覆蓋不足。"
            elif low_result >= 4 or (total >= 6 and low_result / max(total, 1) >= 0.50):
                problem_type = "low_coverage"
                suspected_reason = "Gap Dashboard 偵測到此需求圈候選結果偏少，可能需要補資料或檢查附近公共場域。"
            elif slow_count >= 4:
                problem_type = "low_coverage"
                suspected_reason = "此區查詢耗時偏高，可能依賴外部資料或本地資料覆蓋不足。"
            else:
                # Keep CivicFix focused on actual problems, not every observation point.
                continue

            if _ticket_exists_near(cur, "toilet", problem_type, lat_f, lon_f):
                skipped_duplicate += 1
                continue

            priority = "high" if gap_score >= 80 or no_result >= 5 else ("medium" if gap_score >= 45 or total >= 6 else "low")
            evidence = {
                "source": "gap_dashboard",
                "range": range_key,
                "cluster_id": row.get("cluster_id"),
                "area_name": row.get("area_name"),
                "demand_label": row.get("demand_label"),
                "lat": lat_f,
                "lon": lon_f,
                "radius_m": row.get("radius_m"),
                "gap_score": row.get("gap_score"),
                "gap_level": row.get("gap_level"),
                "effective_queries": total,
                "unique_users": row.get("unique_users"),
                "active_days": row.get("active_days"),
                "no_result_count": no_result,
                "low_result_count": low_result,
                "slow_query_count": slow_count,
                "no_result_rate": row.get("no_result_rate"),
                "low_result_rate": row.get("low_result_rate"),
                "slow_query_rate": row.get("slow_query_rate"),
                "sample_queries": row.get("sample_queries") or [],
                "map_url": row.get("map_url"),
                "generated_from": "CivicFix from Gap Dashboard",
            }
            suggested = row.get("action_label") or row.get("suggestion") or "請管理者依缺口證據查核附近資料，必要時補點位或修正既有資料。"
            cur.execute("""
                INSERT INTO rescue_tickets (
                    ticket_code, facility_type, area_name, lat, lon, problem_type,
                    evidence_json, suspected_reason, suggested_action, priority_level,
                    status, created_at, updated_at
                ) VALUES (%s, 'toilet', %s, %s, %s, %s, %s, %s, %s, %s, 'open', NOW(), NOW())
            """, (
                _make_ticket_code(),
                row.get("demand_label") or row.get("area_name") or "Gap Dashboard 缺口",
                lat_f,
                lon_f,
                problem_type,
                json.dumps(evidence, ensure_ascii=False),
                suspected_reason,
                suggested,
                priority,
            ))
            created += 1
        conn.commit()
        return {"ok": True, "source": "gap_dashboard", "range": range_key, "scanned": scanned, "created": created, "skipped_duplicate": skipped_duplicate}
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def create_ticket_from_sync_status(stale_days=30):
    """Create a rescue ticket when official public-toilet data sync is stale.

    This turns source-sync state into a CivicFix task instead of leaving it as a hidden backend detail.
    """
    if not POSTGRES_ENABLED:
        raise RuntimeError("CivicFix sync-status ticket requires Postgres/DATABASE_URL")
    stale_days = max(1, min(int(stale_days or 30), 365))
    conn = _pg_connect()
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT finished_at, total_rows, inserted_count, updated_count, error_count, file_name
            FROM source_sync_logs
            WHERE source = 'moenv_fac_p_07' AND facility_type = 'toilet'
            ORDER BY COALESCE(finished_at, started_at) DESC
            LIMIT 1
        """)
        latest = cur.fetchone()
        if latest:
            cur.execute("""
                SELECT EXTRACT(EPOCH FROM (NOW() - COALESCE(%s, NOW()))) / 86400.0 AS days_old
            """, (latest.get("finished_at"),))
            age_row = cur.fetchone() or {}
            days_old = float(age_row.get("days_old") or 0)
        else:
            days_old = 9999

        if latest and days_old < stale_days and int(latest.get("error_count") or 0) == 0:
            return {"ok": True, "created": 0, "reason": "sync_not_stale", "days_old": round(days_old, 1)}

        cur.execute("""
            SELECT id FROM rescue_tickets
            WHERE facility_type = 'toilet'
              AND problem_type = 'outdated_official_data'
              AND status IN ('open', 'processing')
            LIMIT 1
        """)
        if cur.fetchone():
            return {"ok": True, "created": 0, "reason": "open_ticket_exists", "days_old": round(days_old, 1)}

        evidence = {
            "source": "source_sync_logs",
            "latest_sync": dict(latest) if latest else None,
            "days_old": round(days_old, 1),
            "stale_days_threshold": stale_days,
        }
        cur.execute("""
            INSERT INTO rescue_tickets (
                ticket_code, facility_type, area_name, problem_type, evidence_json,
                suspected_reason, suggested_action, priority_level, status,
                created_at, updated_at
            ) VALUES (%s, 'toilet', '環境部公廁官方資料同步', 'outdated_official_data', %s, %s, %s, 'medium', 'open', NOW(), NOW())
        """, (
            _make_ticket_code(),
            json.dumps(evidence, ensure_ascii=False, default=str),
            "官方公廁資料可能已過期或最近同步有錯誤，會影響 LINE Bot 查詢資料的新鮮度。",
            "請重新同步環境部 FAC_P_07 公廁資料；同步後檢查新增、更新與錯誤筆數。",
        ))
        conn.commit()
        return {"ok": True, "created": 1, "reason": "ticket_created", "days_old": round(days_old, 1)}
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()