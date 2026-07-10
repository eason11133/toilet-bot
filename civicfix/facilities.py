from datetime import datetime, timezone

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None


def configure_facilities(postgres_enabled, pg_connect, psycopg2_module):
    global POSTGRES_ENABLED, _pg_connect, psycopg2
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module


def get_civicfix_overview():
    if not POSTGRES_ENABLED:
        return {"postgres_enabled": False}
    conn = _pg_connect()
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT
                COUNT(*) FILTER (WHERE facility_type = 'toilet') AS toilet_total,
                COUNT(*) FILTER (WHERE facility_type = 'toilet' AND official_status = 'active') AS toilet_active,
                COUNT(*) FILTER (WHERE facility_type = 'toilet' AND official_status <> 'active') AS toilet_inactive,
                COUNT(*) FILTER (WHERE facility_type = 'toilet' AND civicfix_status <> 'active') AS toilet_flagged
            FROM facilities
        """)
        counts = dict(cur.fetchone() or {})
        cur.execute("""
            SELECT * FROM source_sync_logs
            WHERE source = 'moenv_fac_p_07' AND facility_type = 'toilet'
            ORDER BY started_at DESC
            LIMIT 1
        """)
        last_sync = dict(cur.fetchone() or {})
        cur.execute("""
            SELECT COUNT(*) AS open_tickets
            FROM rescue_tickets
            WHERE facility_type = 'toilet' AND status IN ('open', 'processing')
        """)
        open_tickets = (cur.fetchone() or {}).get("open_tickets", 0)
        cur.execute("""
            SELECT COUNT(*) AS feedbacks
            FROM toilet_feedbacks
            WHERE created_at >= NOW() - INTERVAL '90 days'
        """)
        feedbacks = (cur.fetchone() or {}).get("feedbacks", 0)
        counts.update({
            "postgres_enabled": True,
            "last_sync": last_sync,
            "open_tickets": open_tickets,
            "recent_feedbacks_90d": feedbacks,
        })
        return counts
    finally:
        conn.close()


def get_recent_sync_logs(limit=10):
    if not POSTGRES_ENABLED:
        return []
    conn = _pg_connect()
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT * FROM source_sync_logs
            ORDER BY started_at DESC
            LIMIT %s
        """, (int(limit),))
        return [dict(r) for r in (cur.fetchall() or [])]
    finally:
        conn.close()
