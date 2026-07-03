import os
import logging
import time

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None
norm_coord = None
haversine = None
_STATUS_INDEX_TTL = 180

# 近點/快取/有效期
_STATUS_NEAR_M = 35
_STATUS_TTL_HOURS = 6
_status_index_cache = {"ts": 0, "data": {}}
# _STATUS_INDEX_TTL is defined in global config section (see above)


def configure_status(postgres_enabled=False, pg_connect=None, psycopg2_module=None, norm_coord_func=None, haversine_func=None, status_index_ttl=180):
    global POSTGRES_ENABLED, _pg_connect, psycopg2, norm_coord, haversine, _STATUS_INDEX_TTL
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module
    norm_coord = norm_coord_func
    haversine = haversine_func
    _STATUS_INDEX_TTL = status_index_ttl

def submit_status_update(lat, lon, status_text, user_id="", display_name="", note=""):
    """Write toilet status reports to Neon."""
    if not POSTGRES_ENABLED:
        return False
    try:
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO toilet_status_reports (user_id, display_name, lat, lon, status, note, created_at)
            VALUES (%s, %s, %s, %s, %s, %s, NOW())
        """, (user_id or "", display_name or "", float(lat), float(lon), (status_text or "").strip(), (note or "").strip()))
        conn.commit()
        conn.close()
        _status_index_cache["ts"] = 0
        return True
    except Exception as e:
        logging.error(f"寫入 Neon 狀態失敗: {e}", exc_info=True)
        return False

def _is_close_m(lat1, lon1, lat2, lon2, th=_STATUS_NEAR_M):
    try:
        return haversine(float(lat1), float(lon1), float(lat2), float(lon2)) <= th
    except:
        return False

def build_status_index():
    """Build recent status index from Neon toilet_status_reports."""
    if not POSTGRES_ENABLED:
        return {}
    now = time.time()
    if (now - _status_index_cache["ts"] < _STATUS_INDEX_TTL) and _status_index_cache["data"]:
        return _status_index_cache["data"]
    try:
        STATUS_INDEX_MAX_KEYS = int(os.getenv("STATUS_INDEX_MAX_KEYS", "800"))
    except Exception:
        STATUS_INDEX_MAX_KEYS = 800
    out = {}
    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT lat, lon, status, created_at
            FROM toilet_status_reports
            WHERE created_at >= NOW() - (%s || ' hours')::interval
            ORDER BY created_at DESC
            LIMIT 4000
        """, (str(_STATUS_TTL_HOURS),))
        rows = cur.fetchall()
        conn.close()
        merged = []
        for r in rows:
            lat_s, lon_s = norm_coord(r.get("lat")), norm_coord(r.get("lon"))
            st = (r.get("status") or "").strip()
            ts = r.get("created_at")
            ts_s = ts.isoformat() if hasattr(ts, "isoformat") else str(ts or "")
            if not st:
                continue
            placed = False
            for m in merged:
                if _is_close_m(lat_s, lon_s, m["lat"], m["lon"]):
                    placed = True
                    break
            if not placed and len(merged) < STATUS_INDEX_MAX_KEYS:
                merged.append({"lat": lat_s, "lon": lon_s, "status": st, "ts": ts_s})
        for m in merged:
            out[(m["lat"], m["lon"])] = {"status": m["status"], "ts": m["ts"]}
        _status_index_cache.update(ts=now, data=out)
        return out
    except Exception as e:
        logging.warning(f"建立 Neon 狀態索引失敗：{e}")
        _status_index_cache.update(ts=now, data={})
        return {}

def _get_liff_status_id() -> str:
    return (
        os.getenv("LIFF_STATUS_ID")      
        or os.getenv("LIFF_ID_STATUS")
        or os.getenv("LIFF_ID")
        or ""
    ).strip()

def _read_status_rows():
    """Read status rows from Neon for achievements/badges pages."""
    if not POSTGRES_ENABLED:
        return []
    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT lat, lon, status, user_id, display_name, created_at
            FROM toilet_status_reports
            ORDER BY created_at DESC
            LIMIT 4000
        """)
        rows = cur.fetchall()
        conn.close()
        out = []
        for r in rows:
            ts = r.get("created_at")
            out.append({
                "lat": norm_coord(r.get("lat")),
                "lon": norm_coord(r.get("lon")),
                "status": r.get("status") or "",
                "user_id": r.get("user_id") or "",
                "display_name": r.get("display_name") or "",
                "timestamp": ts.isoformat() if hasattr(ts, "isoformat") else str(ts or ""),
            })
        return out
    except Exception as e:
        logging.error(f"_read_status_rows Neon error: {e}")
        return []

