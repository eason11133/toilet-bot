import os
import time
import logging
import math
import hashlib
import sqlite3
import threading
from datetime import datetime, timezone

from config import TW_TZ
from dashboard.routes import _dashboard_range_to_sqlite

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None
ANALYTICS_DB_PATH = None
get_cached_data = None
save_cache = None
get_area_name = None

def configure_gap_analysis(
    postgres_enabled,
    pg_connect,
    psycopg2_module,
    analytics_db_path,
    get_cached_data_func,
    save_cache_func,
    get_area_name_func,
):
    global POSTGRES_ENABLED, _pg_connect, psycopg2, ANALYTICS_DB_PATH
    global get_cached_data, save_cache, get_area_name
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module
    ANALYTICS_DB_PATH = analytics_db_path
    get_cached_data = get_cached_data_func
    save_cache = save_cache_func
    get_area_name = get_area_name_func

def _gap_area_name_from_event(e):
    """Return a demand-location label from coordinates.

    V4 intentionally prioritizes the actual demand location over old stored broad labels.
    Example: a point between Zhongshan and Shuanglian should be shown as 中山雙連周邊,
    not 台北車站 just because an earlier coarse bounding box wrote that label.
    """
    old = (e.get("area_name") or "").strip()
    lat = _safe_float(e.get("lat"))
    lon = _safe_float(e.get("lon"))
    if lat is not None and lon is not None:
        inferred = get_area_name(lat, lon) or "待分類區域"
        # Use finer inferred names whenever possible. Keep old names only if inference fails.
        if inferred and inferred != "待分類區域":
            return inferred
    return old or "待分類區域"
def _backfill_area_names_async(events, max_rows=1000):
    """Persist inferred area names for old analytics rows so we do not re-infer forever."""
    if not POSTGRES_ENABLED:
        return
    updates = []
    for e in events:
        try:
            old = (e.get("area_name") or "").strip()
            lat = _safe_float(e.get("lat")); lon = _safe_float(e.get("lon"))
            if lat is None or lon is None:
                continue
            inferred = get_area_name(lat, lon)
            if not inferred or inferred == old:
                continue
            # Update blank/unknown/coarse labels. This is intentionally broader than V3
            # because micro-location labels are more useful for a demand-cluster research dashboard.
            if old and not (old in ("其他區域", "待分類區域") or old.startswith("待分類") or inferred not in ("台北市", "新北市")):
                continue
            eid = e.get("id")
            if eid is None:
                continue
            updates.append((inferred, eid))
            if len(updates) >= max_rows:
                break
        except Exception:
            continue
    if not updates:
        return

    def worker(batch):
        try:
            conn = _pg_connect()
            cur = conn.cursor()
            cur.executemany(
                """
                UPDATE analytics_events
                SET area_name = %s
                WHERE id = %s
                """,
                batch
            )
            conn.commit()
            conn.close()
            logging.info(f"✅ gap area_name backfilled: {len(batch)} rows")
        except Exception as e:
            logging.warning(f"gap area_name backfill skipped: {e}")

    try:
        threading.Thread(target=worker, args=(updates,), name="gap-area-backfill", daemon=True).start()
    except Exception:
        pass
# === Demand Gap Dashboard v165：去重、需求群聚與建議設點分析 ===
_GAP_SUMMARY_CACHE = {}
# Gap summary is expensive because it scans and clusters analytics_events.
# Default to 12 hours so the research/dashboard page opens fast.
# Manual refresh still works via ?force=1 / ?refresh=1.
_GAP_SUMMARY_CACHE_TTL = int(os.getenv("GAP_SUMMARY_CACHE_TTL_SECONDS", "43200"))


def _gap_cache_get(key):
    """Read gap-summary cache.

    Uses two layers:
    1) in-memory cache for same worker speed
    2) SQLite request_cache so Gunicorn workers share the same cached result

    Manual refresh bypasses this function via ?force=1 / ?refresh=1.
    """
    try:
        item = _GAP_SUMMARY_CACHE.get(key)
        if item:
            ts, data = item
            if time.time() - ts <= _GAP_SUMMARY_CACHE_TTL:
                return data
    except Exception:
        pass

    try:
        data = get_cached_data(f"gap_summary:{key}", ttl_sec=_GAP_SUMMARY_CACHE_TTL)
        if data is not None:
            try:
                _GAP_SUMMARY_CACHE[key] = (time.time(), data)
            except Exception:
                pass
            return data
    except Exception as e:
        logging.debug(f"gap sqlite cache read skipped: {e}")

    return None
def _gap_cache_set(key, data):
    try:
        _GAP_SUMMARY_CACHE[key] = (time.time(), data)
        if len(_GAP_SUMMARY_CACHE) > 30:
            oldest = sorted(_GAP_SUMMARY_CACHE.items(), key=lambda kv: kv[1][0])[:10]
            for k, _ in oldest:
                _GAP_SUMMARY_CACHE.pop(k, None)
    except Exception:
        pass

    try:
        save_cache(f"gap_summary:{key}", data)
    except Exception as e:
        logging.debug(f"gap sqlite cache write skipped: {e}")
def _safe_float(v, default=None):
    try:
        if v is None or v == "":
            return default
        return float(v)
    except Exception:
        return default
# Gap dashboard should show all valid Taiwan demand signals, not global/outlier test coordinates.
# Bounds include Taiwan proper plus Penghu / Kinmen / Matsu. They can be overridden by env.
_GAP_VALID_LAT_MIN = float(os.getenv("GAP_VALID_LAT_MIN", "21.5"))
_GAP_VALID_LAT_MAX = float(os.getenv("GAP_VALID_LAT_MAX", "26.6"))
_GAP_VALID_LON_MIN = float(os.getenv("GAP_VALID_LON_MIN", "118.0"))
_GAP_VALID_LON_MAX = float(os.getenv("GAP_VALID_LON_MAX", "123.5"))

def _gap_coord_in_scope(lat, lon):
    lat = _safe_float(lat)
    lon = _safe_float(lon)
    if lat is None or lon is None:
        return False
    if not (math.isfinite(lat) and math.isfinite(lon)):
        return False
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        return False
    return (_GAP_VALID_LAT_MIN <= lat <= _GAP_VALID_LAT_MAX and
            _GAP_VALID_LON_MIN <= lon <= _GAP_VALID_LON_MAX)
def _gap_parse_dt(v):
    try:
        if isinstance(v, datetime):
            return v
        s = str(v or "").strip()
        if not s:
            return None
        # 支援 PostgreSQL / SQLite 常見字串
        s = s.replace("Z", "+00:00")
        return datetime.fromisoformat(s)
    except Exception:
        try:
            return datetime.strptime(str(v)[:19], "%Y-%m-%d %H:%M:%S")
        except Exception:
            return None
def _gap_day_key(v):
    dt = _gap_parse_dt(v)
    if not dt:
        return "unknown"
    try:
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        dt = dt.astimezone(TW_TZ)
    except Exception:
        pass
    return dt.strftime("%Y-%m-%d")
def _gap_minutes(v):
    dt = _gap_parse_dt(v)
    if not dt:
        return 0
    try:
        return int(dt.timestamp() // 60)
    except Exception:
        return 0
def _gap_user_key(uid):
    if uid:
        return hashlib.sha256(str(uid).encode("utf-8")).hexdigest()[:12]
    return "anon"
def _gap_cell(lat, lon, decimals=3):
    try:
        return f"{round(float(lat), decimals):.{decimals}f},{round(float(lon), decimals):.{decimals}f}"
    except Exception:
        return "unknown"
def _gap_cell_center(cell):
    try:
        a, b = str(cell).split(",", 1)
        return float(a), float(b)
    except Exception:
        return None, None
def _gap_haversine_m(lat1, lon1, lat2, lon2):
    try:
        lat1, lon1, lat2, lon2 = map(float, [lat1, lon1, lat2, lon2])
        R = 6371000.0
        p1, p2 = math.radians(lat1), math.radians(lat2)
        dp = math.radians(lat2 - lat1)
        dl = math.radians(lon2 - lon1)
        a = math.sin(dp/2)**2 + math.cos(p1)*math.cos(p2)*math.sin(dl/2)**2
        return 2 * R * math.asin(math.sqrt(a))
    except Exception:
        return 0
def _gap_google_maps_url(lat, lon):
    try:
        return f"https://www.google.com/maps/search/?api=1&query={float(lat):.6f},{float(lon):.6f}"
    except Exception:
        return ""
def _gap_level(score, unique_users=0, active_days=0):
    try:
        s = float(score or 0)
    except Exception:
        s = 0
    # v2 不只看分數，也看是否跨使用者/跨日期，避免單人連續查詢造成假熱點
    if s >= 80 and (unique_users >= 2 or active_days >= 2):
        return "高可信缺口"
    if s >= 45:
        return "中可信缺口"
    if s >= 18:
        return "低可信缺口"
    return "觀察中"
def _gap_action_label(row):
    no_result = int(row.get("no_result_count") or 0)
    low_result = int(row.get("low_result_count") or 0)
    slow = int(row.get("slow_query_count") or 0)
    total = int(row.get("effective_queries") or row.get("total_queries") or 0)
    unique_users = int(row.get("unique_users") or 0)
    active_days = int(row.get("active_days") or 0)
    no_rate = no_result / max(total, 1)
    low_rate = low_result / max(total, 1)
    slow_rate = slow / max(total, 1)

    confidence = ""
    if unique_users < 2 and active_days < 2:
        confidence = "（但目前獨立性較低，需再觀察）"

    if no_result >= 3 or (total >= 5 and no_rate >= 0.35):
        return "優先現地/地圖確認：疑似設施不足或資料未收錄" + confidence
    if low_result >= 4 or (total >= 6 and low_rate >= 0.55):
        return "優先補資料：檢查附近商場、車站、公園、學校是否漏收" + confidence
    if slow >= 4 or (total >= 6 and slow_rate >= 0.45):
        return "優先補本地資料：降低 OSM 或外部查詢依賴" + confidence
    if total >= 8 or unique_users >= 3:
        return "持續觀察：需求量足夠，可列入人工抽樣清單"
    return "先觀察：資料量仍少"
def _gap_suggestion(row):
    no_result = int(row.get("no_result_count") or 0)
    low_result = int(row.get("low_result_count") or 0)
    slow = int(row.get("slow_query_count") or 0)
    total = int(row.get("effective_queries") or row.get("total_queries") or 0)
    if no_result >= 3 or (total >= 5 and no_result / max(total, 1) >= 0.35):
        return "可能設施不足或資料缺漏，建議優先檢查"
    if low_result >= 4 or (total >= 6 and low_result / max(total, 1) >= 0.50):
        return "候選結果偏少，可能需要補資料或擴充設施"
    if slow >= 4:
        return "查詢耗時偏高，可能依賴外部資料或資料分布不足"
    if total >= 8:
        return "需求量較高，可列為持續觀察區域"
    return "資料量較少，先觀察"
def _gap_sample_event(e):
    lat = _safe_float(e.get("lat"))
    lon = _safe_float(e.get("lon"))
    if lat is None or lon is None:
        return None
    return {
        "created_at": str(e.get("created_at") or ""),
        "lat": round(lat, 6),
        "lon": round(lon, 6),
        "result_count": int(e.get("result_count") or 0),
        "success": int(e.get("success") or 0),
        "response_time_ms": int(e.get("response_time_ms") or 0),
        "area_name": (e.get("area_name") or "其他區域"),
        "map_url": _gap_google_maps_url(lat, lon)
    }
def _gap_add_metrics(obj, event, low_threshold, slow_ms):
    rc = int(event.get("result_count") or 0)
    rt = int(event.get("response_time_ms") or 0)
    success = int(event.get("success") or 0) == 1
    obj["effective_queries"] = obj.get("effective_queries", 0) + 1
    obj["total_queries"] = obj.get("total_queries", 0) + 1  # 相容前端舊欄位
    obj["no_result_count"] = obj.get("no_result_count", 0) + (1 if rc == 0 else 0)
    obj["low_result_count"] = obj.get("low_result_count", 0) + (1 if rc <= low_threshold else 0)
    obj["slow_query_count"] = obj.get("slow_query_count", 0) + (1 if rt >= slow_ms else 0)
    obj["success_count"] = obj.get("success_count", 0) + (1 if success else 0)
    if rt > 0:
        obj.setdefault("response_values", []).append(rt)
    obj.setdefault("user_set", set()).add(event.get("user_key") or "anon")
    obj.setdefault("day_set", set()).add(event.get("day_key") or "unknown")
    obj["raw_queries"] = obj.get("raw_queries", 0) + int(event.get("raw_weight") or 1)
def _gap_finish_row(r):
    vals = r.pop("response_values", [])
    user_set = r.pop("user_set", set())
    day_set = r.pop("day_set", set())
    total = int(r.get("effective_queries") or r.get("total_queries") or 0)
    avg_rt = round(sum(vals) / len(vals)) if vals else 0
    r["avg_response_ms"] = avg_rt
    r["unique_users"] = len(user_set) if isinstance(user_set, set) else int(r.get("unique_users") or 0)
    r["active_days"] = len(day_set) if isinstance(day_set, set) else int(r.get("active_days") or 0)
    r["no_result_rate"] = round((int(r.get("no_result_count") or 0) / max(total, 1)) * 100, 1)
    r["low_result_rate"] = round((int(r.get("low_result_count") or 0) / max(total, 1)) * 100, 1)
    r["slow_query_rate"] = round((int(r.get("slow_query_count") or 0) / max(total, 1)) * 100, 1)

    # Demand Gap Score v2：加入去重後有效需求、獨立使用者與跨日期，降低單人連續查詢灌分
    score = (
        int(r.get("no_result_count") or 0) * 5
        + int(r.get("low_result_count") or 0) * 2
        + int(r.get("slow_query_count") or 0) * 1
        + int(r.get("effective_queries") or 0) * 1
        + int(r.get("unique_users") or 0) * 3
        + int(r.get("active_days") or 0) * 2
    )
    # 若幾乎只有單一使用者同一天，分數打折，但不完全刪除，避免早期資料看不到訊號
    if int(r.get("unique_users") or 0) <= 1 and int(r.get("active_days") or 0) <= 1:
        score *= 0.65
        r["confidence_note"] = "單一使用者/單日訊號，需再觀察"
    elif int(r.get("unique_users") or 0) <= 1:
        score *= 0.80
        r["confidence_note"] = "使用者數偏少，需搭配現地確認"
    else:
        r["confidence_note"] = "可信度較高"

    r["gap_score"] = round(score, 2)
    r["gap_level"] = _gap_level(score, int(r.get("unique_users") or 0), int(r.get("active_days") or 0))
    r["suggestion"] = _gap_suggestion(r)
    r["action_label"] = _gap_action_label(r)
    if r.get("lat") is not None and r.get("lon") is not None:
        r["map_url"] = _gap_google_maps_url(r.get("lat"), r.get("lon"))
    return r
def _gap_cluster_rows(rows, radius_m=500):
    """把相近缺口格點合併為需求群，輸出建議中心點。"""
    candidates = []
    for r in rows:
        lat = _safe_float(r.get("lat"))
        lon = _safe_float(r.get("lon"))
        if lat is None or lon is None or not _gap_coord_in_scope(lat, lon):
            continue
        # 只把真的有缺口訊號的點拿去群聚
        if int(r.get("no_result_count") or 0) <= 0 and int(r.get("low_result_count") or 0) <= 0 and int(r.get("slow_query_count") or 0) <= 0:
            continue
        candidates.append(dict(r))

    candidates.sort(key=lambda x: (float(x.get("gap_score") or 0), int(x.get("effective_queries") or 0)), reverse=True)
    used = set()
    clusters = []

    for i, seed in enumerate(candidates):
        if i in used:
            continue
        members = []
        seed_lat, seed_lon = float(seed["lat"]), float(seed["lon"])
        for j, r in enumerate(candidates):
            if j in used:
                continue
            d = _gap_haversine_m(seed_lat, seed_lon, r.get("lat"), r.get("lon"))
            if d <= radius_m:
                used.add(j)
                rr = dict(r)
                rr["distance_to_seed_m"] = round(d, 1)
                members.append(rr)

        if not members:
            continue
        weight_sum = 0.0
        lat_sum = 0.0
        lon_sum = 0.0
        for m in members:
            w = max(float(m.get("gap_score") or 0), 1.0)
            weight_sum += w
            lat_sum += float(m.get("lat") or 0) * w
            lon_sum += float(m.get("lon") or 0) * w
        center_lat = lat_sum / max(weight_sum, 1)
        center_lon = lon_sum / max(weight_sum, 1)
        radius = max([_gap_haversine_m(center_lat, center_lon, m.get("lat"), m.get("lon")) for m in members] or [0])

        area_counts = {}
        for m in members:
            area = m.get("area_name") or "其他區域"
            area_counts[area] = area_counts.get(area, 0) + int(m.get("effective_queries") or 1)
        area_name = get_area_name(center_lat, center_lon) or (sorted(area_counts.items(), key=lambda kv: kv[1], reverse=True)[0][0] if area_counts else "待分類區域")
        display_radius = max(120, int(round(radius)))
        demand_label = f"{area_name}附近約 {display_radius}m 需求圈"

        agg = {
            "cluster_id": f"C{len(clusters)+1}",
            "center": f"{center_lat:.5f},{center_lon:.5f}",
            "lat": round(center_lat, 6),
            "lon": round(center_lon, 6),
            "area_name": area_name,
            "demand_label": demand_label,
            "radius_label": f"約 {display_radius} 公尺",
            "point_count": len(members),
            "radius_m": display_radius,
            "effective_queries": sum(int(m.get("effective_queries") or 0) for m in members),
            "total_queries": sum(int(m.get("effective_queries") or 0) for m in members),
            "raw_queries": sum(int(m.get("raw_queries") or 0) for m in members),
            "no_result_count": sum(int(m.get("no_result_count") or 0) for m in members),
            "low_result_count": sum(int(m.get("low_result_count") or 0) for m in members),
            "slow_query_count": sum(int(m.get("slow_query_count") or 0) for m in members),
            "unique_users": sum(int(m.get("unique_users") or 0) for m in members),
            "active_days": len(set([str(m.get("day_hint") or "") for m in members if m.get("day_hint")])) or max([int(m.get("active_days") or 0) for m in members] or [0]),
            "member_grids": [m.get("grid") for m in members[:8]],
            "sample_queries": sum([m.get("sample_queries") or [] for m in members], [])[:6],
            "map_url": _gap_google_maps_url(center_lat, center_lon),
        }
        agg = _gap_finish_row({**agg, "response_values": sum([m.get("response_values_raw") or [] for m in members], []), "user_set": set(), "day_set": set()})
        # _gap_finish_row 會以空 set 覆蓋 unique_users；補回聚合值並重算關鍵欄位
        agg["unique_users"] = max(sum(int(m.get("unique_users") or 0) for m in members), 0)
        agg["active_days"] = max([int(m.get("active_days") or 0) for m in members] or [0])
        agg["gap_score"] = round(sum(float(m.get("gap_score") or 0) for m in members) + agg["point_count"] * 3, 2)
        agg["gap_level"] = _gap_level(agg["gap_score"], agg["unique_users"], agg["active_days"])
        agg["suggestion"] = _gap_suggestion(agg)
        agg["action_label"] = _gap_action_label(agg)
        if agg["unique_users"] < 2 and agg["active_days"] < 2:
            agg["confidence_note"] = "可能受單人重複查詢影響，展示前建議人工確認"
        else:
            agg["confidence_note"] = "已合併附近點位，較適合做公共設施檢查"
        agg["priority_reason"] = (
            f"半徑{agg.get('radius_label','約數百公尺')}內累積 {agg.get('effective_queries',0)} 筆有效需求，"
            f"其中查無 {agg.get('no_result_count',0)} 次、低覆蓋 {agg.get('low_result_count',0)} 次、慢查詢 {agg.get('slow_query_count',0)} 次。"
        )
        clusters.append(agg)

    clusters.sort(key=lambda x: (float(x.get("gap_score") or 0), int(x.get("effective_queries") or 0)), reverse=True)
    return clusters
def _build_gap_summary(range_key="all", anchor_date=None):
    if range_key not in ("all", "1h", "1d", "7d", "30d", "1y"):
        range_key = "all"

    start, end, _, _ = _dashboard_range_to_sqlite(range_key, anchor_date)

    events = []
    osm_summary = {
        "total_source_calls": 0,
        "osm_calls": 0,
        "osm_success_calls": 0,
        "avg_osm_elapsed_ms": 0,
        "avg_non_osm_elapsed_ms": 0,
        "max_osm_elapsed_ms": 0,
        "osm_reasons": []
    }

    if POSTGRES_ENABLED:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT id, user_id, event_type, result_count, success, response_time_ms,
                   lat, lon, area_name, query_text, created_at
            FROM analytics_events
            WHERE created_at >= %s AND created_at <= %s
              AND event_type = 'location_query'
              AND COALESCE(response_time_ms, 0) > 0
            ORDER BY created_at ASC
        """, (start, end))
        events = [dict(r) for r in cur.fetchall()]

        try:
            cur.execute("""
                SELECT
                  COUNT(*) AS total_source_calls,
                  COUNT(*) FILTER (WHERE used_osm = TRUE OR source_name = 'osm') AS osm_calls,
                  COUNT(*) FILTER (WHERE (used_osm = TRUE OR source_name = 'osm') AND success = TRUE) AS osm_success_calls,
                  AVG(elapsed_ms) FILTER (WHERE used_osm = TRUE OR source_name = 'osm') AS avg_osm_elapsed_ms,
                  AVG(elapsed_ms) FILTER (WHERE NOT (used_osm = TRUE OR source_name = 'osm')) AS avg_non_osm_elapsed_ms,
                  MAX(elapsed_ms) FILTER (WHERE used_osm = TRUE OR source_name = 'osm') AS max_osm_elapsed_ms
                FROM source_query_logs
                WHERE created_at >= %s AND created_at <= %s
            """, (start, end))
            r = dict(cur.fetchone() or {})
            osm_summary.update({
                "total_source_calls": int(r.get("total_source_calls") or 0),
                "osm_calls": int(r.get("osm_calls") or 0),
                "osm_success_calls": int(r.get("osm_success_calls") or 0),
                "avg_osm_elapsed_ms": round(float(r.get("avg_osm_elapsed_ms") or 0), 2),
                "avg_non_osm_elapsed_ms": round(float(r.get("avg_non_osm_elapsed_ms") or 0), 2),
                "max_osm_elapsed_ms": int(r.get("max_osm_elapsed_ms") or 0),
            })
            cur.execute("""
                SELECT COALESCE(reason, 'unknown') AS reason, COUNT(*) AS count
                FROM source_query_logs
                WHERE created_at >= %s AND created_at <= %s
                  AND (used_osm = TRUE OR source_name = 'osm')
                GROUP BY COALESCE(reason, 'unknown')
                ORDER BY count DESC
                LIMIT 8
            """, (start, end))
            osm_summary["osm_reasons"] = [dict(x) for x in cur.fetchall()]
        except Exception as e:
            logging.warning(f"gap osm summary skipped: {e}")

        conn.close()
    else:
        conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        cur = conn.cursor()
        cur.execute("""
            SELECT id, user_id, event_type, result_count, success, response_time_ms,
                   lat, lon, area_name, query_text, created_at
            FROM analytics_events
            WHERE created_at >= ? AND created_at <= ?
              AND event_type = 'location_query'
              AND COALESCE(response_time_ms, 0) > 0
            ORDER BY created_at ASC
        """, (start.isoformat(), end.isoformat()))
        events = [dict(r) for r in cur.fetchall()]
        conn.close()

    # Keep all valid demand points, but exclude out-of-scope/global/test coordinates so the map
    # does not zoom out to the whole world. This dashboard is for Taiwan public facility research.
    raw_total_queries_before_scope = len(events)
    scoped_events = []
    excluded_coord_count = 0
    for e in events:
        if _gap_coord_in_scope(e.get("lat"), e.get("lon")):
            scoped_events.append(e)
        else:
            excluded_coord_count += 1
    events = scoped_events

    _backfill_area_names_async(events)

    raw_total_queries = len(events)
    LOW_RESULT_THRESHOLD = int(os.getenv("GAP_LOW_RESULT_THRESHOLD", "2"))
    SLOW_QUERY_MS = int(os.getenv("GAP_SLOW_QUERY_MS", "5000"))
    DEDUPE_MINUTES = int(os.getenv("GAP_DEDUPE_MINUTES", "10"))
    CLUSTER_RADIUS_M = int(os.getenv("GAP_CLUSTER_RADIUS_M", "500"))

    # 1) 同人同地短時間去重：同 user、同約 100m 格點、10 分鐘內，只算一筆有效需求
    deduped = []
    last_seen = {}
    duplicate_skipped = 0
    for e in events:
        lat = _safe_float(e.get("lat"))
        lon = _safe_float(e.get("lon"))
        if lat is None or lon is None:
            continue
        user_key = _gap_user_key(e.get("user_id"))
        cell_key = _gap_cell(lat, lon, 3)
        minute = _gap_minutes(e.get("created_at"))
        # 沒 user_id 時，用較短時間窗，避免把不同使用者誤合併
        identity = user_key if user_key != "anon" else f"anon:{cell_key}"
        dedupe_key = (identity, cell_key)
        last_min = last_seen.get(dedupe_key)
        window = DEDUPE_MINUTES if user_key != "anon" else min(3, DEDUPE_MINUTES)
        if last_min is not None and minute and (minute - last_min) <= window:
            duplicate_skipped += 1
            continue
        last_seen[dedupe_key] = minute
        ee = dict(e)
        ee["user_key"] = user_key
        ee["cell_key"] = cell_key
        ee["day_key"] = _gap_day_key(e.get("created_at"))
        ee["raw_weight"] = 1
        deduped.append(ee)

    total_queries = len(deduped)
    no_result_count = 0
    low_result_count = 0
    slow_query_count = 0
    success_count = 0
    response_values = []
    area_map = {}
    grid_map = {}
    all_users = set()
    all_days = set()

    for e in deduped:
        rc = int(e.get("result_count") or 0)
        rt = int(e.get("response_time_ms") or 0)
        success = int(e.get("success") or 0) == 1
        area = _gap_area_name_from_event(e)
        all_users.add(e.get("user_key") or "anon")
        all_days.add(e.get("day_key") or "unknown")

        if success:
            success_count += 1
        if rc == 0:
            no_result_count += 1
        if rc <= LOW_RESULT_THRESHOLD:
            low_result_count += 1
        if rt >= SLOW_QUERY_MS:
            slow_query_count += 1
        if rt > 0:
            response_values.append(rt)

        if area not in area_map:
            area_map[area] = {
                "area_name": area,
                "effective_queries": 0,
                "total_queries": 0,
                "raw_queries": 0,
                "no_result_count": 0,
                "low_result_count": 0,
                "slow_query_count": 0,
                "success_count": 0,
                "response_values": [],
                "user_set": set(),
                "day_set": set(),
            }
        _gap_add_metrics(area_map[area], e, LOW_RESULT_THRESHOLD, SLOW_QUERY_MS)

        lat = _safe_float(e.get("lat"))
        lon = _safe_float(e.get("lon"))
        if lat is not None and lon is not None:
            # 100m 級別格點：先精準聚合，再由 cluster 合成約 500m 建議設點區
            glat = round(lat, 3)
            glon = round(lon, 3)
            gkey = f"{glat:.3f},{glon:.3f}"
            if gkey not in grid_map:
                grid_map[gkey] = {
                    "grid": gkey,
                    "lat": glat,
                    "lon": glon,
                    "area_name": area,
                    "effective_queries": 0,
                    "total_queries": 0,
                    "raw_queries": 0,
                    "no_result_count": 0,
                    "low_result_count": 0,
                    "slow_query_count": 0,
                    "success_count": 0,
                    "response_values": [],
                    "response_values_raw": [],
                    "user_set": set(),
                    "day_set": set(),
                    "day_hint": e.get("day_key"),
                    "sample_queries": [],
                    "map_url": _gap_google_maps_url(glat, glon),
                }
            g = grid_map[gkey]
            _gap_add_metrics(g, e, LOW_RESULT_THRESHOLD, SLOW_QUERY_MS)
            if rt > 0:
                g.setdefault("response_values_raw", []).append(rt)
            sample = _gap_sample_event(e)
            if sample and (rc == 0 or rc <= LOW_RESULT_THRESHOLD or rt >= SLOW_QUERY_MS):
                if len(g.get("sample_queries") or []) < 5:
                    g["sample_queries"].append(sample)

    area_rows = [_gap_finish_row(dict(v)) for v in area_map.values()]
    area_rows.sort(key=lambda x: (x["gap_score"], x["effective_queries"]), reverse=True)

    hotspot_rows = [_gap_finish_row(dict(v)) for v in grid_map.values()]
    hotspot_rows.sort(key=lambda x: (x["gap_score"], x["effective_queries"]), reverse=True)

    clusters = _gap_cluster_rows(hotspot_rows, radius_m=CLUSTER_RADIUS_M)

    avg_response = round(sum(response_values) / len(response_values)) if response_values else 0
    top_area = area_rows[0]["area_name"] if area_rows else "-"
    top_cluster = clusters[0]["center"] if clusters else "-"
    classified_queries = sum(int(r.get("effective_queries") or 0) for r in area_rows if not str(r.get("area_name") or "").startswith("待分類") and r.get("area_name") != "其他區域")
    pending_queries = max(total_queries - classified_queries, 0)
    area_classification_rate = round((classified_queries / max(total_queries, 1)) * 100, 1)

    # Dashboard/export output limits.
    # Default is now unlimited for demand circles and hotspots because this page is
    # used for research/export. Top recommended sites remain limited to keep the
    # numbered candidate pins readable.
    # You can still cap rows by setting these env vars to a positive integer.
    # Values: 0 / all / none / empty = unlimited.
    def _gap_output_limit(name, default="0"):
        raw = str(os.getenv(name, default) or "").strip().lower()
        if raw in ("", "0", "all", "none", "unlimited"):
            return 0
        try:
            return max(0, int(raw))
        except Exception:
            return 0

    def _gap_take(rows, limit):
        return rows if not limit else rows[:limit]

    GAP_CLUSTER_OUTPUT_LIMIT = _gap_output_limit("GAP_CLUSTER_OUTPUT_LIMIT", "0")
    GAP_HOTSPOT_OUTPUT_LIMIT = _gap_output_limit("GAP_HOTSPOT_OUTPUT_LIMIT", "0")
    GAP_PRECISE_HOTSPOT_LIMIT = _gap_output_limit("GAP_PRECISE_HOTSPOT_LIMIT", "0")
    GAP_RECOMMENDED_LIMIT = _gap_output_limit("GAP_RECOMMENDED_LIMIT", "10") or 10

    return {
        "ok": True,
        "version": "demand_gap_v7_taiwan_valid_unlimited_points",
        "range": range_key,
        "anchor_date": anchor_date,
        "generated_at": datetime.now(TW_TZ).isoformat(),
        "thresholds": {
            "low_result_threshold": LOW_RESULT_THRESHOLD,
            "slow_query_ms": SLOW_QUERY_MS,
            "dedupe_minutes": DEDUPE_MINUTES,
            "cluster_radius_m": CLUSTER_RADIUS_M,
            "cache_ttl_seconds": _GAP_SUMMARY_CACHE_TTL,
        },
        "summary": {
            "raw_total_queries": raw_total_queries,
            "duplicate_skipped": duplicate_skipped,
            "total_queries": total_queries,
            "effective_queries": total_queries,
            "unique_users": len(all_users),
            "active_days": len(all_days),
            "success_count": success_count,
            "no_result_count": no_result_count,
            "low_result_count": low_result_count,
            "slow_query_count": slow_query_count,
            "avg_response_ms": avg_response,
            "top_gap_area": top_area,
            "top_gap_cluster": top_cluster,
            "cluster_count": len(clusters),
            "no_result_rate": round((no_result_count / max(total_queries, 1)) * 100, 1),
            "low_result_rate": round((low_result_count / max(total_queries, 1)) * 100, 1),
            "slow_query_rate": round((slow_query_count / max(total_queries, 1)) * 100, 1),
        },
        "data_quality": {
            "area_classification_rate": area_classification_rate,
            "classified_queries": classified_queries,
            "pending_area_queries": pending_queries,
            "pending_area_rate": round((pending_queries / max(total_queries, 1)) * 100, 1),
            "area_label_method": "local_bbox_with_grid_fallback",
            "coordinate_scope": "Taiwan + offshore islands",
            "raw_total_queries_before_scope_filter": raw_total_queries_before_scope,
            "excluded_out_of_scope_queries": excluded_coord_count,
        },
        "demand_clusters": _gap_take(clusters, GAP_CLUSTER_OUTPUT_LIMIT),
        "recommended_sites": clusters[:GAP_RECOMMENDED_LIMIT],
        "area_gaps": area_rows,
        "hotspots": _gap_take(hotspot_rows, GAP_HOTSPOT_OUTPUT_LIMIT),
        "precise_hotspots": _gap_take(hotspot_rows, GAP_PRECISE_HOTSPOT_LIMIT),
        "osm_summary": osm_summary,
        "interpretation": [
            "v2 先去除同一使用者、同一地點、短時間內的重複查詢，避免單人連續查詢把缺口分數灌高。",
            "v2 會把附近約 500 公尺內的缺口點合併成需求群，產生建議中心點，比單一查詢點更適合用來討論補資料或新增設施。",
            "建議設點不是直接代表一定要新建廁所，而是代表該區值得先做地圖/現地檢查：可能是資料漏收、室內場域資訊不足，或真的設施覆蓋不足。",
            "若同一需求群有多名獨立使用者、跨多天查詢、查無/低覆蓋比例高，可信度會比單人單日查詢更高。",
            "OSM fallback 或慢查詢高的區域，通常優先做本地資料補強，降低外部 API 延遲。"
        ]
    }
