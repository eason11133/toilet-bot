import os
import logging
import sqlite3
import requests
from datetime import datetime, timezone, timedelta

from flask import request, jsonify, render_template

from config import TW_TZ

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None
ANALYTICS_DB_PATH = None
_get_db = None
mask_user_id = None
_maintenance_auth_ok = None
CHANNEL_ACCESS_TOKEN = None
get_cached_data = None
save_cache = None

def configure_dashboard(
    postgres_enabled,
    pg_connect,
    psycopg2_module,
    analytics_db_path,
    _get_db_func=None,
    mask_user_id_func=None,
    maintenance_auth_ok_func=None,
    channel_access_token=None,
    get_cached_data_func=None,
    save_cache_func=None,
):
    global POSTGRES_ENABLED, _pg_connect, psycopg2, ANALYTICS_DB_PATH
    global _get_db, mask_user_id, _maintenance_auth_ok, CHANNEL_ACCESS_TOKEN, get_cached_data, save_cache
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module
    ANALYTICS_DB_PATH = analytics_db_path
    if _get_db_func is not None:
        _get_db = _get_db_func
    if mask_user_id_func is not None:
        mask_user_id = mask_user_id_func
    if maintenance_auth_ok_func is not None:
        _maintenance_auth_ok = maintenance_auth_ok_func
    if channel_access_token is not None:
        CHANNEL_ACCESS_TOKEN = channel_access_token
    if get_cached_data_func is not None:
        get_cached_data = get_cached_data_func
    if save_cache_func is not None:
        save_cache = save_cache_func

# === Dashboard ===
_DASHBOARD_RANGE_SECONDS = {
    "1h": 3600,
    "1d": 86400,
    "7d": 7 * 86400,
    "30d": 30 * 86400,
    "1y": 365 * 86400,
    # Gap dashboard can use all historical records instead of a time-window view.
    "all": None,
}
def _dashboard_range_to_sqlite(range_key: str, anchor_date: str = None):
    if anchor_date:
        try:
            base = datetime.strptime(anchor_date, "%Y-%m-%d").replace(tzinfo=TW_TZ)
        except Exception:
            base = datetime.now(TW_TZ)
    else:
        base = datetime.now(TW_TZ)

    now = datetime.now(TW_TZ)

    if range_key == "all":
        # Use all known analytics data. Keep a finite lower bound so the existing
        # SQL shape can stay simple across both Postgres and SQLite paths.
        start = datetime(2000, 1, 1, tzinfo=TW_TZ)
        end = now
        bucket = "month"
        labels = []

    elif range_key == "1h":
        # 1h 維持即時最近一小時
        end = now
        start = end - timedelta(hours=1)
        bucket = "5min"
        labels = [f"{i * 5}分" for i in range(12)]

    elif range_key == "1d":
        # 1d = 指定那一天 00:00 ~ 23:59:59
        start = base.replace(hour=0, minute=0, second=0, microsecond=0)
        end = start + timedelta(days=1)
        bucket = "hour"
        labels = [f"{str(i).zfill(2)}:00" for i in range(24)]

    elif range_key == "7d":
        # 以 anchor_date 為結尾日
        end = base.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=1)
        start = end - timedelta(days=7)
        bucket = "day"
        labels = [(start + timedelta(days=i)).strftime("%m/%d") for i in range(7)]

    elif range_key == "30d":
        end = base.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=1)
        start = end - timedelta(days=30)
        bucket = "day"
        labels = [(start + timedelta(days=i)).strftime("%m/%d") for i in range(30)]

    else:  # 1y
        end = base.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=1)
        start = end - timedelta(days=365)
        bucket = "month"
        labels = []
        cur = start.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
        while cur < end:
            labels.append(cur.strftime("%Y-%m"))
            if cur.month == 12:
                cur = cur.replace(year=cur.year + 1, month=1)
            else:
                cur = cur.replace(month=cur.month + 1)

    return start, end, bucket, labels
def _bucket_label(dt_obj, range_key):
    if dt_obj.tzinfo is None:
        dt_obj = dt_obj.replace(tzinfo=TW_TZ)
    else:
        dt_obj = dt_obj.astimezone(TW_TZ)

    if range_key == "1h":
        return f"{(dt_obj.minute // 5) * 5}分"
    elif range_key == "1d":
        return f"{dt_obj.hour:02d}:00"
    elif range_key in ("7d", "30d"):
        return dt_obj.strftime("%m/%d")
    elif range_key == "1y":
        return dt_obj.strftime("%Y-%m")
    return None
def _generate_dashboard_data(range_key="1h", anchor_date=None):
    start, end, bucket, default_labels = _dashboard_range_to_sqlite(range_key, anchor_date)

    if POSTGRES_ENABLED:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT
                id,
                user_id,
                event_type,
                result_count,
                success,
                response_time_ms,
                lat,
                lon,
                area_name,
                query_text,
                created_at
            FROM analytics_events
            WHERE created_at >= %s AND created_at <= %s
            ORDER BY created_at DESC
        """, (start, end))
        rows = cur.fetchall()
        conn.close()

        events = [dict(r) for r in rows]
        for e in events:
            if isinstance(e.get("created_at"), datetime):
                dt = e["created_at"]
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=TW_TZ)
                dt = dt.astimezone(TW_TZ)
                e["created_at"] = dt.isoformat()
    else:
        conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        cur = conn.cursor()
        cur.execute("""
            SELECT *
            FROM analytics_events
            WHERE created_at >= ? AND created_at <= ?
            ORDER BY created_at DESC
        """, (start.isoformat(), end.isoformat()))
        rows = cur.fetchall()
        conn.close()

        events = [dict(r) for r in rows]

    valid_query_events = [
        e for e in events
        if e["event_type"] == "location_query" and int(e.get("response_time_ms") or 0) > 0
    ]

    total_queries = len(valid_query_events)
    user_ids = [e["user_id"] for e in valid_query_events if e["user_id"]]
    active_users = len(set(user_ids))

    success_events = valid_query_events
    success_count = len([e for e in success_events if int(e.get("success") or 0) == 1])
    success_rate = round((success_count / len(success_events)) * 100, 1) if success_events else 0.0

    response_values = [int(e["response_time_ms"]) for e in valid_query_events if e.get("response_time_ms") is not None]

    instant_responses = [t for t in response_values if t < 50]
    valid_responses = [t for t in response_values if t >= 50]

    avg_response = round(sum(valid_responses) / len(valid_responses)) if valid_responses else 0

    no_result_count = len([e for e in success_events if int(e.get("result_count") or 0) == 0])
    error_count = len([e for e in events if e["event_type"] == "error" or int(e.get("success") or 0) == 0])

    new_users = 0
    returning_users = 0

    if POSTGRES_ENABLED:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        for uid in set(user_ids):
            cur.execute("""
                SELECT MIN(created_at) AS first_seen, COUNT(*) AS cnt
                FROM analytics_events
                WHERE user_id = %s
            """, (uid,))
            r = cur.fetchone()
            if not r:
                continue
            first_seen = r.get("first_seen")
            cnt = r.get("cnt") or 0
            if first_seen:
                if isinstance(first_seen, str):
                    first_seen = datetime.fromisoformat(first_seen.replace("Z", "+00:00"))
                if first_seen.tzinfo is None:
                    first_seen = first_seen.replace(tzinfo=TW_TZ)

                if first_seen >= start:
                    new_users += 1
            if cnt >= 2:
                returning_users += 1
        conn.close()
    else:
        conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        cur = conn.cursor()
        for uid in set(user_ids):
            cur.execute("""
                SELECT MIN(created_at) AS first_seen, COUNT(*) AS cnt
                FROM analytics_events
                WHERE user_id = ?
            """, (uid,))
            r = cur.fetchone()
            if not r:
                continue
            first_seen = r["first_seen"]
            cnt = r["cnt"] or 0
            if first_seen and first_seen >= start.isoformat():
                new_users += 1
            if cnt >= 2:
                returning_users += 1
        conn.close()

    retention_rate = round((returning_users / active_users) * 100, 1) if active_users else 0.0

    trend_map_queries = {label: 0 for label in default_labels}
    trend_map_users = {label: set() for label in default_labels}

    for e in events:
        try:
            raw_time = e.get("created_at") or e.get("time")
            if not raw_time:
                continue

            dt_obj = datetime.fromisoformat(str(raw_time).replace("Z", "+00:00"))
            if dt_obj.tzinfo is None:
                dt_obj = dt_obj.replace(tzinfo=TW_TZ)
            else:
                dt_obj = dt_obj.astimezone(TW_TZ)

            label = _bucket_label(dt_obj, range_key)
            if label not in trend_map_queries:
                continue

            if e.get("event_type") == "location_query" and int(e.get("response_time_ms") or 0) > 0:
                trend_map_queries[label] += 1

            uid = (e.get("user_id") or "").strip()
            if uid:
                trend_map_users[label].add(uid)

        except Exception:
            continue

    trend_queries = [trend_map_queries[label] for label in default_labels]
    trend_users = [len(trend_map_users[label]) for label in default_labels]

    hourly_map = {f"{i:02d}:00": 0 for i in range(24)}
    for e in events:
        try:
            raw_time = e.get("created_at") or e.get("time")
            if not raw_time:
                continue

            dt_obj = datetime.fromisoformat(str(raw_time).replace("Z", "+00:00"))
            if dt_obj.tzinfo is None:
                dt_obj = dt_obj.replace(tzinfo=TW_TZ)
            else:
                dt_obj = dt_obj.astimezone(TW_TZ)

            hourly_key = f"{dt_obj.hour:02d}:00"
            if hourly_key in hourly_map:
                hourly_map[hourly_key] += 1
        except Exception:
            continue

    type_counts = {
        "定位查詢": len([e for e in events if e["event_type"] == "location_query" and int(e.get("response_time_ms") or 0) > 0]),
        "文字查詢": len([e for e in events if e["event_type"] == "text_query"]),
        "點擊結果": len([e for e in events if e["event_type"] == "search_result"]),
        "錯誤": len([e for e in events if e["event_type"] == "error"]),
    }

    area_counter = {}
    for e in events:
        area = e.get("area_name") or "其他區域"
        area_counter[area] = area_counter.get(area, 0) + 1
    areas = sorted(area_counter.items(), key=lambda x: x[1], reverse=True)[:8]

    event_rows = []
    visible_events = [
        e for e in events
        if not (e.get("event_type") == "location_query" and int(e.get("response_time_ms") or 0) <= 0)
    ]
    for e in visible_events[:10]:
        event_rows.append({
            "time": e.get("created_at", ""),
            "user_id": e.get("user_id", "") or "-",
            "event_type": e.get("event_type", ""),
            "result_count": e.get("result_count", 0) or 0,
            "response_time_ms": e.get("response_time_ms", 0) or 0,
            "success": bool(int(e.get("success") or 0))
        })

    response_sorted = sorted(valid_responses)
    median_value = response_sorted[len(response_sorted)//2] if response_sorted else 0
    p95_index = min(len(response_sorted)-1, int(len(response_sorted)*0.95)) if response_sorted else 0
    p95_value = response_sorted[p95_index] if response_sorted else 0

    return {
        "summary": {
            "total_queries": total_queries,
            "active_users": active_users,
            "success_rate": success_rate,
            "avg_response": avg_response,
            "no_result_count": no_result_count,
            "error_count": error_count,
            "retention_rate": retention_rate,
            "instant_responses": len(instant_responses)
        },
        "trend": {
            "labels": default_labels,
            "queries": trend_queries,
            "users": trend_users
        },
        "hourly": {
            "labels": list(hourly_map.keys()),
            "values": list(hourly_map.values())
        },
        "typeData": {
            "labels": list(type_counts.keys()),
            "values": list(type_counts.values())
        },
        "areas": areas,
        "events": event_rows,
        "detail": {
            "totalQueries": {
                "peak": max(trend_queries) if trend_queries else 0,
                "low": min(trend_queries) if trend_queries else 0,
                "avgPerPoint": round(total_queries / len(default_labels)) if default_labels else 0,
                "topTimePoints": sorted(
                    [{"label": default_labels[i], "value": trend_queries[i]} for i in range(len(default_labels))],
                    key=lambda x: x["value"],
                    reverse=True
                )[:5]
            },
            "activeUsers": {
                "inactiveUsersEstimate": max(0, total_queries - active_users),
                "avgQueriesPerUser": f"{(total_queries / active_users):.2f}" if active_users else "0.00",
                "topUserSamples": []
            },
            "successRate": {
                "successCount": success_count,
                "failedCount": max(0, len(success_events) - success_count),
                "successRate": success_rate
            },
            "avgResponse": {
                "min": min(response_values) if response_values else 0,
                "median": median_value,
                "p95": p95_value,
                "max": max(response_values) if response_values else 0
            },
            "newUsers": {
                "newUsers": new_users,
                "existingUsers": max(0, active_users - new_users),
                "newUserRate": f"{(new_users / active_users * 100):.1f}" if active_users else "0.0"
            },
            "retentionRate": {
                "returningUsers": returning_users,
                "oneTimeUsers": max(0, active_users - returning_users),
                "retentionRate": retention_rate
            },
            "noResultCount": {
                "noResultCount": no_result_count,
                "noResultRate": f"{(no_result_count / total_queries * 100):.1f}" if total_queries else "0.0",
                "samples": []
            },
            "errorCount": {
                "errorCount": error_count,
                "errorRate": f"{(error_count / total_queries * 100):.1f}" if total_queries else "0.0",
                "samples": []
            }
        }
    }


# === Dashboard route registration ===
def dashboard_page():
    return render_template("dashboard.html")


def api_dashboard():
    range_key = (request.args.get("range") or "1h").strip()
    if range_key not in ("1h", "1d", "7d", "30d", "1y"):
        range_key = "1h"

    anchor_date = (request.args.get("anchor_date") or "").strip() or None
    return jsonify(_generate_dashboard_data(range_key, anchor_date))


def api_events():
    # Read-only dashboard data. IDs are masked before returning.
    # Keep token protection by setting DASHBOARD_PUBLIC_READ=0.
    public_read = os.getenv("DASHBOARD_PUBLIC_READ", "1") == "1"
    if not public_read and not _maintenance_auth_ok():
        return jsonify({"ok": False, "message": "unauthorized"}), 401

    events = []

    # Production analytics are written to Postgres when DATABASE_URL is enabled.
    # The old dashboard queried SQLite only, so the main dashboard looked empty.
    if POSTGRES_ENABLED:
        conn = None
        try:
            conn = _pg_connect()
            cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
            cur.execute("""
                SELECT created_at, user_id, event_type,
                       result_count, response_time_ms, success
                FROM analytics_events
                WHERE response_time_ms > 0
                ORDER BY created_at DESC
                LIMIT 100
            """)
            rows = cur.fetchall()
            for r in rows:
                events.append({
                    "time": str(r.get("created_at")),
                    "user": mask_user_id(r.get("user_id")),
                    "type": r.get("event_type"),
                    "result": r.get("result_count"),
                    "response_time": r.get("response_time_ms"),
                    "status": "success" if r.get("success") else "failed"
                })
            cur.close()
            conn.close()
            return jsonify(events)
        except Exception as e:
            logging.warning(f"api_events Postgres read failed; falling back to SQLite: {e}")
            try:
                if conn:
                    conn.close()
            except Exception:
                pass

    try:
        conn = _get_db()
        cur = conn.cursor()
        cur.execute("""
            SELECT created_at, user_id, event_type,
                   result_count, response_time_ms, success
            FROM analytics_events
            WHERE response_time_ms > 0
            ORDER BY created_at DESC
            LIMIT 100
        """)
        rows = cur.fetchall()
        for r in rows:
            events.append({
                "time": str(r[0]),
                "user": mask_user_id(r[1]),
                "type": r[2],
                "result": r[3],
                "response_time": r[4],
                "status": "success" if r[5] else "failed"
            })
        cur.close()
        conn.close()
        return jsonify(events)
    except Exception as e:
        logging.exception("api_events failed")
        return jsonify([]), 200


def api_line_insights():
    # Read-only dashboard data. Set DASHBOARD_PUBLIC_READ=0 to require ADMIN_TOKEN.
    public_read = os.getenv("DASHBOARD_PUBLIC_READ", "1") == "1"
    if not public_read and not _maintenance_auth_ok():
        return jsonify({"ok": False, "message": "unauthorized"}), 401

    force = (
        (request.args.get("force") or "0").strip() == "1"
        or (request.args.get("refresh") or "0").strip() == "1"
    )
    ttl = int(os.getenv("LINE_INSIGHTS_CACHE_TTL_SECONDS", "21600"))  # 6 hours
    cache_key = "line_insights:v1"

    if not force:
        try:
            cached = get_cached_data(cache_key, ttl_sec=ttl)
            if isinstance(cached, dict):
                cached["cached"] = True
                return jsonify(cached)
        except Exception as e:
            logging.debug(f"line insights cache read skipped: {e}")

    try:
        if not CHANNEL_ACCESS_TOKEN:
            raise RuntimeError("LINE_CHANNEL_ACCESS_TOKEN not set")

        headers = {
            "Authorization": f"Bearer {CHANNEL_ACCESS_TOKEN}"
        }

        tw_now = datetime.now(timezone(timedelta(hours=8)))
        query_date = (tw_now.date() - timedelta(days=1)).isoformat()

        followers = 0
        targeted = 0
        blocks = 0
        block_rate = 0.0
        gender = []
        age = []
        area = []
        app_type = []
        subscription_period = []

        r = requests.get(
            f"https://api.line.me/v2/bot/insight/followers?date={query_date}",
            headers=headers,
            timeout=10
        )
        if r.status_code == 200:
            j = r.json()
            followers = j.get("followers", 0) or 0
            targeted = j.get("targetedReaches", 0) or 0
            blocks = j.get("blocks", 0) or 0
            block_rate = round((blocks / followers) * 100, 1) if followers else 0.0
        else:
            logging.warning(f"followers insight failed: {r.status_code} {r.text}")

        r2 = requests.get(
            "https://api.line.me/v2/bot/insight/demographic",
            headers=headers,
            timeout=10
        )
        if r2.status_code == 200:
            j = r2.json()

            gender = [
                {"label": item.get("gender"), "percentage": item.get("percentage", 0)}
                for item in j.get("genders", [])
            ]
            age = [
                {"label": item.get("age"), "percentage": item.get("percentage", 0)}
                for item in j.get("ages", [])
            ]
            area = [
                {"label": item.get("area"), "percentage": item.get("percentage", 0)}
                for item in j.get("areas", [])
            ]
            app_type = [
                {"label": item.get("appType"), "percentage": item.get("percentage", 0)}
                for item in j.get("appTypes", [])
            ]
            subscription_period = [
                {"label": item.get("subscriptionPeriod"), "percentage": item.get("percentage", 0)}
                for item in j.get("subscriptionPeriods", [])
            ]
        else:
            logging.warning(f"demographic insight failed: {r2.status_code} {r2.text}")

        out = {
            "followers": followers,
            "targetedReaches": targeted,
            "blocks": blocks,
            "blockRate": block_rate,
            "gender": gender,
            "age": age,
            "area": area,
            "appType": app_type,
            "subscriptionPeriod": subscription_period,
            "queryDate": query_date,
            "cached": False
        }
        try:
            save_cache(cache_key, out)
        except Exception as e:
            logging.debug(f"line insights cache write skipped: {e}")
        return jsonify(out)
    except Exception as e:
        logging.exception("api_line_insights failed")
        # Fall back to stale cache if LINE API is temporarily unavailable.
        try:
            stale = get_cached_data(cache_key, ttl_sec=60*60*24*30)
            if isinstance(stale, dict):
                stale["cached"] = True
                stale["stale"] = True
                stale["error"] = str(e)
                return jsonify(stale), 200
        except Exception:
            pass
        return jsonify({
            "followers": 0,
            "targetedReaches": 0,
            "blocks": 0,
            "blockRate": 0,
            "gender": [],
            "age": [],
            "area": [],
            "appType": [],
            "subscriptionPeriod": [],
            "cached": False,
            "error": str(e)
        }), 200


def register_dashboard_routes(app):
    app.add_url_rule('/dashboard', endpoint='dashboard_page', view_func=dashboard_page, methods=['GET'])
    app.add_url_rule('/api/dashboard', endpoint='api_dashboard', view_func=api_dashboard, methods=['GET'])
    app.add_url_rule('/api/dashboard', endpoint='api_dashboard', view_func=api_dashboard, methods=['GET'])
    app.add_url_rule('/api/events', endpoint='api_events', view_func=api_events)
    app.add_url_rule('/api/line-insights', endpoint='api_line_insights', view_func=api_line_insights)
