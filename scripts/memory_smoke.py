"""Local memory regression smoke test; uses only synthetic analytics rows."""

import os
import sqlite3
import sys
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

os.environ.setdefault("GAP_MAX_EVENTS", "20000")
os.environ.setdefault("OSM_FALLBACK_ENABLE", "0")

from core.memory import process_rss_mb
from core.database import ANALYTICS_DB_PATH


MARKER = "memory-smoke"


def rss():
    value = process_rss_mb()
    return round(value, 1) if value is not None else None


def seed(count=20000):
    conn = sqlite3.connect(ANALYTICS_DB_PATH)
    conn.execute("DELETE FROM analytics_events WHERE query_text = ?", (MARKER,))
    rows = (
        (
            f"smoke-{i % 200}", "location_query", i % 5, 1,
            100 + (i % 30) * 250, 25.02 + (i % 200) * 0.0001,
            121.50 + (i % 150) * 0.0001, "測試區", MARKER,
            f"2026-09-{1 + (i % 26):02d} 12:{i % 60:02d}:00",
        )
        for i in range(count)
    )
    conn.executemany(
        """INSERT INTO analytics_events
        (user_id,event_type,result_count,success,response_time_ms,lat,lon,area_name,query_text,created_at)
        VALUES (?,?,?,?,?,?,?,?,?,?)""",
        rows,
    )
    conn.commit()
    conn.close()


def cleanup():
    conn = sqlite3.connect(ANALYTICS_DB_PATH)
    conn.execute("DELETE FROM analytics_events WHERE query_text = ?", (MARKER,))
    conn.execute("DELETE FROM request_cache WHERE query_key LIKE 'gap_summary:v251_memory_bounded:%'")
    conn.commit()
    conn.close()


def main():
    print({"stage": "process_start", "rss_mb": rss()})
    import app
    from toilet.data_sources import query_public_csv_toilets

    print({"stage": "app_startup", "rss_mb": rss(), "routes": len(app.app.url_map._rules)})
    before_search = rss()
    result_count = 0
    for _ in range(20):
        result_count = len(query_public_csv_toilets(25.0478, 121.5170, 500))
    print({"stage": "20_csv_queries", "rss_mb": rss(), "before_mb": before_search, "results": result_count})

    seed()
    try:
        client = app.app.test_client()
        before_gap = rss()
        response = client.get("/api/gap-summary?range=all&force=1")
        after_gap = rss()
        payload = response.get_json() or {}
        print({
            "stage": "gap_force", "status": response.status_code,
            "rss_before_mb": before_gap, "rss_after_mb": after_gap,
            "source_rows": payload.get("data_quality", {}).get("raw_total_queries_before_scope_filter"),
        })
        for _ in range(10):
            assert client.get("/api/gap-summary?range=all").status_code == 200
        print({"stage": "gap_10_cached", "rss_mb": rss()})
        forced_rss = []
        for _ in range(5):
            assert client.get("/api/gap-summary?range=all&force=1").status_code == 200
            forced_rss.append(rss())
        print({"stage": "gap_5_forced", "rss_mb_each": forced_rss})
        for _ in range(10):
            assert client.get("/api/dashboard?range=1d").status_code == 200
        print({"stage": "dashboard_10", "rss_mb": rss()})
        assert client.get("/dashboard").status_code == 200
        assert client.get("/dashboard/gap").status_code == 200
    finally:
        cleanup()


if __name__ == "__main__":
    main()
