import os
import sqlite3
import tempfile
import time
import unittest
from unittest import mock

from flask import Flask

os.environ.setdefault("DATABASE_URL", "")
os.environ.setdefault("LINE_CHANNEL_ACCESS_TOKEN", "test")
os.environ.setdefault("LINE_CHANNEL_SECRET", "test")

from core import database
from dashboard import gap_analysis
from dashboard import gap_routes
from linebot_app import handlers
from toilet import search


class QueryLifecycleTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.db_path = os.path.join(self.tmp.name, "analytics.db")
        self.old_database_path = database.ANALYTICS_DB_PATH
        self.old_handler_path = handlers.ANALYTICS_DB_PATH
        database.ANALYTICS_DB_PATH = self.db_path
        handlers.ANALYTICS_DB_PATH = self.db_path
        database.create_analytics_tables()
        handlers._RECENT_LOCATION_QUERIES.clear()

    def tearDown(self):
        database.ANALYTICS_DB_PATH = self.old_database_path
        handlers.ANALYTICS_DB_PATH = self.old_handler_path
        self.tmp.cleanup()

    def test_lifecycle_updates_one_row(self):
        handlers._start_location_query("Q1", "U1", 25.0, 121.5, "測試區")
        handlers._finish_location_query(
            "Q1", "success", 3, 125, cache_hit=True,
            reply_attempted=True, reply_accepted=True,
        )
        conn = sqlite3.connect(self.db_path)
        row = conn.execute("""
            SELECT query_id, user_id_hash, cache_hit, result_count, status,
                   reply_attempted, reply_accepted, COUNT(*) OVER ()
            FROM analytics_events
        """).fetchone()
        conn.close()
        self.assertEqual(row[0], "Q1")
        self.assertEqual(len(row[1]), 64)
        self.assertEqual(row[2:7], (1, 3, "success", 1, 1))
        self.assertEqual(row[7], 1)

    def test_rapid_same_location_is_suppressed(self):
        self.assertTrue(handlers._accept_user_location_query("U1", 25.0, 121.5, now=10))
        self.assertFalse(handlers._accept_user_location_query("U1", 25.0001, 121.5001, now=12))
        self.assertTrue(handlers._accept_user_location_query("U1", 25.0001, 121.5001, now=20))

    def test_legacy_raw_user_id_is_backfilled_to_canonical_hash(self):
        conn = sqlite3.connect(self.db_path)
        conn.execute(
            "INSERT INTO analytics_events (user_id,event_type,created_at) VALUES (?,?,?)",
            ("legacy-user", "location_query", "2026-10-15T12:00:00+08:00"),
        )
        conn.commit()
        conn.close()
        updated = database.backfill_analytics_user_hashes(handlers._analytics_user_hash)
        conn = sqlite3.connect(self.db_path)
        user_id, user_id_hash = conn.execute(
            "SELECT user_id,user_id_hash FROM analytics_events"
        ).fetchone()
        conn.close()
        self.assertEqual(updated, 1)
        self.assertEqual(user_id, handlers._analytics_user_hash("legacy-user"))
        self.assertEqual(user_id_hash, user_id)

    def test_cache_metadata_is_explicit_even_for_empty_results(self):
        with mock.patch.object(search, "get_cached_data", return_value=[]):
            result, meta = search.build_nearby_toilets(
                "U1", 25.0, 121.5, return_metadata=True
            )
        self.assertEqual(result, [])
        self.assertEqual(meta, {
            "cache_hit": True,
            "source_status": "cached",
            "source_failures": [],
        })

    def test_all_source_failure_is_explicit_and_not_cached(self):
        failed = mock.Mock()
        failed.result.side_effect = RuntimeError("source unavailable")
        with mock.patch.object(search, "get_cached_data", return_value=None), \
             mock.patch.object(search._pool, "submit", return_value=failed), \
             mock.patch.object(search, "save_cache") as save_cache, \
             mock.patch.object(search, "log_source_query"), \
             mock.patch.dict(os.environ, {"OSM_FALLBACK_ENABLE": "0"}):
            result, meta = search.build_nearby_toilets(
                "U1", 25.0, 121.5, return_metadata=True
            )
        self.assertEqual(result, [])
        self.assertEqual(meta["source_status"], "failed")
        self.assertEqual(len(meta["source_failures"]), 2)
        save_cache.assert_not_called()

    def test_distance_top_k_is_selected_before_nts_reranking(self):
        toilets = [
            {"name": f"T{i}", "distance": distance, "verification_status": "pending"}
            for i, distance in enumerate([500, 40, 300, 20, 200, 100])
        ]
        seen_distances = []

        def fake_nts(items):
            seen_distances.extend(item["distance"] for item in items)
            return list(reversed(items))

        with mock.patch.object(search, "sort_toilets_nts", side_effect=fake_nts):
            result = search._rank_two_stage(
                toilets, algo="nts_score", candidate_top_k=4, result_top_k=2
            )

        self.assertEqual(seen_distances, [20, 40, 100, 200])
        self.assertEqual([item["distance"] for item in result], [200, 100])

    def test_rejected_items_do_not_consume_candidate_slots(self):
        toilets = [
            {"name": "rejected", "distance": 1, "verification_status": "rejected"},
            {"name": "valid-a", "distance": 10, "verification_status": "pending"},
            {"name": "valid-b", "distance": 20, "verification_status": "approved"},
        ]
        result = search._rank_two_stage(
            toilets, algo="distance_only", candidate_top_k=2, result_top_k=2
        )
        self.assertEqual([item["name"] for item in result], ["valid-a", "valid-b"])

    def test_paused_toilet_is_excluded_before_top_k(self):
        toilets = [
            {"name": "paused", "lat": 25.0, "lon": 121.5, "distance": 5},
            {"name": "open", "lat": 25.001, "lon": 121.501, "distance": 20},
        ]
        status_index = {
            (search.norm_coord(25.0), search.norm_coord(121.5)): {
                "status": "暫停使用"
            }
        }
        filtered = search._apply_live_status(toilets, status_index=status_index)
        self.assertEqual([item["name"] for item in filtered], ["open"])

    def test_recovered_toilet_returns_to_candidate_pool(self):
        toilets = [{"name": "open-again", "lat": 25.0, "lon": 121.5, "distance": 5}]
        status_index = {
            (search.norm_coord(25.0), search.norm_coord(121.5)): {
                "status": "恢復正常"
            }
        }
        filtered = search._apply_live_status(toilets, status_index=status_index)
        self.assertEqual(len(filtered), 1)
        self.assertEqual(filtered[0]["status"], "恢復正常")


class GapDefinitionTests(unittest.TestCase):
    def test_no_result_and_low_coverage_are_exclusive(self):
        row = {}
        gap_analysis._gap_add_metrics(row, {"result_count": 0}, 2, 5000)
        gap_analysis._gap_add_metrics(row, {"result_count": 2}, 2, 5000)
        self.assertEqual(row["no_result_count"], 1)
        self.assertEqual(row["low_result_count"], 1)

    def test_cluster_uses_true_user_and_day_unions(self):
        gap_analysis.get_area_name = lambda lat, lon: "測試區"
        base = {
            "area_name": "測試區", "effective_queries": 2, "total_queries": 2,
            "raw_queries": 2, "no_result_count": 1, "low_result_count": 1,
            "slow_query_count": 0, "success_count": 2,
            "response_sum": 200, "response_count": 2, "sample_queries": [],
        }
        first = gap_analysis._gap_finish_row({
            **base, "grid": "25.000,121.500", "lat": 25.0, "lon": 121.5,
            "user_set": {"A", "B"}, "day_set": {"2026-10-15"},
        })
        second = gap_analysis._gap_finish_row({
            **base, "grid": "25.001,121.501", "lat": 25.001, "lon": 121.501,
            "user_set": {"B", "C"}, "day_set": {"2026-10-15", "2026-10-16"},
        })
        clusters = gap_analysis._gap_cluster_rows([first, second], radius_m=500)
        self.assertEqual(len(clusters), 1)
        self.assertEqual(clusters[0]["unique_users"], 3)
        self.assertEqual(clusters[0]["active_days"], 2)

    def test_gap_excludes_failed_and_degraded_source_queries(self):
        with tempfile.TemporaryDirectory() as tmp:
            db_path = os.path.join(tmp, "analytics.db")
            old_db_path = database.ANALYTICS_DB_PATH
            old_gap_path = gap_analysis.ANALYTICS_DB_PATH
            database.ANALYTICS_DB_PATH = db_path
            gap_analysis.ANALYTICS_DB_PATH = db_path
            try:
                database.create_analytics_tables()
                conn = sqlite3.connect(db_path)
                rows = [
                    ("ok", "A", 0, 1, "success", "ok"),
                    ("failed", "B", 0, 0, "failed", "failed"),
                    ("degraded", "C", 0, 1, "success", "degraded"),
                ]
                conn.executemany("""
                    INSERT INTO analytics_events
                    (query_id,user_id,event_type,result_count,success,response_time_ms,
                     lat,lon,area_name,created_at,status,source_status)
                    VALUES (?,?, 'location_query', ?, ?, 100, 25.03, 121.52,
                            '測試區', '2026-10-16T12:00:00+08:00', ?, ?)
                """, rows)
                conn.commit()
                conn.close()
                result = gap_analysis._build_gap_summary("all")
                self.assertEqual(result["summary"]["total_queries"], 1)
                self.assertEqual(result["summary"]["no_result_count"], 1)
                self.assertEqual(result["source_watermark"], 3)
                self.assertGreater(result["generated_epoch"], 0)
                self.assertEqual(result["data_quality"]["excluded_failed_queries"], 1)
                self.assertEqual(result["data_quality"]["excluded_degraded_queries"], 1)
            finally:
                database.ANALYTICS_DB_PATH = old_db_path
                gap_analysis.ANALYTICS_DB_PATH = old_gap_path


class GapSnapshotRouteTests(unittest.TestCase):
    def test_stale_snapshot_returns_immediately_and_starts_background_refresh(self):
        app = Flask(__name__)
        gap_routes.register_gap_routes(app)
        snapshot = {
            "ok": True,
            "generated_epoch": time.time() - 600,
            "source_watermark": 10,
        }
        with mock.patch.object(gap_routes, "_gap_cache_get", return_value=snapshot), \
             mock.patch.object(gap_routes, "_gap_latest_event_id", return_value=11), \
             mock.patch.object(gap_routes, "_start_gap_refresh", return_value=True), \
             mock.patch.object(gap_routes, "_build_gap_summary") as build:
            response = app.test_client().get("/api/gap-summary?range=all")
        payload = response.get_json()
        self.assertEqual(response.status_code, 200)
        self.assertTrue(payload["cached"])
        self.assertTrue(payload["new_data_available"])
        self.assertTrue(payload["refreshing"])
        build.assert_not_called()

    def test_recent_snapshot_with_new_data_starts_background_refresh(self):
        app = Flask(__name__)
        gap_routes.register_gap_routes(app)
        snapshot = {
            "ok": True,
            "generated_epoch": time.time(),
            "source_watermark": 10,
        }
        with mock.patch.object(gap_routes, "_gap_cache_get", return_value=snapshot), \
             mock.patch.object(gap_routes, "_gap_latest_event_id", return_value=11), \
             mock.patch.object(gap_routes, "_start_gap_refresh", return_value=True):
            response = app.test_client().get("/api/gap-summary?range=all")
        payload = response.get_json()
        self.assertTrue(payload["new_data_available"])
        self.assertTrue(payload["refreshing"])

    def test_unchanged_snapshot_does_not_rebuild(self):
        app = Flask(__name__)
        gap_routes.register_gap_routes(app)
        snapshot = {
            "ok": True,
            "generated_epoch": time.time(),
            "source_watermark": 10,
        }
        with mock.patch.object(gap_routes, "_gap_cache_get", return_value=snapshot), \
             mock.patch.object(gap_routes, "_gap_latest_event_id", return_value=10), \
             mock.patch.object(gap_routes, "_start_gap_refresh") as refresh:
            response = app.test_client().get("/api/gap-summary?range=all")
        payload = response.get_json()
        self.assertFalse(payload["new_data_available"])
        self.assertFalse(payload["refreshing"])
        refresh.assert_not_called()


if __name__ == "__main__":
    unittest.main()
