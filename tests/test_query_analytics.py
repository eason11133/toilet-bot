import os
import sqlite3
import tempfile
import unittest
from unittest import mock

os.environ.setdefault("DATABASE_URL", "")
os.environ.setdefault("LINE_CHANNEL_ACCESS_TOKEN", "test")
os.environ.setdefault("LINE_CHANNEL_SECRET", "test")

from core import database
from dashboard import gap_analysis
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

    def test_cache_metadata_is_explicit_even_for_empty_results(self):
        with mock.patch.object(search, "get_cached_data", return_value=[]):
            result, meta = search.build_nearby_toilets(
                "U1", 25.0, 121.5, return_metadata=True
            )
        self.assertEqual(result, [])
        self.assertEqual(meta, {"cache_hit": True})


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


if __name__ == "__main__":
    unittest.main()
