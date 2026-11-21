import unittest
from unittest import mock

from flask import Flask

from dashboard import routes


class DashboardCacheTests(unittest.TestCase):
    def setUp(self):
        self.app = Flask(__name__)

    def test_api_dashboard_uses_cached_result(self):
        cached = {"summary": {"total_queries": 7}}
        with self.app.test_request_context("/api/dashboard?range=7d"), \
             mock.patch.object(routes, "get_cached_data", return_value=cached) as read, \
             mock.patch.object(routes, "_generate_dashboard_data") as generate:
            response = routes.api_dashboard()
        payload = response.get_json()
        self.assertTrue(payload["cached"])
        self.assertEqual(payload["summary"]["total_queries"], 7)
        read.assert_called_once_with("dashboard:v2:7d:latest", ttl_sec=300)
        generate.assert_not_called()

    def test_force_refresh_rebuilds_and_saves(self):
        fresh = {"summary": {"total_queries": 8}}
        with self.app.test_request_context("/api/dashboard?range=7d&force=1"), \
             mock.patch.object(routes, "get_cached_data") as read, \
             mock.patch.object(routes, "save_cache") as save, \
             mock.patch.object(routes, "_generate_dashboard_data", return_value=fresh) as generate:
            response = routes.api_dashboard()
        payload = response.get_json()
        self.assertFalse(payload["cached"])
        self.assertIn("generated_at", payload)
        read.assert_not_called()
        generate.assert_called_once_with("7d", None)
        save.assert_called_once()

    def test_anchor_date_is_part_of_cache_key(self):
        with self.app.test_request_context(
            "/api/dashboard?range=1y&anchor_date=2026-11-20"
        ), mock.patch.object(
            routes, "get_cached_data", return_value={"summary": {}}
        ) as read:
            routes.api_dashboard()
        read.assert_called_once_with(
            "dashboard:v2:1y:2026-11-20", ttl_sec=300
        )


if __name__ == "__main__":
    unittest.main()
