import os
import time
import unittest
from unittest import mock

from flask import Flask

from linebot_app import consent_routes
from linebot_app import consent


class ConsentRouteTests(unittest.TestCase):
    def setUp(self):
        self.app = Flask(__name__, template_folder="../templates")
        consent_routes.register_consent_routes(self.app)
        consent_routes._last_consent_ts.clear()
        consent._consent_cache.clear()

    def test_consent_page_prefers_dedicated_liff_id(self):
        with mock.patch.dict(
            os.environ,
            {"LIFF_CONSENT_ID": "dedicated-123", "LIFF_ID": "shared-456"},
            clear=False,
        ):
            response = self.app.test_client().get("/consent")
        self.assertEqual(response.status_code, 200)
        self.assertIn(b'dedicated-123', response.data)
        self.assertNotIn(b'shared-456', response.data)

    def test_consent_page_falls_back_to_shared_liff_id(self):
        with mock.patch.dict(os.environ, {"LIFF_ID": "shared-456"}, clear=False):
            with mock.patch.dict(os.environ, {"LIFF_CONSENT_ID": "", "LIFF_ID_CONSENT": ""}):
                response = self.app.test_client().get("/consent")
        self.assertEqual(response.status_code, 200)
        self.assertIn(b'shared-456', response.data)

    def test_failed_write_is_not_reported_as_success(self):
        with mock.patch.object(consent_routes, "upsert_consent", return_value=False):
            response = self.app.test_client().post(
                "/api/consent",
                json={"userId": "U123", "agree": True},
            )
        payload = response.get_json()
        self.assertEqual(response.status_code, 503)
        self.assertFalse(payload["ok"])
        self.assertTrue(payload["retryable"])

    def test_successful_write_returns_success(self):
        with mock.patch.object(consent_routes, "upsert_consent", return_value=True):
            response = self.app.test_client().post(
                "/api/consent",
                json={"userId": "U123", "agree": True},
            )
        self.assertEqual(response.status_code, 200)
        self.assertTrue(response.get_json()["ok"])

    def test_string_false_is_not_mistaken_for_consent(self):
        with mock.patch.object(consent_routes, "upsert_consent", return_value=True) as write:
            response = self.app.test_client().post(
                "/api/consent",
                json={"userId": "U123", "agree": "false"},
            )
        self.assertEqual(response.status_code, 200)
        self.assertFalse(write.call_args.args[1])


class ConsentStateTests(unittest.TestCase):
    def setUp(self):
        consent._consent_cache.clear()

    def test_negative_result_is_not_cached_across_workers(self):
        cursor = mock.MagicMock()
        cursor.fetchone.return_value = (True,)
        connection = mock.MagicMock()
        connection.cursor.return_value = cursor
        consent._consent_cache["U123"] = (time.time(), False)

        with mock.patch.object(consent, "POSTGRES_ENABLED", True), \
             mock.patch.object(consent, "_pg_connect", return_value=connection):
            self.assertTrue(consent.has_consented("U123"))

        cursor.execute.assert_called_once()
        self.assertTrue(consent._consent_cache["U123"][1])

    def test_false_write_removes_stale_positive_cache(self):
        consent._consent_cache_set("U123", True)
        consent._consent_cache_set("U123", False)
        self.assertNotIn("U123", consent._consent_cache)

    def test_prompt_builds_request_url_when_public_url_is_missing(self):
        app = Flask(__name__)
        with app.test_request_context("/callback", base_url="https://example.test"):
            with mock.patch.object(consent, "has_consented", return_value=False), \
                 mock.patch.object(consent, "CONSENT_PAGE_URL", ""), \
                 mock.patch.object(
                     consent,
                     "T",
                     side_effect=lambda key, uid, url: f"consent:{url}",
                 ):
                message = consent.ensure_consent_or_prompt("U123")
        self.assertEqual(message.text, "consent:https://example.test/consent")


if __name__ == "__main__":
    unittest.main()
