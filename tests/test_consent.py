import os
import unittest
from unittest import mock

from flask import Flask

from linebot_app import consent_routes


class ConsentRouteTests(unittest.TestCase):
    def setUp(self):
        self.app = Flask(__name__, template_folder="../templates")
        consent_routes.register_consent_routes(self.app)
        consent_routes._last_consent_ts.clear()

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


if __name__ == "__main__":
    unittest.main()
