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
        self.real_verify = consent_routes._verify_line_id_token
        self.verify_patcher = mock.patch.object(
            consent_routes,
            "_verify_line_id_token",
            return_value=({"sub": "U123", "name": "Verified User"}, "", 200),
        )
        self.verify_patcher.start()

    def tearDown(self):
        self.verify_patcher.stop()

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

    def test_verified_line_user_must_match_claimed_user(self):
        with mock.patch.object(consent_routes, "upsert_consent") as write:
            response = self.app.test_client().post(
                "/api/consent",
                json={"idToken": "token", "userId": "U-DIFFERENT", "agree": True},
            )
        self.assertEqual(response.status_code, 401)
        self.assertFalse(response.get_json()["ok"])
        write.assert_not_called()

    def test_verified_identity_is_used_for_database_write(self):
        with mock.patch.object(consent_routes, "upsert_consent", return_value=True) as write:
            response = self.app.test_client().post(
                "/api/consent",
                json={
                    "idToken": "token",
                    "userId": "U123",
                    "displayName": "Untrusted Name",
                    "agree": True,
                },
            )
        self.assertEqual(response.status_code, 200)
        self.assertEqual(write.call_args.args[0], "U123")
        self.assertEqual(write.call_args.args[2], "Verified User")

    def test_missing_identity_token_is_rejected(self):
        with mock.patch.object(
            consent_routes, "_verify_line_id_token", side_effect=self.real_verify
        ):
            response = self.app.test_client().post(
                "/api/consent", json={"userId": "U123", "agree": True}
            )
        self.assertEqual(response.status_code, 401)
        self.assertFalse(response.get_json()["ok"])

    def test_non_object_json_is_rejected_cleanly(self):
        response = self.app.test_client().post("/api/consent", json=["bad"])
        self.assertEqual(response.status_code, 400)
        self.assertFalse(response.get_json()["ok"])

    def test_malformed_json_is_rejected_as_client_error(self):
        response = self.app.test_client().post(
            "/api/consent",
            data="{broken",
            content_type="application/json",
        )
        self.assertEqual(response.status_code, 400)
        self.assertFalse(response.get_json()["ok"])

    def test_missing_agree_field_is_rejected(self):
        response = self.app.test_client().post(
            "/api/consent", json={"idToken": "token", "userId": "U123"}
        )
        self.assertEqual(response.status_code, 400)
        self.assertFalse(response.get_json()["ok"])

    def test_oversized_identity_token_is_rejected_before_line_call(self):
        with mock.patch.object(consent_routes, "_verify_line_id_token") as verify:
            response = self.app.test_client().post(
                "/api/consent",
                json={"idToken": "x" * 9000, "userId": "U123", "agree": True},
            )
        self.assertEqual(response.status_code, 400)
        verify.assert_not_called()

    def test_line_verification_uses_channel_id_from_liff_id(self):
        line_response = mock.MagicMock()
        line_response.status_code = 200
        line_response.json.return_value = {"sub": "U123", "name": "Verified User"}
        with mock.patch.dict(
            os.environ,
            {
                "LIFF_CONSENT_ID": "2007674330-abcdef",
                "LIFF_CONSENT_CHANNEL_ID": "",
                "LINE_LOGIN_CHANNEL_ID": "",
            },
            clear=False,
        ), mock.patch.object(consent_routes.requests, "post", return_value=line_response) as post:
            verified, error, status = self.real_verify("signed-token")
        self.assertEqual(status, 200)
        self.assertEqual(error, "")
        self.assertEqual(verified["sub"], "U123")
        self.assertEqual(post.call_args.kwargs["data"]["client_id"], "2007674330")

    def test_line_verification_timeout_is_retryable(self):
        with mock.patch.dict(
            os.environ, {"LIFF_CONSENT_ID": "2007674330-abcdef"}, clear=False
        ), mock.patch.object(
            consent_routes.requests,
            "post",
            side_effect=consent_routes.requests.Timeout("timeout"),
        ):
            verified, message, status = self.real_verify("signed-token")
        self.assertIsNone(verified)
        self.assertEqual(status, 503)
        self.assertIn("稍後再試", message)

    def test_line_rejected_token_is_not_accepted(self):
        line_response = mock.MagicMock()
        line_response.status_code = 400
        line_response.json.return_value = {"error": "invalid_request"}
        with mock.patch.dict(
            os.environ, {"LIFF_CONSENT_ID": "2007674330-abcdef"}, clear=False
        ), mock.patch.object(consent_routes.requests, "post", return_value=line_response):
            verified, message, status = self.real_verify("bad-token")
        self.assertIsNone(verified)
        self.assertEqual(status, 401)


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

    def test_default_zero_ttl_rechecks_database_even_after_positive_cache(self):
        cursor = mock.MagicMock()
        cursor.fetchone.return_value = (False,)
        connection = mock.MagicMock()
        connection.cursor.return_value = cursor
        consent._consent_cache_set("U123", True)
        with mock.patch.object(consent, "POSTGRES_ENABLED", True), \
             mock.patch.object(consent, "_CONSENT_TTL", 0), \
             mock.patch.object(consent, "_pg_connect", return_value=connection):
            self.assertFalse(consent.has_consented("U123"))
        cursor.execute.assert_called_once()

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


class ConsentEndToEndTests(unittest.TestCase):
    def test_verified_api_write_is_immediately_visible_to_webhook_gate(self):
        state = {}

        class Cursor:
            def __init__(self):
                self.row = None

            def execute(self, sql, params):
                if sql.lstrip().upper().startswith("SELECT"):
                    self.row = (state.get(params[0], False),) if params[0] in state else None
                else:
                    state[params[0]] = bool(params[1])

            def fetchone(self):
                return self.row

        class Connection:
            def cursor(self):
                return Cursor()

            def commit(self):
                pass

            def close(self):
                pass

        app = Flask(__name__, template_folder="../templates")
        consent_routes.register_consent_routes(app)
        consent._consent_cache.clear()
        with mock.patch.object(consent, "POSTGRES_ENABLED", True), \
             mock.patch.object(consent, "_pg_connect", return_value=Connection()), \
             mock.patch.object(
                 consent_routes,
                 "_verify_line_id_token",
                 return_value=({"sub": "U123", "name": "Verified User"}, "", 200),
             ), \
             mock.patch.object(consent_routes, "upsert_consent", side_effect=consent.upsert_consent):
            response = app.test_client().post(
                "/api/consent",
                json={"idToken": "valid-token", "userId": "U123", "agree": True},
            )
            self.assertEqual(response.status_code, 200)
            self.assertTrue(consent.has_consented("U123"))


if __name__ == "__main__":
    unittest.main()
