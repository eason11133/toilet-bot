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
            return_value=({"sub": "U123", "name": "Verified User"}, "", 200, "ok"),
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
        self.assertEqual(response.headers["Cache-Control"], "no-store, no-cache, must-revalidate, max-age=0")
        self.assertIn(b'consent-flow-version', response.data)

    def test_consent_page_falls_back_to_shared_liff_id(self):
        with mock.patch.dict(os.environ, {"LIFF_ID": "shared-456"}, clear=False):
            with mock.patch.dict(os.environ, {"LIFF_CONSENT_ID": "", "LIFF_ID_CONSENT": ""}):
                response = self.app.test_client().get("/consent")
        self.assertEqual(response.status_code, 200)
        self.assertIn(b'shared-456', response.data)

    def test_privacy_page_uses_instagram_contact(self):
        response = self.app.test_client().get("/privacy")
        self.assertEqual(response.status_code, 200)
        self.assertIn(b"instagram.com/toiletmvp", response.data)
        self.assertIn(b"jplx=MWRvMnV2MTNyN2RkMw==", response.data)

    def test_health_reports_config_and_storage_without_user_data(self):
        with mock.patch.dict(
            os.environ, {"LIFF_CONSENT_ID": "2007674330-abcdef"}, clear=False
        ), mock.patch.object(
            consent_routes, "consent_storage_health", return_value=(True, "ok")
        ):
            response = self.app.test_client().get("/api/consent/health")
        payload = response.get_json()
        self.assertEqual(response.status_code, 200)
        self.assertTrue(payload["ok"])
        self.assertTrue(payload["liff_configured"])
        self.assertTrue(payload["channel_configured"])
        self.assertTrue(payload["storage_ok"])
        self.assertNotIn("user_id", payload)

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
            verified, error, status, code = self.real_verify("signed-token")
        self.assertEqual(status, 200)
        self.assertEqual(error, "")
        self.assertEqual(code, "ok")
        self.assertEqual(verified["sub"], "U123")
        self.assertEqual(post.call_args.kwargs["data"]["client_id"], "2007674330")

    def test_generic_login_channel_cannot_override_consent_liff_channel(self):
        with mock.patch.dict(
            os.environ,
            {
                "LIFF_CONSENT_ID": "2007674330-abcdef",
                "LIFF_CONSENT_CHANNEL_ID": "",
                "LINE_LOGIN_CHANNEL_ID": "wrong-channel",
            },
            clear=False,
        ):
            self.assertEqual(consent_routes._get_liff_channel_id(), "2007674330")

    def test_line_verification_timeout_is_retryable(self):
        with mock.patch.dict(
            os.environ, {"LIFF_CONSENT_ID": "2007674330-abcdef"}, clear=False
        ), mock.patch.object(
            consent_routes.requests,
            "post",
            side_effect=consent_routes.requests.Timeout("timeout"),
        ):
            verified, message, status, code = self.real_verify("signed-token")
        self.assertIsNone(verified)
        self.assertEqual(status, 503)
        self.assertEqual(code, "line_verify_unavailable")
        self.assertIn("稍後再試", message)

    def test_line_rejected_token_is_not_accepted(self):
        line_response = mock.MagicMock()
        line_response.status_code = 400
        line_response.json.return_value = {"error": "invalid_request"}
        with mock.patch.dict(
            os.environ, {"LIFF_CONSENT_ID": "2007674330-abcdef"}, clear=False
        ), mock.patch.object(consent_routes.requests, "post", return_value=line_response):
            verified, message, status, code = self.real_verify("bad-token")
        self.assertIsNone(verified)
        self.assertEqual(status, 401)
        self.assertEqual(code, "invalid_id_token")

    def test_access_token_is_verified_and_profile_is_loaded(self):
        verify_response = mock.MagicMock()
        verify_response.status_code = 200
        verify_response.json.return_value = {"client_id": "2007674330", "expires_in": 3600}
        profile_response = mock.MagicMock()
        profile_response.status_code = 200
        profile_response.json.return_value = {"userId": "U123", "displayName": "LINE User"}
        with mock.patch.dict(
            os.environ,
            {"LIFF_CONSENT_ID": "2007674330-abcdef", "LIFF_CONSENT_CHANNEL_ID": ""},
            clear=False,
        ), mock.patch.object(
            consent_routes.requests,
            "get",
            side_effect=[verify_response, profile_response],
        ) as get:
            verified, error, status, code = consent_routes._verify_line_access_token("access-token")
        self.assertEqual((error, status, code), ("", 200, "ok"))
        self.assertEqual(verified["sub"], "U123")
        self.assertEqual(get.call_count, 2)
        self.assertEqual(get.call_args_list[1].kwargs["headers"]["Authorization"], "Bearer access-token")

    def test_access_token_channel_mismatch_is_rejected(self):
        verify_response = mock.MagicMock()
        verify_response.status_code = 200
        verify_response.json.return_value = {"client_id": "different-channel"}
        with mock.patch.dict(
            os.environ,
            {"LIFF_CONSENT_ID": "2007674330-abcdef", "LIFF_CONSENT_CHANNEL_ID": ""},
            clear=False,
        ), mock.patch.object(
            consent_routes.requests, "get", return_value=verify_response
        ):
            verified, _, status, code = consent_routes._verify_line_access_token("access-token")
        self.assertIsNone(verified)
        self.assertEqual(status, 500)
        self.assertEqual(code, "channel_mismatch")


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

    def test_neon_read_failure_falls_back_to_staging(self):
        with mock.patch.object(consent, "POSTGRES_ENABLED", True), \
             mock.patch.object(consent, "_pg_connect", side_effect=RuntimeError("quota")), \
             mock.patch.object(consent, "_staging_has_consented", return_value=True) as staging:
            self.assertTrue(consent.has_consented("U123"))
        staging.assert_called_once_with("U123")

    def test_neon_write_failure_falls_back_to_verified_staging_write(self):
        with mock.patch.object(consent, "POSTGRES_ENABLED", True), \
             mock.patch.object(consent, "_pg_connect", side_effect=RuntimeError("quota")), \
             mock.patch.object(consent, "_staging_upsert", return_value=True) as staging:
            ok = consent.upsert_consent(
                "U123", True, "Verified", "line-client", "agent", "now",
                access_token="line-token",
            )
        self.assertTrue(ok)
        staging.assert_called_once_with("line-token", True, "line-client", "agent")

    def test_staged_sync_upserts_neon_then_marks_rows(self):
        cursor = mock.MagicMock()
        connection = mock.MagicMock()
        connection.cursor.return_value = cursor
        row = {
            "user_id": "U123", "agreed": True, "display_name": "User",
            "source_type": "line-client", "user_agent": "agent",
            "consented_at": "2026-11-22T00:00:00+00:00",
            "updated_at": "2026-11-22T00:00:00+00:00",
        }
        with mock.patch.object(consent, "POSTGRES_ENABLED", True), \
             mock.patch.object(consent, "CONSENT_STAGING_URL", "https://staging.test"), \
             mock.patch.object(consent, "CONSENT_STAGING_SECRET", "secret"), \
             mock.patch.object(consent, "_pg_connect", return_value=connection), \
             mock.patch.object(
                 consent, "_staging_post",
                 side_effect=[{"ok": True, "rows": [row]}, {"ok": True, "updated": 1}],
             ) as staging:
            synced = consent.sync_staged_consents(batch_limit=500, max_batches=1)
        self.assertEqual(synced, 1)
        cursor.executemany.assert_called_once()
        connection.commit.assert_called_once()
        self.assertEqual(staging.call_args_list[1].args[0], "mark_synced")

    def test_storage_health_distinguishes_connection_failure(self):
        with mock.patch.object(consent, "POSTGRES_ENABLED", True), \
             mock.patch.object(consent, "_pg_connect", side_effect=RuntimeError("secret")):
            ok, status = consent.consent_storage_health()
        self.assertFalse(ok)
        self.assertEqual(status, "connection_failed:RuntimeError:other")
        self.assertNotIn("secret", status)

    def test_storage_health_safely_classifies_bad_credentials(self):
        error = RuntimeError("password authentication failed for user private-name")
        with mock.patch.object(consent, "POSTGRES_ENABLED", True), \
             mock.patch.object(consent, "_pg_connect", side_effect=error):
            ok, status = consent.consent_storage_health()
        self.assertFalse(ok)
        self.assertEqual(status, "connection_failed:RuntimeError:invalid_credentials")
        self.assertNotIn("private-name", status)

    def test_database_error_category_handles_neon_connection_shutdown(self):
        error = RuntimeError("server closed the connection unexpectedly")
        self.assertEqual(consent._database_error_category(error), "server_closed")

    def test_database_error_category_handles_neon_quota_suspension(self):
        error = RuntimeError("Your account or project has exceeded the quota")
        self.assertEqual(consent._database_error_category(error), "quota_exceeded")

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
        self.assertTrue(message.text.startswith("consent:https://example.test/consent?cv="))

    def test_consent_url_replaces_existing_flow_version(self):
        with mock.patch.object(consent, "has_consented", return_value=False), \
             mock.patch.object(
                 consent,
                 "CONSENT_PAGE_URL",
                 "https://example.test/consent?source=line&cv=old",
             ), \
             mock.patch.object(consent, "T", side_effect=lambda key, uid, url: url):
            url = consent.ensure_consent_or_prompt("U123").text
        self.assertIn("source=line", url)
        self.assertIn(f"cv={consent.CONSENT_FLOW_VERSION}", url)
        self.assertNotIn("cv=old", url)


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
                 return_value=({"sub": "U123", "name": "Verified User"}, "", 200, "ok"),
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
