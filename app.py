import os
import logging
import threading

from dotenv import load_dotenv
from flask import Flask
from flask_cors import CORS

load_dotenv()

from config import FEEDBACK_LOOKBACK_LIMIT, _STATUS_INDEX_TTL

from core.database import (
    POSTGRES_ENABLED,
    psycopg2,
    _pg_connect,
    CACHE_DB_PATH,
    ANALYTICS_DB_PATH,
    _get_db,
    create_cache_db,
    tune_sqlite_for_concurrency,
    create_analytics_tables,
    get_cached_data,
    save_cache,
    _start_persistent_store_init_background,
)
from core.cache import _CACHE, _ENRICH_CACHE
from core.utils import (
    _in_bbox,
    mask_user_id,
    norm_coord,
    safe_html,
    _parse_lat_lon,
    haversine,
)
from core.i18n import (
    configure_i18n,
    get_user_lang,
    T,
    L,
    _api_L,
    resolve_lang,
)
from core.app_support import (
    configure_app_support,
    register_app_support_routes,
    _self_keepalive_background,
)

from dashboard.routes import configure_dashboard, register_dashboard_routes
from dashboard.gap_analysis import configure_gap_analysis
from dashboard.gap_routes import register_gap_routes
from dashboard.nts_routes import configure_nts_routes, register_nts_routes

from features.usage import configure_usage, register_usage_routes, build_ai_nearby_recommendation

from linebot_app.reply_tokens import CHANNEL_ACCESS_TOKEN
from linebot_app.replies import configure_replies
from linebot_app.consent import configure_consent, _start_consent_worker
from linebot_app.consent_routes import register_consent_routes
from linebot_app.handlers import (
    register_linebot_routes,
    _base_url,
    _append_uid_lang,
    _user_lang_q,
    get_area_name,
    get_user_contributions,
)

from toilet.scoring import compute_nts_score, sort_toilets_nts_1_0
from toilet.floor import _floor_from_name
from toilet.identity import _make_toilet_id
from toilet.data_sources import TOILETS_FILE_PATH, geocode_address
from toilet.search import register_search_routes, build_nearby_toilets
from toilet.cleanliness import configure_cleanliness, expected_from_feats, compute_nowcast_ci, LAST_N_HISTORY
from toilet.feedback import (
    configure_feedback,
    _insert_feedback_pg,
    _fetch_feedback_pg_by_coord,
    get_feedbacks_by_coord,
    get_feedback_summary_by_coord,
    build_feedback_index,
)
from toilet.feedback_routes import configure_feedback_routes, register_feedback_routes
from toilet.status import configure_status, submit_status_update, build_status_index, _get_liff_status_id, _read_status_rows
from toilet.status_routes import configure_status_routes, register_status_routes
from toilet.recommendation_logs import configure_recommendation_logs, log_user_action
from toilet.auto_verify import configure_auto_verify, _build_auto_verify_context, auto_verify_user_toilet
from toilet.submission import configure_submission, register_submission_routes
from toilet.favorites import configure_favorites, get_user_favorites

from admin.routes import configure_admin_routes, register_admin_routes, _maintenance_auth_ok


# -----------------------------------------------------------------------------
# 1) Cross-module dependency wiring
# -----------------------------------------------------------------------------
configure_dashboard(
    POSTGRES_ENABLED,
    _pg_connect,
    psycopg2,
    ANALYTICS_DB_PATH,
    _get_db_func=_get_db,
    mask_user_id_func=mask_user_id,
    maintenance_auth_ok_func=_maintenance_auth_ok,
    channel_access_token=CHANNEL_ACCESS_TOKEN,
    get_cached_data_func=get_cached_data,
    save_cache_func=save_cache,
)
configure_nts_routes(POSTGRES_ENABLED, _pg_connect, psycopg2)

try:
    logging.info(
        f"🔍 ENRICH_CACHE={_ENRICH_CACHE.__class__.__name__} "
        f"NEARBY_CACHE={_CACHE.__class__.__name__}"
    )
except Exception:
    pass

configure_i18n(_get_db)
configure_replies(L)
configure_feedback(
    postgres_enabled=POSTGRES_ENABLED,
    pg_connect=_pg_connect,
    psycopg2_module=psycopg2,
    mask_user_id_func=mask_user_id,
    parse_lat_lon_func=_parse_lat_lon,
    safe_html_func=safe_html,
    feedback_lookback_limit=FEEDBACK_LOOKBACK_LIMIT,
)
configure_status(
    postgres_enabled=POSTGRES_ENABLED,
    pg_connect=_pg_connect,
    psycopg2_module=psycopg2,
    norm_coord_func=norm_coord,
    haversine_func=haversine,
    status_index_ttl=_STATUS_INDEX_TTL,
)
configure_cleanliness(_fetch_feedback_pg_by_coord)
configure_recommendation_logs(
    postgres_enabled=POSTGRES_ENABLED,
    pg_connect=_pg_connect,
    mask_user_id_func=mask_user_id,
    compute_nts_score_func=compute_nts_score,
    sort_toilets_nts_1_0_func=sort_toilets_nts_1_0,
    make_toilet_id_func=_make_toilet_id,
)
_start_consent_worker()


# -----------------------------------------------------------------------------
# 2) Flask app creation
# -----------------------------------------------------------------------------
logging.basicConfig(level=logging.INFO)
app = Flask(__name__)
CORS(app)

configure_app_support(POSTGRES_ENABLED, log_user_action)
register_app_support_routes(app)


# -----------------------------------------------------------------------------
# 3) Runtime data paths and persistent storage initialization
# -----------------------------------------------------------------------------
DATA_DIR = os.path.join(os.getcwd(), "data")
FAVORITES_FILE_PATH = os.path.join(DATA_DIR, "favorites.txt")
os.makedirs(DATA_DIR, exist_ok=True)
if not os.path.exists(FAVORITES_FILE_PATH):
    open(FAVORITES_FILE_PATH, "a", encoding="utf-8").close()

_PUBLIC_URL_FOR_CONSENT = (os.getenv("PUBLIC_URL") or "").rstrip("/")
CONSENT_PAGE_URL = os.getenv("CONSENT_PAGE_URL") or (
    f"{_PUBLIC_URL_FOR_CONSENT}/consent" if _PUBLIC_URL_FOR_CONSENT else ""
)
configure_consent(
    postgres_enabled=POSTGRES_ENABLED,
    pg_connect=_pg_connect,
    T_func=T,
    consent_page_url=CONSENT_PAGE_URL,
)

create_cache_db()
tune_sqlite_for_concurrency()
create_analytics_tables()
_start_persistent_store_init_background()


# -----------------------------------------------------------------------------
# 4) Feature module configuration
# -----------------------------------------------------------------------------
configure_gap_analysis(
    POSTGRES_ENABLED,
    _pg_connect,
    psycopg2,
    ANALYTICS_DB_PATH,
    get_cached_data,
    save_cache,
    get_area_name,
)
configure_favorites(
    postgres_enabled=POSTGRES_ENABLED,
    pg_connect=_pg_connect,
    favorites_file_path=FAVORITES_FILE_PATH,
    psycopg2_module=psycopg2,
)
configure_auto_verify(
    postgres_enabled=POSTGRES_ENABLED,
    pg_connect=_pg_connect,
    psycopg2_module=psycopg2,
    toilets_file_path=TOILETS_FILE_PATH,
    geocode_address_func=geocode_address,
    haversine_func=haversine,
    in_bbox_func=_in_bbox,
)
configure_submission(
    postgres_enabled=POSTGRES_ENABLED,
    pg_connect=_pg_connect,
    cache=_CACHE,
    floor_from_name_func=_floor_from_name,
    parse_lat_lon_func=_parse_lat_lon,
    geocode_address_func=geocode_address,
    norm_coord_func=norm_coord,
    auto_verify_user_toilet_func=auto_verify_user_toilet,
)

ADMIN_TOKEN = os.getenv("ADMIN_TOKEN", "")
configure_admin_routes(
    admin_token=ADMIN_TOKEN,
    postgres_enabled=POSTGRES_ENABLED,
    pg_connect=_pg_connect,
    psycopg2_module=psycopg2,
    cache=_CACHE,
    build_auto_verify_context_func=_build_auto_verify_context,
    auto_verify_user_toilet_func=auto_verify_user_toilet,
)

PUBLIC_URL = os.getenv("PUBLIC_URL", "").rstrip("/")
configure_usage(
    get_db_func=_get_db,
    read_status_rows_func=_read_status_rows,
    get_user_contributions_func=get_user_contributions,
    get_user_favorites_func=get_user_favorites,
    get_user_lang_func=get_user_lang,
    build_feedback_index_func=build_feedback_index,
    build_status_index_func=build_status_index,
    norm_coord_func=norm_coord,
    L_func=L,
    public_url=PUBLIC_URL,
    liff_id_status=_get_liff_status_id(),
    base_url_func=_base_url,
    get_liff_status_id_func=_get_liff_status_id,
)
configure_feedback_routes(
    postgres_enabled=POSTGRES_ENABLED,
    parse_lat_lon_func=_parse_lat_lon,
    norm_coord_func=norm_coord,
    floor_from_name_func=_floor_from_name,
    expected_from_feats_func=expected_from_feats,
    fetch_feedback_pg_by_coord_func=_fetch_feedback_pg_by_coord,
    insert_feedback_pg_func=_insert_feedback_pg,
    get_feedback_summary_by_coord_func=get_feedback_summary_by_coord,
    get_feedbacks_by_coord_func=get_feedbacks_by_coord,
    compute_nowcast_ci_func=compute_nowcast_ci,
    last_n_history=LAST_N_HISTORY,
    feedback_lookback_limit=FEEDBACK_LOOKBACK_LIMIT,
    append_uid_lang_func=_append_uid_lang,
    user_lang_q_func=_user_lang_q,
    public_url=PUBLIC_URL,
    L_func=L,
    resolve_lang_func=resolve_lang,
    get_liff_status_id_func=_get_liff_status_id,
)
configure_status_routes(
    build_nearby_toilets_func=build_nearby_toilets,
    norm_coord_func=norm_coord,
    submit_status_update_func=submit_status_update,
    api_L_func=_api_L,
    get_liff_status_id_func=_get_liff_status_id,
    get_user_lang_func=get_user_lang,
)


# -----------------------------------------------------------------------------
# 5) Route registration
# -----------------------------------------------------------------------------
register_search_routes(app)
register_linebot_routes(app)
register_submission_routes(app)
register_admin_routes(app)
register_gap_routes(app)
register_nts_routes(app)
register_dashboard_routes(app)
register_usage_routes(app)
register_feedback_routes(app)
register_status_routes(app)
register_consent_routes(app)


# -----------------------------------------------------------------------------
# 6) Local development entry point
# -----------------------------------------------------------------------------
if __name__ == "__main__":
    threading.Thread(target=_self_keepalive_background, daemon=True).start()

    port = int(os.getenv("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
