"""Postgres persistent-store helpers extracted from app.py.

This module intentionally keeps the original function bodies unchanged.
Only the module boundary changed.
"""

import os
import json
import logging
import sqlite3
import threading
import time

from dotenv import load_dotenv

try:
    import psycopg2
    import psycopg2.extras
except Exception:
    psycopg2 = None

# Keep .env loading safe when this module is imported directly.
load_dotenv()

# === Persistent DB (Postgres) ===
DATABASE_URL = (os.getenv("DATABASE_URL") or "").strip()
POSTGRES_ENABLED = bool(DATABASE_URL and psycopg2 is not None)

def _pg_connect():
    if not POSTGRES_ENABLED:
        raise RuntimeError("Postgres not enabled")
    conn = psycopg2.connect(DATABASE_URL, sslmode="require")
    conn.autocommit = False
    return conn

def _persistent_store_ready() -> bool:
    return POSTGRES_ENABLED

def init_persistent_store():
    if not POSTGRES_ENABLED:
        if DATABASE_URL and psycopg2 is None:
            logging.warning("DATABASE_URL 已設定，但缺少 psycopg2；請安裝 psycopg2-binary")
        return

    try:
        conn = _pg_connect()
        cur = conn.cursor()

        # === Dashboard / analytics events ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS analytics_events (
            id BIGSERIAL PRIMARY KEY,
            user_id TEXT,
            event_type TEXT,
            result_count INTEGER DEFAULT 0,
            success INTEGER DEFAULT 1,
            response_time_ms INTEGER,
            lat DOUBLE PRECISION,
            lon DOUBLE PRECISION,
            area_name TEXT,
            query_text TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_created_at ON analytics_events(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_user_id ON analytics_events(user_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_event_type ON analytics_events(event_type)")

        # === User-added toilets ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS user_toilets (
            id BIGSERIAL PRIMARY KEY,
            user_id TEXT,
            name TEXT NOT NULL,
            address TEXT,
            lat DOUBLE PRECISION NOT NULL,
            lon DOUBLE PRECISION NOT NULL,
            level TEXT,
            floor_hint TEXT,
            entrance_hint TEXT,
            access_note TEXT,
            open_hours TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            updated_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)

        # 補齊已存在資料表的欄位（Neon 主儲存）
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS source TEXT DEFAULT 'neon'")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS verification_status TEXT DEFAULT 'pending'")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS verification_score INTEGER DEFAULT 0")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS verification_reason TEXT")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS verified_at TIMESTAMPTZ")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS verified_by TEXT")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS reject_reason TEXT")
        # === Auto Verification 1.0：使用者新增資料自動驗證 ===
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS auto_verification_score INTEGER DEFAULT 0")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS auto_verification_result TEXT DEFAULT 'pending'")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS auto_verification_reason TEXT")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS risk_flags TEXT")
        cur.execute("ALTER TABLE user_toilets ADD COLUMN IF NOT EXISTS similar_toilets_json TEXT")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_toilets_auto_result ON user_toilets(auto_verification_result)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_toilets_lat_lon ON user_toilets(lat, lon)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_toilets_created_at ON user_toilets(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_toilets_verification ON user_toilets(verification_status)")

        # === Maintenance Action 1.1：人工審核紀錄 / audit log ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS user_toilet_review_logs (
            id BIGSERIAL PRIMARY KEY,
            toilet_id BIGINT,
            toilet_name TEXT,
            old_status TEXT,
            new_status TEXT,
            old_score INTEGER,
            new_score INTEGER,
            auto_verification_score INTEGER,
            reviewer TEXT,
            action_reason TEXT,
            reject_reason TEXT,
            risk_flags TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_review_logs_toilet_id ON user_toilet_review_logs(toilet_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_review_logs_created_at ON user_toilet_review_logs(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_review_logs_new_status ON user_toilet_review_logs(new_status)")

        # === User consent ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS user_consent (
            user_id TEXT PRIMARY KEY,
            agreed BOOLEAN NOT NULL DEFAULT FALSE,
            display_name TEXT,
            source_type TEXT,
            user_agent TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            updated_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)

        # === Toilet status reports ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS toilet_status_reports (
            id BIGSERIAL PRIMARY KEY,
            user_id TEXT,
            display_name TEXT,
            lat DOUBLE PRECISION,
            lon DOUBLE PRECISION,
            status TEXT,
            note TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_status_reports_lat_lon ON toilet_status_reports(lat, lon)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_status_reports_created_at ON toilet_status_reports(created_at)")

        # === Toilet feedbacks ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS toilet_feedbacks (
            id BIGSERIAL PRIMARY KEY,
            name TEXT,
            address TEXT,
            rating INTEGER,
            toilet_paper TEXT,
            accessibility TEXT,
            time_of_use TEXT,
            comment TEXT,
            cleanliness_score DOUBLE PRECISION,
            lat DOUBLE PRECISION NOT NULL,
            lon DOUBLE PRECISION NOT NULL,
            floor_hint TEXT,
            user_id_hash TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW()
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_toilet_feedbacks_lat_lon ON toilet_feedbacks(lat, lon)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_toilet_feedbacks_created_at ON toilet_feedbacks(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_toilet_feedbacks_name ON toilet_feedbacks(name)")

        # === Favorites ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS favorites (
            id BIGSERIAL PRIMARY KEY,
            user_id TEXT NOT NULL,
            name TEXT NOT NULL,
            lat DOUBLE PRECISION NOT NULL,
            lon DOUBLE PRECISION NOT NULL,
            address TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            UNIQUE(user_id, name, lat, lon)
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_favorites_user_id ON favorites(user_id)")

        # === NTS 2.0：推薦結果紀錄 ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS recommendation_logs (
            id BIGSERIAL PRIMARY KEY,
            query_id TEXT NOT NULL,
            user_id_hash TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            user_lat DOUBLE PRECISION,
            user_lon DOUBLE PRECISION,
            rank INTEGER,
            toilet_id TEXT,
            toilet_name TEXT,
            distance_m DOUBLE PRECISION,
            distance_score DOUBLE PRECISION,
            trust_score DOUBLE PRECISION,
            info_score DOUBLE PRECISION,
            status_score DOUBLE PRECISION,
            nts_score DOUBLE PRECISION,
            source TEXT,
            verification_status TEXT
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_recommendation_logs_query_id ON recommendation_logs(query_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_recommendation_logs_user_id_hash ON recommendation_logs(user_id_hash)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_recommendation_logs_created_at ON recommendation_logs(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_recommendation_logs_toilet_id ON recommendation_logs(toilet_id)")
        cur.execute("ALTER TABLE recommendation_logs ADD COLUMN IF NOT EXISTS model_version TEXT DEFAULT 'nts_1_0'")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_recommendation_logs_model_version ON recommendation_logs(model_version)")

        # === NTS 2.0：使用者後續行為紀錄 ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS user_actions (
            id BIGSERIAL PRIMARY KEY,
            query_id TEXT,
            user_id_hash TEXT,
            toilet_id TEXT,
            action_type TEXT NOT NULL,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            extra_info TEXT
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_actions_query_id ON user_actions(query_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_actions_user_id_hash ON user_actions(user_id_hash)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_actions_created_at ON user_actions(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_user_actions_action_type ON user_actions(action_type)")

        # === NTS 2.0 Shadow Ranking：使用者看 2.0，後台同步記錄 1.0 排序 ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS recommendation_shadow_logs (
            id BIGSERIAL PRIMARY KEY,
            query_id TEXT NOT NULL,
            user_id_hash TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            user_lat DOUBLE PRECISION,
            user_lon DOUBLE PRECISION,
            production_model_version TEXT,
            shadow_model_version TEXT,
            rank INTEGER,
            toilet_id TEXT,
            toilet_name TEXT,
            distance_m DOUBLE PRECISION,
            distance_score DOUBLE PRECISION,
            trust_score DOUBLE PRECISION,
            info_score DOUBLE PRECISION,
            status_score DOUBLE PRECISION,
            nts_score DOUBLE PRECISION,
            source TEXT,
            verification_status TEXT
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_shadow_logs_query_id ON recommendation_shadow_logs(query_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_shadow_logs_toilet_id ON recommendation_shadow_logs(toilet_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_shadow_logs_created_at ON recommendation_shadow_logs(created_at)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_shadow_logs_models ON recommendation_shadow_logs(production_model_version, shadow_model_version)")

        # === NTS 2.0：資料來源查詢耗時與 OSM fallback 紀錄 ===
        cur.execute("""
        CREATE TABLE IF NOT EXISTS source_query_logs (
            id BIGSERIAL PRIMARY KEY,
            query_id TEXT,
            user_id_hash TEXT,
            model_version TEXT,
            created_at TIMESTAMPTZ DEFAULT NOW(),
            source_name TEXT NOT NULL,
            used_osm BOOLEAN DEFAULT FALSE,
            result_count INTEGER DEFAULT 0,
            elapsed_ms INTEGER,
            success BOOLEAN DEFAULT TRUE,
            reason TEXT,
            error_message TEXT
        )
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_source_query_logs_query_id ON source_query_logs(query_id)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_source_query_logs_model_version ON source_query_logs(model_version)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_source_query_logs_source_name ON source_query_logs(source_name)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_source_query_logs_created_at ON source_query_logs(created_at)")

        conn.commit()
        conn.close()
        logging.info("✅ Postgres persistent store ready")

    except Exception as e:
        logging.error(f"❌ init_persistent_store failed: {e}")

# === SQLite 本機快取與分析資料 ===
# 設定 SQLite 資料庫位置
# Keep the same runtime location as the old app.py: project_root/cache.db.
_BASE_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
CACHE_DB_PATH = os.path.join(_BASE_DIR, "cache.db")

def _get_db():
    """Return a SQLite connection to the app database (CACHE_DB_PATH).

    This is the single entry point for all SQLite access in the app
    (user_lang, search_log, ai_quota, request_cache, analytics_events).
    It was previously provided by a now-deleted initialization block;
    restored here so that set_user_lang / get_user_lang /
    handle_location / _ai_quota_check_and_inc work correctly.
    """
    conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn

# 建立 SQLite 連線

def create_cache_db():
    # Always open (not just when file is missing) so that new tables added
    # here are created on existing deployments that already have cache.db.
    conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
    cursor = conn.cursor()

    # Original request cache table
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS request_cache (
        query_key TEXT PRIMARY KEY,
        data TEXT,
        timestamp REAL
    )
    """)

    # User language preference — read/written by set_user_lang / get_user_lang.
    # Was missing after Google Sheets removal; restored here.
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS user_lang (
        user_id TEXT PRIMARY KEY,
        lang TEXT NOT NULL DEFAULT 'zh'
    )
    """)

    # Per-user location query log — written by handle_location,
    # read by get_search_count for the usage-review / badges pages.
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS search_log (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id TEXT,
        lat TEXT,
        lon TEXT,
        ts TEXT
    )
    """)
    cursor.execute(
        "CREATE INDEX IF NOT EXISTS idx_search_log_user_id ON search_log(user_id)"
    )

    # AI quota tracking — read/written by _ai_quota_check_and_inc.
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS ai_quota (
        key  TEXT NOT NULL,
        date TEXT NOT NULL,
        count INTEGER NOT NULL DEFAULT 0,
        PRIMARY KEY (key, date)
    )
    """)

    conn.commit()
    conn.close()

# === SQLite 參數強化（新增） ===
def tune_sqlite_for_concurrency():
    try:
        conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
        cur = conn.cursor()
        # 啟用 WAL 提高多執行緒讀/寫並行能力
        cur.execute("PRAGMA journal_mode=WAL;")
        # 設定 busy timeout（毫秒），避免短暫鎖衝突直接拋錯
        cur.execute("PRAGMA busy_timeout=3000;")
        conn.commit()
        conn.close()
        logging.info("✅ SQLite tuned: WAL + busy_timeout")
    except Exception as e:
        logging.warning(f"SQLite tuning skipped: {e}")

# 確認快取是否有效
def get_cached_data(query_key, ttl_sec=60*5):
    conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
    cursor = conn.cursor()
    cursor.execute("SELECT data, timestamp FROM request_cache WHERE query_key = ?", (query_key,))
    result = cursor.fetchone()
    conn.close()

    if result:
        data, timestamp = result
        if time.time() - timestamp < ttl_sec:
            return json.loads(data)
    return None

# 儲存快取
def save_cache(query_key, data):
    conn = sqlite3.connect(CACHE_DB_PATH, timeout=5, check_same_thread=False)
    cursor = conn.cursor()
    cursor.execute("""
    INSERT OR REPLACE INTO request_cache (query_key, data, timestamp)
    VALUES (?, ?, ?)
    """, (query_key, json.dumps(data), time.time()))
    conn.commit()
    conn.close()

ANALYTICS_DB_PATH = CACHE_DB_PATH

def create_analytics_tables():
    conn = sqlite3.connect(ANALYTICS_DB_PATH, timeout=5, check_same_thread=False)
    cur = conn.cursor()

    cur.execute("""
    CREATE TABLE IF NOT EXISTS analytics_events (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id TEXT,
        event_type TEXT,
        result_count INTEGER,
        success INTEGER,
        response_time_ms INTEGER,
        lat REAL,
        lon REAL,
        area_name TEXT,
        query_text TEXT,
        created_at TEXT
    )
    """)

    cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_created_at ON analytics_events(created_at)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_user_id ON analytics_events(user_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_analytics_event_type ON analytics_events(event_type)")

    conn.commit()
    conn.close()

# === Postgres startup init ===
_PERSISTENT_INIT_STARTED = False
_PERSISTENT_INIT_LOCK = threading.Lock()

def _start_persistent_store_init_background():
    global _PERSISTENT_INIT_STARTED
    with _PERSISTENT_INIT_LOCK:
        if _PERSISTENT_INIT_STARTED:
            return
        _PERSISTENT_INIT_STARTED = True

    def _job():
        try:
            init_persistent_store()
        except Exception as e:
            logging.error(f"❌ background init_persistent_store failed: {e}", exc_info=True)

    try:
        threading.Thread(target=_job, name="postgres-init", daemon=True).start()
        logging.info("⏳ Postgres init scheduled in background")
    except Exception as e:
        logging.error(f"❌ failed to start Postgres init thread: {e}", exc_info=True)

