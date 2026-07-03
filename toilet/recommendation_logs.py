import os
import logging

POSTGRES_ENABLED = False
_pg_connect = None
mask_user_id = None
compute_nts_score = None
sort_toilets_nts_1_0 = None
_make_toilet_id = None

def configure_recommendation_logs(
    postgres_enabled,
    pg_connect,
    mask_user_id_func,
    compute_nts_score_func,
    sort_toilets_nts_1_0_func,
    make_toilet_id_func,
):
    global POSTGRES_ENABLED, _pg_connect, mask_user_id, compute_nts_score, sort_toilets_nts_1_0, _make_toilet_id
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    mask_user_id = mask_user_id_func
    compute_nts_score = compute_nts_score_func
    sort_toilets_nts_1_0 = sort_toilets_nts_1_0_func
    _make_toilet_id = make_toilet_id_func

def log_recommendation_results(query_id, uid, user_lat, user_lon, toilets, limit=5):
    """
    記錄這次系統推薦了哪些結果。
    """
    if not POSTGRES_ENABLED:
        return

    try:
        rows = []
        user_id_hash = mask_user_id(uid)
        model_version = os.getenv("NTS_MODEL_VERSION", "nts_1_0").strip() or "nts_1_0"

        for rank, t in enumerate((toilets or [])[:limit], start=1):
            # 確保 NTS 四個節點分數存在
            try:
                if "nts_score" not in t:
                    compute_nts_score(t)
            except Exception:
                pass

            rows.append((
                query_id,
                user_id_hash,
                float(user_lat),
                float(user_lon),
                rank,
                _make_toilet_id(t),
                t.get("name") or "",
                float(t.get("distance", 0) or 0),
                float(t.get("distance_score", 0) or 0),
                float(t.get("trust_score", 0) or 0),
                float(t.get("info_score", 0) or 0),
                float(t.get("status_score", 0) or 0),
                float(t.get("nts_score", 0) or 0),
                t.get("source") or t.get("type") or "",
                t.get("verification_status") or "",
                model_version
            ))

        if not rows:
            return

        conn = _pg_connect()
        cur = conn.cursor()
        cur.executemany("""
            INSERT INTO recommendation_logs (
                query_id, user_id_hash, user_lat, user_lon,
                rank, toilet_id, toilet_name, distance_m,
                distance_score, trust_score, info_score, status_score,
                nts_score, source, verification_status, model_version
            )
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, rows)
        conn.commit()
        conn.close()

    except Exception as e:
        logging.warning(f"log_recommendation_results failed: {e}", exc_info=True)


def log_shadow_recommendation_results(query_id, uid, user_lat, user_lon, toilets, limit=5):
    """
    Shadow mode：實際給使用者看的是 production model（例如 Trust Score 2.0），
    但後台用同一批已取得的回傳候選結果，偷偷以 NTS 1.0 baseline 重新排序並記錄。
    不重新查 CSV / Neon / OSM，只重算分數與排序，因此效率影響很小。
    """
    if not POSTGRES_ENABLED:
        return
    if os.getenv("SHADOW_NTS_ENABLE", "1") != "1":
        return
    production_model_version = os.getenv("NTS_MODEL_VERSION", "nts_1_0").strip() or "nts_1_0"
    shadow_model_version = os.getenv("SHADOW_MODEL_VERSION", "nts_1_0").strip() or "nts_1_0"
    if production_model_version == shadow_model_version:
        return
    try:
        shadow_sorted = sort_toilets_nts_1_0(toilets or [])
        if not shadow_sorted:
            return
        rows = []
        user_id_hash = mask_user_id(uid)
        for rank, t in enumerate(shadow_sorted[:limit], start=1):
            rows.append((
                query_id, user_id_hash, float(user_lat), float(user_lon),
                production_model_version, shadow_model_version, rank,
                _make_toilet_id(t), t.get("name") or "",
                float(t.get("distance", 0) or 0),
                float(t.get("distance_score", 0) or 0),
                float(t.get("trust_score", 0) or 0),
                float(t.get("info_score", 0) or 0),
                float(t.get("status_score", 0) or 0),
                float(t.get("nts_score", 0) or 0),
                t.get("source") or t.get("type") or "",
                t.get("verification_status") or ""
            ))
        conn = _pg_connect()
        cur = conn.cursor()
        cur.executemany("""
            INSERT INTO recommendation_shadow_logs (
                query_id, user_id_hash, user_lat, user_lon,
                production_model_version, shadow_model_version,
                rank, toilet_id, toilet_name, distance_m,
                distance_score, trust_score, info_score, status_score,
                nts_score, source, verification_status
            )
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, rows)
        conn.commit()
        conn.close()
    except Exception as e:
        logging.warning(f"log_shadow_recommendation_results failed: {e}", exc_info=True)


def log_user_action(query_id, uid, toilet_id, action_type, extra_info=""):
    """
    記錄使用者後續行為，例如點導航、回報問題、加入最愛。
    """
    if not POSTGRES_ENABLED:
        return

    try:
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO user_actions (
                query_id, user_id_hash, toilet_id, action_type, extra_info
            )
            VALUES (%s, %s, %s, %s, %s)
        """, (
            query_id or "",
            mask_user_id(uid),
            str(toilet_id or ""),
            action_type,
            extra_info or ""
        ))
        conn.commit()
        conn.close()

    except Exception as e:
        logging.warning(f"log_user_action failed: {e}", exc_info=True)


def log_source_query(query_id, uid, source_name, result_count=0, elapsed_ms=None, success=True, reason="", error_message="", used_osm=False):
    """
    記錄各資料來源查詢耗時與 OSM fallback 使用情形。
    用來比較：不用 OSM / 使用 OSM 的次數與耗時。
    """
    if not POSTGRES_ENABLED:
        return

    try:
        model_version = os.getenv("NTS_MODEL_VERSION", "nts_1_0").strip() or "nts_1_0"
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO source_query_logs (
                query_id, user_id_hash, model_version, source_name,
                used_osm, result_count, elapsed_ms, success, reason, error_message
            )
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, (
            query_id or "",
            mask_user_id(uid),
            model_version,
            source_name,
            bool(used_osm),
            int(result_count or 0),
            int(elapsed_ms) if elapsed_ms is not None else None,
            bool(success),
            reason or "",
            str(error_message or "")[:500]
        ))
        conn.commit()
        conn.close()
    except Exception as e:
        logging.warning(f"log_source_query failed: {e}", exc_info=True)

