import os
import uuid
import time
import logging
from difflib import SequenceMatcher
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeoutError

from flask import request

from config import LOC_QUERY_TIMEOUT_SEC, LOC_MAX_RESULTS
from core.utils import grid_coord, _parse_lat_lon, haversine
from core.database import get_cached_data, save_cache
from core.i18n import _api_L
from toilet.basic_ranking import sort_toilets
from toilet.scoring import sort_toilets_nts
from toilet.data_sources import query_public_csv_toilets, query_saved_toilets, query_overpass_toilets
from toilet.recommendation_logs import log_source_query

# === 共用執行緒池（避免每次臨時建立） ===
_pool = ThreadPoolExecutor(max_workers=2)


def _merge_and_dedupe_lists(*lists, dist_th=35, name_sim_th=0.55):
    all_pts = []
    for l in lists:
        if l:
            all_pts.extend(l)
    all_pts.sort(key=lambda x: x.get("distance", 1e9))

    merged = []
    buckets = {}
    # 0.0005 degrees is roughly 50m in Taiwan latitude, enough for a 35m duplicate threshold.
    grid_size = 0.0005

    def _bucket_key(lat, lon):
        return (int(float(lat) / grid_size), int(float(lon) / grid_size))

    def _neighbor_keys(key):
        x, y = key
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                yield (x + dx, y + dy)

    for p in all_pts:
        try:
            p_key = _bucket_key(p["lat"], p["lon"])
            candidate_pool = []
            for k in _neighbor_keys(p_key):
                candidate_pool.extend(buckets.get(k, []))
        except Exception:
            p_key = None
            candidate_pool = merged

        dup = False
        p_name = (p.get("name") or "").lower()
        for q in candidate_pool:
            try:
                near = haversine(p["lat"], p["lon"], q["lat"], q["lon"]) <= dist_th
            except Exception:
                near = False
            if not near:
                continue

            q_name = (q.get("name") or "").lower()
            sim = SequenceMatcher(None, p_name, q_name).ratio()
            if sim >= name_sim_th:
                dup = True
                break

        if not dup:
            merged.append(p)
            if p_key is not None:
                buckets.setdefault(p_key, []).append(p)
    return merged


def nearby_toilets():
    user_lat = request.args.get('lat')
    user_lon = request.args.get('lon')
    if not user_lat or not user_lon:
        return {"error": _api_L("缺少位置參數", "Missing location parameters")}, 400

    user_lat, user_lon = _parse_lat_lon(user_lat, user_lon)
    if user_lat is None or user_lon is None:
        return {"error": _api_L("位置參數錯誤", "Invalid location parameters")}, 400

    public_csv_toilets = query_public_csv_toilets(user_lat, user_lon, radius=500) or []
    saved_toilets = query_saved_toilets(user_lat, user_lon, radius=500) or []
    osm_toilets = query_overpass_toilets(user_lat, user_lon, radius=500) or []

    all_toilets = _merge_and_dedupe_lists(public_csv_toilets, saved_toilets, osm_toilets)
    sort_toilets(all_toilets)

    if not all_toilets:
        return {"message": _api_L("附近找不到廁所", "No nearby toilets found")}, 404
    return {"toilets": all_toilets}, 200


def build_nearby_toilets(uid, lat, lon, radius=500):
    # 預設使用 NTS 排序；若要回到純距離排序，可設定 TOILET_SORT_ALGO=distance_only
    algo = os.getenv("TOILET_SORT_ALGO", "nts_score").strip().lower()
    model_version = os.getenv("NTS_MODEL_VERSION", "nts_1_0").strip() or "nts_1_0"

    # OSM fallback 策略：先查本地/Neon 資料，不足再查 OSM
    try:
        osm_fallback_min = int(os.getenv("OSM_FALLBACK_MIN_RESULTS", "2"))
    except Exception:
        osm_fallback_min = 2
    osm_fallback_min = max(0, osm_fallback_min)
    osm_enabled = os.getenv("OSM_FALLBACK_ENABLE", "1") == "1"

    # === Grid cache key（加入 algo/model_version/OSM 策略，避免切換後吃到舊快取）===
    lat_g = grid_coord(lat)
    lon_g = grid_coord(lon)
    query_key = f"nearby:{algo}:{model_version}:osm{int(osm_enabled)}:min{osm_fallback_min}:{lat_g},{lon_g},{radius}"

    cached = get_cached_data(query_key)
    if cached:
        logging.debug(f"[cache hit] nearby {query_key}")
        return cached

    query_id_for_source = "SRC_" + uuid.uuid4().hex[:16]
    total_start = time.time()
    csv_res, saved_res, osm_res = [], [], []

    # === 第一階段：只查本地/Neon/政府資料，不先打 OSM，降低延遲 ===
    futures = []
    try:
        futures.append(("csv", _pool.submit(query_public_csv_toilets, lat, lon, radius)))
        futures.append(("saved", _pool.submit(query_saved_toilets, lat, lon, radius)))

        for name, fut in futures:
            source_start = time.time()
            try:
                res = fut.result(timeout=LOC_QUERY_TIMEOUT_SEC)
                elapsed_ms = int((time.time() - source_start) * 1000)
                if name == "csv":
                    csv_res = res or []
                else:
                    saved_res = res or []
                log_source_query(
                    query_id=query_id_for_source,
                    uid=uid,
                    source_name=name,
                    result_count=len(res or []),
                    elapsed_ms=elapsed_ms,
                    success=True,
                    reason="primary_local_search",
                    used_osm=False
                )
            except FuturesTimeoutError:
                elapsed_ms = int((time.time() - source_start) * 1000)
                logging.warning(f"{name} 查詢逾時")
                log_source_query(query_id_for_source, uid, name, 0, elapsed_ms, False, "timeout", "timeout", False)
            except Exception as e:
                elapsed_ms = int((time.time() - source_start) * 1000)
                logging.warning(f"{name} 查詢失敗: {e}")
                log_source_query(query_id_for_source, uid, name, 0, elapsed_ms, False, "error", str(e), False)
    finally:
        for _, fut in futures:
            if not fut.done():
                fut.cancel()

    quick_no_osm = _merge_and_dedupe_lists(csv_res, saved_res)

    # === 第二階段：候選不足才查 OSM ===
    used_osm = False
    if osm_enabled and len(quick_no_osm) < osm_fallback_min:
        used_osm = True
        source_start = time.time()
        try:
            osm_res = query_overpass_toilets(lat, lon, radius) or []
            elapsed_ms = int((time.time() - source_start) * 1000)
            log_source_query(
                query_id=query_id_for_source,
                uid=uid,
                source_name="osm",
                result_count=len(osm_res),
                elapsed_ms=elapsed_ms,
                success=True,
                reason=f"fallback_candidates_lt_{osm_fallback_min}",
                used_osm=True
            )
        except Exception as e:
            elapsed_ms = int((time.time() - source_start) * 1000)
            logging.warning(f"osm fallback 查詢失敗: {e}")
            log_source_query(query_id_for_source, uid, "osm", 0, elapsed_ms, False, f"fallback_candidates_lt_{osm_fallback_min}", str(e), True)
    else:
        # 記錄 skipped，之後可統計省下多少 OSM 查詢
        log_source_query(
            query_id=query_id_for_source,
            uid=uid,
            source_name="osm",
            result_count=0,
            elapsed_ms=0,
            success=True,
            reason=f"skipped_candidates_gte_{osm_fallback_min}" if osm_enabled else "osm_disabled",
            used_osm=False
        )

    quick = _merge_and_dedupe_lists(csv_res, saved_res, osm_res)

    if algo == "distance_only":
        sort_toilets(quick)
    else:
        quick = sort_toilets_nts(quick)

    result = quick[:LOC_MAX_RESULTS]

    total_elapsed_ms = int((time.time() - total_start) * 1000)
    log_source_query(
        query_id=query_id_for_source,
        uid=uid,
        source_name="total",
        result_count=len(result),
        elapsed_ms=total_elapsed_ms,
        success=True,
        reason="used_osm" if used_osm else "without_osm",
        used_osm=used_osm
    )

    # === 寫入 cache（Grid cache）===
    save_cache(query_key, result)

    return result


def register_search_routes(app):
    app.add_url_rule("/nearby_toilets", endpoint="nearby_toilets", view_func=nearby_toilets, methods=["GET"])

