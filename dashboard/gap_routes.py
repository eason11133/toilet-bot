import os
import logging
import threading
import time

from flask import request, jsonify, render_template
from core.memory import log_memory

from dashboard.gap_analysis import (
    _gap_cache_get,
    _gap_cache_set,
    _gap_latest_event_id,
    _build_gap_summary,
    _GAP_SUMMARY_CACHE_TTL,
    _GAP_SUMMARY_STALE_TTL,
    _GAP_VALID_LAT_MIN,
    _GAP_VALID_LAT_MAX,
    _GAP_VALID_LON_MIN,
    _GAP_VALID_LON_MAX,
)

_GAP_BUILD_LOCK = threading.Lock()
_GAP_REFRESHING = set()
_GAP_REFRESHING_LOCK = threading.Lock()


def _gap_snapshot_age_seconds(data):
    try:
        return max(0.0, time.time() - float(data.get("generated_epoch") or 0))
    except Exception:
        return float("inf")


def _start_gap_refresh(cache_key, range_key, anchor_date):
    """Start at most one refresh per cache key in this worker."""
    with _GAP_REFRESHING_LOCK:
        if cache_key in _GAP_REFRESHING:
            return False
        _GAP_REFRESHING.add(cache_key)

    def worker():
        log_memory("gap_background_before", range=range_key)
        try:
            with _GAP_BUILD_LOCK:
                data = _build_gap_summary(range_key, anchor_date)
                data["cached"] = False
                _gap_cache_set(cache_key, data)
        except Exception as exc:
            logging.error("gap background refresh failed: %s", exc, exc_info=True)
        finally:
            with _GAP_REFRESHING_LOCK:
                _GAP_REFRESHING.discard(cache_key)
            log_memory("gap_background_after", range=range_key)

    threading.Thread(
        target=worker,
        name=f"gap-refresh-{range_key}",
        daemon=True,
    ).start()
    return True

# === Gap dashboard routes ===
def dashboard_gap_page():
    """公共設施需求缺口分析頁。"""
    return render_template("gap.html")


def api_gap_summary():
    """公共設施需求缺口分析 API：去重、群聚、建議設點。"""
    log_memory("gap_endpoint_before")
    try:
        range_key = (request.args.get("range") or "all").strip()
        if range_key not in ("all", "1h", "1d", "7d", "30d", "1y"):
            range_key = "all"
        anchor_date = (request.args.get("anchor_date") or "").strip() or None
        force = (
            (request.args.get("force") or "0").strip() == "1"
            or (request.args.get("refresh") or "0").strip() == "1"
        )

        # Bump when calculation semantics change so old persisted summaries are not served.
        cache_key = (
            f"v253_snapshot_swr:{range_key}:{anchor_date or ''}:"
            f"{os.getenv('GAP_CLUSTER_OUTPUT_LIMIT', '0')}:"
            f"{os.getenv('GAP_HOTSPOT_OUTPUT_LIMIT', '1000')}:"
            f"{os.getenv('GAP_MAX_EVENTS', '20000')}:"
            f"{_GAP_VALID_LAT_MIN},{_GAP_VALID_LAT_MAX},{_GAP_VALID_LON_MIN},{_GAP_VALID_LON_MAX}"
        )
        cached = _gap_cache_get(cache_key, ttl_sec=_GAP_SUMMARY_STALE_TTL)
        if cached is not None:
            age_seconds = _gap_snapshot_age_seconds(cached)
            latest_event_id = _gap_latest_event_id(range_key, anchor_date)
            has_new_data = (
                latest_event_id is not None
                and int(latest_event_id) > int(cached.get("source_watermark") or 0)
            )
            should_refresh = force or (
                age_seconds >= _GAP_SUMMARY_CACHE_TTL and has_new_data
            )
            refresh_started = _start_gap_refresh(cache_key, range_key, anchor_date) if should_refresh else False
            out = dict(cached)
            out["cached"] = True
            out["snapshot_age_seconds"] = round(age_seconds, 1)
            out["new_data_available"] = bool(has_new_data)
            out["refreshing"] = bool(refresh_started or cache_key in _GAP_REFRESHING)
            log_memory("gap_endpoint_after", cached=True, refreshing=out["refreshing"])
            return jsonify(out)

        # First build only: no snapshot exists yet, so build synchronously once.
        with _GAP_BUILD_LOCK:
            cached = _gap_cache_get(cache_key, ttl_sec=_GAP_SUMMARY_STALE_TTL)
            if cached is not None:
                out = dict(cached)
                out["cached"] = True
                log_memory("gap_endpoint_after", cached=True, waited=True)
                return jsonify(out)
            data = _build_gap_summary(range_key, anchor_date)
            data["cached"] = False
            _gap_cache_set(cache_key, data)
        log_memory("gap_endpoint_after", cached=False)
        return jsonify(data)
    except Exception as e:
        logging.error(f"/api/gap-summary failed: {e}", exc_info=True)
        return jsonify({"ok": False, "error": str(e)}), 500


def register_gap_routes(app):
    app.add_url_rule('/dashboard/gap', endpoint='dashboard_gap_page', view_func=dashboard_gap_page, methods=['GET'])
    app.add_url_rule('/api/gap-summary', endpoint='api_gap_summary', view_func=api_gap_summary, methods=['GET'])
