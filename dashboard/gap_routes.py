import os
import logging
import threading

from flask import request, jsonify, render_template
from core.memory import log_memory

from dashboard.gap_analysis import (
    _gap_cache_get,
    _gap_cache_set,
    _build_gap_summary,
    _GAP_VALID_LAT_MIN,
    _GAP_VALID_LAT_MAX,
    _GAP_VALID_LON_MIN,
    _GAP_VALID_LON_MAX,
)

_GAP_BUILD_LOCK = threading.Lock()

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

        # Cache key version bumped because global/outlier coordinates are now excluded from the research map.
        cache_key = (
            f"v251_memory_bounded:{range_key}:{anchor_date or ''}:"
            f"{os.getenv('GAP_CLUSTER_OUTPUT_LIMIT', '500')}:"
            f"{os.getenv('GAP_HOTSPOT_OUTPUT_LIMIT', '1000')}:"
            f"{os.getenv('GAP_MAX_EVENTS', '20000')}:"
            f"{_GAP_VALID_LAT_MIN},{_GAP_VALID_LAT_MAX},{_GAP_VALID_LON_MIN},{_GAP_VALID_LON_MAX}"
        )
        if not force:
            cached = _gap_cache_get(cache_key)
            if cached is not None:
                out = dict(cached)
                out["cached"] = True
                log_memory("gap_endpoint_after", cached=True)
                return jsonify(out)

        # A gthread worker can receive multiple expensive refreshes at once.
        # Serialize builds so their large temporary maps cannot multiply RSS.
        with _GAP_BUILD_LOCK:
            if not force:
                cached = _gap_cache_get(cache_key)
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
