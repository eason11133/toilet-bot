"""General utility helpers extracted from app.py.

This module intentionally contains only pure helper functions with no Flask,
LINE, database, or project-data side effects. Function bodies are preserved
from the previous app.py baseline.
"""

import hashlib
import html
import logging
import math
from math import radians, cos, sin, asin, sqrt


def grid_coord(v, g=0.0005):
    """
    座標格點化：
    g=0.0005 ≈ 50 公尺
    """
    try:
        return round(float(v) / g) * g
    except Exception:
        return v


def _in_bbox(lat, lon, clat, clon, radius_m):
    """
    粗略矩形篩選，先擋掉不可能在半徑內的點
    """
    try:
        lat = float(lat); lon = float(lon)
        clat = float(clat); clon = float(clon)
    except Exception:
        return False

    dlat = radius_m / 111000.0
    dlon = radius_m / (111000.0 * math.cos(math.radians(clat)))
    return (
        clat - dlat <= lat <= clat + dlat and
        clon - dlon <= lon <= clon + dlon
    )


def mask_user_id(uid):
    if not uid:
        return None
    return hashlib.sha256(str(uid).encode()).hexdigest()[:10]


def norm_coord(x, ndigits=6):
    try:
        return f"{round(float(x), ndigits):.{ndigits}f}"
    except:
        return str(x)


def safe_html(s):
    return html.escape(s or "")


def _parse_lat_lon(lat_s, lon_s):
    try:
        lat = float(str(lat_s).strip())
        lon = float(str(lon_s).strip())
    except Exception:
        return None, None
    if abs(lat) > 90 and abs(lon) <= 90:
        lat, lon = lon, lat
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        return None, None
    return lat, lon


def haversine(lat1, lon1, lat2, lon2):
    try:
        lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
        dlat = lat2 - lat1
        dlon = lon2 - lon1
        a = sin(dlat / 2) ** 2 + cos(lat1) * cos(lat2) * sin(dlon / 2) ** 2
        return 2 * asin(sqrt(a)) * 6371000  # m
    except Exception as e:
        logging.error(f"計算距離失敗: {e}")
        return float("inf")
