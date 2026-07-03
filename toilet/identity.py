"""Toilet recommendation identity helpers.

Extracted from app.py without behavior changes.
"""

import hashlib
import uuid

from core.utils import norm_coord


def make_query_id():
    return "Q_" + uuid.uuid4().hex[:16]


def _make_toilet_id(t):
    """
    給沒有固定 id 的政府/OSM 資料一個穩定識別碼。
    user_toilets 若本來有 id，就優先用 id。
    """
    raw_id = t.get("id")
    if raw_id not in (None, ""):
        return str(raw_id)

    name = str(t.get("name") or "")
    lat = norm_coord(t.get("lat"))
    lon = norm_coord(t.get("lon"))
    source = str(t.get("source") or t.get("type") or "")
    key = f"{source}|{name}|{lat}|{lon}"
    return hashlib.sha256(key.encode("utf-8")).hexdigest()[:16]
