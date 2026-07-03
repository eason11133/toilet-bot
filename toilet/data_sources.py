import os
import csv
import logging
import requests
import heapq
import math
import threading
import time
from urllib.parse import quote

from config import LOC_MAX_RESULTS
from core.database import POSTGRES_ENABLED, _pg_connect, psycopg2
from core.utils import _in_bbox, haversine, norm_coord
from toilet.floor import _floor_from_tags, _floor_from_name
from toilet.enrichment import enrich_nearby_places

# === 檔案 ===
DATA_DIR = os.path.join(os.getcwd(), "data")
TOILETS_FILE_PATH = os.path.join(DATA_DIR, "public_toilets.csv")

# public_toilets.csv is in the hot path for every location query.
# Cache it in memory and reload only when the file mtime changes.
_PUBLIC_CSV_CACHE = {"mtime": None, "rows": []}
_PUBLIC_CSV_CACHE_LOCK = threading.Lock()


def query_overpass_toilets(lat, lon, radius=500):
    overall_deadline = time.time() + 8.0

    def _left():
        return max(1.0, overall_deadline - time.time())

    ua_email = os.getenv("CONTACT_EMAIL", "you@example.com")
    headers = {"User-Agent": f"ToiletBot/1.0 (+{ua_email})"}
    endpoints = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.openstreetmap.ru/api/interpreter",
    ]

    # 讀取限制值
    try:
        max_items = int(os.getenv("OVERPASS_MAX_ITEMS", "80"))
    except Exception:
        max_items = 80
    try:
        enrich_on = int(os.getenv("ENRICH_ENABLE", "0")) == 1
    except Exception:
        enrich_on = False

    # 先小半徑再原半徑
    for r in (300, radius):
        if time.time() >= overall_deadline:
            break

        query = f"""
        [out:json][timeout:25];
        (
          node["amenity"="toilets"](around:{r},{lat},{lon});
          way["amenity"="toilets"](around:{r},{lat},{lon});
          relation["amenity"="toilets"](around:{r},{lat},{lon});
        );
        out center tags;
        """

        last_err = None
        for idx, url in enumerate(endpoints):
            if time.time() >= overall_deadline:
                break
            try:
                resp = requests.post(
                    url,
                    data=query,
                    headers=headers,
                    timeout=min(8, _left())
                )
                ctype = (resp.headers.get("Content-Type") or "").lower()
                if resp.status_code != 200 or "json" not in ctype:
                    last_err = RuntimeError(f"overpass non-json {resp.status_code}")
                    continue

                data = resp.json()
                elements = data.get("elements", [])

                toilets = []

                # 最多處理 4 * max_items（避免 elements 太多）
                hard_cap = max(40, max_items * 4)
                processed = 0

                for elem in elements:
                    if processed >= hard_cap:
                        break
                    processed += 1

                    if "center" in elem:
                        t_lat = elem["center"].get("lat")
                        t_lon = elem["center"].get("lon")
                    elif elem.get("type") == "node":
                        t_lat = elem.get("lat")
                        t_lon = elem.get("lon")
                    else:
                        continue

                    if t_lat is None or t_lon is None:
                        continue

                    if not _in_bbox(t_lat, t_lon, lat, lon, r):
                        continue

                    tags = elem.get("tags", {}) or {}
                    name = tags.get("name", "無名稱")
                    address = (
                        tags.get("addr:full")
                        or tags.get("addr:street")
                        or ""
                    )

                    floor_hint = _floor_from_tags(tags) or _floor_from_name(name)

                    try:
                        dist = haversine(
                            float(lat), float(lon),
                            float(t_lat), float(t_lon)
                        )
                    except Exception:
                        continue

                    if dist > r:
                        continue

                    toilets.append({
                        "name": name,
                        "lat": float(norm_coord(t_lat)),
                        "lon": float(norm_coord(t_lon)),
                        "address": address,
                        "distance": dist,
                        "type": "osm",
                        "floor_hint": floor_hint,
                        "level": tags.get("level") or tags.get("addr:floor") or "",
                        "open_hours": tags.get("opening_hours") or "",
                        "entrance_hint": tags.get("entrance") or "",
                    })

                if not toilets:
                    continue

                # enrich（保持你原本邏輯，不動）
                if enrich_on:
                    try:
                        nearby_named = enrich_nearby_places(lat, lon, radius=500)
                        if nearby_named:
                            for t in toilets:
                                if (not t.get("name")) or t["name"] == "無名稱":
                                    best = None
                                    best_d = 61.0
                                    for p in nearby_named:
                                        d = haversine(
                                            t["lat"], t["lon"],
                                            p["lat"], p["lon"]
                                        )
                                        if d < best_d:
                                            best_d = d
                                            best = p
                                    if best:
                                        t["place_hint"] = best["name"]
                    except Exception:
                        pass

                toilets = heapq.nsmallest(
                    max_items,
                    toilets,
                    key=lambda x: x["distance"]
                )
                return toilets

            except Exception as e:
                last_err = e
                logging.warning(f"Overpass API 查詢失敗（endpoint {idx}）: {e}")

        logging.warning(f"Overpass 半徑 {r} 失敗：{last_err}")

    return []

def query_saved_toilets(user_lat, user_lon, radius=500):
    if not POSTGRES_ENABLED:
        return []

    heap = []
    limit = max(LOC_MAX_RESULTS * 8, 60)
    try:
        user_lat = float(user_lat)
        user_lon = float(user_lon)
        dlat = radius / 111000.0
        dlon = radius / (111000.0 * max(0.1, math.cos(math.radians(user_lat))))
        min_lat, max_lat = user_lat - dlat, user_lat + dlat
        min_lon, max_lon = user_lon - dlon, user_lon + dlon

        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT user_id, name, address, lat, lon, level, floor_hint, entrance_hint, access_note, open_hours, created_at
            FROM user_toilets
            WHERE lat BETWEEN %s AND %s
              AND lon BETWEEN %s AND %s
              AND COALESCE(verification_status, 'pending') <> 'rejected'
            ORDER BY created_at DESC
            LIMIT 500
        """, (min_lat, max_lat, min_lon, max_lon))
        rows = cur.fetchall()
        conn.close()

        for row in rows:
            try:
                t_lat = float(row.get("lat"))
                t_lon = float(row.get("lon"))
            except Exception:
                continue
            if not _in_bbox(t_lat, t_lon, user_lat, user_lon, radius):
                continue
            dist = haversine(user_lat, user_lon, t_lat, t_lon)
            if dist > radius:
                continue
            item = {
                "name": (row.get("name") or "無名稱").strip(),
                "lat": float(norm_coord(t_lat)),
                "lon": float(norm_coord(t_lon)),
                "address": (row.get("address") or "").strip(),
                "distance": dist,
                "type": "user_db",
                "grade": "使用者新增",
                "category": "使用者補充",
                "floor_hint": (row.get("floor_hint") or _floor_from_name(row.get("name") or "")),
                "entrance_hint": row.get("entrance_hint") or "",
                "access_note": row.get("access_note") or "",
                "open_hours": row.get("open_hours") or "",
            }
            heapq.heappush(heap, (-dist, id(item), item))
            if len(heap) > limit:
                heapq.heappop(heap)
    except Exception as e:
        logging.warning(f"query_saved_toilets failed: {e}")
        return []

    return [item for _, _, item in sorted(heap, key=lambda x: -x[0])]

def _load_public_csv_rows_cached():
    """Load public_toilets.csv once and refresh only when the file changes."""
    if not os.path.exists(TOILETS_FILE_PATH):
        return []

    try:
        mtime = os.path.getmtime(TOILETS_FILE_PATH)
    except Exception as e:
        logging.error(f"讀 public_toilets.csv mtime 失敗：{e}")
        return []

    cached_rows = _PUBLIC_CSV_CACHE.get("rows") or []
    if _PUBLIC_CSV_CACHE.get("mtime") == mtime:
        return cached_rows

    with _PUBLIC_CSV_CACHE_LOCK:
        cached_rows = _PUBLIC_CSV_CACHE.get("rows") or []
        if _PUBLIC_CSV_CACHE.get("mtime") == mtime:
            return cached_rows

        try:
            with open(TOILETS_FILE_PATH, "r", encoding="utf-8-sig", newline="") as f:
                rows = list(csv.DictReader(f))
            _PUBLIC_CSV_CACHE["mtime"] = mtime
            _PUBLIC_CSV_CACHE["rows"] = rows
            logging.info(f"✅ public_toilets.csv cached: {len(rows)} rows")
            return rows
        except Exception as e:
            logging.error(f"讀 public_toilets.csv 失敗：{e}")
            return cached_rows

def query_public_csv_toilets(user_lat, user_lon, radius=500):
    rows = _load_public_csv_rows_cached()
    if not rows:
        return []

    heap = []
    limit = LOC_MAX_RESULTS

    try:
        for row in rows:
            try:
                t_lat = float(row.get("latitude"))
                t_lon = float(row.get("longitude"))
            except Exception:
                continue

            if not _in_bbox(t_lat, t_lon, user_lat, user_lon, radius):
                continue

            dist = haversine(user_lat, user_lon, t_lat, t_lon)
            if dist > radius:
                continue

            name = (row.get("name") or "無名稱").strip()
            addr = (row.get("address") or "").strip()
            floor_hint = _floor_from_name(name)

            item = {
                "name": name,
                "lat": float(norm_coord(t_lat)),
                "lon": float(norm_coord(t_lon)),
                "address": addr,
                "distance": dist,
                "type": "public_csv",
                "grade": row.get("grade", ""),
                "category": row.get("type2", ""),
                "floor_hint": floor_hint,
            }

            heapq.heappush(heap, (-dist, id(item), item))
            if len(heap) > limit:
                heapq.heappop(heap)

    except Exception as e:
        logging.error(f"查詢 public_toilets.csv 快取資料失敗：{e}")
        return []

    return [item for _, _, item in sorted(heap, key=lambda x: -x[0])]

def geocode_address(address):
    try:
        ua_email = os.getenv("CONTACT_EMAIL", "school-toilet-bot@gmail.com")

        url = (
            "https://nominatim.openstreetmap.org/search"
            f"?format=json&q={quote(address)}"
        )

        headers = {
            "User-Agent": f"ToiletBot/1.0 (+{ua_email})"
        }

        resp = requests.get(url, headers=headers, timeout=10)

        # ① HTTP 狀態碼檢查
        if resp.status_code != 200:
            logging.error(
                f"地址轉經緯度失敗: HTTP {resp.status_code}, text={resp.text[:200]}"
            )
            return None, None

        # ② 空回應檢查
        if not resp.text or not resp.text.strip():
            logging.error("地址轉經緯度失敗: 回傳內容為空")
            return None, None

        # ③ JSON 解析保護
        try:
            data = resp.json()
        except Exception:
            logging.error(
                f"地址轉經緯度失敗: 非 JSON 回應, text={resp.text[:200]}"
            )
            return None, None

        # ④ 資料內容檢查
        if not data:
            logging.warning(f"地址轉經緯度失敗: 查無結果 address={address}")
            return None, None

        # ⑤ 正常回傳
        lat = float(data[0].get("lat"))
        lon = float(data[0].get("lon"))
        return lat, lon

    except Exception as e:
        logging.error(f"地址轉經緯度例外錯誤: {e}", exc_info=True)

    return None, None
