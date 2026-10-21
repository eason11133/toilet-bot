"""Current toilet-supply reconciliation for the demand-gap dashboard.

Demand is historical and must not be rewritten when facilities change.  This
module adds a separate, current-supply view that can lower the priority of a
demand circle after government or approved user data improves.
"""

import csv
import hashlib
import math
import os


PUBLIC_TOILETS_PATH = os.path.join(
    os.path.dirname(os.path.dirname(__file__)), "data", "public_toilets.csv"
)


def _safe_float(value):
    try:
        value = float(value)
        return value if math.isfinite(value) else None
    except (TypeError, ValueError):
        return None


def _haversine_m(lat1, lon1, lat2, lon2):
    radius = 6371000.0
    p1, p2 = math.radians(float(lat1)), math.radians(float(lat2))
    dp = math.radians(float(lat2) - float(lat1))
    dl = math.radians(float(lon2) - float(lon1))
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return radius * 2 * math.atan2(math.sqrt(a), math.sqrt(max(0.0, 1 - a)))


def current_supply_watermark(postgres_enabled=False, pg_connect=None):
    """Return a cheap version token for government/user/status supply data."""
    parts = []
    try:
        stat = os.stat(PUBLIC_TOILETS_PATH)
        parts.append(f"government:{stat.st_size}:{stat.st_mtime_ns}")
    except OSError:
        parts.append("government:missing")

    if postgres_enabled and pg_connect:
        conn = None
        try:
            conn = pg_connect()
            cur = conn.cursor()
            cur.execute("""
                SELECT COUNT(*), COALESCE(MAX(updated_at)::text, ''),
                       COUNT(*) FILTER (WHERE verification_status = 'approved')
                FROM user_toilets
            """)
            row = cur.fetchone() or (0, "", 0)
            parts.append(f"users:{row[0]}:{row[1]}:{row[2]}")
            cur.execute("""
                SELECT COUNT(*), COALESCE(MAX(id), 0), COALESCE(MAX(created_at)::text, '')
                FROM toilet_status_reports
            """)
            row = cur.fetchone() or (0, 0, "")
            parts.append(f"status:{row[0]}:{row[1]}:{row[2]}")
        except Exception:
            # Do not make the dashboard unavailable merely because its optional
            # supply watermark cannot be read during a transient DB failure.
            parts.append("database:unavailable")
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
    else:
        parts.append("database:disabled")

    return hashlib.sha256("|".join(parts).encode("utf-8")).hexdigest()[:20]


class SupplyIndex:
    """Small spatial bucket index containing only coordinates and source type."""

    def __init__(self, cell_m=500):
        self.cell_deg = max(float(cell_m) / 111000.0, 0.0001)
        self.buckets = {}
        self.total = 0

    def add(self, lat, lon, source):
        lat = _safe_float(lat)
        lon = _safe_float(lon)
        if lat is None or lon is None or not (18 <= lat <= 27 and 117 <= lon <= 123):
            return
        key = (math.floor(lat / self.cell_deg), math.floor(lon / self.cell_deg))
        # About 11 m precision removes exact/near-exact duplicate rows without
        # merging separate facilities in the same building too aggressively.
        coord_key = (round(lat, 4), round(lon, 4))
        bucket = self.buckets.setdefault(key, {})
        source_mask = {"government": 1, "user_approved": 2, "paused": 4}.get(source, 0)
        item = bucket.setdefault(coord_key, [lat, lon, 0])
        item[2] |= source_mask
        self.total += 1

    def nearby(self, lat, lon, radius_m=500):
        lat = _safe_float(lat)
        lon = _safe_float(lon)
        if lat is None or lon is None:
            return []
        dlat = radius_m / 111000.0
        dlon = radius_m / (111000.0 * max(0.1, math.cos(math.radians(lat))))
        min_lat_key = math.floor((lat - dlat) / self.cell_deg)
        max_lat_key = math.floor((lat + dlat) / self.cell_deg)
        min_lon_key = math.floor((lon - dlon) / self.cell_deg)
        max_lon_key = math.floor((lon + dlon) / self.cell_deg)
        found = []
        seen = set()
        for lat_key in range(min_lat_key, max_lat_key + 1):
            for lon_key in range(min_lon_key, max_lon_key + 1):
                for coord_key, item in self.buckets.get((lat_key, lon_key), {}).items():
                    if coord_key in seen:
                        continue
                    if _haversine_m(lat, lon, item[0], item[1]) <= radius_m:
                        seen.add(coord_key)
                        found.append(item)
        return found


def build_current_supply_index(postgres_enabled=False, pg_connect=None, psycopg2_module=None):
    """Load current government and approved user supply into a compact index."""
    index = SupplyIndex(cell_m=500)
    paused_index = SupplyIndex(cell_m=50)
    approved_user_rows = []

    # Load the latest short-lived status reports first so paused facilities do
    # not falsely make a demand circle look resolved.
    if postgres_enabled and pg_connect and psycopg2_module:
        conn = None
        try:
            conn = pg_connect()
            cur = conn.cursor(cursor_factory=psycopg2_module.extras.RealDictCursor)
            cur.execute("""
                SELECT lat, lon, status
                FROM toilet_status_reports
                WHERE created_at >= NOW() - INTERVAL '6 hours'
                ORDER BY created_at DESC
                LIMIT 4000
            """)
            seen_status = set()
            for row in cur.fetchall():
                lat = _safe_float(row.get("lat"))
                lon = _safe_float(row.get("lon"))
                if lat is None or lon is None:
                    continue
                key = (round(lat, 4), round(lon, 4))
                if key in seen_status:
                    continue
                seen_status.add(key)
                if (row.get("status") or "").strip() == "暫停使用":
                    paused_index.add(lat, lon, "paused")
            cur.execute("""
                SELECT lat, lon
                FROM user_toilets
                WHERE verification_status = 'approved'
                  AND lat IS NOT NULL AND lon IS NOT NULL
            """)
            approved_user_rows = list(cur.fetchall())
        finally:
            if conn is not None:
                conn.close()

    def add_active(lat, lon, source):
        lat_value = _safe_float(lat)
        lon_value = _safe_float(lon)
        if lat_value is None or lon_value is None:
            return
        if paused_index.nearby(lat_value, lon_value, radius_m=35):
            return
        index.add(lat_value, lon_value, source)

    if os.path.exists(PUBLIC_TOILETS_PATH):
        with open(PUBLIC_TOILETS_PATH, "r", encoding="utf-8-sig", newline="") as handle:
            for row in csv.DictReader(handle):
                add_active(row.get("latitude"), row.get("longitude"), "government")

    for row in approved_user_rows:
        add_active(row.get("lat"), row.get("lon"), "user_approved")
    return index


def reconcile_clusters_with_supply(clusters, supply_index, radius_m=500, low_threshold=2):
    """Attach current coverage and adjust priority while retaining demand history."""
    counts = {"unresolved": 0, "low_coverage": 0, "improved": 0}
    factors = {0: 1.0, 1: 0.70, 2: 0.40}
    for row in clusters:
        nearby = supply_index.nearby(row.get("lat"), row.get("lon"), radius_m=radius_m)
        supply_count = len(nearby)
        government_count = sum(1 for item in nearby if item[2] & 1)
        user_count = sum(1 for item in nearby if item[2] & 2)
        demand_score = float(row.get("demand_score", row.get("gap_score")) or 0)
        if supply_count == 0:
            status = "unresolved"
            label = "尚未解決"
            factor = factors[0]
        elif supply_count <= low_threshold:
            status = "low_coverage"
            label = "目前低覆蓋"
            factor = factors.get(supply_count, 0.40)
        else:
            status = "improved"
            label = "目前已改善"
            factor = 0.10
        counts[status] += 1
        row["demand_score"] = round(demand_score, 2)
        row["supply_adjustment_factor"] = factor
        row["gap_score"] = round(demand_score * factor, 2)
        row["current_supply_count"] = supply_count
        row["government_supply_count"] = government_count
        row["user_supply_count"] = user_count
        row["coverage_status"] = status
        row["coverage_label"] = label
        row["coverage_radius_m"] = int(radius_m)
        row["priority_reason"] = (
            f"歷史有效需求 {int(row.get('effective_queries') or 0)} 筆；"
            f"目前 {int(radius_m)} 公尺內有 {supply_count} 個有效供給點"
            f"（政府 {government_count}、使用者核准 {user_count}），狀態為「{label}」。"
        )
    clusters.sort(
        key=lambda x: (float(x.get("gap_score") or 0), float(x.get("demand_score") or 0)),
        reverse=True,
    )
    return counts
