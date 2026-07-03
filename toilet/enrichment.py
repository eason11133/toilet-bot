import os
import time
import requests

from config import ENRICH_MAX_ITEMS
from core.cache import _ENRICH_CACHE
from core.utils import haversine

# === 依附近場館命名 ===
_ENRICH_TTL = 120

def enrich_nearby_places(lat, lon, radius=500):
    # 🔌 總開關：預設關閉（ENV 可設 ENRICH_ENABLE=1 開啟）
    enabled = globals().get("ENRICH_ENABLE", None)
    if enabled is None:
        try:
            enabled = int(os.getenv("ENRICH_ENABLE", "0"))
        except Exception:
            enabled = 0
    if not enabled:
        return []

    key = f"{round(lat,4)},{round(lon,4)}:{radius}"
    now = time.time()
    cached = _ENRICH_CACHE.get(key)
    if cached and (now - cached[0] < _ENRICH_TTL):
        return cached[1]

    q = f"""
    [out:json][timeout:25];
    (
      node(around:{radius},{lat},{lon})["name"]["building"];
      way(around:{radius},{lat},{lon})["name"]["building"];
      node(around:{radius},{lat},{lon})["name"]["shop"];
      way(around:{radius},{lat},{lon})["name"]["shop"];
      node(around:{radius},{lat},{lon})["name"]["amenity"];
      way(around:{radius},{lat},{lon})["name"]["amenity"];
    );
    out center tags;
    """
    endpoints = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.openstreetmap.ru/api/interpreter",
    ]
    headers = {"User-Agent": f"ToiletBot/1.0 (+{os.getenv('CONTACT_EMAIL','you@example.com')})"}

    for url in endpoints:
        try:
            resp = requests.post(url, data=q, headers=headers, timeout=30)
            if resp.status_code == 200 and "json" in (resp.headers.get("Content-Type","").lower()):
                els = resp.json().get("elements", [])
                out = []
                for e in els:
                    if e.get("type") == "node":
                        clat, clon = e.get("lat"), e.get("lon")
                    else:
                        c = e.get("center") or {}
                        clat, clon = c.get("lat"), c.get("lon")
                    if clat is None or clon is None:
                        continue
                    nm = (e.get("tags", {}) or {}).get("name")
                    if nm:
                        try:
                            d = haversine(float(lat), float(lon), float(clat), float(clon))
                        except Exception:
                            d = 9e9
                        out.append({"name": nm, "lat": float(clat), "lon": float(clon), "_d": d})

                # 距離排序 + 截斷，避免記憶體暴衝
                if out:
                    out.sort(key=lambda x: x["_d"])
                    # 使用全域/ENV 的 ENRICH_MAX_ITEMS（若無則預設 60）
                    max_items = globals().get("ENRICH_MAX_ITEMS", None)
                    if max_items is None:
                        try:
                            max_items = int(os.getenv("ENRICH_MAX_ITEMS", "60"))
                        except Exception:
                            max_items = 60
                    out = out[:max_items]
                    for o in out:
                        o.pop("_d", None)

                _ENRICH_CACHE.set(key, (now, out))
                return out
        except Exception:
            continue

    _ENRICH_CACHE.set(key, (now, []))
    return []
