import os
import csv
import logging
import threading

from core.utils import norm_coord

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None
FAVORITES_FILE_PATH = os.path.join(os.getcwd(), "data", "favorites.txt")


def configure_favorites(postgres_enabled=False, pg_connect=None, favorites_file_path=None, psycopg2_module=None):
    global POSTGRES_ENABLED, _pg_connect, FAVORITES_FILE_PATH, psycopg2
    POSTGRES_ENABLED = bool(postgres_enabled)
    _pg_connect = pg_connect
    if favorites_file_path:
        FAVORITES_FILE_PATH = favorites_file_path
    if psycopg2_module is not None:
        psycopg2 = psycopg2_module

# === 最愛管理 ===
# favorites.txt 是純文字/CSV 檔，於多執行緒環境下需要鎖避免同時讀寫造成破檔
# （例如同一時間多位使用者點收藏/取消收藏）
_FAV_LOCK = threading.Lock()

def add_to_favorites(uid, toilet):
    """Add a toilet to favorites.
    Primary store: Neon/Postgres favorites table.
    Fallback: local favorites.txt, only if Postgres is not enabled.
    """
    try:
        if not uid or not toilet:
            return False

        name = (toilet.get("name") or "").strip()
        lat = toilet.get("lat")
        lon = toilet.get("lon")
        address = toilet.get("address", "") or ""

        if not name or lat is None or lon is None:
            return False

        lat_f = float(lat)
        lon_f = float(lon)

        if POSTGRES_ENABLED:
            conn = _pg_connect()
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO favorites (user_id, name, lat, lon, address)
                VALUES (%s, %s, %s, %s, %s)
                ON CONFLICT (user_id, name, lat, lon)
                DO UPDATE SET address = COALESCE(NULLIF(EXCLUDED.address, ''), favorites.address)
            """, (uid, name, lat_f, lon_f, address))
            conn.commit()
            conn.close()
            return True

        lat_s = norm_coord(lat_f)
        lon_s = norm_coord(lon_f)
        with _FAV_LOCK:
            # avoid duplicate rows in fallback file
            exists = False
            if os.path.exists(FAVORITES_FILE_PATH):
                with open(FAVORITES_FILE_PATH, "r", encoding="utf-8", newline="") as f:
                    reader = csv.reader(f)
                    for row in reader:
                        if len(row) >= 4 and row[0] == uid and row[1] == name and row[2] == lat_s and row[3] == lon_s:
                            exists = True
                            break
            if not exists:
                with open(FAVORITES_FILE_PATH, "a", encoding="utf-8", newline="") as f:
                    writer = csv.writer(f)
                    writer.writerow([uid, name, lat_s, lon_s, address])
        return True

    except Exception as e:
        logging.error(f"加入最愛失敗: {e}", exc_info=True)
        return False


def remove_from_favorites(uid, name, lat, lon):
    """Remove a favorite from Neon/Postgres, with local-file fallback."""
    try:
        if not uid or not name:
            return False

        lat_f = float(lat)
        lon_f = float(lon)

        if POSTGRES_ENABLED:
            conn = _pg_connect()
            cur = conn.cursor()
            cur.execute("""
                DELETE FROM favorites
                WHERE user_id = %s
                  AND name = %s
                  AND lat = %s
                  AND lon = %s
                RETURNING id
            """, (uid, name, lat_f, lon_f))
            row = cur.fetchone()
            conn.commit()
            conn.close()
            return bool(row)

        lat_s = norm_coord(lat_f)
        lon_s = norm_coord(lon_f)
        with _FAV_LOCK:
            rows = []
            changed = False
            if os.path.exists(FAVORITES_FILE_PATH):
                with open(FAVORITES_FILE_PATH, "r", encoding="utf-8", newline="") as f:
                    reader = csv.reader(f)
                    for row in reader:
                        if len(row) < 5:
                            rows.append(row)
                            continue
                        if not (row[0] == uid and row[1] == name and row[2] == lat_s and row[3] == lon_s):
                            rows.append(row)
                        else:
                            changed = True
            if changed:
                with open(FAVORITES_FILE_PATH, "w", encoding="utf-8", newline="") as f:
                    writer = csv.writer(f)
                    writer.writerows(rows)
        return changed

    except Exception as e:
        logging.error(f"移除最愛失敗: {e}", exc_info=True)
        return False


def get_user_favorites(uid):
    """Read user's favorites.
    Returned rows include type='favorite' so the Flex card shows '移除最愛'.
    """
    favs = []
    if not uid:
        return favs

    try:
        if POSTGRES_ENABLED:
            conn = _pg_connect()
            cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
            cur.execute("""
                SELECT name, lat, lon, address, created_at
                FROM favorites
                WHERE user_id = %s
                ORDER BY created_at DESC
                LIMIT 50
            """, (uid,))
            rows = cur.fetchall()
            conn.close()

            for r in rows:
                favs.append({
                    "user_id": uid,
                    "name": r.get("name") or "",
                    "lat": float(r.get("lat")),
                    "lon": float(r.get("lon")),
                    "address": r.get("address") or "",
                    "type": "favorite",
                    "source": "最愛",
                })
            return favs

        with _FAV_LOCK:
            if not os.path.exists(FAVORITES_FILE_PATH):
                return favs
            with open(FAVORITES_FILE_PATH, "r", encoding="utf-8", newline="") as f:
                reader = csv.reader(f)
                for row in reader:
                    if len(row) < 5:
                        continue
                    if row[0] != uid:
                        continue
                    favs.append({
                        "user_id": row[0],
                        "name": row[1],
                        "lat": float(row[2]),
                        "lon": float(row[3]),
                        "address": row[4],
                        "type": "favorite",
                        "source": "最愛",
                    })
        return favs

    except Exception as e:
        logging.error(f"讀取最愛失敗: {e}", exc_info=True)
        return favs
