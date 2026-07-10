import argparse
import json
import os
from datetime import datetime

import gspread
import psycopg2
from dotenv import load_dotenv


def norm(s):
    return str(s or "").strip().lower().replace(" ", "").replace("_", "")


def find_col(header, names):
    hmap = {norm(v): i for i, v in enumerate(header)}
    for name in names:
        key = norm(name)
        if key in hmap:
            return hmap[key]

    for i, h in enumerate(header):
        hh = norm(h)
        for name in names:
            key = norm(name)
            if key and key in hh:
                return i
    return None


def cell(row, idx, default=""):
    if idx is None or idx >= len(row):
        return default
    return str(row[idx] or "").strip()


def parse_float(v):
    try:
        if v is None:
            return None
        s = str(v).strip()
        if not s:
            return None
        return float(s)
    except Exception:
        return None


def parse_created_at(v):
    s = str(v or "").strip()
    if not s:
        return None

    candidates = [
        "%Y-%m-%d %H:%M:%S",
        "%Y/%m/%d %H:%M:%S",
        "%Y-%m-%d",
        "%Y/%m/%d",
    ]
    for fmt in candidates:
        try:
            return datetime.strptime(s, fmt)
        except Exception:
            pass
    return None


def map_header(header):
    return {
        "name": find_col(header, ["名稱", "廁所名稱", "name", "toilet_name"]),
        "address": find_col(header, ["地址", "address"]),
        "rating": find_col(header, ["清潔度評分", "rating", "清潔度", "cleanliness_rating"]),
        "toilet_paper": find_col(header, ["是否有衛生紙", "衛生紙", "toilet_paper", "paper"]),
        "accessibility": find_col(header, ["是否有無障礙設施", "無障礙", "accessibility", "accessible"]),
        "time_of_use": find_col(header, ["使用時間", "time_of_use", "time"]),
        "comment": find_col(header, ["備註", "評論", "意見", "comment", "feedback"]),
        "cleanliness_score": find_col(header, ["預測清潔分數", "cleanliness_score", "預測", "clean_score"]),
        "lat": find_col(header, ["lat", "latitude", "緯度"]),
        "lon": find_col(header, ["lon", "lng", "longitude", "經度"]),
        "floor_hint": find_col(header, ["floor_hint", "樓層", "位置/樓層"]),
        "created_at": find_col(header, ["created_at", "timestamp", "時間戳記", "提交時間", "時間"]),
    }


def list_table_columns(conn):
    with conn.cursor() as cur:
        cur.execute("""
            SELECT column_name
            FROM information_schema.columns
            WHERE table_schema = 'public'
              AND table_name = 'toilet_feedbacks'
            ORDER BY ordinal_position
        """)
        return {r[0] for r in cur.fetchall()}


def duplicate_exists(conn, item):
    with conn.cursor() as cur:
        cur.execute("""
            SELECT id
            FROM toilet_feedbacks
            WHERE ABS(lat - %s) <= 0.000001
              AND ABS(lon - %s) <= 0.000001
              AND COALESCE(name, '') = %s
              AND COALESCE(address, '') = %s
              AND COALESCE(rating::text, '') = %s
            LIMIT 1
        """, (
            item["lat"],
            item["lon"],
            item["name"],
            item["address"],
            str(item["rating"]),
        ))
        return cur.fetchone() is not None


def insert_item(conn, item, columns):
    insertable = {
        "name": item["name"],
        "address": item["address"],
        "rating": item["rating"],
        "toilet_paper": item["toilet_paper"],
        "accessibility": item["accessibility"],
        "time_of_use": item["time_of_use"],
        "comment": item["comment"],
        "cleanliness_score": item["cleanliness_score"],
        "lat": item["lat"],
        "lon": item["lon"],
        "floor_hint": item["floor_hint"],
    }

    if "created_at" in columns and item.get("created_at"):
        insertable["created_at"] = item["created_at"]

    insertable = {k: v for k, v in insertable.items() if k in columns}

    keys = list(insertable.keys())
    placeholders = ", ".join(["%s"] * len(keys))
    sql = f"""
        INSERT INTO toilet_feedbacks ({", ".join(keys)})
        VALUES ({placeholders})
    """

    with conn.cursor() as cur:
        cur.execute(sql, [insertable[k] for k in keys])


def collect_rows_from_worksheet(ws):
    values = ws.get_all_values() or []
    if len(values) < 2:
        return []

    header = values[0]
    data = values[1:]
    idx = map_header(header)

    if idx["lat"] is None or idx["lon"] is None or idx["rating"] is None:
        return []

    out = []
    for row in data:
        lat = parse_float(cell(row, idx["lat"]))
        lon = parse_float(cell(row, idx["lon"]))
        if lat is None or lon is None:
            continue

        name = cell(row, idx["name"], "未知廁所")
        address = cell(row, idx["address"], "")
        rating = cell(row, idx["rating"], "")
        if not name and not rating:
            continue

        item = {
            "name": name or "未知廁所",
            "address": address,
            "rating": rating,
            "toilet_paper": cell(row, idx["toilet_paper"], "沒注意"),
            "accessibility": cell(row, idx["accessibility"], "沒注意"),
            "time_of_use": cell(row, idx["time_of_use"], ""),
            "comment": cell(row, idx["comment"], ""),
            "cleanliness_score": parse_float(cell(row, idx["cleanliness_score"], "")),
            "lat": lat,
            "lon": lon,
            "floor_hint": cell(row, idx["floor_hint"], ""),
            "created_at": parse_created_at(cell(row, idx["created_at"], "")),
        }
        out.append(item)

    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--old-env", required=True, help="舊專案 .env 路徑，用來讀 Google Sheet credentials")
    parser.add_argument("--database-url", default="", help="Neon DATABASE_URL；不填就讀環境變數 DATABASE_URL")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    load_dotenv(args.old_env, override=False)

    creds_raw = os.getenv("GSHEET_CREDENTIALS_JSON", "").strip()
    if not creds_raw:
        raise RuntimeError("找不到 GSHEET_CREDENTIALS_JSON")

    creds = json.loads(creds_raw)

    # .env 裡的 private_key 通常是 "\\n"，Google auth 需要真正換行 "\n"
    if "private_key" in creds and isinstance(creds["private_key"], str):
        creds["private_key"] = creds["private_key"].replace("\\n", "\n")

    gc = gspread.service_account_from_dict(creds)

    sheet_ids = []
    for key in ["FEEDBACK_SPREADSHEET_ID", "FEEDBACK_SHEET_ID", "TOILET_SPREADSHEET_ID"]:
        v = os.getenv(key, "").strip().strip('"').strip("'")
        if v and v not in sheet_ids:
            sheet_ids.append(v)

    # 舊 app.py 寫死的 FEEDBACK_SPREADSHEET_ID，保底加入。
    hardcoded_old_feedback_id = "15Ram7EZ9QMN6SZAVYQFNpL5gu4vTaRn4M5mpWUKmmZk"
    if hardcoded_old_feedback_id not in sheet_ids:
        sheet_ids.append(hardcoded_old_feedback_id)

    print("Will scan sheet ids:")
    for sid in sheet_ids:
        print(" -", sid)

    all_items = []

    for sid in sheet_ids:
        try:
            sh = gc.open_by_key(sid)
        except Exception as e:
            print(f"[SKIP] open sheet failed {sid}: {e}")
            continue

        print(f"\nSpreadsheet: {sh.title} ({sid})")
        for ws in sh.worksheets():
            try:
                items = collect_rows_from_worksheet(ws)
                print(f"  worksheet={ws.title!r}, candidate feedback rows={len(items)}")
                for it in items[:3]:
                    print(f"    sample: {it['name']} {it['rating']} {it['lat']},{it['lon']}")
                all_items.extend(items)
            except Exception as e:
                print(f"  [SKIP] worksheet={ws.title!r}: {e}")

    print(f"\nTotal candidate feedback rows: {len(all_items)}")

    if args.dry_run and not args.apply:
        print("Dry run only. No DB write.")
        return

    if not args.apply:
        print("No --apply given. Stop.")
        return

    db_url = args.database_url or os.getenv("DATABASE_URL", "").strip()
    if not db_url:
        raise RuntimeError("找不到 DATABASE_URL，請用 --database-url 或設定環境變數")

    inserted = 0
    skipped = 0

    conn = psycopg2.connect(db_url)
    try:
        columns = list_table_columns(conn)
        for item in all_items:
            if duplicate_exists(conn, item):
                skipped += 1
                continue
            insert_item(conn, item, columns)
            inserted += 1

        conn.commit()
        print(f"Inserted: {inserted}")
        print(f"Skipped duplicates: {skipped}")
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


if __name__ == "__main__":
    main()