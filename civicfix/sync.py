import logging
import os
from datetime import datetime, timezone
from typing import Dict, Iterable, List, Optional

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None


def configure_sync(postgres_enabled, pg_connect, psycopg2_module):
    global POSTGRES_ENABLED, _pg_connect, psycopg2
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module


def _require_postgres():
    if not POSTGRES_ENABLED or _pg_connect is None or psycopg2 is None:
        raise RuntimeError("CivicFix source sync requires Postgres/DATABASE_URL")


def _chunked(items: List[Dict], size: int = 1000):
    for i in range(0, len(items), size):
        yield items[i:i + size]


def sync_moenv_toilets_from_csv(file_path: str, file_name: Optional[str] = None) -> Dict:
    from civicfix.source_adapters.moenv_toilet import parse_public_toilet_csv

    parsed = parse_public_toilet_csv(file_path)
    return upsert_facilities(
        source=parsed["source"],
        facility_type=parsed["facility_type"],
        facilities=parsed["facilities"],
        file_name=file_name or os.path.basename(file_path),
        total_rows=parsed["total_rows"],
        adapter_errors=parsed.get("errors") or [],
    )


def upsert_facilities(
    source: str,
    facility_type: str,
    facilities: List[Dict],
    file_name: str = "",
    total_rows: Optional[int] = None,
    adapter_errors: Optional[List[str]] = None,
    mark_missing_inactive: bool = True,
) -> Dict:
    """Upsert normalized facilities into the CivicFix facilities table.

    Only official/source-owned fields are updated on conflict. CivicFix fields
    such as photo_url, status_note, civicfix_status, trust_level, publish_status
    and Gate results are intentionally preserved.
    """
    _require_postgres()
    adapter_errors = adapter_errors or []
    total_rows = int(total_rows if total_rows is not None else len(facilities))

    # PostgreSQL cannot update the same ON CONFLICT target twice inside one
    # multi-row INSERT.  Real MOENV toilet CSVs contain duplicate `number`
    # values, often only 1-2 rows apart, so we must de-duplicate before
    # execute_values().  Keep the last row for a source_id because it is the
    # freshest/last-seen representation in the uploaded source file.
    deduped = {}
    missing_source_id_count = 0
    duplicate_count = 0
    for f in facilities:
        sid = str(f.get("source_id") or "").strip()
        if not sid:
            missing_source_id_count += 1
            continue
        if sid in deduped:
            duplicate_count += 1
        deduped[sid] = f
    facilities = list(deduped.values())

    started_at = datetime.now(timezone.utc)
    inserted_count = 0
    updated_count = 0
    skipped_count = max(0, total_rows - len(facilities))
    error_count = len(adapter_errors) + missing_source_id_count
    error_lines = list(adapter_errors[:20])
    if missing_source_id_count:
        error_lines.append(f"{missing_source_id_count} row(s) skipped because source_id is empty")
    if duplicate_count:
        error_lines.append(f"{duplicate_count} duplicate source_id row(s) de-duplicated before upsert")
    error_sample = "\n".join(error_lines[:20])

    if not facilities:
        _write_sync_log(source, facility_type, file_name, total_rows, 0, 0, skipped_count, error_count, error_sample, started_at)
        return {
            "ok": True,
            "source": source,
            "facility_type": facility_type,
            "total_rows": total_rows,
            "inserted_count": 0,
            "updated_count": 0,
            "skipped_count": skipped_count,
            "error_count": error_count,
            "error_sample": error_sample,
        }

    conn = None
    try:
        conn = _pg_connect()
        cur = conn.cursor()
        values = []
        for f in facilities:
            values.append((
                f.get("facility_type") or facility_type,
                f.get("source") or source,
                f.get("source_id"),
                f.get("name"),
                f.get("address"),
                f.get("lat"),
                f.get("lon"),
                f.get("official_payload") or "{}",
                started_at,
                f.get("official_status") or "active",
                started_at,
                f.get("trust_level") or "L4",
                f.get("publish_status") or "published",
            ))

        sql = """
            INSERT INTO facilities (
                facility_type, source, source_id, name, address, lat, lon,
                official_payload, official_updated_at, official_status,
                last_seen_in_source, trust_level, publish_status, created_at, updated_at
            ) VALUES %s
            ON CONFLICT (source, source_id) DO UPDATE SET
                name = EXCLUDED.name,
                address = EXCLUDED.address,
                lat = EXCLUDED.lat,
                lon = EXCLUDED.lon,
                official_payload = EXCLUDED.official_payload,
                official_updated_at = EXCLUDED.official_updated_at,
                official_status = 'active',
                last_seen_in_source = EXCLUDED.last_seen_in_source,
                updated_at = NOW()
            RETURNING (xmax = 0) AS inserted
        """
        for chunk in _chunked(values, 1000):
            psycopg2.extras.execute_values(cur, sql, chunk, page_size=1000)
            rows = cur.fetchall() or []
            for row in rows:
                # row may be tuple or dict depending on cursor type.
                is_inserted = row[0] if not isinstance(row, dict) else row.get("inserted")
                if is_inserted:
                    inserted_count += 1
                else:
                    updated_count += 1

        if mark_missing_inactive:
            cur.execute("""
                UPDATE facilities
                SET official_status = 'inactive', updated_at = NOW()
                WHERE source = %s
                  AND facility_type = %s
                  AND COALESCE(last_seen_in_source, TIMESTAMPTZ '2000-01-01') < %s
            """, (source, facility_type, started_at))

        cur.execute("""
            INSERT INTO source_sync_logs (
                source, facility_type, file_name, total_rows, inserted_count,
                updated_count, skipped_count, error_count, error_sample,
                started_at, finished_at
            ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, NOW())
        """, (
            source, facility_type, file_name, total_rows, inserted_count,
            updated_count, skipped_count, error_count, error_sample,
            started_at,
        ))
        conn.commit()
        return {
            "ok": True,
            "source": source,
            "facility_type": facility_type,
            "total_rows": total_rows,
            "inserted_count": inserted_count,
            "updated_count": updated_count,
            "skipped_count": skipped_count,
            "error_count": error_count,
            "error_sample": error_sample,
        }
    except Exception as e:
        if conn:
            try:
                conn.rollback()
            except Exception:
                pass
        logging.error(f"CivicFix sync failed: {e}", exc_info=True)
        try:
            _write_sync_log(source, facility_type, file_name, total_rows, inserted_count, updated_count, skipped_count, error_count + 1, str(e), started_at)
        except Exception:
            pass
        raise
    finally:
        if conn:
            try:
                conn.close()
            except Exception:
                pass


def _write_sync_log(source, facility_type, file_name, total_rows, inserted_count, updated_count, skipped_count, error_count, error_sample, started_at):
    _require_postgres()
    conn = None
    try:
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO source_sync_logs (
                source, facility_type, file_name, total_rows, inserted_count,
                updated_count, skipped_count, error_count, error_sample,
                started_at, finished_at
            ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, NOW())
        """, (source, facility_type, file_name, total_rows, inserted_count, updated_count, skipped_count, error_count, error_sample, started_at))
        conn.commit()
    finally:
        if conn:
            conn.close()
