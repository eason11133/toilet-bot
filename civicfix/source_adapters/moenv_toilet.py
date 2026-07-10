import csv
import hashlib
import json
from typing import Dict, Iterable, List, Tuple

SOURCE = "moenv_fac_p_07"
FACILITY_TYPE = "toilet"
REQUIRED_COLUMNS = {
    "country", "city", "village", "number", "name", "address", "administration",
    "latitude", "longitude", "grade", "type2", "type", "exec", "diaper",
}


def _clean(value) -> str:
    if value is None:
        return ""
    return str(value).strip()


def _to_float(value):
    text = _clean(value)
    if not text:
        return None
    try:
        return float(text)
    except Exception:
        return None


def _fallback_source_id(row: Dict[str, str]) -> str:
    raw = "|".join([
        _clean(row.get("name")),
        _clean(row.get("address")),
        _clean(row.get("latitude")),
        _clean(row.get("longitude")),
    ])
    digest = hashlib.sha1(raw.encode("utf-8")).hexdigest()[:16]
    return f"fallback_{digest}"


def normalize_row(row: Dict[str, str], row_number: int = 0) -> Tuple[Dict, str]:
    """Normalize one MOENV public toilet row.

    Returns (facility, error).  `facility` is None when the row is invalid.
    """
    row = {str(k).strip(): _clean(v) for k, v in (row or {}).items()}

    name = _clean(row.get("name"))
    lat = _to_float(row.get("latitude"))
    lon = _to_float(row.get("longitude"))
    source_id = _clean(row.get("number")) or _fallback_source_id(row)

    if not name:
        return None, f"row {row_number}: missing name"
    if lat is None or lon is None:
        return None, f"row {row_number}: invalid lat/lon"

    # Taiwan rough bounds. Keep this permissive; detailed validation belongs to Gate.
    # Some official rows have latitude/longitude swapped. Auto-correct only when
    # the original order is invalid but the swapped order is clearly valid.
    in_taiwan = 20.0 <= lat <= 27.0 and 118.0 <= lon <= 123.5
    swapped_in_taiwan = 20.0 <= lon <= 27.0 and 118.0 <= lat <= 123.5
    if not in_taiwan and swapped_in_taiwan:
        lat, lon = lon, lat
        row["_civicfix_coord_note"] = "latitude_longitude_swapped_by_adapter"
        in_taiwan = True
    if not in_taiwan:
        return None, f"row {row_number}: lat/lon outside Taiwan bounds ({lat}, {lon})"

    official_payload = {
        "country": row.get("country", ""),
        "city": row.get("city", ""),
        "village": row.get("village", ""),
        "number": row.get("number", ""),
        "administration": row.get("administration", ""),
        "grade": row.get("grade", ""),
        "type2": row.get("type2", ""),
        "type": row.get("type", ""),
        "exec": row.get("exec", ""),
        "diaper": row.get("diaper", ""),
        "raw": row,
    }

    return {
        "facility_type": FACILITY_TYPE,
        "source": SOURCE,
        "source_id": source_id,
        "name": name,
        "address": _clean(row.get("address")),
        "lat": lat,
        "lon": lon,
        "official_payload": json.dumps(official_payload, ensure_ascii=False),
        "trust_level": "L4",
        "publish_status": "published",
        "official_status": "active",
    }, ""


def parse_public_toilet_csv(file_path: str, max_errors: int = 20) -> Dict:
    facilities: List[Dict] = []
    errors: List[str] = []
    total_rows = 0

    with open(file_path, "r", encoding="utf-8-sig", newline="") as f:
        reader = csv.DictReader(f)
        fieldnames = set(reader.fieldnames or [])
        missing = sorted(REQUIRED_COLUMNS - fieldnames)
        if missing:
            raise ValueError(f"CSV 欄位缺少：{', '.join(missing)}")

        for idx, row in enumerate(reader, start=2):
            total_rows += 1
            facility, err = normalize_row(row, row_number=idx)
            if facility:
                facilities.append(facility)
            elif err and len(errors) < max_errors:
                errors.append(err)

    return {
        "source": SOURCE,
        "facility_type": FACILITY_TYPE,
        "total_rows": total_rows,
        "facilities": facilities,
        "errors": errors,
    }
