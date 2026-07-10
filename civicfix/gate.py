import re

_TEST_PATTERNS = ["test", "測試", "asdf", "qwer", "none", "null", "xxx"]


def _clean(v):
    return "" if v is None else str(v).strip()


def _valid_taiwan_coord(lat, lon):
    try:
        lat = float(lat)
        lon = float(lon)
        return 20.0 <= lat <= 27.0 and 118.0 <= lon <= 123.5
    except Exception:
        return False


def evaluate_submission(data):
    """Rule-based CivicFix Gate v1.

    This does not claim to prove truth.  It only decides whether a supplement is
    safe enough to publish, needs review, or should be rejected.
    """
    data = data or {}
    score = 40
    flags = []
    reasons = []

    facility_type = _clean(data.get("facility_type"))
    submission_type = _clean(data.get("submission_type"))
    name = _clean(data.get("name"))
    address = _clean(data.get("address"))
    lat = data.get("lat")
    lon = data.get("lon")
    photo_url = _clean(data.get("photo_url"))
    placement_note = _clean(data.get("placement_note"))
    access_note = _clean(data.get("access_note"))
    submitter_type = _clean(data.get("submitter_type")) or "admin"

    valid_types = {"new_facility", "field_info_update", "photo_update", "status_update", "location_fix", "opening_hours_fix"}
    if submission_type in valid_types:
        score += 10
    else:
        flags.append("invalid_submission_type")
        reasons.append("補資料類型不在允許清單")
        score -= 25

    if facility_type:
        score += 5
    else:
        flags.append("missing_facility_type")
        score -= 10

    # new points and location fixes require coordinates.  Field-info-only updates
    # can rely on related_facility_id and do not always need coordinates.
    if submission_type in {"new_facility", "location_fix"}:
        if _valid_taiwan_coord(lat, lon):
            score += 15
        else:
            flags.append("invalid_coordinate")
            reasons.append("新增點位或修正座標需要有效台灣座標")
            score -= 35
    elif lat not in (None, "") or lon not in (None, ""):
        if _valid_taiwan_coord(lat, lon):
            score += 5
        else:
            flags.append("invalid_coordinate")
            score -= 15

    if submission_type == "new_facility":
        if len(name) >= 2:
            score += 10
        else:
            flags.append("missing_or_short_name")
            reasons.append("新增點位名稱不足")
            score -= 20
        if len(address) >= 4:
            score += 5
        else:
            flags.append("weak_address")
            score -= 5
    elif name:
        score += 3

    # Avoid broad substring patterns like "123" or "無" because normal Taiwan
    # addresses often contain 123 and valid terms such as 無障礙.  Only flag
    # clear test markers or fields that are exactly meaningless placeholders.
    text_fields = [name, address, placement_note, access_note]
    normalized_fields = [f.lower().strip() for f in text_fields if f]
    looks_like_test = False
    for field in normalized_fields:
        if field in _TEST_PATTERNS:
            looks_like_test = True
            break
        if "測試" in field or "test" in field:
            looks_like_test = True
            break
    if looks_like_test:
        flags.append("looks_like_test_data")
        reasons.append("內容疑似測試資料")
        score -= 25

    if photo_url:
        score += 8
    elif submission_type in {"photo_update", "field_info_update"}:
        flags.append("missing_photo")
        score -= 3

    if placement_note:
        score += 8
    elif submission_type in {"field_info_update", "new_facility"}:
        flags.append("missing_placement_note")
        score -= 4

    if access_note:
        score += 5
    elif submission_type == "field_info_update":
        flags.append("missing_access_note")

    if submitter_type in {"admin", "official"}:
        score += 10
    elif submitter_type == "user":
        score += 0
    else:
        flags.append("unknown_submitter_type")

    score = max(0, min(100, score))

    if "invalid_coordinate" in flags and submission_type in {"new_facility", "location_fix"}:
        suggested_action = "reject"
    elif score >= 80:
        suggested_action = "approve"
    elif score >= 45:
        suggested_action = "need_review"
    else:
        suggested_action = "reject"

    if score >= 85:
        trust_level = "L4"
    elif score >= 70:
        trust_level = "L3"
    elif score >= 50:
        trust_level = "L2"
    else:
        trust_level = "L1"

    if photo_url and placement_note and access_note:
        field_info_level = "high"
    elif photo_url or placement_note or access_note:
        field_info_level = "medium"
    else:
        field_info_level = "low"

    reason = "；".join(reasons) if reasons else "規則式 Gate 檢查完成"
    return {
        "score": int(score),
        "trust_level": trust_level,
        "field_info_level": field_info_level,
        "risk_flags": flags,
        "suggested_action": suggested_action,
        "reason": reason,
    }
