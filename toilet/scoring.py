"""Toilet-specific NTS and Trust Score ranking utilities.

Extracted from app.py without changing function bodies.
"""

from datetime import datetime, timezone

def _score_distance(distance_m):
    """
    距離分數：距離越近分數越高。
    0m = 100 分，1000m 以上趨近 0 分。
    """
    try:
        d = float(distance_m or 0)
        return max(0, 100 - d / 10)
    except Exception:
        return 0

def _score_trust(t):
    """
    Trust Score 2.0：資料可信度分數。

    評估重點：
    1. 資料來源
    2. 後台驗證狀態
    3. 後台 verification_score
    4. 資訊完整度輔助
    5. 資料新鮮度
    """
    source = (t.get("source") or t.get("type") or "").lower()
    status = (t.get("verification_status") or "").lower()

    # rejected 直接視為不可信；sort_toilets_nts 也會排除 rejected，這裡再保險一次
    if status == "rejected":
        return 0

    # === 1. 基礎來源分數 ===
    if source in ("public_csv", "government"):
        score = 85
    elif source in ("osm", "overpass"):
        score = 75
    elif source in ("neon", "user_added", "user", "saved"):
        score = 60
    else:
        score = 60

    # === 2. 後台驗證狀態 ===
    if status == "approved":
        score += 20
    elif status == "pending":
        score += 0
    elif status in ("needs_review", "review"):
        score -= 10

    # === 3. 後台 verification_score 輔助 ===
    try:
        v_score = t.get("verification_score")
        if v_score not in (None, ""):
            v_score = float(v_score)
            # verification_score 若是 0~100，轉成最多約 ±10 分影響
            score += (v_score - 50) / 5
    except Exception:
        pass

    # === 4. 資訊完整度輔助 ===
    try:
        completeness_bonus = 0
        if t.get("address"):
            completeness_bonus += 3
        if t.get("floor_hint") or t.get("level"):
            completeness_bonus += 3
        if t.get("entrance_hint"):
            completeness_bonus += 3
        if t.get("open_hours"):
            completeness_bonus += 2
        score += completeness_bonus
    except Exception:
        pass

    # === 5. 資料新鮮度 ===
    try:
        ts = t.get("updated_at") or t.get("created_at")
        if ts:
            if isinstance(ts, str):
                dt = datetime.fromisoformat(ts.replace("Z", "+00:00"))
            else:
                dt = ts

            now = datetime.now(timezone.utc)
            if getattr(dt, "tzinfo", None) is None:
                dt = dt.replace(tzinfo=timezone.utc)

            age_days = (now - dt).days
            if age_days > 730:
                score -= 10
            elif age_days > 365:
                score -= 5
            elif age_days <= 30:
                score += 5
    except Exception:
        pass

    return max(0, min(round(score, 2), 100))

def _score_info(t):
    """
    資訊完整度分數：越容易找到、越完整分數越高。
    """
    score = 0

    if t.get("name"):
        score += 20
    if t.get("address"):
        score += 30
    if t.get("floor_hint") or t.get("level"):
        score += 20
    if t.get("entrance_hint"):
        score += 15
    if t.get("access_note"):
        score += 10
    if t.get("open_hours"):
        score += 5

    return min(score, 100)

def _score_status(t):
    """
    Status Score 2.0：設施目前可用狀態分數。

    評估重點：
    1. 明確停用/故障/維修 → 大幅降分
    2. 明確正常/可使用 → 加分
    3. 沒有狀態 → 中性分數
    4. 使用者文字回報與 note 一併判斷
    """
    texts = []
    for key in ["status", "status_text", "note", "verification_reason", "reject_reason"]:
        val = t.get(key)
        if val:
            texts.append(str(val))

    s = " ".join(texts).strip()
    if not s:
        return 70

    bad_keywords = [
        "暫停", "故障", "維修", "關閉", "不能使用", "無法使用",
        "停用", "封閉", "施工", "撤除", "不存在", "錯誤", "rejected"
    ]
    warning_keywords = [
        "不確定", "待確認", "可能", "髒", "很髒", "沒有衛生紙",
        "位置不清楚", "入口不明", "找不到"
    ]
    good_keywords = [
        "正常", "恢復", "可使用", "開放", "乾淨", "有衛生紙",
        "確認可用", "已確認"
    ]

    if any(k in s for k in bad_keywords):
        return 0
    if any(k in s for k in warning_keywords):
        return 45
    if any(k in s for k in good_keywords):
        return 95
    return 70

def compute_nts_score(t):
    """
    NTS 節點式廁所搜尋演算法總分。
    """
    distance_score = _score_distance(t.get("distance"))
    trust_score = _score_trust(t)
    info_score = _score_info(t)
    status_score = _score_status(t)

    final_score = (
        0.60 * distance_score +
        0.20 * trust_score +
        0.10 * info_score +
        0.10 * status_score
    )

    t["nts_score"] = round(final_score, 2)
    t["distance_score"] = round(distance_score, 2)
    t["trust_score"] = round(trust_score, 2)
    t["info_score"] = round(info_score, 2)
    t["status_score"] = round(status_score, 2)

    return t["nts_score"]

def sort_toilets_nts(toilets):
    """
    使用 NTS 分數排序。
    rejected 資料不顯示，其餘依 NTS 分數由高到低排序。
    """
    clean = []
    for t in toilets:
        status = (t.get("verification_status") or "pending").lower()
        if status == "rejected":
            continue

        compute_nts_score(t)
        clean.append(t)

    clean.sort(key=lambda x: (-x.get("nts_score", 0), x.get("distance", 999999)))
    return clean

def _score_trust_1_0(t):
    """
    NTS 1.0 baseline 的固定可信度分數。
    用於 shadow ranking，不影響實際給使用者看的 Trust Score 2.0。
    """
    source = (t.get("source") or t.get("type") or "").lower()
    status = (t.get("verification_status") or "pending").lower()
    if status == "rejected":
        return 0
    if source in ("public_csv", "government", "osm", "overpass"):
        return 100
    if status == "approved":
        return 90
    if status == "pending":
        return 60
    return 60

def _score_status_1_0(t):
    """NTS 1.0 baseline 的狀態分數。"""
    s = (t.get("status") or t.get("status_text") or "").strip()
    if not s:
        return 70
    bad_keywords = ["暫停", "故障", "維修", "關閉", "不能使用", "無法使用"]
    good_keywords = ["正常", "恢復", "可使用"]
    if any(k in s for k in bad_keywords):
        return 0
    if any(k in s for k in good_keywords):
        return 100
    return 70

def compute_nts_score_1_0(t):
    """
    用 NTS 1.0 baseline 公式計算分數。
    只用於 shadow ranking；會寫入傳入 dict 的分數欄位。
    """
    distance_score = _score_distance(t.get("distance"))
    trust_score = _score_trust_1_0(t)
    info_score = _score_info(t)
    status_score = _score_status_1_0(t)
    final_score = 0.60 * distance_score + 0.20 * trust_score + 0.10 * info_score + 0.10 * status_score
    t["nts_score"] = round(final_score, 2)
    t["distance_score"] = round(distance_score, 2)
    t["trust_score"] = round(trust_score, 2)
    t["info_score"] = round(info_score, 2)
    t["status_score"] = round(status_score, 2)
    return t["nts_score"]

def sort_toilets_nts_1_0(toilets):
    """
    Shadow ranking：同一批已回傳候選資料用 NTS 1.0 baseline 重新排序。
    不重新查 CSV / Neon / OSM，只重算分數與排序。
    """
    clean = []
    for t in toilets or []:
        status = (t.get("verification_status") or "pending").lower()
        if status == "rejected":
            continue
        item = dict(t)
        compute_nts_score_1_0(item)
        clean.append(item)
    clean.sort(key=lambda x: (-x.get("nts_score", 0), x.get("distance", 999999)))
    return clean
