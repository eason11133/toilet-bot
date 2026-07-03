import os
import csv
import time
import re
import logging
from difflib import SequenceMatcher

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None
TOILETS_FILE_PATH = None
geocode_address = None
haversine = None
_in_bbox = None

def configure_auto_verify(
    postgres_enabled,
    pg_connect,
    psycopg2_module,
    toilets_file_path,
    geocode_address_func,
    haversine_func,
    in_bbox_func,
):
    global POSTGRES_ENABLED, _pg_connect, psycopg2, TOILETS_FILE_PATH, geocode_address, haversine, _in_bbox
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module
    TOILETS_FILE_PATH = toilets_file_path
    geocode_address = geocode_address_func
    haversine = haversine_func
    _in_bbox = in_bbox_func

def _valid_global_coordinate(lat, lon):
    """只檢查是否為合法地球座標，不再寫死台灣。"""
    try:
        lat = float(lat); lon = float(lon)
    except Exception:
        return False
    return -90 <= lat <= 90 and -180 <= lon <= 180


def _primary_region_risk(lat, lon):
    """
    選用功能：主要服務區域風險。
    預設不啟用，避免誤殺海外資料。
    若未來要限制主要服務區，可在 Render 設：
      AUTO_VERIFY_PRIMARY_BBOX=21.5,118.0,26.5,123.5
    格式：min_lat,min_lon,max_lat,max_lon
    """
    bbox = (os.getenv("AUTO_VERIFY_PRIMARY_BBOX") or "").strip()
    if not bbox:
        return False
    try:
        min_lat, min_lon, max_lat, max_lon = [float(x.strip()) for x in bbox.split(",")]
        lat = float(lat); lon = float(lon)
        return not (min_lat <= lat <= max_lat and min_lon <= lon <= max_lon)
    except Exception:
        return False


def _normalize_text_for_verify(text):
    """Normalize text for rule-based verification / duplicate checks."""
    s = str(text or "").strip().lower()
    s = re.sub(r"[\s\u3000,，。．.、;；:：/\\|｜()（）\[\]【】{}<>《》\-＿_]+", "", s)
    return s


def _has_meaningful_address(address):
    """地址是否有基本辨識度；不是一定要完整門牌，但不能只有極短文字。"""
    s = _normalize_text_for_verify(address)
    if len(s) < 5:
        return False
    weak = {"無", "沒有", "未知", "不清楚", "none", "null", "na", "n/a"}
    return s not in weak


def _address_coordinate_check(lat, lon, address):
    """
    地址—座標一致性檢查。
    預設關閉外部 geocoding，避免批次驗證變慢；設定 AUTO_VERIFY_GEOCODE_ENABLE=1 後啟用。
    回傳：(flag, distance_m, reason)；flag 為 None 表示不標記。
    """
    if os.getenv("AUTO_VERIFY_GEOCODE_ENABLE", "0") != "1":
        return None, None, None
    if not address or not _valid_global_coordinate(lat, lon):
        return None, None, None
    try:
        g_lat, g_lon = geocode_address(address)
        if g_lat is None or g_lon is None:
            return "address_geocode_failed", None, "地址無法轉換為座標，建議人工確認"
        d = haversine(float(lat), float(lon), float(g_lat), float(g_lon))
        if d >= float(os.getenv("AUTO_VERIFY_ADDR_COORD_HIGH_M", "800")):
            return "address_coordinate_mismatch_high", round(d, 1), f"地址轉換座標與填寫座標相差約 {round(d)} 公尺"
        if d >= float(os.getenv("AUTO_VERIFY_ADDR_COORD_MEDIUM_M", "250")):
            return "address_coordinate_mismatch_medium", round(d, 1), f"地址轉換座標與填寫座標相差約 {round(d)} 公尺"
        return None, round(d, 1), None
    except Exception as e:
        logging.warning(f"address-coordinate check failed: {e}")
        return None, None, None


def _spatial_context_signal(lat, lon, context=None, exclude_id=None, radius_m=None):
    """
    空間孤立/離群標記：只作 soft flag，不直接 rejected。
    目標是抓「附近完全沒有參考資料且本身資訊不足」的可疑資料；偏鄉資料不能被誤殺。
    """
    if not _valid_global_coordinate(lat, lon):
        return {"nearby_count": 0, "nearest_m": None, "flag": None}
    if radius_m is None:
        radius_m = float(os.getenv("AUTO_VERIFY_SPATIAL_RADIUS_M", "800"))
    if not (context and isinstance(context, dict) and isinstance(context.get("items"), list)):
        context = _build_auto_verify_context()
    nearby = 0
    nearest = None
    try:
        lat_f = float(lat); lon_f = float(lon)
        for r in context.get("items") or []:
            try:
                if exclude_id is not None and str(r.get("id")) == str(exclude_id) and (r.get("source") in ("neon", "user_toilets", "user_added")):
                    continue
                r_lat = float(r.get("lat")); r_lon = float(r.get("lon"))
            except Exception:
                continue
            if not _in_bbox(r_lat, r_lon, lat_f, lon_f, radius_m):
                continue
            try:
                d = haversine(lat_f, lon_f, r_lat, r_lon)
            except Exception:
                continue
            if d <= radius_m:
                nearby += 1
                if nearest is None or d < nearest:
                    nearest = d
        flag = None
        if nearby == 0:
            flag = "spatial_outlier_candidate"
        return {"nearby_count": nearby, "nearest_m": round(nearest, 1) if nearest is not None else None, "flag": flag}
    except Exception:
        return {"nearby_count": 0, "nearest_m": None, "flag": None}


def _text_similarity(a, b):
    a = (a or "").strip().lower()
    b = (b or "").strip().lower()
    if not a or not b:
        return 0.0
    return SequenceMatcher(None, a, b).ratio()


def _compact_toilet_name(name):
    s = (name or "").strip().lower()
    for token in ["廁所", "公廁", "男廁", "女廁", "無障礙", "親子", "性別友善", "toilet", "restroom", "wc"]:
        s = s.replace(token, "")
    return re.sub(r"\s+", "", s)


def _facility_context(name="", address="", floor_hint="", entrance_hint="", access_note=""):
    """
    粗略判斷新增資料所屬場域，讓缺樓層/入口的扣分更合理。
    outdoor：公園、流動公廁、宮廟、加油站等，通常不一定需要樓層。
    shop：便利商店/店家型，是否開放給外部使用較不確定，需較保守。
    indoor_complex：商場、車站、醫院、學校、大樓等，樓層/入口資訊較重要。
    generic：名稱太籠統或資訊不足。
    """
    text = " ".join([str(name or ""), str(address or ""), str(floor_hint or ""), str(entrance_hint or ""), str(access_note or "")]).lower()

    shop_keywords = [
        "7-11", "711", "統一超商", "全家", "familymart", "萊爾富", "ok超商", "ok mart",
        "全聯", "寶雅", "小北", "屈臣氏", "康是美", "麥當勞", "mos", "星巴克",
        "便利商店", "超商"
    ]
    indoor_keywords = [
        "百貨", "商場", "購物中心", "mall", "車站", "捷運", "高鐵", "火車站", "轉運站",
        "醫院", "診所", "學校", "大學", "高中", "國中", "國小", "校區",
        "大樓", "辦公", "地下街", "機場", "航廈", "市場", "影城", "圖書館", "美術館", "博物館"
    ]
    outdoor_keywords = [
        "公園", "流動公廁", "活動廁所", "宮", "廟", "寺", "教堂", "戲台", "加油站",
        "服務區", "休息站", "停車場", "海邊", "步道", "廣場", "河濱", "運動場"
    ]

    if any(k.lower() in text for k in shop_keywords):
        return "shop"
    if any(k.lower() in text for k in indoor_keywords):
        return "indoor_complex"
    if any(k.lower() in text for k in outdoor_keywords):
        return "outdoor"
    return "generic"


def _is_test_or_garbage_name(name):
    s = (name or "").strip().lower()
    if not s:
        return True
    garbage = {"test", "testing", "aaa", "aaaa", "123", "111", "測試", "測試資料", "無", "none", "null"}
    return s in garbage


def _build_auto_verify_context():
    """
    高速批次驗證用：一次載入 user_toilets + public_toilets.csv。
    避免每驗證一筆就重新掃 DB / CSV，讓 reverify 速度大幅提升。
    """
    items = []

    if POSTGRES_ENABLED:
        try:
            conn = _pg_connect()
            cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
            cur.execute("""
                SELECT id, name, address, lat, lon, verification_status, source
                FROM user_toilets
                WHERE lat IS NOT NULL AND lon IS NOT NULL
                LIMIT 20000
            """)
            for r in cur.fetchall():
                try:
                    items.append({
                        "source": r.get("source") or "user_toilets",
                        "id": r.get("id"),
                        "name": r.get("name") or "",
                        "address": r.get("address") or "",
                        "lat": float(r.get("lat")),
                        "lon": float(r.get("lon")),
                        "verification_status": r.get("verification_status") or "pending"
                    })
                except Exception:
                    continue
            conn.close()
        except Exception as e:
            logging.warning(f"_build_auto_verify_context user_toilets failed: {e}")

    try:
        if os.path.exists(TOILETS_FILE_PATH):
            with open(TOILETS_FILE_PATH, "r", encoding="utf-8-sig", newline="") as f:
                reader = csv.DictReader(f)
                for row in reader:
                    try:
                        lat = float(row.get("latitude") or row.get("lat") or "")
                        lon = float(row.get("longitude") or row.get("lon") or "")
                    except Exception:
                        continue
                    items.append({
                        "source": "public_csv",
                        "id": row.get("number") or row.get("id") or "",
                        "name": row.get("name") or "",
                        "address": row.get("address") or "",
                        "lat": lat,
                        "lon": lon,
                        "verification_status": "approved"
                    })
    except Exception as e:
        logging.warning(f"_build_auto_verify_context public_csv failed: {e}")

    return {"items": items, "built_at": time.time()}


_CHAIN_BRANDS = {
    "7-11": ["7-11", "7-eleven", "711", "統一超商"],
    "familymart": ["全家", "familymart"],
    "hilife": ["萊爾富", "hilife"],
    "okmart": ["ok超商", "ok mart"],
    "pxmart": ["全聯"],
    "poya": ["寶雅"],
    "simplemart": ["美廉社"],
    "mcdonalds": ["麥當勞", "mcdonald"],
    "starbucks": ["星巴克", "starbucks"],
}


_GENERIC_DUP_NAMES = {
    "廁所", "公廁", "公共廁所", "男廁", "女廁", "洗手間", "化妝室",
    "toilet", "restroom", "wc", "bathroom", "無障礙廁所", "親子廁所"
}


def _detect_chain_brand(text):
    """回傳連鎖品牌 key；同品牌不等於重複，只能當弱輔助。"""
    s = (text or "").strip().lower()
    if not s:
        return ""
    for brand, aliases in _CHAIN_BRANDS.items():
        for a in aliases:
            if a.lower() in s:
                return brand
    return ""


def _strip_chain_brand_for_dup(text):
    """移除連鎖品牌與廁所通用詞，留下門市/場域識別用。"""
    s = _compact_toilet_name(text or "")
    for aliases in _CHAIN_BRANDS.values():
        for a in aliases:
            s = s.replace(a.lower().replace(" ", ""), "")
    s = re.sub(r"[-_()（）・,，。．\s]+", "", s)
    return s


def _is_generic_duplicate_name(text):
    """判斷名稱是否太籠統；籠統名稱不能作為重複資料的強證據。"""
    raw = (text or "").strip().lower()
    compact = _compact_toilet_name(raw)
    no_brand = _strip_chain_brand_for_dup(raw)
    if not raw:
        return True
    if raw in _GENERIC_DUP_NAMES or compact in _GENERIC_DUP_NAMES:
        return True
    # 只剩品牌或只剩很短字串，例如 7-11、全家、寶雅、廁所
    if len(no_brand) <= 1:
        return True
    return False


def _strong_name_similarity_for_dup(a, b):
    """
    名稱相似度只作為輔助：
    - 泛稱或連鎖品牌本身不當強證據
    - 先移除「廁所/公廁」與品牌名，再比對門市/場域識別字
    """
    if _is_generic_duplicate_name(a) or _is_generic_duplicate_name(b):
        return 0.0

    a_core = _strip_chain_brand_for_dup(a)
    b_core = _strip_chain_brand_for_dup(b)
    raw_sim = _text_similarity(a, b)
    core_sim = _text_similarity(a_core, b_core)

    # 如果兩邊都是同一連鎖品牌，但沒有明確門市/場域識別，不用名稱判重複
    brand_a = _detect_chain_brand(a)
    brand_b = _detect_chain_brand(b)
    if brand_a and brand_b and brand_a == brand_b and (len(a_core) < 2 or len(b_core) < 2):
        return 0.0

    return max(raw_sim * 0.85, core_sim)


def _address_similarity_for_dup(a, b):
    """地址比名稱更重要，但兩邊都要有足夠長度才可靠。"""
    a = (a or "").strip()
    b = (b or "").strip()
    if len(a) < 5 or len(b) < 5:
        return 0.0
    return _text_similarity(a, b)


def _duplicate_level(distance_m, name_sim, addr_sim, same_brand=False):
    """
    Duplicate Detection 1.2：距離優先、地址優先，名稱只輔助。
    回傳 high / medium / low / none。
    """
    try:
        d = float(distance_m)
    except Exception:
        return "none"

    # 地址高度相似 + 很近，才是最穩的重複證據
    if d <= 30 and addr_sim >= 0.72:
        return "high"

    # 非泛稱的明確場域/門市名稱高度相似，且距離很近
    if d <= 25 and name_sim >= 0.88:
        return "high"

    # 同品牌不能單獨判重複；必須還有地址或明確名稱輔助
    if same_brand and d <= 20 and (addr_sim >= 0.60 or name_sim >= 0.82):
        return "high"

    if d <= 50 and addr_sim >= 0.62:
        return "medium"
    if d <= 40 and name_sim >= 0.82:
        return "medium"
    if same_brand and d <= 35 and (addr_sim >= 0.52 or name_sim >= 0.76):
        return "medium"

    # 極近但沒有文字證據，只能當低風險提醒，不直接讓資料 pending
    if d <= 10 and (addr_sim >= 0.35 or name_sim >= 0.55):
        return "low"

    return "none"


def find_similar_toilets(lat, lon, name="", address="", radius_m=50, limit=8, context=None, exclude_id=None):
    """
    找疑似重複廁所資料。
    Duplicate Detection 1.2：
    - 距離是必要前提；距離遠不因名稱相似就判重複。
    - 地址相似度比名稱更重要。
    - 「7-11 / 全家 / 公廁」這類泛稱或品牌名不能當重複主證據。
    """
    out = []
    try:
        lat = float(lat); lon = float(lon)
    except Exception:
        return []

    target_name = name or ""
    target_addr = address or ""
    target_brand = _detect_chain_brand(target_name)

    if not (context and isinstance(context, dict) and isinstance(context.get("items"), list)):
        context = _build_auto_verify_context()

    for r in context.get("items") or []:
        try:
            # 批次重驗時，避免把自己判成自己的重複資料
            if exclude_id is not None and str(r.get("id")) == str(exclude_id) and (r.get("source") in ("neon", "user_toilets", "user_added")):
                continue
            t_lat = float(r.get("lat")); t_lon = float(r.get("lon"))
        except Exception:
            continue
        if not _in_bbox(t_lat, t_lon, lat, lon, radius_m):
            continue
        try:
            d = haversine(lat, lon, t_lat, t_lon)
        except Exception:
            continue
        if d > radius_m:
            continue

        nm = r.get("name") or ""
        ad = r.get("address") or ""
        cand_brand = _detect_chain_brand(nm)
        same_brand = bool(target_brand and cand_brand and target_brand == cand_brand)
        name_sim = _strong_name_similarity_for_dup(target_name, nm)
        addr_sim = _address_similarity_for_dup(target_addr, ad)
        level = _duplicate_level(d, name_sim, addr_sim, same_brand=same_brand)

        if level != "none":
            out.append({
                "source": r.get("source") or "user_toilets",
                "id": r.get("id") or "",
                "name": nm,
                "address": ad,
                "distance_m": round(d, 1),
                "name_similarity": round(name_sim, 3),
                "address_similarity": round(addr_sim, 3),
                "same_brand": same_brand,
                "duplicate_level": level,
                "verification_status": r.get("verification_status") or "pending"
            })

    level_order = {"high": 0, "medium": 1, "low": 2}
    out.sort(key=lambda x: (
        level_order.get(x.get("duplicate_level"), 9),
        float(x.get("distance_m") or 9999),
        -max(float(x.get("address_similarity") or 0), float(x.get("name_similarity") or 0))
    ))
    return out[:limit]


def auto_verify_user_toilet(toilet, context=None, exclude_id=None):
    """
    Auto Verification 1.5.4：群眾地理資料品質驗證完整版（實用修正版）。
    只輸出三種 verification_status：approved / pending / rejected。

    設計原則：
    - rejected 只保留給明顯錯誤：非法座標、空白/測試名稱。
    - pending 只保留給真正需要人工確認的資料：高度/中度重複、名稱太籠統、地址缺失且場域不清。
    - shop_access_unclear、missing_entrance_hint、spatial_outlier_candidate 預設是 soft flag，會提醒但不一定把資料打成 pending。
    - 避免 1.5 過嚴導致大量資料從 approved 變 pending。
    """
    name = (toilet.get("name") or "").strip()
    address = (toilet.get("address") or "").strip()
    lat = toilet.get("lat")
    lon = toilet.get("lon")
    level = (toilet.get("level") or "").strip()
    floor_hint = (toilet.get("floor_hint") or "").strip()
    entrance_hint = (toilet.get("entrance_hint") or "").strip()
    access_note = (toilet.get("access_note") or "").strip()
    open_hours = (toilet.get("open_hours") or "").strip()

    score = 82
    flags = []
    reasons = []
    soft_flags = set()

    # 1) 基本欄位與座標合法性
    if _is_test_or_garbage_name(name):
        score -= 80
        flags.append("invalid_or_test_name")
        reasons.append("名稱空白或疑似測試資料")

    coord_ok = _valid_global_coordinate(lat, lon)
    if not coord_ok:
        score -= 95
        flags.append("invalid_coordinate")
        reasons.append("座標不是合法地球座標")
    elif _primary_region_risk(lat, lon):
        score -= 2
        flags.append("outside_primary_region")
        soft_flags.add("outside_primary_region")
        reasons.append("資料位於目前主要服務區域外，建議人工確認")

    facility_type = _facility_context(name, address, floor_hint, entrance_hint, access_note)

    # 2) 名稱品質：只判是否可辨識，不拿泛稱當重複主證據
    generic_names = {"廁所", "公廁", "男廁", "女廁", "無名稱", "toilet", "restroom", "wc", "洗手間", "化妝室"}
    compact_name = _normalize_text_for_verify(name)
    compact_generic = {_normalize_text_for_verify(x) for x in generic_names}
    if not name or len(compact_name) < 2 or name.lower() in generic_names or compact_name in compact_generic:
        score -= 25
        flags.append("name_too_generic")
        reasons.append("名稱過短或過於籠統")
    else:
        score += 7

    # 3) 資料完整度：依場域不同設定門檻
    has_address = _has_meaningful_address(address)
    has_floor = bool(floor_hint or level)
    has_entrance = bool(entrance_hint or access_note)
    has_access_info = bool(entrance_hint or access_note or open_hours)

    if has_address:
        score += 10
    else:
        # 缺地址不一定 pending；要看名稱和場域是否足夠清楚
        score -= 4
        flags.append("missing_address")
        soft_flags.add("missing_address")
        reasons.append("缺少可辨識地址或場域位置")

    if facility_type == "indoor_complex":
        if has_floor:
            score += 7
        else:
            score -= 3
            flags.append("missing_floor_hint")
            soft_flags.add("missing_floor_hint")
            reasons.append("多樓層或室內場域缺少樓層資訊")
        if has_entrance:
            score += 7
        else:
            score -= 3
            flags.append("missing_entrance_hint")
            soft_flags.add("missing_entrance_hint")
            reasons.append("室內或大型場域缺少入口/位置提示")
    elif facility_type == "shop":
        if has_floor:
            score += 3
        # 店家型資料：沒有開放/入口說明時先提醒，不直接全打 pending
        if has_access_info:
            score += 7
        else:
            score -= 3
            flags.append("shop_access_unclear")
            soft_flags.add("shop_access_unclear")
            reasons.append("店家型資料缺少是否開放或入口說明")
        if not has_address:
            score -= 10
            flags.append("shop_missing_address")
            reasons.append("店家型資料缺少地址，需人工確認")
    elif facility_type == "outdoor":
        if has_entrance:
            score += 6
        elif not has_address:
            score -= 2
            flags.append("outdoor_location_unclear")
            soft_flags.add("outdoor_location_unclear")
            reasons.append("戶外場域缺少地址或位置提示")
    else:
        if has_floor:
            score += 3
        if has_entrance:
            score += 4
        else:
            score -= 1
            flags.append("missing_entrance_hint")
            soft_flags.add("missing_entrance_hint")

    if open_hours:
        score += 2

    # 4) 重複資料偵測：距離 + 地址優先，名稱弱化
    similar = []
    if coord_ok:
        similar = find_similar_toilets(lat, lon, name=name, address=address, radius_m=80, limit=8, context=context, exclude_id=exclude_id)

    high_dup = [s_item for s_item in similar if s_item.get("duplicate_level") == "high"]
    medium_dup = [s_item for s_item in similar if s_item.get("duplicate_level") == "medium"]
    low_dup = [s_item for s_item in similar if s_item.get("duplicate_level") == "low"]

    # 1.5.4：重複資料改為「嚴格重複才進 pending」
    # 原本 high duplicate 太容易把靠近官方/既有資料的點全部打成 pending。
    # 現在 possible_duplicate_high / medium 先作為提醒；只有幾乎同點、且有強文字證據時，才標 strict_duplicate。
    strict_dup = []
    if high_dup:
        flags.append("possible_duplicate_high")
        soft_flags.add("possible_duplicate_high")
        reasons.append("附近已有相似廁所資料，系統標記為疑似重複提醒")
        for s_item in high_dup:
            try:
                d_val = float(s_item.get("distance_m") or 9999)
                name_val = float(s_item.get("name_similarity") or 0)
                addr_val = float(s_item.get("address_similarity") or 0)
                src_val = str(s_item.get("source") or "").lower()
                # 極近 + 地址或明確名稱高度相似，才是需要人工合併/確認的嚴格重複。
                # public_csv 只當參考來源，除非幾乎同點且地址/名稱非常像，否則不硬擋。
                if d_val <= 8 and (addr_val >= 0.78 or name_val >= 0.90):
                    strict_dup.append(s_item)
                elif src_val not in ("public_csv", "government") and d_val <= 12 and (addr_val >= 0.70 or name_val >= 0.86):
                    strict_dup.append(s_item)
            except Exception:
                pass
        if strict_dup:
            score -= 18
            flags.append("strict_duplicate")
            reasons.append("疑似與既有資料幾乎同點且文字高度相似，需人工確認是否合併")
        else:
            score -= 2
    elif medium_dup:
        flags.append("possible_duplicate_medium")
        soft_flags.add("possible_duplicate_medium")
        reasons.append("附近有相似廁所資料，僅作維護提醒")
        score -= 1
    elif low_dup:
        flags.append("possible_duplicate_low")
        soft_flags.add("possible_duplicate_low")

    # 5) 地址—座標一致性：預設不啟用 geocoding；啟用後仍以 pending 為主，不直接 rejected
    addr_flag, addr_dist, addr_reason = _address_coordinate_check(lat, lon, address)
    if addr_flag:
        flags.append(addr_flag)
        reasons.append(addr_reason or "地址與座標可能不一致")
        if addr_flag.endswith("high"):
            score -= 8
        elif addr_flag.endswith("medium"):
            score -= 3
        else:
            score -= 4
        soft_flags.add(addr_flag)

    # 6) 空間孤立/離群：soft flag；只有資料也不足時才 pending
    spatial = _spatial_context_signal(lat, lon, context=context, exclude_id=exclude_id) if coord_ok else {}
    if spatial.get("flag"):
        flags.append(spatial["flag"])
        soft_flags.add(spatial["flag"])
        if not has_address or "name_too_generic" in flags:
            score -= 3
            reasons.append("附近缺少參考資料且本筆資訊不足，建議人工確認")
        else:
            score -= 1

    score = max(0, min(100, int(round(score))))

    hard_reject = {"invalid_coordinate", "invalid_or_test_name"}
    # 1.5.4 實用化：只把真正需要人工處理的項目列為 hard pending。
    # high/medium duplicate、缺入口、店家開放不明都只當維護提醒，不直接卡住自動通過。
    hard_pending = {"name_too_generic", "strict_duplicate"}

    if any(f in flags for f in hard_reject):
        status = "rejected"
    elif any(f in flags for f in hard_pending):
        status = "pending"
    elif "shop_missing_address" in flags and score < 60:
        status = "pending"
    elif facility_type == "indoor_complex" and ("missing_floor_hint" in flags or "missing_entrance_hint" in flags) and score < 50:
        status = "pending"
    elif "missing_address" in flags and facility_type == "generic" and score < 48:
        status = "pending"
    elif any(f.startswith("address_coordinate_mismatch_high") for f in flags) and score < 52:
        status = "pending"
    elif "outside_primary_region" in flags and score < 48:
        status = "pending"
    elif score >= 45:
        status = "approved"
    else:
        status = "pending"

    if not reasons:
        if status == "approved":
            reasons.append("資料完整且未發現明顯重複，系統自動判定為低風險")
        elif status == "pending":
            reasons.append("資料可用但仍建議後台確認")
        else:
            reasons.append("資料存在明顯錯誤，系統建議排除")

    return {
        "verification_status": status,
        "auto_verification_score": score,
        "auto_verification_result": status,
        "auto_verification_reason": "；".join(dict.fromkeys(reasons)),
        "risk_flags": sorted(set(flags)),
        "similar_toilets": similar[:5],
        "facility_type": facility_type,
        "verification_version": "auto_verify_1_5_4",
        "soft_flags": sorted(soft_flags),
        "address_coordinate_distance_m": addr_dist,
        "spatial_context": spatial,
    }

