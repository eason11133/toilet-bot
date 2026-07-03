import re

# === 樓層推斷 ===
def _floor_from_tags(tags: dict):
    if not tags:
        return None
    level = tags.get("level") or tags.get("level:ref") or tags.get("addr:floor")
    loc = (tags.get("location") or "").lower()
    try:
        if level is not None and str(level).strip() != "":
            lv_str = str(level).strip().replace("F","").replace("f","")
            lv = int(float(lv_str))
            if lv < 0:
                return f"地下{abs(lv)}F"
            if lv == 0:
                return "地面"
            return f"{lv}F"
    except Exception:
        pass
    if loc == "underground":
        return "地下"
    if loc == "overground":
        return "地面"
    return None

_ZH_DIGIT = {"零":0,"〇":0,"一":1,"二":2,"兩":2,"三":3,"四":4,"五":5,"六":6,"七":7,"八":8,"九":9}

def _zh_to_int_word(word: str):
    if not word:
        return None
    w = word.replace("两","兩")
    if "十" not in w:
        return _ZH_DIGIT.get(w)
    left, _, right = w.partition("十")
    tens = 10 if left == "" else (_ZH_DIGIT.get(left, 0) * 10)
    ones = 0 if right == "" else _ZH_DIGIT.get(right, 0)
    val = tens + ones
    return val if val > 0 else None

def _normalize_floor_label(n: int, underground: bool=False):
    try:
        n = int(n)
    except Exception:
        return None
    if underground:
        return f"地下{abs(n)}F"
    if n == 0:
        return "地面"
    return f"{n}F"

def _floor_from_name(name: str):
    if not name:
        return None
    s = str(name).strip()
    s_lower = s.lower()

    if re.search(r'(?:^|[^a-z])g\s*/?\s*f(?:[^a-z]|$)', s_lower) or re.search(r'ground\s*floor', s_lower):
        return "地面"

    m = re.search(r'(?:^|[^a-z])[bＢ]\s*-?\s*(\d{1,2})\s*(?:f|樓|層)?(?:[^0-9]|$)', s_lower)
    if m:
        n = int(m.group(1))
        if n > 0:
            return _normalize_floor_label(n, underground=True)

    m = re.search(r'地下\s*([一二兩三四五六七八九十〇零\d]{1,3})\s*(?:樓|層|f)?', s_lower)
    if m:
        token = m.group(1)
        n = int(token) if token.isdigit() else _zh_to_int_word(token)
        if n and n > 0:
            return _normalize_floor_label(n, underground=True)

    m = re.search(r'(\d{1,3})\s*(?:f|樓|層)(?:[^a-z0-9]|$)', s_lower)
    if m:
        return _normalize_floor_label(int(m.group(1)))

    m = re.search(r'第?\s*([一二兩三四五六七八九十〇零]{1,3})\s*(?:樓|層)', s_lower)
    if m:
        n = _zh_to_int_word(m.group(1))
        if n:
            return _normalize_floor_label(n)

    m = re.search(r'(?:^|[^a-z])l\s*(\d{1,3})(?:[^0-9]|$)', s_lower)
    if m:
        return _normalize_floor_label(int(m.group(1)))

    return None
