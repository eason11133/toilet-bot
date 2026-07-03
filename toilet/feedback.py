import logging

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None
mask_user_id = None
_parse_lat_lon = None
safe_html = None
FEEDBACK_LOOKBACK_LIMIT = 4000

def configure_feedback(postgres_enabled, pg_connect, psycopg2_module, mask_user_id_func, parse_lat_lon_func, safe_html_func, feedback_lookback_limit=4000):
    global POSTGRES_ENABLED, _pg_connect, psycopg2, mask_user_id, _parse_lat_lon, safe_html, FEEDBACK_LOOKBACK_LIMIT
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module
    mask_user_id = mask_user_id_func
    _parse_lat_lon = parse_lat_lon_func
    safe_html = safe_html_func
    FEEDBACK_LOOKBACK_LIMIT = feedback_lookback_limit


def _insert_feedback_pg(name, address, rating, toilet_paper, accessibility, time_of_use,
                        comment, cleanliness_score, lat, lon, floor_hint="", uid=""):
    if not POSTGRES_ENABLED:
        return False
    conn = None
    try:
        conn = _pg_connect()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO toilet_feedbacks
            (name, address, rating, toilet_paper, accessibility, time_of_use,
             comment, cleanliness_score, lat, lon, floor_hint, user_id_hash, created_at)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, NOW())
        """, (
            name or "",
            address or "",
            int(rating) if str(rating).strip() else None,
            toilet_paper or "",
            accessibility or "",
            time_of_use or "",
            comment or "",
            float(cleanliness_score) if isinstance(cleanliness_score, (int, float)) or str(cleanliness_score).replace('.', '', 1).isdigit() else None,
            float(lat),
            float(lon),
            floor_hint or "",
            mask_user_id(uid) if uid else None,
        ))
        conn.commit()
        return True
    except Exception as e:
        if conn:
            try:
                conn.rollback()
            except Exception:
                pass
        logging.error(f"insert toilet_feedbacks failed: {e}", exc_info=True)
        return False
    finally:
        if conn:
            try:
                conn.close()
            except Exception:
                pass

def _fetch_feedback_pg_by_coord(lat, lon, tol=1e-6, limit=None):
    if not POSTGRES_ENABLED:
        return []
    lat_f, lon_f = _parse_lat_lon(lat, lon)
    if lat_f is None or lon_f is None:
        return []
    try:
        limit = int(limit or FEEDBACK_LOOKBACK_LIMIT or 4000)
    except Exception:
        limit = 4000
    conn = None
    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT name, address, rating, toilet_paper, accessibility, time_of_use,
                   comment, cleanliness_score, lat, lon, floor_hint, created_at
            FROM toilet_feedbacks
            WHERE ABS(lat - %s) <= %s AND ABS(lon - %s) <= %s
            ORDER BY created_at DESC
            LIMIT %s
        """, (float(lat_f), float(tol), float(lon_f), float(tol), limit))
        return [dict(r) for r in (cur.fetchall() or [])]
    except Exception as e:
        logging.error(f"fetch toilet_feedbacks by coord failed: {e}", exc_info=True)
        return []
    finally:
        if conn:
            try:
                conn.close()
            except Exception:
                pass

def _feedback_pg_to_public(row):
    def _clean(v):
        return "" if v is None else str(v)
    created = row.get("created_at")
    if hasattr(created, "isoformat"):
        created_s = created.isoformat()
    else:
        created_s = _clean(created)
    score = row.get("cleanliness_score")
    try:
        score_s = str(round(float(score), 2)) if score is not None else ""
    except Exception:
        score_s = _clean(score)
    return {
        "rating": _clean(row.get("rating")),
        "toilet_paper": _clean(row.get("toilet_paper")),
        "accessibility": _clean(row.get("accessibility")),
        "time_of_use": _clean(row.get("time_of_use")),
        "comment": safe_html(_clean(row.get("comment"))),
        "cleanliness_score": score_s,
        "created_at": created_s,
    }

def _feedback_rows_to_summary(rows):
    if not rows:
        return "尚無回饋資料"
    paper_counts = {"有": 0, "沒有": 0}
    access_counts = {"有": 0, "沒有": 0}
    scores = []
    comments = []
    for row in rows:
        if row.get("toilet_paper") in paper_counts:
            paper_counts[row.get("toilet_paper")] += 1
        if row.get("accessibility") in access_counts:
            access_counts[row.get("accessibility")] += 1
        try:
            if row.get("cleanliness_score") is not None:
                scores.append(float(row.get("cleanliness_score")))
            elif row.get("rating") is not None:
                scores.append(float(row.get("rating")))
        except Exception:
            pass
        c = (row.get("comment") or "").strip()
        if c:
            comments.append(c)
    avg_score = round(sum(scores) / len(scores), 2) if scores else "未預測"
    summary = f"🔍 筆數：{len(rows)}\n"
    summary += f"🧼 平均清潔分數：{avg_score}\n"
    summary += f"🧻 衛生紙：{'有' if paper_counts['有'] >= paper_counts['沒有'] else '沒有'}\n"
    summary += f"♿ 無障礙：{'有' if access_counts['有'] >= access_counts['沒有'] else '沒有'}\n"
    if comments:
        summary += f"💬 最新留言：{comments[0]}"
    return summary

def get_feedbacks_by_coord(lat, lon, tol=1e-6):
    if not POSTGRES_ENABLED:
        return []
    try:
        return [_feedback_pg_to_public(row) for row in _fetch_feedback_pg_by_coord(lat, lon, tol=tol)]
    except Exception as e:
        logging.error(f"❌ 讀取回饋列表（Neon 座標）錯誤: {e}", exc_info=True)
        return []

def get_feedback_summary_by_coord(lat, lon, tol=1e-6):
    if not POSTGRES_ENABLED:
        return "尚無回饋資料"
    try:
        return _feedback_rows_to_summary(_fetch_feedback_pg_by_coord(lat, lon, tol=tol))
    except Exception as e:
        logging.error(f"❌ 查詢回饋統計（Neon 座標）錯誤: {e}", exc_info=True)
        return "讀取錯誤"

# === 指示燈索引 ===
_feedback_index_cache = {"ts": 0, "data": {}}
# _FEEDBACK_INDEX_TTL is defined in global config section (see above)

def build_feedback_index():
    """Feedback feature is disabled; keep interface returning empty indicators."""
    return {}
