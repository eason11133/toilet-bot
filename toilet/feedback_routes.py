import json
import logging
import statistics
import urllib.parse
from urllib.parse import quote

from flask import request, render_template, redirect, jsonify

from features.usage import _ai_quota_check_and_inc, AI_MODEL, client

POSTGRES_ENABLED = False
_parse_lat_lon = None
norm_coord = None
_floor_from_name = None
expected_from_feats = None
_fetch_feedback_pg_by_coord = None
_insert_feedback_pg = None
get_feedback_summary_by_coord = None
get_feedbacks_by_coord = None
compute_nowcast_ci = None
LAST_N_HISTORY = 5
FEEDBACK_LOOKBACK_LIMIT = 4000
_append_uid_lang = None
_user_lang_q = None
PUBLIC_URL = ""
L = None
resolve_lang = None
_get_liff_status_id = lambda: ""


def configure_feedback_routes(
    postgres_enabled,
    parse_lat_lon_func,
    norm_coord_func,
    floor_from_name_func,
    expected_from_feats_func,
    fetch_feedback_pg_by_coord_func,
    insert_feedback_pg_func,
    get_feedback_summary_by_coord_func,
    get_feedbacks_by_coord_func,
    compute_nowcast_ci_func,
    last_n_history,
    feedback_lookback_limit,
    append_uid_lang_func,
    user_lang_q_func,
    public_url,
    L_func,
    resolve_lang_func,
    get_liff_status_id_func=None,
):
    global POSTGRES_ENABLED, _parse_lat_lon, norm_coord, _floor_from_name, expected_from_feats
    global _fetch_feedback_pg_by_coord, _insert_feedback_pg, get_feedback_summary_by_coord, get_feedbacks_by_coord
    global compute_nowcast_ci, LAST_N_HISTORY, FEEDBACK_LOOKBACK_LIMIT
    global _append_uid_lang, _user_lang_q, PUBLIC_URL, L, resolve_lang, _get_liff_status_id

    POSTGRES_ENABLED = postgres_enabled
    _parse_lat_lon = parse_lat_lon_func
    norm_coord = norm_coord_func
    _floor_from_name = floor_from_name_func
    expected_from_feats = expected_from_feats_func
    _fetch_feedback_pg_by_coord = fetch_feedback_pg_by_coord_func
    _insert_feedback_pg = insert_feedback_pg_func
    get_feedback_summary_by_coord = get_feedback_summary_by_coord_func
    get_feedbacks_by_coord = get_feedbacks_by_coord_func
    compute_nowcast_ci = compute_nowcast_ci_func
    LAST_N_HISTORY = last_n_history
    FEEDBACK_LOOKBACK_LIMIT = feedback_lookback_limit
    _append_uid_lang = append_uid_lang_func
    _user_lang_q = user_lang_q_func
    PUBLIC_URL = public_url
    L = L_func
    resolve_lang = resolve_lang_func
    _get_liff_status_id = get_liff_status_id_func or (lambda: "")

def feedback_form(toilet_name, address):
    address = address or request.args.get("address", "")
    return render_template(
        "feedback_form.html",
        toilet_name=toilet_name,
        address=address,
        lat=request.args.get("lat", ""),
        lon=request.args.get("lon", "")
    )


def get_nowcast_by_coord(lat, lon):
    try:
        res = compute_nowcast_ci(lat, lon)
        if not res:
            return {"success": True, "n": 0}, 200
        res["success"] = True
        return res, 200
    except Exception as e:
        logging.error(f"❌ Nowcast API 錯誤: {e}")
        return {"success": False}, 500


def submit_feedback():
    logging.info(f"[submit_feedback] content_type={request.content_type}")

    if not POSTGRES_ENABLED:
        logging.error("submit_feedback failed: Postgres storage is not enabled")
        return "提交失敗：回饋儲存尚未設定", 503

    try:
        payload_json = request.get_json(silent=True)
        if payload_json and isinstance(payload_json, dict) and len(payload_json) > 0:
            data = payload_json
            src = "json"
            getv = lambda k, d="": (data.get(k) if data.get(k) is not None else d)
        else:
            data = request.form
            src = "form"
            getv = lambda k, d="": (data.get(k, d) if data.get(k, d) is not None else d)

        name = (getv("name", "") or "").strip()
        address = (getv("address", "") or "").strip()
        lat_raw = ((getv("lat", "") or request.args.get("lat") or "")).strip()
        lon_raw = ((getv("lon", "") or request.args.get("lon") or "")).strip()

        lat_f, lon_f = _parse_lat_lon(lat_raw, lon_raw)
        if lat_f is None or lon_f is None:
            return "座標格式錯誤", 400

        lat = norm_coord(lat_f)
        lon = norm_coord(lon_f)
        rating = ((getv("rating", "") or "")).strip()
        toilet_paper = ((getv("toilet_paper", "") or "")).strip()
        accessibility = ((getv("accessibility", "") or "")).strip()
        time_of_use = ((getv("time_of_use", "") or "")).strip()
        comment = ((getv("comment", "") or "")).strip()
        floor_hint = ((getv("floor_hint", "") or "")).strip()

        logging.info(
            f"[submit_feedback] src={src} name={name[:40]} rating={rating} "
            f"lat={lat} lon={lon} paper={toilet_paper} access={accessibility}"
        )

        missing = []
        if not name: missing.append("name")
        if not rating: missing.append("rating")
        if not lat_raw: missing.append("lat")
        if not lon_raw: missing.append("lon")
        if not toilet_paper: missing.append("toilet_paper")
        if not accessibility: missing.append("accessibility")
        if missing:
            return "缺少必要欄位：" + ", ".join(missing), 400

        try:
            r = int(rating)
            if r < 1 or r > 10:
                return "清潔度評分必須在 1 到 10 之間", 400
        except ValueError:
            return "清潔度評分必須是數字", 400

        if not floor_hint:
            inferred = _floor_from_name(name)
            if inferred:
                floor_hint = inferred

        paper_map = {"有": 1, "沒有": 0, "沒注意": 0}
        access_map = {"有": 1, "沒有": 0, "沒注意": 0}
        cur_feat = [r, paper_map.get(toilet_paper, 0), access_map.get(accessibility, 0)]

        hist_feats = []
        try:
            recent = _fetch_feedback_pg_by_coord(lat, lon, tol=1e-4, limit=LAST_N_HISTORY)
            for row in recent:
                try:
                    rr = int(row.get("rating"))
                except Exception:
                    continue
                pp = (row.get("toilet_paper") or "沒注意").strip()
                aa = (row.get("accessibility") or "沒注意").strip()
                hist_feats.append([rr, paper_map.get(pp, 0), access_map.get(aa, 0)])
        except Exception as e:
            logging.warning(f"讀歷史回饋失敗，僅用單筆特徵預測：{e}")

        pred_with_hist = expected_from_feats([cur_feat] + hist_feats) or expected_from_feats([cur_feat]) or "未預測"
        uid = (request.args.get("uid") or "").strip()

        ok = _insert_feedback_pg(
            name=name, address=address, rating=rating, toilet_paper=toilet_paper,
            accessibility=accessibility, time_of_use=time_of_use, comment=comment,
            cleanliness_score=pred_with_hist, lat=lat, lon=lon, floor_hint=floor_hint, uid=uid
        )
        if not ok:
            return "提交失敗：回饋資料寫入 Neon 失敗", 500

        lang = (request.args.get("lang") or "").strip().lower()
        target = f"/toilet_feedback_by_coord/{lat}/{lon}"
        if uid:
            target = _append_uid_lang(target, uid, (lang if lang in ("en", "zh") else _user_lang_q(uid)))
        return redirect(target)

    except Exception as e:
        logging.error(f"❌ 提交回饋表單錯誤: {e}", exc_info=True)
        return "提交失敗", 500


def toilet_feedback(toilet_name):
    """Legacy name-based feedback page; use coordinate page."""
    liff_id = _get_liff_status_id()
    uid = (request.args.get("uid") or "").strip()
    lang = (request.args.get("lang") or "").strip().lower()
    if uid and not lang:
        try:
            lang = _user_lang_q(uid)
        except Exception:
            lang = "zh"
        qs = request.args.to_dict(flat=True)
        qs["lang"] = lang
        return redirect(request.path + "?" + urllib.parse.urlencode(qs), code=302)
    return render_template(
        "toilet_feedback.html",
        toilet_name=toilet_name,
        summary="請改用座標版入口（卡片上的『查詢回饋（座標）』）。",
        feedbacks=[], address="", avg_pred_score=("N/A" if lang == "en" else "未預測"),
        lat="", lon="", liff_id=liff_id, uid=uid, lang=(lang if lang in ["en", "zh"] else "zh")
    )


def toilet_feedback_by_coord(lat, lon):
    liff_id = _get_liff_status_id()
    uid = (request.args.get("uid") or "").strip()
    lang = (request.args.get("lang") or "").strip().lower()
    if uid and not lang:
        try:
            lang = _user_lang_q(uid)
        except Exception:
            lang = "zh"
        qs = request.args.to_dict(flat=True)
        qs["lang"] = lang
        return redirect(request.path + "?" + urllib.parse.urlencode(qs), code=302)

    if not POSTGRES_ENABLED:
        return render_template(
            "toilet_feedback.html",
            toilet_name=f"廁所（{lat}, {lon}）",
            summary="（回饋資料庫尚未就緒）",
            feedbacks=[], address=f"{lat},{lon}", avg_pred_score=("N/A" if lang == "en" else "未預測"),
            lat=lat, lon=lon, liff_id=liff_id, uid=uid, lang=(lang if lang in ["en", "zh"] else "zh")
        )

    try:
        name = f"廁所（{lat}, {lon}）"
        summary = get_feedback_summary_by_coord(lat, lon)
        feedbacks = get_feedbacks_by_coord(lat, lon)
        scores = []
        for fb in feedbacks:
            try:
                sc = fb.get("cleanliness_score")
                if sc not in (None, ""):
                    scores.append(float(sc))
            except Exception:
                pass
        avg_pred_score = round(sum(scores) / len(scores), 2) if scores else "未預測"
        return render_template(
            "toilet_feedback.html",
            toilet_name=name, summary=summary, feedbacks=feedbacks, address=f"{lat},{lon}",
            avg_pred_score=avg_pred_score, lat=lat, lon=lon,
            liff_id=liff_id, uid=uid, lang=(lang if lang in ["en", "zh"] else "zh")
        )
    except Exception as e:
        logging.error(f"❌ 渲染回饋頁面（Neon 座標）錯誤: {e}", exc_info=True)
        return "查詢失敗", 500


def get_clean_trend_by_name(toilet_name):
    # Name-based lookup is no longer supported. Use coordinate API instead.
    return {"success": True, "data": []}, 200


def get_clean_trend_by_coord(lat, lon):
    if not POSTGRES_ENABLED:
        return {"success": True, "data": []}, 200
    try:
        rows = _fetch_feedback_pg_by_coord(lat, lon, tol=1e-4)
        data = []
        for row in rows:
            created = row.get("created_at")
            t = created.isoformat() if hasattr(created, "isoformat") else str(created or "")
            score = row.get("cleanliness_score")
            try:
                if score is None and row.get("rating") is not None:
                    score = float(row.get("rating"))
                if score is not None:
                    data.append({"t": t, "score": round(float(score), 2)})
            except Exception:
                continue
        data.sort(key=lambda d: d["t"])
        return {"success": True, "data": data}, 200
    except Exception as e:
        logging.error(f"❌ 趨勢 API（Neon 座標版）錯誤: {e}", exc_info=True)
        return {"success": False, "data": []}, 500


def ai_feedback_summary_page(lat, lon):
    """
    顯示某一個廁所（用座標表示）的 AI 回饋摘要頁面。
    前端會在這個頁面裡用 JS 呼叫 /api/ai_feedback_summary/<lat>/<lon>。
    """
    uid = (request.args.get("uid") or "").strip()

    base = PUBLIC_URL.rstrip("/") if PUBLIC_URL else request.url_root.rstrip("/")
    # 給前端 JS 用的 API URL（順便把 uid 帶進去，用來做每日額度控制）
    api_url = f"{base}/api/ai_feedback_summary/{lat}/{lon}"
    if uid:
        api_url += f"?uid={quote(uid)}"

    # 順便做一個「去留下回饋」的連結（就算沒回饋也可以用）
    feedback_url = (
        f"{base}/feedback_form/"
        f"{quote('這間廁所')}/{quote(lat + ',' + lon)}"
        f"?lat={lat}&lon={lon}&address={quote(lat + ',' + lon)}"
    )

    return render_template(
        "ai_feedback_summary.html",
        lat=lat,
        lon=lon,
        api_url=api_url,
        feedback_url=feedback_url,
        uid=uid,
    )


def api_ai_feedback_summary(lat, lon):
    """Read feedback from Neon/Postgres and ask OpenAI for a summary."""
    uid = (request.args.get("uid") or "").strip()

    try:
        if not POSTGRES_ENABLED:
            return jsonify({
                "success": False,
                "message": L(uid, "回饋資料庫尚未就緒，請稍後再試", "Feedback storage not ready, please try again later")
            }), 503

        if client is None:
            return jsonify({
                "success": False,
                "message": L(uid, "AI 金鑰尚未設定", "AI key not configured")
            }), 500

        lang = resolve_lang(uid=uid, lang=request.args.get("lang"))
        lang_rule = "請使用繁體中文回答。" if lang != "en" else "Please answer in English."
        system_msg = (
            f"You analyze restroom feedback and summarize it clearly. {lang_rule}"
            if lang == "en"
            else f"你負責分析廁所回饋並清楚摘要重點。{lang_rule}"
        )

        lat_f, lon_f = _parse_lat_lon(lat, lon)
        if lat_f is None or lon_f is None:
            return jsonify({
                "success": False,
                "message": L(uid, "lat/lon 格式錯誤", "Invalid latitude / longitude")
            }), 400

        matched = []
        rows = _fetch_feedback_pg_by_coord(lat_f, lon_f, tol=1e-4, limit=FEEDBACK_LOOKBACK_LIMIT)
        for row in rows:
            created = row.get("created_at")
            created_s = created.isoformat() if hasattr(created, "isoformat") else str(created or "")
            matched.append({
                "rating": str(row.get("rating") or ""),
                "paper": row.get("toilet_paper") or "",
                "access": row.get("accessibility") or "",
                "comment": row.get("comment") or "",
                "created_at": created_s,
            })

        if not matched:
            return jsonify({
                "success": True,
                "summary": "",  # 讓前端依 lang 顯示自己的 no_data 文案，避免混語
                "data": [],
                "has_data": False
            }), 200

        # 最多送 30 筆給 AI
        matched = matched[:30]

        # 2️⃣ 每日 AI 額度控制（uid → fallback IP）
        xff = (request.headers.get("X-Forwarded-For") or "").split(",")[0].strip()
        ip = xff or (request.remote_addr or "unknown")
        quota_key = uid or f"ip:{ip}"

        ok, used = _ai_quota_check_and_inc(f"fb:{quota_key}")
        if not ok:
            return jsonify({
                "success": True,
                "summary": L(
                    uid,
                    "今天 AI 摘要查詢次數已達上限，明天再來看看最新的分析吧 🙏",
                    "You’ve reached today’s AI summary limit. Please try again tomorrow 🙏"
                ),
                "data": matched,
                "has_data": True,
                "limit_reached": True
            }), 200

        # 3️⃣ 組 AI Prompt（依語言）
        matched_json = json.dumps(matched, ensure_ascii=False)

        if lang == "en":
            prompt = f"""
You are a restroom cleanliness analysis assistant.

Please read the following feedback data (JSON format) and provide:
1. Common recent issues (e.g. lack of toilet paper, slippery floor, odor, broken facilities)
2. Overall user sentiment (positive / neutral / negative) with a brief explanation
3. Cleanliness trend (getting cleaner / getting worse / mostly stable). If data is insufficient, explain why.
4. A concise recommendation in **no more than 3 lines**

Please respond in **English**, using bullet points or short sentences.

Feedback data (JSON):
{matched_json}
            """.strip()
        else:
            prompt = f"""
你是一個廁所清潔度分析助理，請閱讀以下回饋資料（JSON 格式），並輸出：

1. 最近常見的主要問題（例如：衛生紙不足、地板濕滑、異味、設備老舊等）
2. 使用者整體情緒傾向（正面 / 中性 / 負面），簡短說明原因
3. 清潔度狀態的趨勢（變乾淨 / 變髒 / 大致持平），如果資料不足請說明
4. 最後請用三行以內，給出一段總結建議

請使用繁體中文、條列式或短句，讓一般使用者容易閱讀。

以下是回饋資料（JSON）：
{matched_json}
            """.strip()

        ai_resp = client.chat.completions.create(
            model=AI_MODEL,
            messages=[
                {"role": "system", "content": system_msg},
                {"role": "user", "content": prompt}
            ]
        )

        summary = (ai_resp.choices[0].message.content or "").strip()

        return jsonify({
            "success": True,
            "summary": summary,
            "data": matched,
            "has_data": True
        }), 200

    except Exception as e:
        logging.error(f"AI summary error: {e}", exc_info=True)
        return jsonify({
            "success": False,
            "message": L(uid, "AI 發生錯誤，請稍後再試", "AI error, please try again later")
        }), 500


def _debug_predict():
    try:
        r = int(request.args.get("rating"))
        paper = request.args.get("paper", "沒注意")
        acc = request.args.get("access", "沒注意")

        paper_map = {"有": 1, "沒有": 0, "沒注意": 0}
        access_map = {"有": 1, "沒有": 0, "沒注意": 0}
        feat = [r, paper_map.get(paper, 0), access_map.get(acc, 0)]
        exp = expected_from_feats([feat])

        return {
            "ok": True,
            "input": {"rating": r, "paper": paper, "access": acc},
            "expected": exp
        }, 200
    except Exception as e:
        logging.error(e)
        return {"ok": False}, 500



def register_feedback_routes(app):
    app.add_url_rule('/feedback_form/<toilet_name>/', endpoint='feedback_form', view_func=feedback_form, defaults={'address': ''})
    app.add_url_rule('/feedback_form/<toilet_name>/<path:address>', endpoint='feedback_form', view_func=feedback_form)
    app.add_url_rule('/get_nowcast_by_coord/<lat>/<lon>', endpoint='get_nowcast_by_coord', view_func=get_nowcast_by_coord)
    app.add_url_rule('/submit_feedback', endpoint='submit_feedback', view_func=submit_feedback, methods=['POST'])
    app.add_url_rule('/toilet_feedback/<toilet_name>', endpoint='toilet_feedback', view_func=toilet_feedback)
    app.add_url_rule('/toilet_feedback_by_coord/<lat>/<lon>', endpoint='toilet_feedback_by_coord', view_func=toilet_feedback_by_coord)
    app.add_url_rule('/get_clean_trend/<path:toilet_name>', endpoint='get_clean_trend_by_name', view_func=get_clean_trend_by_name)
    app.add_url_rule('/get_clean_trend_by_coord/<lat>/<lon>', endpoint='get_clean_trend_by_coord', view_func=get_clean_trend_by_coord)
    app.add_url_rule('/ai_feedback_summary_page/<lat>/<lon>', endpoint='ai_feedback_summary_page', view_func=ai_feedback_summary_page)
    app.add_url_rule('/api/ai_feedback_summary/<lat>/<lon>', endpoint='api_ai_feedback_summary', view_func=api_ai_feedback_summary)
    app.add_url_rule('/_debug_predict', endpoint='_debug_predict', view_func=_debug_predict)
