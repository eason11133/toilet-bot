import os
import logging
import statistics

import joblib

try:
    import pandas as pd
except Exception:
    pd = None

from core.database import POSTGRES_ENABLED
from core.utils import _parse_lat_lon

# === 載入模型 ===
# Keep BASE_DIR equivalent to the original app.py directory.
BASE_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))

_fetch_feedback_pg_by_coord = None


def configure_cleanliness(fetch_feedback_pg_by_coord):
    global _fetch_feedback_pg_by_coord
    _fetch_feedback_pg_by_coord = fetch_feedback_pg_by_coord

def load_cleanliness_model():
    try:
        model_path = os.path.join(BASE_DIR, 'models', 'clean_model.pkl')
        model = joblib.load(model_path)
        logging.info("✅ 清潔度模型已載入")
        return model
    except Exception as e:
        logging.error(f"❌ 清潔度模型載入失敗: {e}")
        return None

def load_label_encoder():
    try:
        encoder_path = os.path.join(BASE_DIR, 'models', 'label_encoder.pkl')
        encoder = joblib.load(encoder_path)
        logging.info("✅ LabelEncoder 已載入")
        return encoder
    except Exception as e:
        logging.error(f"❌ LabelEncoder 載入失敗: {e}")
        return None

cleanliness_model = load_cleanliness_model()
label_encoder = load_label_encoder()

# === 參數 ===
LAST_N_HISTORY = 5

# === 清潔度預測 ===
def expected_from_feats(feats):
    try:
        if not feats or cleanliness_model is None:
            return None
        if pd is not None:
            df = pd.DataFrame(feats, columns=["rating","toilet_paper","accessibility"])
            probs = cleanliness_model.predict_proba(df)
        else:
            probs = cleanliness_model.predict_proba(feats)

        try:
            classes_enc = cleanliness_model.classes_
            labels = label_encoder.inverse_transform(classes_enc)
            labels = [float(x) for x in labels]
        except Exception:
            labels = [float(c) + 1.0 for c in cleanliness_model.classes_]

        exps = [sum(float(p)*float(l) for p, l in zip(p_row, labels)) for p_row in probs]
        return round(sum(exps)/len(exps), 2) if exps else None
    except Exception as e:
        logging.error(f"❌ 清潔度預測錯誤: {e}")
        return None

# === 即時預測 / 95% CI ===
def compute_nowcast_ci(lat, lon, k=LAST_N_HISTORY, tol=1e-6):
    """Compute nowcast from Neon/Postgres feedback."""
    if not POSTGRES_ENABLED:
        return None

    try:
        NOWCAST_MAX_K = int(os.getenv("NOWCAST_MAX_K", "8"))
    except Exception:
        NOWCAST_MAX_K = 8
    if k is None or not isinstance(k, int) or k <= 0:
        k = LAST_N_HISTORY
    k = min(k, NOWCAST_MAX_K)

    lat_f, lon_f = _parse_lat_lon(lat, lon)
    if lat_f is None or lon_f is None:
        return None

    try:
        rows = _fetch_feedback_pg_by_coord(lat_f, lon_f, tol=1e-4, limit=max(k * 3, k))
        if not rows:
            return None

        vals = []
        for row in rows[:k]:
            sc = row.get("cleanliness_score")
            try:
                if sc not in (None, ""):
                    vals.append(float(sc))
                    continue
            except Exception:
                pass
            try:
                if row.get("rating") not in (None, ""):
                    vals.append(float(row.get("rating")))
            except Exception:
                pass

        if not vals:
            return None

        n = len(vals)
        mean = round(sum(vals) / n, 2)
        if n == 1:
            return {"mean": mean, "lower": mean, "upper": mean, "n": 1}

        try:
            s = statistics.stdev(vals)
        except statistics.StatisticsError:
            s = 0.0
        se = s / (n ** 0.5)
        return {
            "mean": mean,
            "lower": max(1.0, round(mean - 1.96 * se, 2)),
            "upper": min(10.0, round(mean + 1.96 * se, 2)),
            "n": n,
        }
    except Exception as e:
        logging.error(f"❌ compute_nowcast_ci failed: {e}", exc_info=True)
        return None
