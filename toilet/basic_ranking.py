import math

def _findability_bonus(t):
    b = 0.0
    if t.get("place_hint"): b += 0.5
    if t.get("floor_hint"): b += 0.3
    return b

def sort_toilets(toilets):
    def _dist_key(x):
        # haversine() now returns float("inf") on error (Batch 3A).
        # int(float("inf")) raises OverflowError in Python, so cap the
        # value at 1e9 before converting.  Any non-numeric value also
        # falls back safely to the maximum sentinel distance.
        try:
            d = float(x.get("distance", 1e9))
            if not math.isfinite(d):
                d = 1e9
            return (int(d), -_findability_bonus(x))
        except (TypeError, ValueError, OverflowError):
            return (int(1e9), 0)
    toilets.sort(key=_dist_key)
    return toilets
