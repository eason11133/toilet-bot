"""Project-level configuration for the public toilet LINE Bot.

This module intentionally contains only environment-variable based constants
and pure static settings. Runtime objects such as locks, caches, Flask app,
LINE SDK clients, database connections, and background workers remain in
app.py for now to preserve behavior during the first split.
"""

import os
from datetime import timezone, timedelta

from dotenv import load_dotenv

# Load .env here too, so config.py is safe to import independently.
# app.py also calls load_dotenv(); calling it twice is harmless and keeps
# the original runtime behavior effectively unchanged.
load_dotenv()

# Timezone
TW_TZ = timezone(timedelta(hours=8))

# Nearby location query controls
LOC_MAX_CONCURRENCY = int(os.getenv("LOC_MAX_CONCURRENCY", "3"))
LOC_QUERY_TIMEOUT_SEC = float(os.getenv("LOC_QUERY_TIMEOUT_SEC", "3.0"))
LOC_MAX_RESULTS = int(os.getenv("LOC_MAX_RESULTS", "4"))
SHOW_SEARCHING_BUBBLE = False

# Data enrichment / query limits
ENRICH_MAX_ITEMS = int(os.getenv("ENRICH_MAX_ITEMS", "60"))
OVERPASS_MAX_ITEMS = int(os.getenv("OVERPASS_MAX_ITEMS", "60"))
ENRICH_LRU_SIZE = int(os.getenv("ENRICH_LRU_SIZE", "300"))
NEARBY_LRU_SIZE = int(os.getenv("NEARBY_LRU_SIZE", "300"))

# Feedback / status index cache settings
FEEDBACK_INDEX_TTL = int(os.getenv("FEEDBACK_INDEX_TTL", "180"))
STATUS_INDEX_TTL = int(os.getenv("STATUS_INDEX_TTL", "180"))
FEEDBACK_LOOKBACK_LIMIT = int(os.getenv("FEEDBACK_LOOKBACK_LIMIT", "4000"))

# Internal TTL aliases; keep names unchanged because app.py still uses them.
_FEEDBACK_INDEX_TTL = int(os.getenv("FEEDBACK_INDEX_TTL_SEC", str(FEEDBACK_INDEX_TTL)))
_STATUS_INDEX_TTL = int(os.getenv("STATUS_INDEX_TTL_SEC", str(STATUS_INDEX_TTL)))
