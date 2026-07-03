"""In-memory cache utilities for the toilet bot.

Extracted from app.py without changing behavior.
"""

from collections import OrderedDict

from config import ENRICH_LRU_SIZE, NEARBY_LRU_SIZE


class SimpleLRU(OrderedDict):
    def __init__(self, maxsize=500):
        super().__init__()
        self.maxsize = maxsize

    def get(self, key, default=None):
        if key in self:
            self.move_to_end(key)
            return super().get(key)
        return default

    def set(self, key, value):
        super().__setitem__(key, value)
        self.move_to_end(key)
        while len(self) > self.maxsize:
            self.popitem(last=False)


# ------ 將原本的 dict 換成 LRU（⚠️ 別在檔案其他地方再賦值覆蓋它們）------
_ENRICH_CACHE = SimpleLRU(maxsize=ENRICH_LRU_SIZE)
_CACHE = SimpleLRU(maxsize=NEARBY_LRU_SIZE)
