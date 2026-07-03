# Prompt for Claude: Full Functional Equivalence Review

請你幫我做一次非常嚴格的 code review / diff audit。

我有兩份版本：

1. **原始版**：一個 9000 多行的單檔 `app.py`
2. **新版**：已經模組化拆分的 Flask / LINE Bot 專案，入口是新版 `app.py`，其他功能拆到 `core/`、`toilet/`、`linebot_app/`、`dashboard/`、`admin/`、`features/`

你的任務不是重構、不是優化、不是改寫。你的任務是：

> 確認新版是否跟原始版功能完全等價，找出任何可能被改壞、漏接、少 import、route 消失、handler 沒註冊、變數順序錯誤、路徑跑掉、資料表或 SQL 被改、template 名稱錯、data/model/lang 路徑錯、env 變數讀取不同、LINE Bot 行為不同的地方。

## 絕對要求

- 不要直接修改程式碼。
- 先只輸出檢查報告。
- 不要順手優化。
- 不要改架構。
- 不要刪功能。
- 不要改文字內容。
- 不要改 route path / methods / endpoint 行為。
- 不要改 LINE reply / postback / quick reply 行為。
- 不要改 DB schema / SQL / 欄位名稱。
- 不要改資料路徑：`data/`、`templates/`、`static/`、`models/`、`lang/` 應維持原本專案根目錄位置。

## 請你逐項比對

### 1. Flask routes

請比對原始 `app.py` 與新版所有註冊後的 routes：

- path 是否一樣
- methods 是否一樣
- endpoint/function name 是否等價
- 是否有 route 漏掉
- 是否有重複註冊
- 是否有 route 順序造成衝突

特別檢查：

- `/callback`
- `/`
- `/healthz`
- `/readyz`
- `/go_to_toilet`
- `/nearby_toilets`
- `/dashboard`
- `/api/dashboard`
- `/dashboard/gap`
- `/api/gap-summary`
- `/dashboard/nts`
- `/submit_feedback`
- `/status_liff`
- `/api/status_candidates`
- `/api/status_report`
- `/consent`
- `/privacy`
- `/api/consent`
- `/add`
- `/submit_toilet`
- `/dashboard/maintenance`
- admin review APIs

### 2. LINE Bot handlers

請確認新版仍正確註冊：

- `MessageEvent + TextMessage`
- `MessageEvent + LocationMessage`
- `PostbackEvent`
- `/callback` signature validation
- duplicate event detection
- reply token dedupe
- `safe_reply`
- `reply_only`
- loading indicator

請確認下列流程功能不變：

- 使用者傳「附近廁所」
- 使用者傳位置
- 一般模式附近廁所查詢
- AI 推薦附近廁所
- 收藏 / 取消收藏
- 我的貢獻
- 刪除我的貢獻
- 語言切換
- 同意書檢查
- status LIFF
- feedback links

### 3. Function body equivalence

請逐一比對被搬到模組的函式內容是否與原始版等價，尤其：

- `build_nearby_toilets`
- `_merge_and_dedupe_lists`
- `query_public_csv_toilets`
- `query_saved_toilets`
- `query_overpass_toilets`
- `geocode_address`
- NTS / Trust Score functions
- `sort_toilets_nts`
- `sort_toilets_nts_1_0`
- favorites functions
- feedback functions
- status functions
- consent functions
- dashboard / gap functions
- auto verify functions
- submission / admin review functions
- AI usage / achievements functions

若新版用了 `configure_xxx(...)` 注入依賴，請確認注入順序在使用前、變數內容與原始版一致。

### 4. Imports and circular dependencies

請檢查：

- 是否有 missing import
- 是否有 circular import
- 是否有某個 module import 時就需要 app/request 但順序不對
- 是否有 `configure_xxx(...)` 沒呼叫就使用
- 是否有 global variable 被搬出去後變成另一份狀態，導致行為不同

特別注意：

- `_CACHE`
- `_ENRICH_CACHE`
- `_FAV_LOCK`
- `_LOC_SEM`
- `_USED_REPLY_TOKENS`
- `_consent_q`
- `_feedback_index_cache`
- `_status_index_cache`
- gap cache

### 5. File paths

請確認這些仍指向專案根目錄原位置，不要跑進模組資料夾：

- `data/public_toilets.csv`
- `data/favorites.txt`
- `cache.db`
- `models/clean_model.pkl`
- `models/label_encoder.pkl`
- `lang/zh.json`
- `lang/en.json`
- all `templates/*.html`

### 6. Database and SQL

請確認：

- Postgres `DATABASE_URL` / `POSTGRES_ENABLED` 行為不變
- `_pg_connect()` 行為不變
- `init_persistent_store()` 建表 SQL 沒改
- SQLite cache / analytics table SQL 沒改
- `favorites` Postgres + local fallback 行為不變
- feedback/status/recommendation/admin SQL 沒改

### 7. Dashboard and API response compatibility

請確認 dashboard/gap/nts APIs 回傳欄位不變：

- `/api/dashboard`
- `/api/events`
- `/api/line-insights`
- `/api/gap-summary`
- `/api/nts-behavior`
- `/api/source-query-metrics`
- `/api/shadow-ranking-metrics`
- admin APIs
- feedback/status APIs

### 8. Smoke tests to recommend

請最後列出一份 staging smoke test checklist，至少包含：

- app import / boot
- `/healthz`
- `/readyz`
- `/callback` invalid signature should abort 400
- LINE text message: 附近廁所
- LINE location message
- AI nearby mode
- favorite add/remove/list
- submit feedback
- status report
- consent page
- add toilet
- admin review APIs
- dashboard
- gap dashboard
- NTS dashboard

## 輸出格式

請用以下格式輸出：

1. **總結：是否可視為功能等價**
2. **高風險問題**：會直接壞功能的問題
3. **中風險問題**：可能在某些流程壞掉
4. **低風險問題 / cleanup 建議**
5. **確認沒問題的區塊**
6. **需要我手動 staging 測的清單**
7. **若要修，請列出最小修改方案，不要直接大改**

請務必逐項檢查，不要只看表面架構。
