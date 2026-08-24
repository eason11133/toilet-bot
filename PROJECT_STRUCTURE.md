# 專案結構與模組職責

本文件提供逐層導覽。若想先理解資料如何流動，請先看 [ARCHITECTURE.md](ARCHITECTURE.md)。

## 根目錄

| 路徑 | 職責 |
| --- | --- |
| `app.py` | Flask composition root；組裝依賴、初始化服務並註冊路由 |
| `config.py` | 從環境變數讀取查詢、快取與回饋相關設定 |
| `requirements.txt` | Python runtime dependencies |
| `Procfile` | Render／Gunicorn 啟動命令 |
| `runtime.txt`、`.python-version` | Python runtime 版本 |
| `.env.example` | 可設定環境變數範例，不包含真實憑證 |

## `core/`：共用基礎設施

| 檔案 | 職責 |
| --- | --- |
| `database.py` | PostgreSQL schema、連線、SQLite cache 與分析資料表 |
| `cache.py` | 簡易記憶體 LRU cache |
| `i18n.py` | 使用者語言設定與中英文文字解析 |
| `utils.py` | 座標、距離、遮罩、HTML 安全與輸入解析工具 |
| `app_support.py` | health check、安全 headers、導航追蹤與 keepalive |

## `linebot_app/`：LINE 介面層

| 檔案 | 職責 |
| --- | --- |
| `handlers.py` | webhook 入口、文字／位置／postback 分派與 Flex Message 組裝 |
| `replies.py` | 可重用 Quick Reply 與錯誤提示 |
| `reply_tokens.py` | loading animation 與 reply token 單次使用保護 |
| `dedupe.py` | 依 `webhookEventId` 執行跨 worker 事件去重 |
| `consent.py` | 同意狀態讀寫與同意提示 |
| `consent_routes.py` | 同意頁、隱私頁與同意 API |

## `toilet/`：廁所領域功能

| 檔案 | 職責 |
| --- | --- |
| `search.py` | 搜尋流程編排、快取、來源 fallback、合併與去重 |
| `data_sources.py` | 政府 CSV、PostgreSQL 投稿與 Overpass 查詢 |
| `scoring.py` | NTS 與 Trust Score 計算及正式排序 |
| `basic_ranking.py` | 較單純的基礎排序策略 |
| `cleanliness.py` | 載入清潔度模型、預測與近期回饋信賴區間 |
| `feedback.py` | 回饋資料存取、摘要與索引 |
| `feedback_routes.py` | 回饋表單、趨勢、預測與 AI 摘要頁/API |
| `status.py` | 設施狀態回報的資料存取與彙整 |
| `status_routes.py` | 狀態候選、提交 API 與 LIFF 頁面 |
| `submission.py` | 使用者新增廁所的表單、驗證與儲存 |
| `auto_verify.py` | 投稿的座標、文字、重複性與風險自動檢查 |
| `favorites.py` | 使用者收藏新增、移除與查詢 |
| `recommendation_logs.py` | 推薦結果、shadow ranking、來源查詢與操作紀錄 |
| `floor.py` | 從名稱與 OSM tags 推斷樓層 |
| `enrichment.py` | 外部附近地點資訊補強 |
| `identity.py` | query ID 與 toilet ID 產生規則 |

## `dashboard/`：分析與研究介面

| 檔案 | 職責 |
| --- | --- |
| `routes.py` | 主儀表板、事件與 LINE insights API |
| `gap_analysis.py` | 依地區、網格、時間與使用者聚合服務缺口 |
| `gap_routes.py` | 缺口分析頁與 API |
| `nts_routes.py` | NTS、shadow ranking、來源效能與使用行為指標 |

## `admin/`：管理操作

| 檔案 | 職責 |
| --- | --- |
| `routes.py` | 投稿清單、人工審核、重新驗證與維護摘要 |

## `civicfix/`：公共設施資料維護

| 檔案／目錄 | 職責 |
| --- | --- |
| `routes.py` | CivicFix 頁面、驗證、同步、工單與 Gate 路由 |
| `sync.py` | 正規化後的設施資料批次 upsert 與同步紀錄 |
| `rescue.py` | 從負面回饋、缺口及同步問題建立維護工單 |
| `gate.py` | 投稿基本品質與座標規則評估 |
| `publish.py` | 核准、拒絕、待複查與正式資料發布 |
| `facilities.py` | 設施資料查詢與彙整 |
| `source_adapters/` | 將外部來源轉為系統統一欄位；目前包含環境部廁所 CSV adapter |

## `features/`：跨功能使用體驗

| 檔案 | 職責 |
| --- | --- |
| `usage.py` | 使用統計、成就、徽章、AI 使用摘要與 AI 附近推薦 |

## 資料與介面資產

| 目錄 | 職責 |
| --- | --- |
| `templates/` | LIFF、回饋、儀表板、管理與 CivicFix HTML templates |
| `data/` | 政府公共廁所 CSV 與本機資料檔 |
| `models/` | scikit-learn 清潔度模型及 encoders |
| `lang/` | 中英文 JSON 文字資源 |
| `scripts/` | 一次性資料回填與維運腳本 |

## 閱讀建議

依不同關注點，可從以下路徑開始：

- 想理解整體啟動：`app.py` → `ARCHITECTURE.md`
- 想理解 LINE 對話：`linebot_app/handlers.py` → `toilet/search.py`
- 想理解推薦：`toilet/search.py` → `toilet/scoring.py` → `toilet/recommendation_logs.py`
- 想理解資料品質：`toilet/submission.py` → `toilet/auto_verify.py` → `admin/routes.py`
- 想理解研究分析：`dashboard/routes.py` → `dashboard/gap_analysis.py` → `dashboard/nts_routes.py`
- 想理解維護閉環：`civicfix/rescue.py` → `civicfix/gate.py` → `civicfix/publish.py`
