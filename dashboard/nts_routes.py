import logging

from flask import request, jsonify, Response

POSTGRES_ENABLED = False
_pg_connect = None
psycopg2 = None

def configure_nts_routes(postgres_enabled, pg_connect, psycopg2_module):
    global POSTGRES_ENABLED, _pg_connect, psycopg2
    POSTGRES_ENABLED = postgres_enabled
    _pg_connect = pg_connect
    psycopg2 = psycopg2_module

# === NTS dashboard routes ===
def api_shadow_ranking_metrics():
    """Shadow Ranking 比較 API。"""
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "error": "Postgres not enabled"}), 503
    production_version = (request.args.get("production") or "trust_score_2_0").strip() or "trust_score_2_0"
    shadow_version = (request.args.get("shadow") or "nts_1_0").strip() or "nts_1_0"
    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("""
            SELECT production_model_version, shadow_model_version,
                   COUNT(*) AS shadow_rows, COUNT(DISTINCT query_id) AS query_count,
                   MIN(created_at) AS first_time, MAX(created_at) AS last_time
            FROM recommendation_shadow_logs
            WHERE production_model_version = %s AND shadow_model_version = %s
            GROUP BY production_model_version, shadow_model_version
        """, (production_version, shadow_version))
        shadow_summary = cur.fetchone() or {
            "production_model_version": production_version,
            "shadow_model_version": shadow_version,
            "shadow_rows": 0,
            "query_count": 0,
            "first_time": None,
            "last_time": None,
        }
        cur.execute("""
            WITH clicked AS (
                SELECT a.id AS action_id, a.created_at AS action_time, a.query_id, a.toilet_id,
                       p.rank AS production_rank, s.rank AS shadow_rank,
                       p.toilet_name, p.distance_m,
                       p.nts_score AS production_score, s.nts_score AS shadow_score
                FROM user_actions a
                JOIN recommendation_logs p ON a.query_id = p.query_id AND a.toilet_id = p.toilet_id
                LEFT JOIN recommendation_shadow_logs s ON a.query_id = s.query_id AND a.toilet_id = s.toilet_id
                  AND s.production_model_version = %s AND s.shadow_model_version = %s
                WHERE a.action_type = 'click_navigation' AND p.model_version = %s
            )
            SELECT COUNT(*) AS clicked_items,
                   ROUND(AVG(production_rank)::numeric, 2) AS avg_production_clicked_rank,
                   ROUND(AVG(shadow_rank)::numeric, 2) AS avg_shadow_clicked_rank,
                   SUM(CASE WHEN production_rank = 1 THEN 1 ELSE 0 END) AS production_rank1_clicks,
                   SUM(CASE WHEN shadow_rank = 1 THEN 1 ELSE 0 END) AS shadow_rank1_clicks,
                   SUM(CASE WHEN shadow_rank IS NULL THEN 1 ELSE 0 END) AS unmatched_shadow_clicks
            FROM clicked
        """, (production_version, shadow_version, production_version))
        click_compare = cur.fetchone()
        cur.execute("""
            WITH clicked AS (
                SELECT a.id AS action_id, p.rank AS production_rank, s.rank AS shadow_rank
                FROM user_actions a
                JOIN recommendation_logs p ON a.query_id = p.query_id AND a.toilet_id = p.toilet_id
                LEFT JOIN recommendation_shadow_logs s ON a.query_id = s.query_id AND a.toilet_id = s.toilet_id
                  AND s.production_model_version = %s AND s.shadow_model_version = %s
                WHERE a.action_type = 'click_navigation' AND p.model_version = %s
            )
            SELECT 'production' AS model, production_rank AS rank, COUNT(*) AS click_count
            FROM clicked GROUP BY production_rank
            UNION ALL
            SELECT 'shadow' AS model, shadow_rank AS rank, COUNT(*) AS click_count
            FROM clicked WHERE shadow_rank IS NOT NULL GROUP BY shadow_rank
            ORDER BY model, rank
        """, (production_version, shadow_version, production_version))
        rank_distribution = cur.fetchall()
        cur.execute("""
            SELECT a.created_at AS action_time, p.query_id, p.toilet_name,
                   p.rank AS production_rank, s.rank AS shadow_rank,
                   p.nts_score AS production_score, s.nts_score AS shadow_score, p.distance_m
            FROM user_actions a
            JOIN recommendation_logs p ON a.query_id = p.query_id AND a.toilet_id = p.toilet_id
            LEFT JOIN recommendation_shadow_logs s ON a.query_id = s.query_id AND a.toilet_id = s.toilet_id
              AND s.production_model_version = %s AND s.shadow_model_version = %s
            WHERE a.action_type = 'click_navigation' AND p.model_version = %s
            ORDER BY a.created_at DESC
            LIMIT 20
        """, (production_version, shadow_version, production_version))
        recent_shadow_clicks = cur.fetchall()
        conn.close()
        return jsonify({
            "ok": True,
            "production_version": production_version,
            "shadow_version": shadow_version,
            "shadow_summary": shadow_summary,
            "click_compare": click_compare,
            "rank_distribution": rank_distribution,
            "recent_shadow_clicks": recent_shadow_clicks,
        })
    except Exception as e:
        logging.error(f"/api/shadow-ranking-metrics failed: {e}", exc_info=True)
        return jsonify({"ok": False, "error": str(e)}), 500


def dashboard_nts_page():
    """獨立的 NTS 行為分析頁：版本比較 + OSM fallback 效率分析。"""
    html = """
<!doctype html>
<html lang="zh-Hant">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width,initial-scale=1" />
  <title>NTS 排序行為分析</title>
  <style>
    :root{--bg:#f4f6fb;--card:#fff;--text:#1f2937;--muted:#6b7280;--line:#e5e7eb;--accent:#2563eb;--good:#059669;--warn:#d97706;--bad:#dc2626;--soft:#f8fafc;}
    *{box-sizing:border-box} body{margin:0;background:var(--bg);color:var(--text);font-family:-apple-system,BlinkMacSystemFont,"Segoe UI","Noto Sans TC",Arial,sans-serif;}
    .wrap{max-width:1220px;margin:0 auto;padding:24px 18px 48px}.top{display:flex;justify-content:space-between;align-items:flex-start;gap:16px;margin-bottom:18px}.title h1{margin:0;font-size:30px;letter-spacing:.02em}.title p{margin:8px 0 0;color:var(--muted)}
    .nav{display:flex;gap:10px;align-items:center;flex-wrap:wrap}.btn,.select{border:1px solid var(--line);background:#fff;border-radius:12px;padding:10px 14px;color:var(--text);text-decoration:none;font-weight:700}.btn:hover{border-color:var(--accent)}.select{min-width:220px}
    .grid{display:grid;grid-template-columns:repeat(5,1fr);gap:14px;margin:18px 0}@media(max-width:960px){.grid{grid-template-columns:repeat(2,1fr)}}@media(max-width:560px){.grid{grid-template-columns:1fr}.top{display:block}.nav{margin-top:12px}}
    .card{background:var(--card);border-radius:18px;padding:18px;box-shadow:0 8px 24px rgba(15,23,42,.06)}.k{color:var(--muted);font-size:13px;font-weight:700}.v{font-size:30px;font-weight:800;margin-top:8px}.s{font-size:13px;color:var(--muted);margin-top:8px}.section{background:var(--card);border-radius:18px;padding:18px;margin-top:16px;box-shadow:0 8px 24px rgba(15,23,42,.06)}
    .section h2{font-size:19px;margin:0 0 12px}.hint{color:var(--muted);font-size:13px;margin-bottom:12px;line-height:1.6}table{width:100%;border-collapse:collapse;font-size:14px}th,td{text-align:left;padding:12px;border-bottom:1px solid var(--line);vertical-align:top}th{color:#374151;background:#f9fafb}.rate{font-weight:800;color:var(--good)}.empty{color:var(--muted);padding:18px}.bar{height:8px;background:#eef2ff;border-radius:999px;overflow:hidden;min-width:90px}.bar>span{display:block;height:100%;background:var(--accent);border-radius:999px}.split{display:grid;grid-template-columns:1fr 1fr;gap:16px}@media(max-width:960px){.split{grid-template-columns:1fr}}
    .loading{color:var(--muted);padding:14px}.err{color:#b91c1c;background:#fee2e2;border:1px solid #fecaca;padding:12px;border-radius:12px;display:none}.tag{display:inline-block;background:#eef2ff;color:#3730a3;border-radius:999px;padding:4px 8px;font-size:12px;font-weight:700}.tag2{background:#ecfdf5;color:#047857}.tag0{background:#f3f4f6;color:#4b5563}.pos{color:var(--good);font-weight:800}.neg{color:var(--bad);font-weight:800}.neu{color:var(--muted);font-weight:800}.toolbar{display:flex;gap:10px;align-items:center;justify-content:space-between;flex-wrap:wrap}.mini{font-size:12px;color:var(--muted)}.pill{display:inline-flex;align-items:center;gap:6px;border-radius:999px;padding:6px 10px;background:var(--soft);border:1px solid var(--line);font-size:12px;font-weight:700;color:#475569}
    .explain-row{display:flex;gap:10px;flex-wrap:wrap;margin:14px 0 8px}.explain-btn{border:1px solid var(--line);background:#fff;border-radius:12px;padding:10px 14px;font-weight:800;cursor:pointer;color:#1f2937}.explain-btn:hover{border-color:var(--accent);color:var(--accent)}
    .modal-mask{position:fixed;inset:0;background:rgba(15,23,42,.45);display:none;align-items:center;justify-content:center;padding:18px;z-index:9999}.modal-mask.show{display:flex}.modal-box{width:min(760px,100%);max-height:86vh;overflow:auto;background:#fff;border-radius:20px;box-shadow:0 24px 70px rgba(15,23,42,.25);padding:22px}.modal-head{display:flex;justify-content:space-between;gap:12px;align-items:flex-start;margin-bottom:12px}.modal-head h2{margin:0;font-size:22px}.modal-close{border:0;background:#f3f4f6;border-radius:10px;width:38px;height:38px;font-size:22px;cursor:pointer}.modal-close:hover{background:#e5e7eb}.modal-box h3{margin:18px 0 8px;font-size:16px}.modal-box p,.modal-box li{line-height:1.7;color:#374151}.modal-box ul{padding-left:22px}.compare-mini{width:100%;border-collapse:collapse;margin-top:10px}.compare-mini th,.compare-mini td{border-bottom:1px solid var(--line);padding:10px;text-align:left}.compare-mini th{background:#f9fafb;color:#374151}
  </style>
</head>
<body>
  <div class="wrap">
    <div class="top">
      <div class="title">
        <h1>NTS 排序行為分析</h1>
        <p>比較 NTS 1.0 與 Trust Score 2.0 在真實使用者導航點擊與 OSM fallback 效率上的差異</p>
        <div class="explain-row">
          <button type="button" class="explain-btn" onclick="openExplainModal('nts1')">說明 NTS 1.0</button>
          <button type="button" class="explain-btn" onclick="openExplainModal('trust2')">說明 Trust Score 2.0</button>
        </div>
      </div>
      <div class="nav">
        <a class="btn" href="/dashboard">← 回總覽儀表板</a>
        <select id="versionSelect" class="select">
          <option value="all">全部版本</option>
          <option value="nts_1_0" selected>NTS 1.0 baseline</option>
          <option value="trust_score_2_0">Trust Score 2.0</option>
        </select>
      </div>
    </div>

    <div id="errorBox" class="err"></div>
    <div id="loading" class="loading">載入 NTS 行為資料中...</div>

    <div id="content" style="display:none">
      <div class="section">
        <div class="toolbar">
          <div>
            <h2>版本比較總表</h2>
            <div class="hint">並排比較 NTS 1.0 與 Trust Score 2.0。Trust Score 2.0 剛上線時會先顯示 0，跑一段時間後即可比較。</div>
          </div>
          <span class="pill">版本依 recommendation_logs.model_version 分組</span>
        </div>
        <div id="compareTable"></div>
      </div>

      <div class="grid">
        <div class="card"><div class="k">查詢數</div><div id="qCount" class="v">--</div><div class="s">Distinct query_id</div></div>
        <div class="card"><div class="k">推薦展示筆數</div><div id="recRows" class="v">--</div><div class="s">Top-k 推薦列數</div></div>
        <div class="card"><div class="k">導航點擊數</div><div id="navClicks" class="v">--</div><div class="s">click_navigation</div></div>
        <div class="card"><div class="k">查詢導航率</div><div id="queryRate" class="v">--</div><div class="s">點擊數 / 查詢數</div></div>
        <div class="card"><div class="k">推薦點擊率</div><div id="recRate" class="v">--</div><div class="s">點擊數 / 展示筆數</div></div>
      </div>

      <div class="section">
        <h2>版本資料量</h2>
        <div class="hint">確認 NTS 1.0 與 Trust Score 2.0 是否分開累積資料。</div>
        <div id="versionCounts"></div>
      </div>

      <div class="split">
        <div class="section">
          <h2>各 Rank 點擊率</h2>
          <div class="hint">觀察使用者是否主要點擊排序前面的推薦結果。</div>
          <div id="rankTable"></div>
        </div>
        <div class="section">
          <h2>NTS 分數區間點擊率</h2>
          <div class="hint">觀察 NTS 分數越高，導航點擊率是否越高。</div>
          <div id="scoreTable"></div>
        </div>
      </div>

      <div class="section">
        <div class="toolbar">
          <div>
            <h2>資料來源效率分析 / OSM fallback</h2>
            <div class="hint">觀察 csv、saved、osm、total 的查詢次數與耗時。OSM fallback 目標是：只有本地候選不足時才啟用，降低 Overpass 延遲風險。</div>
          </div>
          <span class="pill">讀取 /api/source-query-metrics</span>
        </div>
        <div id="sourceMetrics"></div>
      </div>

      <div class="section">
        <h2>OSM fallback 觸發原因</h2>
        <div class="hint">total 紀錄中的 reason 可用來判斷查詢是否使用 OSM、是否因候選不足而補查 OSM。</div>
        <div id="sourceReasons"></div>
      </div>

      <div class="section">
        <div class="toolbar">
          <div>
            <h2>Shadow Ranking：2.0 實際推薦 vs 1.0 後台比較</h2>
            <div class="hint">使用者實際看到 Trust Score 2.0，後台同步用 NTS 1.0 重新排序同一批推薦結果，比較使用者點擊的廁所在兩套模型中的名次。</div>
          </div>
          <span class="pill">讀取 /api/shadow-ranking-metrics</span>
        </div>
        <div id="shadowSummary"></div>
        <div id="shadowRankTable" style="margin-top:12px"></div>
        <div id="shadowRecent" style="margin-top:12px"></div>
      </div>

      <div class="section">
        <h2>最近導航點擊紀錄</h2>
        <div class="hint">檢查推薦結果與使用者點擊是否成功串接。</div>
        <div id="recentTable"></div>
      </div>
    </div>
  </div>


  <div id="explainModal" class="modal-mask" onclick="closeExplainModal(event)">
    <div class="modal-box" role="dialog" aria-modal="true" aria-labelledby="explainTitle" onclick="event.stopPropagation()">
      <div class="modal-head">
        <h2 id="explainTitle">模型說明</h2>
        <button type="button" class="modal-close" onclick="closeExplainModal()" aria-label="關閉">×</button>
      </div>
      <div id="explainBody"></div>
    </div>
  </div>

<script>
const $ = (id)=>document.getElementById(id);
const MODEL_EXPLAINS = {
  nts1: {
    title: 'NTS 1.0：固定權重 baseline 在做什麼？',
    body: `
      <p><b>NTS 1.0</b> 是本研究的「基準排序模型」。它的目的不是追求最複雜，而是先建立一套穩定、可解釋、可被驗證的公共廁所推薦排序方式。</p>

      <h3>一、它解決什麼問題？</h3>
      <p>一般找廁所系統常只看距離，但「最近」不一定代表「最適合」。例如最近的地點可能是資料未驗證、地址不完整、狀態異常，或根本已經被判定不可信。NTS 1.0 的核心就是把推薦問題從「找最近」提升成「找距離接近且資料比較可靠的廁所」。</p>

      <h3>二、它怎麼排序？</h3>
      <p>NTS 1.0 會把每一個候選廁所拆成四個節點分數，再用固定權重加總：</p>
      <table class="compare-mini">
        <tr><th>節點</th><th>代表意義</th><th>目前用途</th></tr>
        <tr><td>Distance 距離</td><td>離使用者越近分數越高</td><td>確保推薦結果仍然接近使用者</td></tr>
        <tr><td>Trust 可信度</td><td>資料來源與驗證狀態是否可信</td><td>避免未驗證或 rejected 資料排太前面</td></tr>
        <tr><td>Info 完整度</td><td>地址、樓層、入口提示、開放時間是否完整</td><td>提高使用者實際找到廁所的機率</td></tr>
        <tr><td>Status 狀態</td><td>是否有維修、停用、故障、正常等資訊</td><td>降低不可用廁所被推薦的風險</td></tr>
      </table>

      <h3>三、為什麼叫 baseline？</h3>
      <p>因為 NTS 1.0 使用固定規則，方便作為後續升級版本的比較基準。之後 Trust Score 2.0、OSM fallback、Shadow Ranking 都要和它比較，才能知道升級到底有沒有讓結果更好。</p>

      <h3>四、Dashboard 在看什麼？</h3>
      <ul>
        <li><b>Rank 點擊率</b>：第 1 名、第 2 名、第 3 名被點導航的比例。</li>
        <li><b>NTS 分數區間點擊率</b>：NTS 分數越高，使用者是否越容易點導航。</li>
        <li><b>最近導航紀錄</b>：每次使用者點導航時，那筆推薦當時的名次、距離、NTS、Trust 分數。</li>
      </ul>

      <h3>五、目前 NTS 1.0 的意義</h3>
      <p>如果 Rank 1 點擊率明顯高於後面名次，或高 NTS 分數區間的點擊率比較高，就代表 NTS 排序和使用者實際選擇有初步一致性。這可以作為研究中的真實使用者行為證據。</p>

      <table class="compare-mini">
        <tr><th>定位</th><td>固定權重、可解釋的排序基準線</td></tr>
        <tr><th>優點</th><td>簡單、穩定、可解釋，適合做 baseline</td></tr>
        <tr><th>限制</th><td>Trust 分數較固定，較難反映資料新鮮度、細部驗證品質與最近回報狀態</td></tr>
      </table>
    `
  },
  trust2: {
    title: 'Trust Score 2.0：動態可信度模型在做什麼？',
    body: `
      <p><b>Trust Score 2.0</b> 是 NTS 1.0 的升級版。它不是把整個系統推翻，而是把原本比較固定的 Trust 節點，升級成會依資料狀態變化的「動態可信度模型」。</p>

      <h3>一、為什麼需要 2.0？</h3>
      <p>NTS 1.0 裡，政府資料或 OSM 通常會拿到固定高分，使用者新增資料則依 approved / pending / rejected 給固定分數。但真實情境比較複雜：政府資料也可能很久沒更新，使用者新增資料如果資訊完整且後台已驗證，也可能很可靠。因此 2.0 的目標是讓可信度更接近真實資料品質。</p>

      <h3>二、Trust Score 2.0 多考慮了什麼？</h3>
      <table class="compare-mini">
        <tr><th>因素</th><th>說明</th><th>效果</th></tr>
        <tr><td>資料來源</td><td>政府資料、OSM、使用者新增資料給不同基礎分</td><td>保留來源差異</td></tr>
        <tr><td>驗證狀態</td><td>approved、pending、rejected 影響可信度</td><td>防止未驗證資料直接變高分</td></tr>
        <tr><td>verification_score</td><td>後台人工檢核分數可影響 Trust</td><td>讓後台檢核結果進入排序</td></tr>
        <tr><td>資訊完整度</td><td>地址、樓層、入口提示、開放時間完整會加分</td><td>鼓勵可找到、可使用的資料</td></tr>
        <tr><td>資料新鮮度</td><td>近期更新資料加分，太久未更新資料降分</td><td>避免過期資料長期佔高位</td></tr>
        <tr><td>狀態文字</td><td>維修、停用、故障、待確認、正常可用等字詞會影響狀態分數</td><td>更接近即時可用性</td></tr>
      </table>

      <h3>三、OSM fallback 在做什麼？</h3>
      <p>OSM / Overpass 可以補足政府資料不足的地方，但即時查詢很慢，也容易 timeout。所以 2.0 不是每次都查 OSM，而是先查本地資料：政府資料 + 使用者新增資料。只有當候選結果少於設定門檻，例如少於 2 筆時，才啟用 OSM fallback。</p>
      <ul>
        <li><b>沒用 OSM</b>：代表本地資料已足夠，速度通常較快。</li>
        <li><b>有用 OSM</b>：代表本地資料不足，需要外部資料補位，但耗時可能增加。</li>
        <li><b>Dashboard 會記錄</b>：csv、saved、osm、total 的查詢次數、平均耗時、是否 used_osm。</li>
      </ul>

      <h3>四、Shadow Ranking 在做什麼？</h3>
      <p>這是最重要的研究升級。使用者實際看到的是 <b>Trust Score 2.0</b> 的排序結果，但後台會用同一批候選廁所偷偷再跑一次 <b>NTS 1.0</b> 排序。注意：它不會重新查 OSM、CSV 或 Neon，只是用同一批資料重算分數與排序，所以效能負擔很小。</p>
      <p>這樣可以公平比較：同一次查詢、同一批候選資料，如果使用者點了某一間廁所，這間在 2.0 是第幾名？在 1.0 shadow ranking 又是第幾名？</p>

      <h3>五、我們要觀察什麼？</h3>
      <ul>
        <li><b>Rank 1 點擊率</b>：2.0 排第一的結果是否更常被點。</li>
        <li><b>查詢導航率</b>：每次查詢後，使用者是否更常點導航。</li>
        <li><b>NTS 高分區間點擊率</b>：高分結果是否真的比較吸引使用者。</li>
        <li><b>Shadow 比較</b>：使用者點擊的廁所在 2.0 的排名是否比 1.0 更前面。</li>
        <li><b>OSM 效率</b>：OSM fallback 是否減少不必要的外部查詢與延遲。</li>
      </ul>

      <h3>六、這個版本的研究意義</h3>
      <p>Trust Score 2.0 讓系統從「固定公式排序」往「資料品質會隨驗證、更新與回報而變動」前進。搭配 Shadow Ranking 後，系統不只是上線新模型，而是能用真實使用者導航點擊來驗證新模型是否比舊模型更接近使用者選擇。</p>

      <table class="compare-mini">
        <tr><th>定位</th><td>動態可信度 + OSM fallback + 真實行為驗證版本</td></tr>
        <tr><th>優點</th><td>更能反映資料品質、更新狀態、後台驗證與即時可用性</td></tr>
        <tr><th>注意</th><td>2.0 需要累積足夠查詢與導航點擊後，才適合和 1.0 做正式比較</td></tr>
      </table>
    `
  }
};

function openExplainModal(type){
  const item = MODEL_EXPLAINS[type] || MODEL_EXPLAINS.nts1;
  $('explainTitle').textContent = item.title;
  $('explainBody').innerHTML = item.body;
  $('explainModal').classList.add('show');
}
function closeExplainModal(e){
  if(e && e.target && e.target.id !== 'explainModal') return;
  $('explainModal').classList.remove('show');
}
document.addEventListener('keydown', (e)=>{ if(e.key === 'Escape' && $('explainModal')) $('explainModal').classList.remove('show'); });

function num(v){ const n = Number(v); return Number.isFinite(n) ? n : 0; }
function fmt(n){ if(n===null||n===undefined||n==='') return '--'; return Number(n).toLocaleString(); }
function pct(v){ if(v===null||v===undefined||v==='') return '--'; return `${v}%`; }
function esc(s){
  const map = {'&':'&amp;','<':'&lt;','>':'&gt;','\"':'&quot;',"'":'&#39;'};
  return String(s ?? '').replace(/[&<>\"']/g, m => map[m] || m);
}
function bar(rate){ const v=Math.max(0, Math.min(100, Number(rate)||0)); return `<div class="bar"><span style="width:${v}%"></span></div>`; }
function table(headers, rows, empty='目前沒有資料'){
  if(!rows || rows.length===0) return `<div class="empty">${empty}</div>`;
  return `<table><thead><tr>${headers.map(h=>`<th>${h}</th>`).join('')}</tr></thead><tbody>${rows.join('')}</tbody></table>`;
}
function deltaCell(v1, v2, suffix='%'){
  if(v1===null || v1===undefined || v2===null || v2===undefined || v1==='' || v2==='') return '<span class="neu">--</span>';
  const d = num(v2) - num(v1);
  const cls = d > 0 ? 'pos' : (d < 0 ? 'neg' : 'neu');
  const sign = d > 0 ? '+' : '';
  return `<span class="${cls}">${sign}${d.toFixed(2)}${suffix}</span>`;
}
function getRankRate(data, rank){
  const row = (data.rank_click_rate||[]).find(x => Number(x.rank) === Number(rank));
  return row ? row.click_rate_percent : null;
}
function getScoreRate(data, range){
  const row = (data.nts_score_click_rate||[]).find(x => x.nts_score_range === range);
  return row ? row.click_rate_percent : null;
}
async function fetchJson(url){
  const res = await fetch(url, {cache:'no-store'});
  const data = await res.json();
  if(!data.ok) throw new Error(data.error || 'API 回傳失敗');
  return data;
}
async function loadCompareTable(){
  const [v1, v2] = await Promise.all([
    fetchJson('/api/nts-behavior?version=nts_1_0'),
    fetchJson('/api/nts-behavior?version=trust_score_2_0')
  ]);
  const s1 = v1.summary || {}, s2 = v2.summary || {};
  const rows = [
    ['查詢數', fmt(s1.query_count), fmt(s2.query_count), ''],
    ['推薦展示筆數', fmt(s1.recommendation_rows), fmt(s2.recommendation_rows), ''],
    ['導航點擊數', fmt(s1.navigation_clicks), fmt(s2.navigation_clicks), ''],
    ['查詢導航率', pct(s1.click_rate_by_query_percent), pct(s2.click_rate_by_query_percent), deltaCell(s1.click_rate_by_query_percent, s2.click_rate_by_query_percent)],
    ['推薦點擊率', pct(s1.click_rate_by_recommendation_percent), pct(s2.click_rate_by_recommendation_percent), deltaCell(s1.click_rate_by_recommendation_percent, s2.click_rate_by_recommendation_percent)],
    ['Rank 1 點擊率', pct(getRankRate(v1,1)), pct(getRankRate(v2,1)), deltaCell(getRankRate(v1,1), getRankRate(v2,1))],
    ['Rank 2 點擊率', pct(getRankRate(v1,2)), pct(getRankRate(v2,2)), deltaCell(getRankRate(v1,2), getRankRate(v2,2))],
    ['90–100 分區間點擊率', pct(getScoreRate(v1,'90-100')), pct(getScoreRate(v2,'90-100')), deltaCell(getScoreRate(v1,'90-100'), getScoreRate(v2,'90-100'))],
    ['80–89 分區間點擊率', pct(getScoreRate(v1,'80-89')), pct(getScoreRate(v2,'80-89')), deltaCell(getScoreRate(v1,'80-89'), getScoreRate(v2,'80-89'))]
  ];
  $('compareTable').innerHTML = table(['指標','NTS 1.0','Trust Score 2.0','變化'], rows.map(r=>`<tr><td>${r[0]}</td><td>${r[1]}</td><td>${r[2]}</td><td>${r[3] || '<span class="mini">跑量後比較</span>'}</td></tr>`));
}
async function loadSourceMetrics(){
  const version = $('versionSelect').value;
  const data = await fetchJson(`/api/source-query-metrics?version=${encodeURIComponent(version)}`);
  $('sourceMetrics').innerHTML = table(['版本','來源','呼叫次數','使用 OSM 次數','平均耗時','最大耗時','結果總數','成功次數'], (data.by_source||[]).map(r=>
    `<tr><td><span class="tag ${r.model_version==='trust_score_2_0'?'tag2':'tag0'}">${esc(r.model_version)}</span></td><td>${esc(r.source_name)}</td><td>${fmt(r.call_count)}</td><td>${fmt(r.used_osm_count)}</td><td>${fmt(r.avg_elapsed_ms)} ms</td><td>${fmt(r.max_elapsed_ms)} ms</td><td>${fmt(r.total_result_count)}</td><td>${fmt(r.success_count)}</td></tr>`
  ), '目前沒有 source_query_logs 資料，部署 Trust Score 2.0 + OSM metrics 後會開始累積。');
  $('sourceReasons').innerHTML = table(['版本','原因','次數','平均總耗時'], (data.total_reason||[]).map(r=>
    `<tr><td><span class="tag ${r.model_version==='trust_score_2_0'?'tag2':'tag0'}">${esc(r.model_version)}</span></td><td>${esc(r.reason)}</td><td>${fmt(r.count)}</td><td>${fmt(r.avg_elapsed_ms)} ms</td></tr>`
  ), '目前沒有 total reason 資料。');
}
async function loadShadowMetrics(){
  try{
    const data = await fetchJson('/api/shadow-ranking-metrics?production=trust_score_2_0&shadow=nts_1_0');
    const s = data.shadow_summary || {};
    const c = data.click_compare || {};
    $('shadowSummary').innerHTML = table(['指標','數值'], [
      `<tr><td>Production model</td><td><span class="tag tag2">${esc(data.production_version||'trust_score_2_0')}</span></td></tr>`,
      `<tr><td>Shadow model</td><td><span class="tag tag0">${esc(data.shadow_version||'nts_1_0')}</span></td></tr>`,
      `<tr><td>Shadow 查詢數</td><td>${fmt(s.query_count)}</td></tr>`,
      `<tr><td>Shadow 推薦列數</td><td>${fmt(s.shadow_rows)}</td></tr>`,
      `<tr><td>已點擊且可比較筆數</td><td>${fmt(c.clicked_items)}</td></tr>`,
      `<tr><td>2.0 被點擊平均名次</td><td>${fmt(c.avg_production_clicked_rank)}</td></tr>`,
      `<tr><td>1.0 shadow 被點擊平均名次</td><td>${fmt(c.avg_shadow_clicked_rank)}</td></tr>`,
      `<tr><td>2.0 Rank1 點擊數</td><td>${fmt(c.production_rank1_clicks)}</td></tr>`,
      `<tr><td>1.0 shadow Rank1 點擊數</td><td>${fmt(c.shadow_rank1_clicks)}</td></tr>`
    ], '尚無 shadow ranking 資料。請確認 NTS_MODEL_VERSION=trust_score_2_0 且 SHADOW_NTS_ENABLE=1，並累積導航點擊。');
    $('shadowRankTable').innerHTML = table(['模型','被點擊名次','點擊數'], (data.rank_distribution||[]).map(r=>
      `<tr><td>${esc(r.model)}</td><td>${esc(r.rank)}</td><td>${fmt(r.click_count)}</td></tr>`
    ), '尚無 rank distribution 資料。');
    $('shadowRecent').innerHTML = table(['時間','廁所','2.0 Rank','1.0 Shadow Rank','2.0 分數','1.0 分數','距離'], (data.recent_shadow_clicks||[]).map(r=>
      `<tr><td>${esc(r.action_time)}</td><td>${esc(r.toilet_name)}</td><td>${esc(r.production_rank)}</td><td>${esc(r.shadow_rank)}</td><td>${esc(r.production_score)}</td><td>${esc(r.shadow_score)}</td><td>${Number(r.distance_m||0).toFixed(1)}m</td></tr>`
    ), '尚無最近 shadow 點擊資料。');
  }catch(e){
    $('shadowSummary').innerHTML = `<div class="empty">Shadow metrics 尚未可用：${esc(e.message)}</div>`;
    $('shadowRankTable').innerHTML = '';
    $('shadowRecent').innerHTML = '';
  }
}

async function loadNtsBehavior(){
  const version = $('versionSelect').value;
  $('loading').style.display='block'; $('content').style.display='none'; $('errorBox').style.display='none';
  try{
    const data = await fetchJson(`/api/nts-behavior?version=${encodeURIComponent(version)}`);
    const s = data.summary || {};
    $('qCount').textContent = fmt(s.query_count);
    $('recRows').textContent = fmt(s.recommendation_rows);
    $('navClicks').textContent = fmt(s.navigation_clicks);
    $('queryRate').textContent = pct(s.click_rate_by_query_percent);
    $('recRate').textContent = pct(s.click_rate_by_recommendation_percent);

    $('versionCounts').innerHTML = table(['版本','推薦展示','查詢數'], (data.version_counts||[]).map(r=>
      `<tr><td><span class="tag ${r.model_version==='trust_score_2_0'?'tag2':'tag0'}">${esc(r.model_version)}</span></td><td>${fmt(r.recommendation_rows)}</td><td>${fmt(r.query_count)}</td></tr>`
    ));
    $('rankTable').innerHTML = table(['Rank','展示','點擊','點擊率',''], (data.rank_click_rate||[]).map(r=>
      `<tr><td>${esc(r.rank)}</td><td>${fmt(r.shown_count)}</td><td>${fmt(r.click_count)}</td><td class="rate">${pct(r.click_rate_percent)}</td><td>${bar(r.click_rate_percent)}</td></tr>`
    ));
    $('scoreTable').innerHTML = table(['分數區間','展示','點擊','點擊率',''], (data.nts_score_click_rate||[]).map(r=>
      `<tr><td>${esc(r.nts_score_range)}</td><td>${fmt(r.shown_count)}</td><td>${fmt(r.click_count)}</td><td class="rate">${pct(r.click_rate_percent)}</td><td>${bar(r.click_rate_percent)}</td></tr>`
    ));
    $('recentTable').innerHTML = table(['時間','版本','Rank','廁所','距離','NTS','Trust','Info','Status'], (data.recent_clicks||[]).map(r=>
      `<tr><td>${esc(r.action_time)}</td><td>${esc(r.model_version)}</td><td>${esc(r.rank)}</td><td>${esc(r.toilet_name)}</td><td>${Number(r.distance_m||0).toFixed(1)}m</td><td>${esc(r.nts_score)}</td><td>${esc(r.trust_score)}</td><td>${esc(r.info_score)}</td><td>${esc(r.status_score)}</td></tr>`
    ));
    try { await loadCompareTable(); } catch(e) { $('compareTable').innerHTML = `<div class="empty">版本比較暫時無法載入：${esc(e.message)}</div>`; }
    try { await loadSourceMetrics(); } catch(e) { $('sourceMetrics').innerHTML = `<div class="empty">資料來源效率暫時無法載入：${esc(e.message)}</div>`; $('sourceReasons').innerHTML = ''; }
    try { await loadShadowMetrics(); } catch(e) { $('shadowSummary').innerHTML = `<div class="empty">Shadow metrics 暫時無法載入：${esc(e.message)}</div>`; $('shadowRankTable').innerHTML = ''; $('shadowRecent').innerHTML = ''; }
    $('loading').style.display='none'; $('content').style.display='block';
  }catch(e){
    $('loading').style.display='none'; $('errorBox').style.display='block'; $('errorBox').textContent = '載入失敗：' + e.message;
  }
}
$('versionSelect').addEventListener('change', loadNtsBehavior);
document.addEventListener('DOMContentLoaded', loadNtsBehavior);
</script>
</body>
</html>
    """
    return Response(html, mimetype="text/html; charset=utf-8")


def api_source_query_metrics():
    """
    資料來源查詢耗時分析 API
    用法：
    /api/source-query-metrics
    /api/source-query-metrics?version=trust_score_2_0
    """
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "error": "Postgres not enabled"}), 503

    version = (request.args.get("version") or "all").strip() or "all"

    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)

        cur.execute("""
            SELECT
                COALESCE(model_version, 'unknown') AS model_version,
                source_name,
                COUNT(*) AS call_count,
                SUM(CASE WHEN used_osm THEN 1 ELSE 0 END) AS used_osm_count,
                ROUND(AVG(elapsed_ms)::numeric, 2) AS avg_elapsed_ms,
                MAX(elapsed_ms) AS max_elapsed_ms,
                SUM(result_count) AS total_result_count,
                SUM(CASE WHEN success THEN 1 ELSE 0 END) AS success_count
            FROM source_query_logs
            WHERE (%s = 'all' OR model_version = %s)
            GROUP BY COALESCE(model_version, 'unknown'), source_name
            ORDER BY model_version, source_name
        """, (version, version))
        by_source = cur.fetchall()

        cur.execute("""
            SELECT
                COALESCE(model_version, 'unknown') AS model_version,
                reason,
                COUNT(*) AS count,
                ROUND(AVG(elapsed_ms)::numeric, 2) AS avg_elapsed_ms
            FROM source_query_logs
            WHERE (%s = 'all' OR model_version = %s)
              AND source_name = 'total'
            GROUP BY COALESCE(model_version, 'unknown'), reason
            ORDER BY model_version, reason
        """, (version, version))
        total_reason = cur.fetchall()

        conn.close()
        return jsonify({
            "ok": True,
            "version": version,
            "by_source": by_source,
            "total_reason": total_reason
        })
    except Exception as e:
        logging.error(f"/api/source-query-metrics failed: {e}", exc_info=True)
        return jsonify({"ok": False, "error": str(e)}), 500


def api_nts_behavior():
    """
    NTS 行為分析 API
    用法：
    /api/nts-behavior
    /api/nts-behavior?version=nts_1_0
    /api/nts-behavior?version=trust_score_2_0
    """
    if not POSTGRES_ENABLED:
        return jsonify({"ok": False, "error": "Postgres not enabled"}), 503

    version = (request.args.get("version") or "all").strip() or "all"

    try:
        conn = _pg_connect()
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)

        cur.execute("""
            SELECT
                COALESCE(model_version, 'unknown') AS model_version,
                COUNT(*) AS recommendation_rows,
                COUNT(DISTINCT query_id) AS query_count
            FROM recommendation_logs
            GROUP BY COALESCE(model_version, 'unknown')
            ORDER BY model_version
        """)
        version_counts = cur.fetchall()

        cur.execute("""
            WITH filtered AS (
                SELECT *
                FROM recommendation_logs
                WHERE (%s = 'all' OR model_version = %s)
            ),
            clicks AS (
                SELECT DISTINCT a.id
                FROM user_actions a
                JOIN filtered r
                  ON a.query_id = r.query_id
                 AND a.toilet_id = r.toilet_id
                WHERE a.action_type = 'click_navigation'
            )
            SELECT
                COUNT(*) AS recommendation_rows,
                COUNT(DISTINCT query_id) AS query_count,
                (SELECT COUNT(*) FROM clicks) AS navigation_clicks,
                ROUND((SELECT COUNT(*) FROM clicks)::numeric / NULLIF(COUNT(*), 0) * 100, 2) AS click_rate_by_recommendation_percent,
                ROUND((SELECT COUNT(*) FROM clicks)::numeric / NULLIF(COUNT(DISTINCT query_id), 0) * 100, 2) AS click_rate_by_query_percent
            FROM filtered
        """, (version, version))
        summary = cur.fetchone()

        cur.execute("""
            WITH filtered AS (
                SELECT *
                FROM recommendation_logs
                WHERE (%s = 'all' OR model_version = %s)
            ),
            impressions AS (
                SELECT rank, COUNT(*) AS shown_count
                FROM filtered
                GROUP BY rank
            ),
            clicks AS (
                SELECT r.rank, COUNT(DISTINCT a.id) AS click_count
                FROM user_actions a
                JOIN filtered r
                  ON a.query_id = r.query_id
                 AND a.toilet_id = r.toilet_id
                WHERE a.action_type = 'click_navigation'
                GROUP BY r.rank
            )
            SELECT
                i.rank,
                i.shown_count,
                COALESCE(c.click_count, 0) AS click_count,
                ROUND(COALESCE(c.click_count, 0)::numeric / NULLIF(i.shown_count, 0) * 100, 2) AS click_rate_percent
            FROM impressions i
            LEFT JOIN clicks c ON i.rank = c.rank
            ORDER BY i.rank ASC
        """, (version, version))
        rank_click_rate = cur.fetchall()

        cur.execute("""
            WITH filtered AS (
                SELECT *
                FROM recommendation_logs
                WHERE (%s = 'all' OR model_version = %s)
            ),
            shown AS (
                SELECT
                    r.id,
                    r.query_id,
                    r.toilet_id,
                    r.rank,
                    r.nts_score,
                    CASE WHEN a.id IS NULL THEN 0 ELSE 1 END AS clicked
                FROM filtered r
                LEFT JOIN user_actions a
                  ON r.query_id = a.query_id
                 AND r.toilet_id = a.toilet_id
                 AND a.action_type = 'click_navigation'
            ),
            grouped AS (
                SELECT
                    CASE
                        WHEN nts_score >= 90 THEN '90-100'
                        WHEN nts_score >= 80 THEN '80-89'
                        WHEN nts_score >= 70 THEN '70-79'
                        WHEN nts_score >= 60 THEN '60-69'
                        ELSE '<60'
                    END AS nts_score_range,
                    COUNT(*) AS shown_count,
                    SUM(clicked) AS click_count,
                    ROUND(SUM(clicked)::numeric / NULLIF(COUNT(*), 0) * 100, 2) AS click_rate_percent
                FROM shown
                GROUP BY
                    CASE
                        WHEN nts_score >= 90 THEN '90-100'
                        WHEN nts_score >= 80 THEN '80-89'
                        WHEN nts_score >= 70 THEN '70-79'
                        WHEN nts_score >= 60 THEN '60-69'
                        ELSE '<60'
                    END
            )
            SELECT *
            FROM grouped
            ORDER BY
                CASE nts_score_range
                    WHEN '90-100' THEN 1
                    WHEN '80-89' THEN 2
                    WHEN '70-79' THEN 3
                    WHEN '60-69' THEN 4
                    ELSE 5
                END
        """, (version, version))
        nts_score_click_rate = cur.fetchall()

        cur.execute("""
            WITH filtered AS (
                SELECT *
                FROM recommendation_logs
                WHERE (%s = 'all' OR model_version = %s)
            )
            SELECT
                a.created_at AS action_time,
                a.action_type,
                r.model_version,
                r.query_id,
                r.rank,
                r.toilet_name,
                r.distance_m,
                r.nts_score,
                r.distance_score,
                r.trust_score,
                r.info_score,
                r.status_score
            FROM user_actions a
            JOIN filtered r
              ON a.query_id = r.query_id
             AND a.toilet_id = r.toilet_id
            WHERE a.action_type = 'click_navigation'
            ORDER BY a.created_at DESC
            LIMIT 20
        """, (version, version))
        recent_clicks = cur.fetchall()

        conn.close()
        return jsonify({
            "ok": True,
            "version": version,
            "version_counts": version_counts,
            "summary": summary,
            "rank_click_rate": rank_click_rate,
            "nts_score_click_rate": nts_score_click_rate,
            "recent_clicks": recent_clicks
        })

    except Exception as e:
        logging.error(f"/api/nts-behavior failed: {e}", exc_info=True)
        return jsonify({"ok": False, "error": str(e)}), 500


def register_nts_routes(app):
    app.add_url_rule('/api/shadow-ranking-metrics', endpoint='api_shadow_ranking_metrics', view_func=api_shadow_ranking_metrics)
    app.add_url_rule('/dashboard/nts', endpoint='dashboard_nts_page', view_func=dashboard_nts_page, methods=['GET'])
    app.add_url_rule('/api/source-query-metrics', endpoint='api_source_query_metrics', view_func=api_source_query_metrics)
    app.add_url_rule('/api/nts-behavior', endpoint='api_nts_behavior', view_func=api_nts_behavior)
