# Modular Project Structure

```text
app.py
config.py
core/
  app_support.py
  cache.py
  database.py
  i18n.py
  utils.py
linebot_app/
  handlers.py
  reply_tokens.py
  dedupe.py
  replies.py
  consent.py
  consent_routes.py
toilet/
  search.py
  data_sources.py
  scoring.py
  basic_ranking.py
  floor.py
  enrichment.py
  identity.py
  favorites.py
  cleanliness.py
  feedback.py
  feedback_routes.py
  status.py
  status_routes.py
  auto_verify.py
  submission.py
  recommendation_logs.py
dashboard/
  routes.py
  gap_analysis.py
  gap_routes.py
  nts_routes.py
admin/
  routes.py
features/
  usage.py
```

Keep existing asset/data folders next to this code:

```text
data/
templates/
static/
models/
lang/
```
