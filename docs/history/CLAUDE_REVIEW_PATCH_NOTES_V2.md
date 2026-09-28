# V2 Patch Notes After Claude Equivalence Review

Claude's review found no critical blockers and judged the modular refactor safe for staging, but it flagged one small behavior difference:

- `features/usage.py` captured `LIFF_STATUS_ID` once at startup instead of reading it through `_get_liff_status_id()` per request.

V2 fixes that difference by:

- Passing `_get_liff_status_id` into `configure_usage()` as `get_liff_status_id_func`.
- Adding `_current_liff_status_id()` in `features/usage.py`.
- Using `_current_liff_status_id()` in `achievements_liff_page()` and `badges_liff_page()`.

This makes the LIFF ID behavior closer to the original app.py behavior.

Other Claude notes were not changed because they were either harmless startup logging details, pre-existing original behavior, or already false in the final bundle (`reply_only` exists in `linebot_app/handlers.py`).

Validation performed:

- `python -m py_compile` passed for all Python files in the V2 bundle.
