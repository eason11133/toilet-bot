# GitHub Clean Replacement Package

This package is the modular V2 code plus the production assets needed from the current repository.

## Included

- Modular Python code: `app.py`, `config.py`, `core/`, `toilet/`, `linebot_app/`, `dashboard/`, `admin/`, `features/`
- Required app assets: `templates/`, `lang/`, `models/`, `data/public_toilets.csv`, `data/favorites.txt`
- Deployment files: `requirements.txt`, `Procfile`, `runtime.txt`, `.python-version`

## Not included on purpose

- `.git/`
- `.env`
- `credentials.json`
- `secrets_backup.txt`
- `__pycache__/`
- old practice/experiment/mirror files
- runtime `cache.db`

## Safe replacement method

1. Make a backup branch first.
2. Delete old junk files from the repository root, but keep Git history.
3. Copy the contents of this package into the repository root.
4. Commit and push.
5. Deploy to staging and run the checklist in `VERIFICATION_REPORT.md`.

Do not upload `.env` or credentials to GitHub. Configure secrets in Render/GitHub environment variables instead.
