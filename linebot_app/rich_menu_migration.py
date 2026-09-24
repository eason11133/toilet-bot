"""One-time repair for legacy rich-menu help postbacks.

LINE Official Account keyword replies only receive real text-message events.
Older menus used a postback with ``displayText``, which looks like user text in
the chat but cannot trigger an OA keyword reply.  This migration clones each
active legacy menu, preserves its image and every other action, replaces only
``cmd=help`` with a message action, and repoints the existing aliases/default.
"""

from __future__ import annotations

import copy
import logging
import os
import threading
from urllib.parse import parse_qs

import requests

from core.database import POSTGRES_ENABLED, _pg_connect


_API = "https://api.line.me/v2/bot"
_DATA_API = "https://api-data.line.me/v2/bot"
_LOCK_ID = 764_202_609
_LOCAL_LOCK = threading.Lock()


def _is_help_postback(action: dict) -> bool:
    if action.get("type") != "postback":
        return False
    data = str(action.get("data") or "")
    try:
        return (parse_qs(data).get("cmd") or [None])[0] == "help"
    except Exception:
        return data == "cmd=help" or data.startswith("cmd=help&")


def _help_message_text(action: dict) -> str:
    displayed = str(action.get("displayText") or "").strip()
    if displayed in {"使用說明", "User Guide"}:
        return displayed
    data = str(action.get("data") or "")
    lang = (parse_qs(data).get("lang") or [""])[0].lower()
    return "User Guide" if lang == "en" else "使用說明"


def _replace_help_actions(menu: dict) -> tuple[dict, bool]:
    repaired = copy.deepcopy(menu)
    changed = False
    for area in repaired.get("areas") or []:
        action = area.get("action") or {}
        if not _is_help_postback(action):
            continue
        message_action = {
            "type": "message",
            "text": _help_message_text(action),
        }
        if action.get("label"):
            message_action["label"] = action["label"]
        area["action"] = message_action
        changed = True
    return repaired, changed


def _json_request(method: str, path: str, headers: dict, **kwargs):
    response = requests.request(
        method,
        f"{_API}{path}",
        headers=headers,
        timeout=30,
        **kwargs,
    )
    response.raise_for_status()
    return response.json() if response.content else {}


def _active_menu_ids(headers: dict, menus: list[dict]) -> tuple[set[str], list[dict], str | None]:
    aliases = _json_request("GET", "/richmenu/alias/list", headers).get("aliases", [])
    default_id = None
    response = requests.get(f"{_API}/user/all/richmenu", headers=headers, timeout=30)
    if response.status_code == 200:
        default_id = response.json().get("richMenuId")
    elif response.status_code != 404:
        response.raise_for_status()

    active = {a.get("richMenuId") for a in aliases if a.get("richMenuId")}
    if default_id:
        active.add(default_id)
    # A legacy project may have created menus before aliases/default helpers
    # were added. In that case inspect every menu, but activate nothing new
    # unless an existing alias/default points to it.
    if not active:
        active = {m.get("richMenuId") for m in menus if m.get("richMenuId")}
    return active, aliases, default_id


def _clone_repaired_menu(token: str, menu: dict, repaired: dict) -> str:
    headers = {"Authorization": f"Bearer {token}"}
    create_payload = {
        "size": repaired["size"],
        "selected": bool(repaired.get("selected", False)),
        "name": f"{repaired.get('name', 'Rich menu')} [help fixed]"[:300],
        "chatBarText": repaired["chatBarText"],
        "areas": repaired["areas"],
    }
    new_id = _json_request(
        "POST",
        "/richmenu",
        {**headers, "Content-Type": "application/json"},
        json=create_payload,
    )["richMenuId"]

    image = requests.get(
        f"{_DATA_API}/richmenu/{menu['richMenuId']}/content",
        headers=headers,
        timeout=30,
    )
    image.raise_for_status()
    upload = requests.post(
        f"{_DATA_API}/richmenu/{new_id}/content",
        headers={
            **headers,
            "Content-Type": image.headers.get("Content-Type", "image/png"),
        },
        data=image.content,
        timeout=60,
    )
    upload.raise_for_status()
    return new_id


def _repair_active_menus() -> int:
    token = (os.getenv("LINE_CHANNEL_ACCESS_TOKEN") or "").strip()
    if not token:
        logging.info("[rich-menu] token missing; skip help-action repair")
        return 0

    headers = {"Authorization": f"Bearer {token}"}
    menus = _json_request("GET", "/richmenu/list", headers).get("richmenus", [])
    active_ids, aliases, default_id = _active_menu_ids(headers, menus)
    repaired_count = 0

    for menu in menus:
        old_id = menu.get("richMenuId")
        if not old_id or old_id not in active_ids:
            continue
        repaired, changed = _replace_help_actions(menu)
        if not changed:
            continue

        new_id = _clone_repaired_menu(token, menu, repaired)

        for alias in aliases:
            if alias.get("richMenuId") != old_id or not alias.get("richMenuAliasId"):
                continue
            _json_request(
                "POST",
                f"/richmenu/alias/{alias['richMenuAliasId']}",
                {**headers, "Content-Type": "application/json"},
                json={"richMenuId": new_id},
            )

        if default_id == old_id:
            _json_request("POST", f"/user/all/richmenu/{new_id}", headers)

        repaired_count += 1
        logging.info(
            "[rich-menu] repaired active help action: old=%s new=%s",
            old_id,
            new_id,
        )

    return repaired_count


def repair_rich_menu_help_actions_once() -> None:
    if os.getenv("AUTO_REPAIR_RICH_MENU_HELP", "1").strip().lower() not in {"1", "true", "yes", "on"}:
        return

    conn = None
    cur = None
    try:
        with _LOCAL_LOCK:
            if POSTGRES_ENABLED:
                conn = _pg_connect()
                cur = conn.cursor()
                cur.execute("SELECT pg_advisory_lock(%s)", (_LOCK_ID,))

            count = _repair_active_menus()
            logging.info("[rich-menu] help-action repair complete; menus_changed=%s", count)
    except Exception as exc:
        logging.warning("[rich-menu] help-action repair failed: %s", exc, exc_info=True)
    finally:
        if cur is not None:
            try:
                cur.execute("SELECT pg_advisory_unlock(%s)", (_LOCK_ID,))
            except Exception:
                pass
            try:
                cur.close()
            except Exception:
                pass
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass


def start_rich_menu_help_repair() -> None:
    threading.Thread(
        target=repair_rich_menu_help_actions_once,
        name="rich-menu-help-repair",
        daemon=True,
    ).start()
