from linebot.models import (
    TextSendMessage,
    QuickReply,
    QuickReplyButton,
    LocationAction,
    MessageAction,
    PostbackAction,
)

L = None

def configure_replies(l_func):
    global L
    L = l_func


def make_location_quick_reply(prompt_text, mode="normal", uid=None):
    """
    prompt_text: 主訊息文字（建議呼叫前就用 L(uid, zh, en) 產好）
    mode: "normal" or "ai"
    uid: LINE user id（用來判斷語言）
    """

    # 防呆：如果沒傳 uid，就用中文
    def _L(zh, en):
        return L(uid, zh, en) if uid else zh

    items = [
        QuickReplyButton(
            action=LocationAction(
                label=_L("傳送我的位置", "Share location")
            )
        )
    ]

    if mode == "normal":
        # 👉 切換到 AI 模式（走 postback，不再送文字）
        items.append(
            QuickReplyButton(
                action=PostbackAction(
                    label=_L("AI 推薦附近廁所", "AI nearby"),
                    data="ask_ai_location",
                    display_text=_L("切換成 AI 推薦模式", "Switch to AI mode")
                )
            )
        )
    else:  # mode == "ai"
        # 👉 切回一般模式
        items.append(
            QuickReplyButton(
                action=PostbackAction(
                    label=_L("切換回一般模式", "Normal mode"),
                    data="ask_location",
                    display_text=_L("切換回一般模式", "Switch to normal mode")
                )
            )
        )

    return TextSendMessage(
        text=prompt_text,
        quick_reply=QuickReply(items=items)
    )


def make_retry_location_text(uid=None):
    return TextSendMessage(
        text=L(uid,
               "現在查詢人數有點多，我排一下隊；你可再傳一次位置或稍候幾秒～",
               "Too many requests now. Please send your location again or try in a few seconds."),
        quick_reply=QuickReply(items=[
            QuickReplyButton(action=LocationAction(label=L(uid, "傳送我的位置", "Share location")))
        ])
    )


def make_no_toilet_quick_reply(uid, lat=None, lon=None):
    return TextSendMessage(
        text=L(uid, "附近沒有廁所 😥 要不要補上一間？",
                  "No toilets nearby 😥 Want to add one?"),
        quick_reply=QuickReply(items=[
            QuickReplyButton(action=LocationAction(label=L(uid, "傳送我的位置", "Share location"))),
            QuickReplyButton(action=MessageAction(label=L(uid, "新增廁所", "Add toilet"),
                                                  text=L(uid, "新增廁所", "Add toilet")))
        ])
    )

