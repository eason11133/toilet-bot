import requests
import time
from PIL import Image
import os

# ======== 你要填的部分 ==========
channel_access_token = 'A3wh6NHTa+AG/CsTcqLZiRxRJ0ftzyU2vUACWB201yInAgpIA0HzezG9N6xX9tJC+dBFN/O1319yU/y5xSWBSmS7FtPIB2J8ECo3IZWYedKQWFYO9ad2FSeHKKgws09Qn0JLFr5tjuMJ4/vcKe3PmAdB04t89/1O/w1cDnyilFU='
image_path = r"C:\Users\eason\Downloads\rich_menu_test.png"
# =================================

headers = {
    'Authorization': f'Bearer {channel_access_token}',
}

def check_image(image_path):
    if not os.path.exists(image_path):
        print("❌ 圖片檔案不存在:", image_path)
        return False
    img = Image.open(image_path)
    size = img.size
    file_size_kb = os.path.getsize(image_path) / 1024
    print(f"圖片尺寸: {size}, 檔案大小: {file_size_kb:.2f} KB")
    if size != (2500, 843):
        print("❌ 圖片尺寸不符合 2500x843 請調整圖片尺寸")
        return False
    if file_size_kb > 1024:
        print("❌ 檔案大小超過 1MB，請壓縮圖片")
        return False
    return True

def list_rich_menus():
    res = requests.get('https://api.line.me/v2/bot/richmenu/list', headers=headers)
    if res.status_code == 200:
        return res.json().get('richmenus', [])
    else:
        print(f"查詢失敗，狀態碼: {res.status_code}, 內容: {res.text}")
        return []

def delete_rich_menu(rich_menu_id):
    res = requests.delete(f'https://api.line.me/v2/bot/richmenu/{rich_menu_id}', headers=headers)
    if res.status_code == 200:
        print(f"✅ 成功刪除 Rich Menu: {rich_menu_id}")
    else:
        print(f"❌ 刪除 Rich Menu 失敗: {rich_menu_id}, 狀態碼：{res.status_code}")

def create_rich_menu():
    rich_menu_data = {
        "size": {"width": 2500, "height": 843},
        "selected": True,
        "name": "Toilet Menu",
        "chatBarText": "打開選單",
        "areas": [
            {
                "bounds": {"x": 0, "y": 0, "width": 1250, "height": 843},
                "action": {"type": "location", "label": "傳送位置"}
            },
            {
                "bounds": {"x": 1250, "y": 0, "width": 1250, "height": 843},
                "action": {"type": "message", "label": "找廁所", "text": "找最近廁所"}
            }
        ]
    }
    res = requests.post('https://api.line.me/v2/bot/richmenu', headers={**headers, 'Content-Type': 'application/json'}, json=rich_menu_data)
    if res.status_code == 200:
        rich_menu_id = res.json()['richMenuId']
        print(f"✅ 建立 Rich Menu 成功，ID: {rich_menu_id}")
        return rich_menu_id
    else:
        print(f"❌ 建立 Rich Menu 失敗，狀態碼: {res.status_code}, 內容: {res.text}")
        return None

def is_rich_menu_exist(rich_menu_id):
    richmenus = list_rich_menus()
    for rm in richmenus:
        if rm['richMenuId'] == rich_menu_id:
            return True
    return False

def wait_rich_menu_active(rich_menu_id, timeout=180, interval=20):
    elapsed = 0
    while elapsed < timeout:
        if is_rich_menu_exist(rich_menu_id):
            print(f"✅ Rich Menu {rich_menu_id} 已生效")
            return True
        print(f"等待中...已等待 {elapsed} 秒，尚未生效")
        time.sleep(interval)
        elapsed += interval
    print(f"❌ 超過 {timeout} 秒，Rich Menu {rich_menu_id} 尚未生效")
    return False

def upload_image(rich_menu_id):
    headers_image = {
        'Authorization': f'Bearer {channel_access_token}',
        'Content-Type': 'image/png'
    }
    with open(image_path, 'rb') as f:
        res = requests.post(f'https://api.line.me/v2/bot/richmenu/{rich_menu_id}/content', headers=headers_image, data=f)
    if res.status_code == 200:
        print("✅ 圖片上傳成功")
        return True
    else:
        print(f"❌ 圖片上傳失敗，狀態碼: {res.status_code}, 內容: {res.text}")
        return False

def set_rich_menu_all_user(rich_menu_id):
    res = requests.post(f'https://api.line.me/v2/bot/user/all/richmenu/{rich_menu_id}', headers=headers)
    if res.status_code == 200:
        print("✅ 已設定 Rich Menu 給所有使用者")
    else:
        print(f"❌ 設定 Rich Menu 給所有使用者失敗，狀態碼: {res.status_code}, 內容: {res.text}")

def main():
    if not check_image(image_path):
        print("結束程序，圖片格式或大小不符合要求。")
        return

    richmenus = list_rich_menus()
    print("目前 Rich Menu:")
    for rm in richmenus:
        print(f" - {rm['richMenuId']}")
    print("開始刪除所有 Rich Menu...")
    for rm in richmenus:
        delete_rich_menu(rm['richMenuId'])

    rich_menu_id = create_rich_menu()
    if not rich_menu_id:
        print("結束程序，建立 Rich Menu 失敗。")
        return

    print("⏳ 等待 Rich Menu 生效中...")
    if not wait_rich_menu_active(rich_menu_id):
        print("結束程序，Rich Menu 尚未生效，無法上傳圖片。")
        return

    if not upload_image(rich_menu_id):
        print("結束程序，圖片上傳失敗。")
        return

    set_rich_menu_all_user(rich_menu_id)

if __name__ == "__main__":
    main()
