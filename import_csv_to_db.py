import pandas as pd
import sqlite3

# 指定 CSV 路徑
csv_path = r"C:\Users\eason\AppData\Local\Temp\b0bcea19-e09b-4120-855b-6219ffffcc28_FAC_P_07_Resource.zip.c28\全國公廁建檔資料.csv"

# 嘗試用不同編碼讀取
try:
    df = pd.read_csv(csv_path, encoding='utf-8')
except UnicodeDecodeError:
    print("⚠️ utf-8 解碼失敗，改用 cp950 嘗試...")
    df = pd.read_csv(csv_path, encoding='cp950')

# 只保留需要的欄位
df = df[['name', 'address', 'longitude', 'latitude']]

# 連線到 SQLite（如果沒有這個檔案就會自動建立）
conn = sqlite3.connect("toilets.db")
cursor = conn.cursor()

# 建立資料表（如果尚未存在）
cursor.execute('''
    CREATE TABLE IF NOT EXISTS toilets (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT,
        address TEXT,
        longitude REAL,
        latitude REAL
    )
''')

# 清空舊資料（如果你不希望重複匯入）
cursor.execute('DELETE FROM toilets')

# 將資料匯入
df.to_sql('toilets', conn, if_exists='append', index=False)

# 儲存變更並關閉
conn.commit()
conn.close()

print("✅ 資料成功匯入 toilets.db")
