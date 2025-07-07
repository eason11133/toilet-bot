# train_model.py

import joblib
from sklearn.linear_model import LinearRegression
import numpy as np
import os

# 模擬訓練資料
X = np.array([
    [5, 1, 1],
    [4, 1, 1],
    [3, 1, 0],
    [2, 0, 1],
    [0, 1, 0],
])
y = np.array([5, 4, 3, 2, 5])

# 訓練模型
model = LinearRegression()
model.fit(X, y)

# 儲存模型
model_path = os.path.join("models", "cleanliness_model.pkl")
os.makedirs(os.path.dirname(model_path), exist_ok=True)  # ✅ 建立 models/ 資料夾（若尚未存在）
joblib.dump(model, model_path)

print(f"✅ 模型已儲存至：{model_path}")
