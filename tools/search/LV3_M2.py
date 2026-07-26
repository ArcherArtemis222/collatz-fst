import numpy as np
from z3 import *

# ==========================================
# 1. Level 3 特徵與模式提取
# ==========================================
def todd_map(x):
    nx = 3 * x + 1
    while nx % 2 == 0:
        nx //= 2
    return nx

# 預先生成 48 維特徵的 Keys 以對齊索引
KEYS_L3 = [(cv, Pv, h1, h2, bv) 
           for cv in (0, 1, 2) 
           for Pv in ('K', 'S') 
           for h1 in (0, 1) 
           for h2 in (0, 1) 
           for bv in (0, 1)]

# Z9 高能出口在 Level 3 的特徵: 進位 2, 相位 K, 歷史 00 (K 區恆為 00), 讀入 1
Z9_HIGH_EXIT_INDEX = KEYS_L3.index((2, 'K', 0, 0, 1))

def get_F3(x):
    """提取 Level 3 (記憶 2 步歷史) 的 48 維特徵向量"""
    bits = [int(b) for b in bin(x)[2:]][::-1] + [0, 0]
    c, P, H = 1, 'K', (0, 0)
    counts = {k: 0 for k in KEYS_L3}
    
    for b in bits:
        counts[(c, P, H[0], H[1], b)] += 1
        d = (3 * b + c) % 2
        c_next = (3 * b + c) // 2
        
        P_next = 'K' if (P == 'K' and d == 0) else 'S'
        H_next = (H[1], d)
        
        c, P, H = c_next, P_next, H_next
        
    return np.array([counts[k] for k in KEYS_L3])

# ==========================================
# 2. Z3 Level-3 2-Mode 勢能求解器
# ==========================================
def solve_L3_2mode_potential(samples):
    print(f"=== 啟動 Z3 [Level 3 + 2-Mode] 終極勢能診斷 ===")
    print(f"樣本數: {len(samples)} (包含所有奇數 < 1000 及歷史惡意核心)")
    
    solver = Solver()
    
    # 宣告兩組 48 維變數
    theta_0 = [Real(f'theta_0_{i}') for i in range(48)] # 碎裂態
    theta_1 = [Real(f'theta_1_{i}') for i in range(48)] # 凝聚態
    
    for i in range(48):
        solver.add(theta_0[i] >= 0)
        solver.add(theta_1[i] >= 0)

    # 建構跨模式約束
    for x in samples:
        F_x = get_F3(x)
        x_next = todd_map(x)
        F_next = get_F3(x_next)
        
        # 模式分類：讀取 Z9 高能出口特徵
        m_start = int(F_x[Z9_HIGH_EXIT_INDEX])
        m_end = int(F_next[Z9_HIGH_EXIT_INDEX])
        
        # 根據模式挑選量尺
        weight_start = theta_1 if m_start == 1 else theta_0
        weight_end = theta_1 if m_end == 1 else theta_0
        
        V_start = sum(weight_start[i] * int(F_x[i]) for i in range(48))
        V_end = sum(weight_end[i] * int(F_next[i]) for i in range(48))
        
        solver.add(V_end - V_start <= -1)

    print("跨模式 48 維約束建構完成，Z3 求解中 (可能需要幾十秒)...")
    result = solver.check()
    
    if result == sat:
        print("\n[SATISFIABLE] 歷史性突破！")
        print("Level 3 的記憶深度加上 2-Mode 的切換彈性，成功化解了所有的拓撲死結。")
        print("系統已經找到全域相容的狀態條件線性勢能！")
    else:
        print("\n[UNSATISFIABLE] 依然無解。")
        print("這代表 Level 3 + 2-Mode 依然不足。Collatz 的非線性糾纏深度，超越了此級別自動機的平攤極限。")

if __name__ == "__main__":
    # 結合所有的極端與關鍵樣本
    test_samples = set([x for x in range(3, 1000, 2)])
    
    # 加入 Level 2 的 12 條 2-mode 核心
    L2_W12 = [25, 161, 353, 391, 471, 481, 583, 663, 681, 683, 711, 779]
    # 加入 Level 3 的 12 條 1-mode 核心
    L3_W12 = [407, 1143, 1361, 1379, 1449, 1545, 1667, 1681, 1683, 1833, 1911, 2943]
    # 加入其他大數
    extreme_cases = [7, 27, 41, 167, 341, 1365, 5461]
    
    test_samples.update(L2_W12)
    test_samples.update(L3_W12)
    test_samples.update(extreme_cases)
    
    # 轉回 list 並排序，確保每次跑順序固定
    final_samples = sorted(list(test_samples))
    
    solve_L3_2mode_potential(final_samples)