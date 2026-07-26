import numpy as np
from z3 import *
import random

# ==========================================
# 1. 核心映射與特徵向量 F(x) 提取 (對齊 Lean 4 occ2 定義)
# ==========================================
def todd_map(x):
    """計算單步 Todd 映射 (3x+1) 並消除所有尾零"""
    nx = 3 * x + 1
    while nx % 2 == 0:
        nx //= 2
    return nx

def get_F(x):
    """
    計算字串 x 的 18 維特徵向量 F(x)。
    對應 Lean 4 中的 occ2 (1, Phase.K, 0) (extIn x)
    """
    # extIn x: LSB-first 二進位，加上兩個哨兵零 [0, 0]
    bits = [int(b) for b in bin(x)[2:]][::-1] + [0, 0]
    c, P, d_prev = 1, 'K', 0
    
    counts = {
        'K': {(cv, 0, bv): 0 for cv in (0,1,2) for bv in (0,1)},
        'S': {(cv, dpv, bv): 0 for cv in (0,1,2) for dpv in (0,1) for bv in (0,1)}
    }
    
    for b in bits:
        counts[P][(c, d_prev, b)] += 1
        d = (3 * b + c) % 2
        c_next = (3 * b + c) // 2
        
        if P == 'K':
            P_next, dp_next = ('K', 0) if d == 0 else ('S', 1)
        else:
            P_next, dp_next = ('S', d)
            
        c, P, d_prev = c_next, P_next, dp_next
        
    # 嚴格對齊 KEYS 索引順序
    keys_K = [(cv, 0, bv) for cv in (0,1,2) for bv in (0,1)]
    keys_S = [(cv, dpv, bv) for cv in (0,1,2) for dpv in (0,1) for bv in (0,1)]
    return np.array([counts['K'][k] for k in keys_K] + [counts['S'][k] for k in keys_S])

# ==========================================
# 2. Z3 多片勢能求解器 (State-Conditioned Potential)
# ==========================================
def solve_multiphase_potential(samples):
    print(f"=== 啟動 Z3 狀態條件勢能診斷 (樣本數={len(samples)}) ===")
    
    solver = Solver()
    
    # 宣告兩組 18 維變數
    # theta_0: 碎裂態 (m=0, 走低能出口)
    # theta_1: 凝聚態 (m=1, 走高能出口)
    theta_0 = [Real(f'theta_0_{i}') for i in range(18)]
    theta_1 = [Real(f'theta_1_{i}') for i in range(18)]
    
    # 基礎約束：權重非負，死狀態 (0, 1) 恆為 0
    for i in range(18):
        solver.add(theta_0[i] >= 0)
        solver.add(theta_1[i] >= 0)
    solver.add(theta_0[0] == 0); solver.add(theta_0[1] == 0)
    solver.add(theta_1[0] == 0); solver.add(theta_1[1] == 0)

    # 建構跨模式約束
    for x in samples:
        F_x = get_F(x)
        x_next = todd_map(x)
        F_next = get_F(x_next)
        
        # 模式分類：直接讀取索引 5 (Phase K 走 b=1 且 c=2 的出口特徵)
        m_x = int(F_x[5])
        m_next = int(F_next[5])
        
        # 選擇對應的尺
        weight_start = theta_1 if m_x == 1 else theta_0
        weight_end = theta_1 if m_next == 1 else theta_0
        
        # 勢能計算 V_m(x) = \theta_m \cdot F(x)
        V_start = sum(weight_start[i] * int(F_x[i]) for i in range(18))
        V_end = sum(weight_end[i] * int(F_next[i]) for i in range(18))
        
        # 負漂移條件
        solver.add(V_end - V_start <= -1)

    print("跨模式(Cross-Mode)約束建構完成，Z3 求解中...")
    result = solver.check()
    
    if result == sat:
        print("\n[SATISFIABLE] 突破幾何死結！成功解出 2-Mode 狀態條件勢能。")
        model = solver.model()
        
        def print_weights(theta_vars, mode_name):
            print(f"\n--- {mode_name} ---")
            for i in range(18):
                val = model[theta_vars[i]]
                if val is not None:
                    num = val.numerator_as_long()
                    den = val.denominator_as_long()
                    if num > 0:
                        print(f"  θ_{i:02d}: {num}/{den} (≈ {float(num)/float(den):.4f})")
                        
        print_weights(theta_0, "θ_0 (碎裂態權重, m=0)")
        print_weights(theta_1, "θ_1 (凝聚態權重, m=1)")
    else:
        print("\n[UNSATISFIABLE] 即使切分 2-Mode，矛盾依舊存在。")
        print("表示凝聚或碎裂的路徑中，仍隱藏著需要更高維度記憶(如 Level 3)才能解開的拓撲糾纏。")

if __name__ == "__main__":
    # 混合隨機樣本與已知的惡意極端態
    test_samples = [random.randrange(3, 10**5, 2) for _ in range(500)]
    test_samples.extend([7, 27, 41, 167, 341, 1365, 5461])
    test_samples.extend([231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511])
    
    solve_multiphase_potential(test_samples)