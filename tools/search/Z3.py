import numpy as np
from z3 import *
import random

# ==========================================
# 1. 核心映射與 18 維特徵提取 (對齊 Level 2 規格)
# ==========================================
def todd_map(x):
    """計算單步 Todd 映射: (3x+1) 消除所有尾零"""
    nx = 3 * x + 1
    while nx % 2 == 0:
        nx //= 2
    return nx

def extract_level2_features(x):
    """18 維特徵提取 (包含死狀態，維持完整 18 維以對齊 θ)"""
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
            if d == 0:
                P_next, dp_next = 'K', 0
            else:
                P_next, dp_next = 'S', 1
        else:
            P_next, dp_next = 'S', d
            
        c, P, d_prev = c_next, P_next, dp_next
        
    keys_K = [(cv, 0, bv) for cv in (0,1,2) for bv in (0,1)]
    keys_S = [(cv, dpv, bv) for cv in (0,1,2) for dpv in (0,1) for bv in (0,1)]
    return np.array([counts['K'][k] for k in keys_K] + [counts['S'][k] for k in keys_S])

# ==========================================
# 2. Z3 SMT 前瞻窗口求解器 (K=3)
# ==========================================
def solve_bounded_lookahead(samples, K=3):
    print(f"=== 啟動 Z3 Bounded-Lookahead 診斷 (K={K}, 樣本數={len(samples)}) ===")
    
    # 建立 Z3 求解器
    solver = Solver()
    
    # 宣告 18 維勢能權重變數 (實數)
    theta = [Real(f'theta_{i}') for i in range(18)]
    
    # 基本約束：所有權重非負
    for i in range(18):
        solver.add(theta[i] >= 0)
        
    # 加入已知無效的死狀態約束 (特徵 0 與 1 恆為零，強制權重為 0 可加速求解)
    solver.add(theta[0] == 0)
    solver.add(theta[1] == 0)

    # 建立所有樣本的前瞻軌跡約束
    for x in samples:
        f_start = extract_level2_features(x)
        
        delta_Fs = []
        curr_x = x
        for step in range(1, K + 1):
            curr_x = todd_map(curr_x)
            f_end = extract_level2_features(curr_x)
            delta_Fs.append(f_end - f_start)
            
        # 建構 Z3 的內積表示式
        dot_products = []
        for dF in delta_Fs:
            dot_expr = sum(theta[i] * int(dF[i]) for i in range(18))
            dot_products.append(dot_expr)
            
        # 析取約束 (OR): 至少有一步的勢能差 <= -1
        # 例如 K=3: Or(ΔV1 <= -1, ΔV2 <= -1, ΔV3 <= -1)
        solver.add(Or([dot <= -1 for dot in dot_products]))

    print("約束建構完成，Z3 求解中 (這可能需要幾十秒)...")
    result = solver.check()
    
    if result == sat:
        print("\n[SATISFIABLE] 找到前瞻勢能！呼吸效應已被 K 步窗口成功吸收。")
        model = solver.model()
        print("--- 非零權重 θ ---")
        for i in range(18):
            val = model[theta[i]]
            # 將 Z3 分數轉為浮點數方便閱讀
            if val is not None:
                float_val = float(val.numerator_as_long()) / float(val.denominator_as_long())
                if float_val > 1e-5:
                    print(f"θ_{i:02d}: {float_val:.4f}")
    elif result == unsat:
        print("\n[UNSATISFIABLE] 矛盾依然存在！")
        print("即使給予 K 步的前瞻窗口，18 維狀態機仍無法消化某些軌跡的長期凝聚現象。")
        print("這代表 Level 2 特徵的『記憶表達能力』面臨硬性天花板。")
    else:
        print("\n[UNKNOWN] Z3 求解超時或遇到未知狀態。")

if __name__ == "__main__":
    # 混合隨機樣本與已知的惡意極端態
    test_samples = [random.randrange(3, 10**5, 2) for _ in range(500)]
    test_samples.extend([7, 27, 41, 167, 341, 1365, 5461])
    # 形式化團隊找出的 W10 單步憑證死穴
    test_samples.extend([231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511])
    
    # 測試 K=2 與 K=3
    solve_bounded_lookahead(test_samples, K=3)