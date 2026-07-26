import numpy as np
from z3 import *
import random

def todd_map(x):
    """計算單步 Todd 映射 (3x+1) 並消除所有尾零"""
    nx = 3 * x + 1
    while nx % 2 == 0:
        nx //= 2
    return nx

def get_F3(x):
    """提取 Level 3 (記憶 2 步歷史) 的 48 維特徵向量"""
    bits = [int(b) for b in bin(x)[2:]][::-1] + [0, 0]
    c, P, H = 1, 'K', (0, 0)
    
    keys = [(cv, Pv, h1, h2, bv) 
            for cv in (0, 1, 2) 
            for Pv in ('K', 'S') 
            for h1 in (0, 1) 
            for h2 in (0, 1) 
            for bv in (0, 1)]
    
    counts = {k: 0 for k in keys}
    
    for b in bits:
        counts[(c, P, H[0], H[1], b)] += 1
        d = (3 * b + c) % 2
        c_next = (3 * b + c) // 2
        
        P_next = 'K' if (P == 'K' and d == 0) else 'S'
        H_next = (H[1], d)
        
        c, P, H = c_next, P_next, H_next
        
    return np.array([counts[k] for k in keys])

def run_z3_test(samples, stage_name):
    print(f"\n=== 執行 {stage_name} (樣本數: {len(samples)}) ===")
    solver = Solver()
    theta = [Real(f'theta_{i}') for i in range(48)]
    
    # 基本約束：權重非負
    for i in range(48):
        solver.add(theta[i] >= 0)

    # 建構單一勢能的負漂移約束
    for x in samples:
        F_x = get_F3(x)
        F_next = get_F3(todd_map(x))
        
        V_start = sum(theta[i] * int(F_x[i]) for i in range(48))
        V_end = sum(theta[i] * int(F_next[i]) for i in range(48))
        
        solver.add(V_end - V_start <= -1)

    print("Z3 求解中...")
    result = solver.check()
    
    if result == sat:
        print("[SATISFIABLE] 測試通過！Level 3 成功容納了這些軌跡的動態。")
    else:
        print("[UNSATISFIABLE] 矛盾發生！")
        print("Level 3 雖然解開了舊的死結，但又在更長期的宏觀行為中形成了新的拓撲超循環。")

if __name__ == "__main__":
    # 階段 1：已確認線性獨立的 12 條核心軌跡
    W12_samples = [25, 161, 353, 391, 471, 481, 583, 663, 681, 683, 711, 779]
    run_z3_test(W12_samples, "階段 1: W12 矛盾核心測試")
    
    # 階段 2：全域壓力測試 (W12 + 固定極端態 + 500 隨機大數)
    broad_samples = W12_samples.copy()
    broad_samples.extend([7, 27, 41, 167, 341, 1365, 5461])
    # 固定 seed 確保可重現性
    random.seed(42)
    broad_samples.extend([random.randrange(3, 10**5, 2) for _ in range(500)])
    
    run_z3_test(broad_samples, "階段 2: 隨機大數全域壓力測試")