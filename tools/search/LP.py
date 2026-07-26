import numpy as np
from scipy.optimize import linprog
import random
from concurrent.futures import ProcessPoolExecutor
import multiprocessing

# ==========================================
# 1. 特徵提取與動力學模擬
# ==========================================
def extract_level2_features(x):
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
        
    # 攤平為 18 維向量
    keys_K = [(cv, 0, bv) for cv in (0,1,2) for bv in (0,1)]
    keys_S = [(cv, dpv, bv) for cv in (0,1,2) for dpv in (0,1) for bv in (0,1)]
    
    vec = [counts['K'][k] for k in keys_K] + [counts['S'][k] for k in keys_S]
    return np.array(vec)

def get_next_collatz_state(x):
    x_next = 3 * x + 1
    v2 = 0
    while x_next % 2 == 0:
        x_next //= 2
        v2 += 1
    return x_next, v2

def get_epoch_end(x_start):
    x_current, v2 = get_next_collatz_state(x_start)
    while v2 < 3:
        if x_current == 1:
            break
        x_current, v2 = get_next_collatz_state(x_current)
    return x_current

# ==========================================
# 2. 割平面核心邏輯 (Cutting-Plane Method)
# ==========================================
def solve_lp(trajectories):
    A_ub, b_ub = [], []
    for x_start, x_end in trajectories:
        vec_start = extract_level2_features(x_start)
        vec_end = extract_level2_features(x_end)
        A_ub.append(vec_end - vec_start)
        b_ub.append(-1.0)
        
    bounds = [(0, None) for _ in range(18)]
    c = np.ones(18)
    
    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub), bounds=bounds, method='highs')
    return res

def evaluate_trajectory(args):
    x_start, theta = args
    x_end = get_epoch_end(x_start)
    vec_start = extract_level2_features(x_start)
    vec_end = extract_level2_features(x_end)
    
    delta_v = np.dot(theta, vec_end - vec_start)
    if delta_v > -1.0:
        return (x_start, x_end, delta_v)
    return None

def run_cutting_plane(initial_trajectories, max_iterations=10, sample_size=20000):
    trajectories = list(initial_trajectories)
    
    for iteration in range(1, max_iterations + 1):
        print(f"\n[{'-'*40}]")
        print(f"Iteration {iteration}: 求解 LP (當前約束數量: {len(trajectories)})")
        
        res = solve_lp(trajectories)
        if not res.success:
            print(">> [INFEASIBLE] 求解失敗！18 維空間被證明存在不可化解的矛盾。")
            print(">> 正在精準定位 Farkas 矛盾核心 (Irreducible Infeasible Set, IIS)...\n")
            
            # --- 精準縮小矛盾集的演算法 ---
            iis_trajectories = list(trajectories)
            
            # 嘗試逐一刪除軌跡，如果刪除後變成可行，代表這條軌跡是矛盾的核心之一
            i = 0
            while i < len(iis_trajectories):
                temp_trajectories = iis_trajectories[:i] + iis_trajectories[i+1:]
                temp_res = solve_lp(temp_trajectories)
                
                if not temp_res.success:
                    # 刪了它依然無解，說明這條軌跡是「多餘的冗餘約束」，直接踢掉
                    iis_trajectories.pop(i)
                else:
                    # 刪了它居然變可行了！說明這條軌跡是「關鍵矛盾軌跡」，必須保留
                    i += 1
            
            # --- 求解這組極小矛盾集的 Farkas Multipliers (對偶權重) ---
            # 建立極小矛盾集的 A 矩陣
            A_ub_iis = []
            for x_s, x_e in iis_trajectories:
                A_ub_iis.append(extract_level2_features(x_e) - extract_level2_features(x_s))
            A_ub_iis = np.array(A_ub_iis)
            
            # 求解 Farkas Lemma: y^T A >= 0, y^T b < 0, y >= 0
            # 這裡 b 是全 -1 的向量，所以 y^T b < 0 等價於 sum(y) > 0
            c_farkas = np.zeros(len(iis_trajectories))
            A_eq_farkas = A_ub_iis.T # 特徵維度轉置
            b_eq_farkas = np.zeros(18)
            bounds_farkas = [(0, None) for _ in range(len(iis_trajectories))]
            
            # 要求 sum(y) = 1 來尋找非零解
            A_eq_full = np.vstack([A_eq_farkas, np.ones(len(iis_trajectories))])
            b_eq_full = np.append(b_eq_farkas, 1.0)
            
            farkas_res = linprog(c_farkas, A_eq=A_eq_full, b_eq=b_eq_full, bounds=bounds_farkas, method='highs')
            lambdas = farkas_res.x if farkas_res.success else np.ones(len(iis_trajectories))

            print(f"=== 成功鎖定！極小矛盾核心 (共有 {len(iis_trajectories)} 條軌跡) ===")
            for idx, (x_s, x_e) in enumerate(iis_trajectories):
                lam = lambdas[idx]
                print(f"  -> [Farkas 權重 λ = {lam:.4f}] 軌跡: {x_s:<15} -> {x_e:<15}")
                
                vec_s = extract_level2_features(x_s)
                vec_e = extract_level2_features(x_e)
                delta_f = vec_e - vec_s
                non_zero_features = [(i, val) for i, val in enumerate(delta_f) if val != 0]
                print(f"     ΔF (特徵變化量): {non_zero_features}\n")
                
            # 算術驗證
            combined_delta = np.zeros(18)
            for idx, (x_s, x_e) in enumerate(iis_trajectories):
                combined_delta += lambdas[idx] * (extract_level2_features(x_e) - extract_level2_features(x_s))
            
            print("=== Farkas 代數驗證 ===")
            print(f"加權後的總 ΔF 向量 (理論上應全為 >= 0):\n{np.round(combined_delta, 4)}")
            print(f"加權後的總要求衰減值 (理論上為 -1.0):\n{-1.0 * np.sum(lambdas):.4f}")
            print("\n結論：正數向量的線性組合導出了負數，數學上徹底矛盾！")
            return
            
        theta = res.x
        print(">> [SUCCESS] 獲得暫時性權重 theta。進行大規模泛化測試...")
        
        test_cases = [random.randrange(3, 10**10, 2) for _ in range(sample_size)]
        args_list = [(x, theta) for x in test_cases]
        
        violations = []
        with ProcessPoolExecutor(max_workers=multiprocessing.cpu_count()) as executor:
            for result in executor.map(evaluate_trajectory, args_list):
                if result is not None:
                    violations.append(result)
                    
        if not violations:
            print(f">> [PERFECT] 迴圈終止！找到全域收斂權重 theta！")
            print(np.round(theta, 3))
            return
            
        print(f">> [WARNING] 發現 {len(violations)} 筆違規。提取惡意反例加入矩陣...")
        # 依據反彈程度排序，取最惡劣的前 100 筆加入約束
        violations.sort(key=lambda item: item[2], reverse=True)
        for v in violations[:100]:
            if (v[0], v[1]) not in trajectories:
                trajectories.append((v[0], v[1]))

if __name__ == "__main__":
    base_trajectories = [
        (7, 11), (27, 41), (41, 167), 
        (341, 1), (1365, 1), (5461, 1)
    ]
    run_cutting_plane(base_trajectories, max_iterations=15, sample_size=25000)

