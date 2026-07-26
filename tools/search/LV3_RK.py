import numpy as np

# 形式化團隊驗證過的 12 條 Level 2 矛盾軌跡對 (起點, 終點)
W12_pairs = [
    (25, 19), (161, 121), (353, 265), (391, 587),
    (471, 707), (481, 361), (583, 875), (663, 995),
    (681, 511), (683, 1025), (711, 1067), (779, 1169)
]

def get_F3(x):
    """提取 Level 3 (記憶 2 步歷史) 的 48 維特徵向量"""
    bits = [int(b) for b in bin(x)[2:]][::-1] + [0, 0]
    # 初始狀態：進位 1, 相位 K, 歷史記憶 (d_{i-2}, d_{i-1}) = (0, 0)
    c, P, H = 1, 'K', (0, 0)
    
    # 建立 48 維特徵的鍵值與計數器
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
        
        # 相位更新邏輯
        if P == 'K':
            P_next = 'K' if d == 0 else 'S'
        else:
            P_next = 'S'
            
        # 歷史記憶滑動更新
        H_next = (H[1], d)
        
        c, P, H = c_next, P_next, H_next
        
    return np.array([counts[k] for k in keys])

def analyze_linear_independence():
    print("=== Level 3 差分特徵線性獨立性診斷 ===")
    
    delta_matrix = []
    for x, y in W12_pairs:
        dF = get_F3(y) - get_F3(x)
        delta_matrix.append(dF)
        
    # 轉換為 12 x 48 的矩陣
    delta_matrix = np.array(delta_matrix)
    
    # 計算矩陣的 Rank
    rank = np.linalg.matrix_rank(delta_matrix)
    
    print(f"矩陣形狀: {delta_matrix.shape} (12 條軌跡, 48 維特徵)")
    print(f"矩陣秩 (Rank): {rank}")
    
    if rank == len(W12_pairs):
        print("\n[結果] 完美線性獨立！")
        print("這 12 條軌跡在 Level 3 空間中不再形成封閉的拓撲死結。Level 3 具備解開此矛盾的表達潛力。")
    else:
        print("\n[結果] 存在線性相依。")
        print(f"有 {len(W12_pairs) - rank} 個維度發生了退化。我們需要檢查這個退化是否會再次引發 Farkas 矛盾。")

if __name__ == "__main__":
    analyze_linear_independence()