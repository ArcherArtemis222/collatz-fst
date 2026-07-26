import numpy as np
from scipy.linalg import null_space
import sympy

def get_next_state(c, P, d_prev, b):
    d = (3 * b + c) % 2
    c_next = (3 * b + c) // 2
    
    if P == 'K':
        if d == 0:
            return (c_next, 'K', 0)
        else:
            return (c_next, 'S', 1)
    else:
        return (c_next, 'S', d)

def analyze_incidence_matrix():
    # 1. 定義 8 個可達狀態 (排除 c=0, P=K 的死狀態)
    states = [
        (1, 'K', 0), (2, 'K', 0),
        (0, 'S', 0), (0, 'S', 1),
        (1, 'S', 0), (1, 'S', 1),
        (2, 'S', 0), (2, 'S', 1)
    ]
    state_to_idx = {s: i for i, s in enumerate(states)}
    
    # 2. 窮舉 16 條轉移邊
    edges = []
    for s in states:
        for b in (0, 1):
            s_next = get_next_state(s[0], s[1], s[2], b)
            edges.append({'src': s, 'dst': s_next, 'b': b})
            
    # 3. 建構關聯矩陣 B (大小: 8 states x 16 edges)
    B = np.zeros((len(states), len(edges)), dtype=int)
    
    for e_idx, edge in enumerate(edges):
        src_idx = state_to_idx[edge['src']]
        dst_idx = state_to_idx[edge['dst']]
        
        # 流量流出 src 為 -1，流入 dst 為 +1
        # 若自環 (src == dst)，則為 0 (不改變該節點流量)
        if src_idx != dst_idx:
            B[src_idx, e_idx] = -1
            B[dst_idx, e_idx] += 1
            
    print(f"=== 關聯矩陣 B 結構分析 ===")
    print(f"狀態數 |V| = {len(states)}")
    print(f"轉移邊 |E| = {len(edges)}")
    print(f"矩陣 B 的形狀: {B.shape}")
    
    # 4. 計算矩陣的秩 (Rank) 與零空間 (Null Space)
    rank_B = np.linalg.matrix_rank(B)
    nullity = len(edges) - rank_B
    
    print(f"\n矩陣 Rank(B) = {rank_B}")
    print(f"循環空間維度 (Nullity / 自由度) = 16 - {rank_B} = {nullity}")
    
    # 5. 提取有理數循環基底 (Rational Cycle Basis)
    # 使用 sympy 獲得精確的有理數基底，避免浮點數誤差
    B_sym = sympy.Matrix(B)
    null_basis = B_sym.nullspace()
    
    print(f"\n=== 獨立循環基底 (Cycle Basis) ===")
    for i, basis_vec in enumerate(null_basis):
        # 將基底轉為平攤的 list 方便閱讀
        vec_list = [int(val) for val in basis_vec]
        print(f"基底向量 C_{i+1}: {vec_list}")

if __name__ == "__main__":
    analyze_incidence_matrix()