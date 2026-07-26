def verify_exact_farkas_certificate():
    print("=== 精確整數 Farkas 矛盾證書驗證 ===")
    
    # 來自 Codex 的 4 條核心軌跡的 Delta F (已確認前兩個維度 K_00, K_01 為 0)
    # 軌跡 1: 7 -> 11
    df_1 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1]
    # 軌跡 2: 27 -> 41
    df_2 = [0, 0, 1, 0, 1, -1, 0, 0, 1, 2, -1, -1, 2, 0, 0, -1, -2, 0]
    # 軌跡 3: 41 -> 167
    df_3 = [0, 0, -1, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1]
    # 軌跡 4: 5709867599 -> 7226551181
    df_4 = [0, 0, 0, 1, 1, 0, 0, 0, -1, -7, 1, 3, -8, 1, -1, 5, 5, 0]
    
    # 提取的對偶變數 (乘上 16 轉為純整數權重)
    lambda_weights = [5, 5, 5, 1]
    
    print(f"整數對偶權重 (λ): {lambda_weights}")
    print(f"權重總和 (Σλ) = {sum(lambda_weights)}\n")
    
    # 計算線性組合 Σ (λ_i * ΔF_i)
    combined_df = [0] * 18
    for i, df in enumerate([df_1, df_2, df_3, df_4]):
        for j in range(18):
            combined_df[j] += lambda_weights[i] * df[j]
            
    print("=== 矛盾組合向量 Σ (λ_i * ΔF_i) ===")
    print(combined_df)
    
    # 驗證代數矛盾
    is_non_negative = all(val >= 0 for val in combined_df)
    
    print("\n=== 數學矛盾宣判 ===")
    if is_non_negative:
        print("[證明成立] 組合向量的所有分量皆 >= 0。")
        print("若要求勢能權重 θ >= 0，則其內積 θ^T * Σ(λ_i * ΔF_i) 必定 >= 0。")
        print("但依照負漂移約束條件，該內積必須 <= -Σλ_i = -16。")
        print("得出 0 <= -16 的絕對矛盾！(No-Go Theorem Established)")
    else:
        print("[驗證失敗] 組合向量存在負值分量。")

if __name__ == "__main__":
    verify_exact_farkas_certificate()