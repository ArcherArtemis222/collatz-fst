/-
# 雙模式狀態條件勢能：規格驗證偵察（資訊齊全，待令開工）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_Level2.lean`。

## 驗證結論（本檔 #eval 全綠）

1. **12 對 Todd 全部吻合**（25→19、…、779→1169）。
2. **12 條模式轉移與表格逐條吻合**，且索引約定確認為 **0-based**：
   m(x) = F(x)[5]（0-based）＝ 1-based 特徵 #6 ＝ E^K_{(2,K,0),b=1}。
3. **m ∈ {0,1} 不是假設而是定理的投影**：所有 24 個端點滿足
   F[2] + F[5] = 1——這正是 `boundary_step_unique`（唯一邊界觸發步）
   在特徵層的形式：出口不是 (1,K,0)-b0（碎裂態，F[2]=1）
   就是 (2,K,0)-b1（凝聚態，F[5]=1），恰居其一。
   形式化時將附上此橋（24 端點 decide 版；一般版可由
   `boundary_step_unique` + 狀態空間有界性導出）。
4. **36 維 Farkas 組合精確吻合**：λ =
   (72, 936, 864, 1107, 1502, 900, 588, 326, 648, 162, 163, 558)，Σ = 7826；
   組合 S 之非零座標恰為 θ₀[11]=θ₀[15]=θ₀[16]=θ₀[17]=36、
   θ₁[7]=94、θ₁[8]=522、θ₁[9]=527、θ₁[12]=621，其餘 28 維全零，逐分量 ≥ 0。
5. 跨批一致性：每條軌跡 Δ(K 區塊和) = Δv₂（`sum_EK_components` 差分形式）。

## 定案之定理形式（開工即照此證）

```
theorem no_go_2mode_potential :
    ¬ ∃ (θ₀ θ₁ : Fin 18 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W12,
        (if (F (Todd x)).getD 5 0 = 1 then dot θ₁ (F (Todd x)) else dot θ₀ (F (Todd x)))
          - (if (F x).getD 5 0 = 1 then dot θ₁ (F x) else dot θ₀ (F x)) < 0
```

註：`(F x)[5]` 實作為全函數 `getD 5 0`；`if m = 1 … else θ₀` 分支語義下
即使 m 越界也落到 θ₀，但由第 3 點 m 恆為位元，語義封閉。

## 證明路線（與 W₁₀ 定理同構，純機械）

24 條 F 求值引理（decide，digits kernel 可展開）＋ 12 條 Todd 引理
（`padicValNat_two_pow_mul`；v₂ = 2,2,2,1,1,2,1,1,2,1,1,1）＋
模式化簡（if_pos/if_neg）＋ 36 變數的組合恆等式（`ring`）＋
八項非負與嚴格負和對撞。
-/
import Lean4RealConstruction.Core.Collatz_FST_Level2

namespace CollatzFST.TwoMode

open CollatzFST

def KEYS : List ((ℕ × Phase × ℕ) × ℕ) :=
  ([0,1,2].flatMap fun c => [0,1].map fun b => ((c, Phase.K, 0), b)) ++
  ([0,1,2].flatMap fun c => [0,1].flatMap fun p => [0,1].map fun b => ((c, Phase.S, p), b))
def F (x : ℕ) : List ℤ := KEYS.map (fun k => (occ2 (1, Phase.K, 0) (extIn x) k : ℤ))

def W12 : List ℕ := [25, 161, 353, 391, 471, 481, 583, 663, 681, 683, 711, 779]

/-- (起點, 終點, λ, m_start, m_end) -/
def cert : List (ℕ × ℕ × ℤ × ℤ × ℤ) :=
  [(25,19,72,0,1), (161,121,936,0,0), (353,265,864,0,0), (391,587,1107,1,1),
   (471,707,1502,1,1), (481,361,900,0,0), (583,875,588,1,1), (663,995,326,1,1),
   (681,511,648,0,1), (683,1025,162,1,0), (711,1067,163,1,1), (779,1169,558,1,0)]

/-! ## 驗證（全部應輸出 `true`） -/

section Verification

-- Todd 對
#eval cert.all fun t => Todd t.1 == t.2.1

-- 模式（0-based [5]）與表格吻合
#eval cert.all fun t =>
  (F t.1).getD 5 0 == t.2.2.2.1 && (F t.2.1).getD 5 0 == t.2.2.2.2

-- m ∈ {0,1} 且 F[2]+F[5] = 1（boundary_step_unique 的特徵層投影）
#eval (cert.flatMap fun t => [t.1, t.2.1]).all fun n =>
  ((F n).getD 5 0 == 0 || (F n).getD 5 0 == 1) &&
  (F n).getD 2 0 + (F n).getD 5 0 == 1

-- 36 維組合：非零座標恰為宣稱之八個，其餘全零、逐分量 ≥ 0
#eval
  let S := cert.foldl (fun acc t =>
    let (x, y, lam, ms, me) := t
    (List.range 36).map fun j =>
      acc.getD j 0
      + (if (j : ℤ) / 18 == me then lam * (F y).getD (j % 18) 0 else 0)
      - (if (j : ℤ) / 18 == ms then lam * (F x).getD (j % 18) 0 else 0))
    (List.replicate 36 (0 : ℤ))
  S == ((List.range 36).map fun j =>
    if j == 11 || j == 15 || j == 16 || j == 17 then (36 : ℤ)
    else if j == 18 + 7 then 94 else if j == 18 + 8 then 522
    else if j == 18 + 9 then 527 else if j == 18 + 12 then 621 else 0)

-- λ 總和
#eval cert.foldl (fun a t => a + t.2.2.1) 0 == (7826 : ℤ)

-- 跨批一致性：Δ(K 區塊和) = Δv₂
#eval cert.all fun t =>
  ((F t.2.1).take 6).foldl (· + ·) 0 - ((F t.1).take 6).foldl (· + ·) 0
    == (padicValNat 2 (3 * t.2.1 + 1) : ℤ) - (padicValNat 2 (3 * t.1 + 1) : ℤ)

end Verification

end CollatzFST.TwoMode
