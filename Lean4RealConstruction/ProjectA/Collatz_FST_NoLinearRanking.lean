/-
# 最終定理：Level 2 特徵類上不存在非負線性 additive ranking（**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_Level2.lean`。
依對方定案規格形式化：索引順序 = 逆向鎖定之 KEYS；Epoch = 單次 Todd 映射；
函數類 = θ ≥ 0；下降 = 嚴格 < 0；見證集 = W₁₀。

## 主定理

`no_nonneg_linear_ranking`：
  ¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧ ∀ x ∈ W₁₀, dot θ (ΔF x) < 0

`no_global_odd_ranking`（標題句）：對本 Level 2 automaton occupation feature class，
**不存在**對每個奇數 x 的單次加速迭代皆嚴格下降的非負線性勢能——
由 W₁₀ ⊆ 奇數 a fortiori 得出。

## 證明骨架（Farkas 憑證內嵌於證明）

十個見證的 ΔF 由**已證正確的機器計算**（`occ2` + `Todd`），非外掛數據：
* `Todd_x`（×10）：v₂ 由 `padicValNat_two_pow_mul` 落地（如 3·681+1 = 2²·511）。
* `ΔF_x`（×10）：`decide` 直接 kernel 求值——`Nat.digits` 於此版本
  標記 `@[semireducible]`，kernel 可展開其 well-founded 遞迴。
* 組合恆等式 `key`：Σ wᵢ·(θ·ΔFᵢ) = 31·θ₆，由 `ring` 於 ℚ 上收掉
  （λ = (100,64,119,51,56,183,164,18,191,78)/1024，Σw = 1024）。
* 矛盾：十項皆負 ⇒ 左邊 < 0；θ ≥ 0 ⇒ 31·θ₆ ≥ 0。

`dot` 為 18 分量的線性形式（顯式展開定義，對字面串列 rfl 級化簡）；
kernel 級的憑證算術獨立驗證見 §35。

## 語意鏈（為什麼這 18 個數字談的是 Collatz）

ΔF 的每個分量都經由本專案的定理鏈接地：`occ2` 的佔用計數 ↔ 微觀轉移
（`count2_pair` 邊界捕捉）、K 區計數 ↔ v₂（`sum_EK_components`）、
S 區計數 ↔ 區塊誕生/死亡（`birth_death_conservation`）、
`Todd` ↔ 尾零消去（`Todd_eq_dropWhile`、`digits_Todd_eq_drop`）。
-/
import Lean4RealConstruction.Core.Collatz_FST_Level2
import Mathlib.Algebra.Order.Field.Rat

namespace CollatzFST.LP

open CollatzFST

/-! ## §32 定義（照定案規格） -/

/-- 鎖定的特徵順序（同 LPRecon/CycleBasis）。 -/
def KEYS : List ((ℕ × Phase × ℕ) × ℕ) :=
  ([0,1,2].flatMap fun c => [0,1].map fun b => ((c, Phase.K, 0), b)) ++
  ([0,1,2].flatMap fun c => [0,1].flatMap fun p => [0,1].map fun b => ((c, Phase.S, p), b))

/-- 18 維佔用特徵（由已證機器 `occ2` 計算）。 -/
def F (x : ℕ) : List ℤ := KEYS.map (fun k => (occ2 (1, Phase.K, 0) (extIn x) k : ℤ))

/-- 單次加速迭代的特徵差分 ΔF(x) = F(Todd x) − F(x)。 -/
def ΔF (x : ℕ) : List ℤ := (F (Todd x)).zipWith (· - ·) (F x)

/-- 十個見證。 -/
def W₁₀ : List ℕ := [231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511]

/-- 線性形式 θ ⬝ v（18 分量顯式展開；非 18 長度時取 0）。 -/
def dot (θ : Fin 18 → ℚ) : List ℤ → ℚ
  | [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17] =>
      θ 0 * (a0 : ℚ) + θ 1 * (a1 : ℚ) + θ 2 * (a2 : ℚ) + θ 3 * (a3 : ℚ)
      + θ 4 * (a4 : ℚ) + θ 5 * (a5 : ℚ) + θ 6 * (a6 : ℚ) + θ 7 * (a7 : ℚ)
      + θ 8 * (a8 : ℚ) + θ 9 * (a9 : ℚ) + θ 10 * (a10 : ℚ) + θ 11 * (a11 : ℚ)
      + θ 12 * (a12 : ℚ) + θ 13 * (a13 : ℚ) + θ 14 * (a14 : ℚ) + θ 15 * (a15 : ℚ)
      + θ 16 * (a16 : ℚ) + θ 17 * (a17 : ℚ)
  | _ => 0

/-! ## §33 十個 Todd 值 -/

lemma Todd_231 : Todd 231 = 347 := by
  have hv : padicValNat 2 (3 * 231 + 1) = 1 := by
    rw [show (3 * 231 + 1 : ℕ) = 2 ^ 1 * 347 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_323 : Todd 323 = 485 := by
  have hv : padicValNat 2 (3 * 323 + 1) = 1 := by
    rw [show (3 * 323 + 1 : ℕ) = 2 ^ 1 * 485 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_403 : Todd 403 = 605 := by
  have hv : padicValNat 2 (3 * 403 + 1) = 1 := by
    rw [show (3 * 403 + 1 : ℕ) = 2 ^ 1 * 605 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_551 : Todd 551 = 827 := by
  have hv : padicValNat 2 (3 * 551 + 1) = 1 := by
    rw [show (3 * 551 + 1 : ℕ) = 2 ^ 1 * 827 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_681 : Todd 681 = 511 := by
  have hv : padicValNat 2 (3 * 681 + 1) = 2 := by
    rw [show (3 * 681 + 1 : ℕ) = 2 ^ 2 * 511 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_877 : Todd 877 = 329 := by
  have hv : padicValNat 2 (3 * 877 + 1) = 3 := by
    rw [show (3 * 877 + 1 : ℕ) = 2 ^ 3 * 329 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_983 : Todd 983 = 1475 := by
  have hv : padicValNat 2 (3 * 983 + 1) = 1 := by
    rw [show (3 * 983 + 1 : ℕ) = 2 ^ 1 * 1475 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_1079 : Todd 1079 = 1619 := by
  have hv : padicValNat 2 (3 * 1079 + 1) = 1 := by
    rw [show (3 * 1079 + 1 : ℕ) = 2 ^ 1 * 1619 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_1305 : Todd 1305 = 979 := by
  have hv : padicValNat 2 (3 * 1305 + 1) = 2 := by
    rw [show (3 * 1305 + 1 : ℕ) = 2 ^ 2 * 979 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_1511 : Todd 1511 = 2267 := by
  have hv : padicValNat 2 (3 * 1511 + 1) = 1 := by
    rw [show (3 * 1511 + 1 : ℕ) = 2 ^ 1 * 2267 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num

/-! ## §34 十條 ΔF 求值（kernel 直接計算） -/

lemma ΔF_231 : ΔF 231 = [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 3, 0, -1, 2, 0, 0, -1] := by
  unfold ΔF
  rw [Todd_231]
  decide
lemma ΔF_323 : ΔF 323 = [0, 0, 1, 1, 2, -1, -1, -1, -2, 0, 0, 0, -2, 1, 0, 1, 0, 1] := by
  unfold ΔF
  rw [Todd_323]
  decide
lemma ΔF_403 : ΔF 403 = [0, 0, 0, 1, 1, 0, 0, -1, 0, 0, -1, 1, 0, -1, 0, 0, 0, 1] := by
  unfold ΔF
  rw [Todd_403]
  decide
lemma ΔF_551 : ΔF 551 = [0, 0, 0, 0, 0, 0, -1, -1, -2, 0, 1, 1, -2, 1, 1, 1, 1, 0] := by
  unfold ΔF
  rw [Todd_551]
  decide
lemma ΔF_681 : ΔF 681 = [0, 0, -1, 0, -1, 1, 0, 0, -1, -4, 1, 0, -4, 0, 0, 0, 1, 7] := by
  unfold ΔF
  rw [Todd_681]
  decide
lemma ΔF_877 : ΔF 877 = [0, 0, 1, -1, 0, -1, 0, 1, 2, 2, -1, -2, 3, 0, 0, -2, -3, 0] := by
  unfold ΔF
  rw [Todd_877]
  decide
lemma ΔF_983 : ΔF 983 = [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, -1, 0, 1, 0, 0, 0, -3] := by
  unfold ΔF
  rw [Todd_983]
  decide
lemma ΔF_1079 : ΔF 1079 = [0, 0, 0, 0, 0, 0, -1, 0, -1, 2, 1, -1, 1, 1, 1, -1, -1, -1] := by
  unfold ΔF
  rw [Todd_1079]
  decide
lemma ΔF_1305 : ΔF 1305 = [0, 0, -1, 0, -1, 1, 0, -1, -2, 0, 1, 0, -1, 0, -1, 1, 2, 1] := by
  unfold ΔF
  rw [Todd_1305]
  decide
lemma ΔF_1511 : ΔF 1511 = [0, 0, 0, 0, 0, 0, 0, 1, 2, -1, -1, 1, 1, -1, -1, 1, 1, -2] := by
  unfold ΔF
  rw [Todd_1511]
  decide

/-! ## §35 憑證算術（kernel 驗證：Σ wᵢ·ΔFᵢ = 31·e₇） -/

example :
    (([(100, [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 3, 0, -1, 2, 0, 0, -1]),
     (64, [0, 0, 1, 1, 2, -1, -1, -1, -2, 0, 0, 0, -2, 1, 0, 1, 0, 1]),
     (119, [0, 0, 0, 1, 1, 0, 0, -1, 0, 0, -1, 1, 0, -1, 0, 0, 0, 1]),
     (51, [0, 0, 0, 0, 0, 0, -1, -1, -2, 0, 1, 1, -2, 1, 1, 1, 1, 0]),
     (56, [0, 0, -1, 0, -1, 1, 0, 0, -1, -4, 1, 0, -4, 0, 0, 0, 1, 7]),
     (183, [0, 0, 1, -1, 0, -1, 0, 1, 2, 2, -1, -2, 3, 0, 0, -2, -3, 0]),
     (164, [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, -1, 0, 1, 0, 0, 0, -3]),
     (18, [0, 0, 0, 0, 0, 0, -1, 0, -1, 2, 1, -1, 1, 1, 1, -1, -1, -1]),
     (191, [0, 0, -1, 0, -1, 1, 0, -1, -2, 0, 1, 0, -1, 0, -1, 1, 2, 1]),
     (78, [0, 0, 0, 0, 0, 0, 0, 1, 2, -1, -1, 1, 1, -1, -1, 1, 1, -2])] : List (ℤ × List ℤ)).foldl
        (fun acc p => acc.zipWith (· + ·) (p.2.map (p.1 * ·))) (List.replicate 18 0))
    = [0, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide

/-! ## §36 主定理 -/

private lemma addneg {a b : ℚ} (ha : a < 0) (hb : b < 0) : a + b < 0 := by
  have h := add_lt_add ha hb
  simpa using h

/-- **主定理（照定案敘述）**：不存在非負權重使勢能在 W₁₀ 的每一步皆嚴格下降。 -/
theorem no_nonneg_linear_ranking :
    ¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧ ∀ x ∈ W₁₀, dot θ (ΔF x) < 0 := by
  rintro ⟨θ, hθ, hdesc⟩
  have h1 := hdesc 231 (by decide)
  have h2 := hdesc 323 (by decide)
  have h3 := hdesc 403 (by decide)
  have h4 := hdesc 551 (by decide)
  have h5 := hdesc 681 (by decide)
  have h6 := hdesc 877 (by decide)
  have h7 := hdesc 983 (by decide)
  have h8 := hdesc 1079 (by decide)
  have h9 := hdesc 1305 (by decide)
  have h10 := hdesc 1511 (by decide)
  have t1 : (100 : ℚ) * dot θ (ΔF 231) < 0 := mul_neg_of_pos_of_neg (by norm_num) h1
  have t2 : (64 : ℚ) * dot θ (ΔF 323) < 0 := mul_neg_of_pos_of_neg (by norm_num) h2
  have t3 : (119 : ℚ) * dot θ (ΔF 403) < 0 := mul_neg_of_pos_of_neg (by norm_num) h3
  have t4 : (51 : ℚ) * dot θ (ΔF 551) < 0 := mul_neg_of_pos_of_neg (by norm_num) h4
  have t5 : (56 : ℚ) * dot θ (ΔF 681) < 0 := mul_neg_of_pos_of_neg (by norm_num) h5
  have t6 : (183 : ℚ) * dot θ (ΔF 877) < 0 := mul_neg_of_pos_of_neg (by norm_num) h6
  have t7 : (164 : ℚ) * dot θ (ΔF 983) < 0 := mul_neg_of_pos_of_neg (by norm_num) h7
  have t8 : (18 : ℚ) * dot θ (ΔF 1079) < 0 := mul_neg_of_pos_of_neg (by norm_num) h8
  have t9 : (191 : ℚ) * dot θ (ΔF 1305) < 0 := mul_neg_of_pos_of_neg (by norm_num) h9
  have t10 : (78 : ℚ) * dot θ (ΔF 1511) < 0 := mul_neg_of_pos_of_neg (by norm_num) h10
  have hlt : 100 * dot θ (ΔF 231) + 64 * dot θ (ΔF 323) + 119 * dot θ (ΔF 403) + 51 * dot θ (ΔF 551) + 56 * dot θ (ΔF 681) + 183 * dot θ (ΔF 877) + 164 * dot θ (ΔF 983) + 18 * dot θ (ΔF 1079) + 191 * dot θ (ΔF 1305) + 78 * dot θ (ΔF 1511) < 0 :=
    addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (t1) t2) t3) t4) t5) t6) t7) t8) t9) t10
  have key : 100 * dot θ (ΔF 231) + 64 * dot θ (ΔF 323) + 119 * dot θ (ΔF 403) + 51 * dot θ (ΔF 551) + 56 * dot θ (ΔF 681) + 183 * dot θ (ΔF 877) + 164 * dot θ (ΔF 983) + 18 * dot θ (ΔF 1079) + 191 * dot θ (ΔF 1305) + 78 * dot θ (ΔF 1511) = 31 * θ 6 := by
    rw [ΔF_231, ΔF_323, ΔF_403, ΔF_551, ΔF_681, ΔF_877, ΔF_983, ΔF_1079, ΔF_1305, ΔF_1511]
    simp only [dot]
    push_cast
    ring
  rw [key] at hlt
  exact absurd hlt (not_lt.mpr (mul_nonneg (by norm_num) (hθ 6)))

lemma W₁₀_odd : ∀ x ∈ W₁₀, x % 2 = 1 := by decide

/-- **標題句**：對此 Level 2 occupation feature class，不存在對**每個奇數**的
單次加速迭代皆嚴格下降的非負線性 additive ranking function。 -/
theorem no_global_odd_ranking :
    ¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧ ∀ x : ℕ, x % 2 = 1 → dot θ (ΔF x) < 0 := by
  rintro ⟨θ, hθ, h⟩
  exact no_nonneg_linear_ranking ⟨θ, hθ, fun x hx => h x (W₁₀_odd x hx)⟩

/-! ## §37 數據驗證（回歸；全部應輸出 `true`） -/

section Verification

#eval W₁₀.all (fun x => x % 2 == 1)
#eval [(231,347),(323,485),(403,605),(551,827),(681,511),(877,329),(983,1475),(1079,1619),(1305,979),(1511,2267)].all
  (fun p => Todd p.1 == p.2)
#eval ΔF 231 == [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 3, 0, -1, 2, 0, 0, -1]
#eval ΔF 323 == [0, 0, 1, 1, 2, -1, -1, -1, -2, 0, 0, 0, -2, 1, 0, 1, 0, 1]
#eval ΔF 403 == [0, 0, 0, 1, 1, 0, 0, -1, 0, 0, -1, 1, 0, -1, 0, 0, 0, 1]
#eval ΔF 551 == [0, 0, 0, 0, 0, 0, -1, -1, -2, 0, 1, 1, -2, 1, 1, 1, 1, 0]
#eval ΔF 681 == [0, 0, -1, 0, -1, 1, 0, 0, -1, -4, 1, 0, -4, 0, 0, 0, 1, 7]
#eval ΔF 877 == [0, 0, 1, -1, 0, -1, 0, 1, 2, 2, -1, -2, 3, 0, 0, -2, -3, 0]
#eval ΔF 983 == [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, -1, 0, 1, 0, 0, 0, -3]
#eval ΔF 1079 == [0, 0, 0, 0, 0, 0, -1, 0, -1, 2, 1, -1, 1, 1, 1, -1, -1, -1]
#eval ΔF 1305 == [0, 0, -1, 0, -1, 1, 0, -1, -2, 0, 1, 0, -1, 0, -1, 1, 2, 1]
#eval ΔF 1511 == [0, 0, 0, 0, 0, 0, 0, 1, 2, -1, -1, 1, 1, -1, -1, 1, 1, -2]

end Verification

end CollatzFST.LP
