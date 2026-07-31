/-
# Level 3 下界與維度定理：`dim span(dF96) = 31`（ROADMAP A-3 Level 3 收官）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_L3_DimUpper.lean`（§79–81）。

上界 `≤ 31` 已由 65 條差分層泛函給出（`finrank_span_dFQ96_le`）。本檔補下界：
31 個具體見證（`tools/l3_recon.py` 的 `LEAN_L3_WITNESSES`，貪心取最小奇數）
投影到 §81 那 31 個自由座標（`freeIdx96`）構成 31×31 可逆矩陣——
行列式 = **1**（么模；比 Level 2 的 31 更乾淨），其整數逆矩陣 `B`
（max |B| = 3）錨在 `LEAN_L3_WITNESS_INV`。

與 Level 2 `DimLower` 的差異：31 元 31 式不餵 `linarith`（搜尋成本對變數數
敏感），每個 `g i = 0` 直接給方程的顯式整數組合 `g i = Σₜ B[t][i]·hₜ`，
一行 `linear_combination`——由 `Mw·B = I`（CI 對帳）保證恰好回到 `g i`。

見證值引理走 `simp only [展開 + Todd 改寫] ; decide +kernel`：
elaborator 端的化約會卡在 Mathlib 的 ℚ 實例鏈（`Rat.sub` 的結構投影），
kernel 端不吃 `irreducible` 且 `Nat.gcd` 有內建加速。
`Todd`（`padicValNat`）不可 kernel 求值，必須先用 `Todd_w` 引理換掉。

本檔為**機械生成**（`tools/gen_l3dim.py`，錨資料同 `l3_recon.py` ⑦，
CI 重生成並 diff），維護時改生成器不改手寫。

## 主定理

`finrank_span_dFQ96_eq_31 : Module.finrank ℚ (span ℚ (Set.range dFQ96)) = 31`

即 HandOver「Level 3 雙模式有效差分生成空間 = 31 維（不是 96）」的形式化。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_DimUpper
import Mathlib.Tactic.LinearCombination

namespace CollatzFST.L3

open CollatzFST

/-! ## §82 31 個見證的 Todd 求值 -/

private lemma Todd_3 : Todd 3 = 5 := by
  have hv : padicValNat 2 (3 * 3 + 1) = 1 := by
    rw [show (3 * 3 + 1 : ℕ) = 2 ^ 1 * 5 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_5 : Todd 5 = 1 := by
  have hv : padicValNat 2 (3 * 5 + 1) = 4 := by
    rw [show (3 * 5 + 1 : ℕ) = 2 ^ 4 * 1 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_7 : Todd 7 = 11 := by
  have hv : padicValNat 2 (3 * 7 + 1) = 1 := by
    rw [show (3 * 7 + 1 : ℕ) = 2 ^ 1 * 11 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_9 : Todd 9 = 7 := by
  have hv : padicValNat 2 (3 * 9 + 1) = 2 := by
    rw [show (3 * 9 + 1 : ℕ) = 2 ^ 2 * 7 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_11 : Todd 11 = 17 := by
  have hv : padicValNat 2 (3 * 11 + 1) = 1 := by
    rw [show (3 * 11 + 1 : ℕ) = 2 ^ 1 * 17 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_13 : Todd 13 = 5 := by
  have hv : padicValNat 2 (3 * 13 + 1) = 3 := by
    rw [show (3 * 13 + 1 : ℕ) = 2 ^ 3 * 5 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_15 : Todd 15 = 23 := by
  have hv : padicValNat 2 (3 * 15 + 1) = 1 := by
    rw [show (3 * 15 + 1 : ℕ) = 2 ^ 1 * 23 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_17 : Todd 17 = 13 := by
  have hv : padicValNat 2 (3 * 17 + 1) = 2 := by
    rw [show (3 * 17 + 1 : ℕ) = 2 ^ 2 * 13 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_19 : Todd 19 = 29 := by
  have hv : padicValNat 2 (3 * 19 + 1) = 1 := by
    rw [show (3 * 19 + 1 : ℕ) = 2 ^ 1 * 29 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_23 : Todd 23 = 35 := by
  have hv : padicValNat 2 (3 * 23 + 1) = 1 := by
    rw [show (3 * 23 + 1 : ℕ) = 2 ^ 1 * 35 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_25 : Todd 25 = 19 := by
  have hv : padicValNat 2 (3 * 25 + 1) = 2 := by
    rw [show (3 * 25 + 1 : ℕ) = 2 ^ 2 * 19 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_27 : Todd 27 = 41 := by
  have hv : padicValNat 2 (3 * 27 + 1) = 1 := by
    rw [show (3 * 27 + 1 : ℕ) = 2 ^ 1 * 41 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_33 : Todd 33 = 25 := by
  have hv : padicValNat 2 (3 * 33 + 1) = 2 := by
    rw [show (3 * 33 + 1 : ℕ) = 2 ^ 2 * 25 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_39 : Todd 39 = 59 := by
  have hv : padicValNat 2 (3 * 39 + 1) = 1 := by
    rw [show (3 * 39 + 1 : ℕ) = 2 ^ 1 * 59 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_43 : Todd 43 = 65 := by
  have hv : padicValNat 2 (3 * 43 + 1) = 1 := by
    rw [show (3 * 43 + 1 : ℕ) = 2 ^ 1 * 65 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_49 : Todd 49 = 37 := by
  have hv : padicValNat 2 (3 * 49 + 1) = 2 := by
    rw [show (3 * 49 + 1 : ℕ) = 2 ^ 2 * 37 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_51 : Todd 51 = 77 := by
  have hv : padicValNat 2 (3 * 51 + 1) = 1 := by
    rw [show (3 * 51 + 1 : ℕ) = 2 ^ 1 * 77 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_55 : Todd 55 = 83 := by
  have hv : padicValNat 2 (3 * 55 + 1) = 1 := by
    rw [show (3 * 55 + 1 : ℕ) = 2 ^ 1 * 83 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_57 : Todd 57 = 43 := by
  have hv : padicValNat 2 (3 * 57 + 1) = 2 := by
    rw [show (3 * 57 + 1 : ℕ) = 2 ^ 2 * 43 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_59 : Todd 59 = 89 := by
  have hv : padicValNat 2 (3 * 59 + 1) = 1 := by
    rw [show (3 * 59 + 1 : ℕ) = 2 ^ 1 * 89 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_65 : Todd 65 = 49 := by
  have hv : padicValNat 2 (3 * 65 + 1) = 2 := by
    rw [show (3 * 65 + 1 : ℕ) = 2 ^ 2 * 49 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_67 : Todd 67 = 101 := by
  have hv : padicValNat 2 (3 * 67 + 1) = 1 := by
    rw [show (3 * 67 + 1 : ℕ) = 2 ^ 1 * 101 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_73 : Todd 73 = 55 := by
  have hv : padicValNat 2 (3 * 73 + 1) = 2 := by
    rw [show (3 * 73 + 1 : ℕ) = 2 ^ 2 * 55 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_87 : Todd 87 = 131 := by
  have hv : padicValNat 2 (3 * 87 + 1) = 1 := by
    rw [show (3 * 87 + 1 : ℕ) = 2 ^ 1 * 131 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_99 : Todd 99 = 149 := by
  have hv : padicValNat 2 (3 * 99 + 1) = 1 := by
    rw [show (3 * 99 + 1 : ℕ) = 2 ^ 1 * 149 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_115 : Todd 115 = 173 := by
  have hv : padicValNat 2 (3 * 115 + 1) = 1 := by
    rw [show (3 * 115 + 1 : ℕ) = 2 ^ 1 * 173 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_121 : Todd 121 = 91 := by
  have hv : padicValNat 2 (3 * 121 + 1) = 2 := by
    rw [show (3 * 121 + 1 : ℕ) = 2 ^ 2 * 91 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_123 : Todd 123 = 185 := by
  have hv : padicValNat 2 (3 * 123 + 1) = 1 := by
    rw [show (3 * 123 + 1 : ℕ) = 2 ^ 1 * 185 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_147 : Todd 147 = 221 := by
  have hv : padicValNat 2 (3 * 147 + 1) = 1 := by
    rw [show (3 * 147 + 1 : ℕ) = 2 ^ 1 * 221 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_217 : Todd 217 = 163 := by
  have hv : padicValNat 2 (3 * 217 + 1) = 2 := by
    rw [show (3 * 217 + 1 : ℕ) = 2 ^ 2 * 163 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
private lemma Todd_249 : Todd 249 = 187 := by
  have hv : padicValNat 2 (3 * 249 + 1) = 2 := by
    rw [show (3 * 249 + 1 : ℕ) = 2 ^ 2 * 187 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num

/-! ## §83 見證族 -/

/-- 31 個下界見證（`tools/l3_recon.py` 的 `LEAN_L3_WITNESSES`，貪心取最小奇數；
投影到自由座標的行列式 = 1）。 -/
def wit31 : Fin 31 → ℕ := ![3, 5, 7, 9, 11, 13, 15, 17, 19, 23, 25, 27, 33, 39, 43, 49, 51, 55, 57, 59, 65, 67, 73, 87, 99, 115, 121, 123, 147, 217, 249]

/-- 見證的 96 維雙模式差分向量族。 -/
def dFW96 : Fin 31 → (Fin 96 → ℚ) := fun i => dFQ96 (wit31 i)

/-! ## §84 見證值：自由座標上的 31×31 矩陣（每見證一條 `decide +kernel`） -/

private lemma row_3 : ∀ t : Fin 31, dFQ96 3 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_3]
  decide +kernel
private lemma row_5 : ∀ t : Fin 31, dFQ96 5 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_5]
  decide +kernel
private lemma row_7 : ∀ t : Fin 31, dFQ96 7 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0,
      -1, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_7]
  decide +kernel
private lemma row_9 : ∀ t : Fin 31, dFQ96 9 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_9]
  decide +kernel
private lemma row_11 : ∀ t : Fin 31, dFQ96 11 (freeIdx96 t) =
    (![0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_11]
  decide +kernel
private lemma row_13 : ∀ t : Fin 31, dFQ96 13 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_13]
  decide +kernel
private lemma row_15 : ∀ t : Fin 31, dFQ96 15 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      -1] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_15]
  decide +kernel
private lemma row_17 : ∀ t : Fin 31, dFQ96 17 (freeIdx96 t) =
    (![0, -1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0,
      0, 0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_17]
  decide +kernel
private lemma row_19 : ∀ t : Fin 31, dFQ96 19 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1, 0, 0,
      1, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_19]
  decide +kernel
private lemma row_23 : ∀ t : Fin 31, dFQ96 23 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, 0, 0, -1, 0, 1, 0, 0,
      -1, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_23]
  decide +kernel
private lemma row_25 : ∀ t : Fin 31, dFQ96 25 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_25]
  decide +kernel
private lemma row_27 : ∀ t : Fin 31, dFQ96 27 (freeIdx96 t) =
    (![0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, -2, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_27]
  decide +kernel
private lemma row_33 : ∀ t : Fin 31, dFQ96 33 (freeIdx96 t) =
    (![0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_33]
  decide +kernel
private lemma row_39 : ∀ t : Fin 31, dFQ96 39 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 1, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_39]
  decide +kernel
private lemma row_43 : ∀ t : Fin 31, dFQ96 43 (freeIdx96 t) =
    (![1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -2, 0, -1, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_43]
  decide +kernel
private lemma row_49 : ∀ t : Fin 31, dFQ96 49 (freeIdx96 t) =
    (![0, -1, -1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_49]
  decide +kernel
private lemma row_51 : ∀ t : Fin 31, dFQ96 51 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 0, 0, 0, -1, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_51]
  decide +kernel
private lemma row_55 : ∀ t : Fin 31, dFQ96 55 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 2, 0, 0, 0, -1, 0, 0, 0,
      -1, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_55]
  decide +kernel
private lemma row_57 : ∀ t : Fin 31, dFQ96 57 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0,
      0, 0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_57]
  decide +kernel
private lemma row_59 : ∀ t : Fin 31, dFQ96 59 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, -1, 0, 0,
      -1, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_59]
  decide +kernel
private lemma row_65 : ∀ t : Fin 31, dFQ96 65 (freeIdx96 t) =
    (![-1, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_65]
  decide +kernel
private lemma row_67 : ∀ t : Fin 31, dFQ96 67 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_67]
  decide +kernel
private lemma row_73 : ∀ t : Fin 31, dFQ96 73 (freeIdx96 t) =
    (![0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0,
      0, 1, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_73]
  decide +kernel
private lemma row_87 : ∀ t : Fin 31, dFQ96 87 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, -1, 0, 0, 0, -2, 0, 1, 0, 0,
      -1, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_87]
  decide +kernel
private lemma row_99 : ∀ t : Fin 31, dFQ96 99 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1,
      0, 0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_99]
  decide +kernel
private lemma row_115 : ∀ t : Fin 31, dFQ96 115 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 1, 2, 0, -1, 0, -1,
      0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_115]
  decide +kernel
private lemma row_121 : ∀ t : Fin 31, dFQ96 121 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 2, 0,
      0, 0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_121]
  decide +kernel
private lemma row_123 : ∀ t : Fin 31, dFQ96 123 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, -1, 0, 0,
      -1, -1] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_123]
  decide +kernel
private lemma row_147 : ∀ t : Fin 31, dFQ96 147 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 1, -1, 0, 1, 0, 1, 0, 0, 0,
      1, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_147]
  decide +kernel
private lemma row_217 : ∀ t : Fin 31, dFQ96 217 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0,
      0, 0, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_217]
  decide +kernel
private lemma row_249 : ∀ t : Fin 31, dFQ96 249 (freeIdx96 t) =
    (![0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 1, 0,
      0, 1, 0] : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_249]
  decide +kernel

/-! ## §85 純量讀出（`rw` 用的字面形式；由 row 引理 defeq 取出） -/

-- 自由座標 0（96 維索引 8）
private lemma v_0_0 : dFQ96 3 (8 : Fin 96) = 0 := row_3 0
private lemma v_0_1 : dFQ96 5 (8 : Fin 96) = 0 := row_5 0
private lemma v_0_2 : dFQ96 7 (8 : Fin 96) = 0 := row_7 0
private lemma v_0_3 : dFQ96 9 (8 : Fin 96) = 0 := row_9 0
private lemma v_0_4 : dFQ96 11 (8 : Fin 96) = 0 := row_11 0
private lemma v_0_5 : dFQ96 13 (8 : Fin 96) = 0 := row_13 0
private lemma v_0_6 : dFQ96 15 (8 : Fin 96) = 0 := row_15 0
private lemma v_0_7 : dFQ96 17 (8 : Fin 96) = 0 := row_17 0
private lemma v_0_8 : dFQ96 19 (8 : Fin 96) = 0 := row_19 0
private lemma v_0_9 : dFQ96 23 (8 : Fin 96) = 0 := row_23 0
private lemma v_0_10 : dFQ96 25 (8 : Fin 96) = 0 := row_25 0
private lemma v_0_11 : dFQ96 27 (8 : Fin 96) = 0 := row_27 0
private lemma v_0_12 : dFQ96 33 (8 : Fin 96) = 0 := row_33 0
private lemma v_0_13 : dFQ96 39 (8 : Fin 96) = 0 := row_39 0
private lemma v_0_14 : dFQ96 43 (8 : Fin 96) = 1 := row_43 0
private lemma v_0_15 : dFQ96 49 (8 : Fin 96) = 0 := row_49 0
private lemma v_0_16 : dFQ96 51 (8 : Fin 96) = 0 := row_51 0
private lemma v_0_17 : dFQ96 55 (8 : Fin 96) = 0 := row_55 0
private lemma v_0_18 : dFQ96 57 (8 : Fin 96) = 0 := row_57 0
private lemma v_0_19 : dFQ96 59 (8 : Fin 96) = 0 := row_59 0
private lemma v_0_20 : dFQ96 65 (8 : Fin 96) = -1 := row_65 0
private lemma v_0_21 : dFQ96 67 (8 : Fin 96) = 0 := row_67 0
private lemma v_0_22 : dFQ96 73 (8 : Fin 96) = 0 := row_73 0
private lemma v_0_23 : dFQ96 87 (8 : Fin 96) = 0 := row_87 0
private lemma v_0_24 : dFQ96 99 (8 : Fin 96) = 0 := row_99 0
private lemma v_0_25 : dFQ96 115 (8 : Fin 96) = 0 := row_115 0
private lemma v_0_26 : dFQ96 121 (8 : Fin 96) = 0 := row_121 0
private lemma v_0_27 : dFQ96 123 (8 : Fin 96) = 0 := row_123 0
private lemma v_0_28 : dFQ96 147 (8 : Fin 96) = 0 := row_147 0
private lemma v_0_29 : dFQ96 217 (8 : Fin 96) = 0 := row_217 0
private lemma v_0_30 : dFQ96 249 (8 : Fin 96) = 0 := row_249 0
-- 自由座標 1（96 維索引 10）
private lemma v_1_0 : dFQ96 3 (10 : Fin 96) = 0 := row_3 1
private lemma v_1_1 : dFQ96 5 (10 : Fin 96) = 0 := row_5 1
private lemma v_1_2 : dFQ96 7 (10 : Fin 96) = 0 := row_7 1
private lemma v_1_3 : dFQ96 9 (10 : Fin 96) = 0 := row_9 1
private lemma v_1_4 : dFQ96 11 (10 : Fin 96) = 1 := row_11 1
private lemma v_1_5 : dFQ96 13 (10 : Fin 96) = 0 := row_13 1
private lemma v_1_6 : dFQ96 15 (10 : Fin 96) = 0 := row_15 1
private lemma v_1_7 : dFQ96 17 (10 : Fin 96) = -1 := row_17 1
private lemma v_1_8 : dFQ96 19 (10 : Fin 96) = 0 := row_19 1
private lemma v_1_9 : dFQ96 23 (10 : Fin 96) = 0 := row_23 1
private lemma v_1_10 : dFQ96 25 (10 : Fin 96) = 0 := row_25 1
private lemma v_1_11 : dFQ96 27 (10 : Fin 96) = 0 := row_27 1
private lemma v_1_12 : dFQ96 33 (10 : Fin 96) = -1 := row_33 1
private lemma v_1_13 : dFQ96 39 (10 : Fin 96) = 0 := row_39 1
private lemma v_1_14 : dFQ96 43 (10 : Fin 96) = 1 := row_43 1
private lemma v_1_15 : dFQ96 49 (10 : Fin 96) = -1 := row_49 1
private lemma v_1_16 : dFQ96 51 (10 : Fin 96) = 0 := row_51 1
private lemma v_1_17 : dFQ96 55 (10 : Fin 96) = 0 := row_55 1
private lemma v_1_18 : dFQ96 57 (10 : Fin 96) = 0 := row_57 1
private lemma v_1_19 : dFQ96 59 (10 : Fin 96) = 0 := row_59 1
private lemma v_1_20 : dFQ96 65 (10 : Fin 96) = 0 := row_65 1
private lemma v_1_21 : dFQ96 67 (10 : Fin 96) = 0 := row_67 1
private lemma v_1_22 : dFQ96 73 (10 : Fin 96) = 0 := row_73 1
private lemma v_1_23 : dFQ96 87 (10 : Fin 96) = 0 := row_87 1
private lemma v_1_24 : dFQ96 99 (10 : Fin 96) = 0 := row_99 1
private lemma v_1_25 : dFQ96 115 (10 : Fin 96) = 0 := row_115 1
private lemma v_1_26 : dFQ96 121 (10 : Fin 96) = 0 := row_121 1
private lemma v_1_27 : dFQ96 123 (10 : Fin 96) = 0 := row_123 1
private lemma v_1_28 : dFQ96 147 (10 : Fin 96) = 0 := row_147 1
private lemma v_1_29 : dFQ96 217 (10 : Fin 96) = 0 := row_217 1
private lemma v_1_30 : dFQ96 249 (10 : Fin 96) = 0 := row_249 1
-- 自由座標 2（96 維索引 13）
private lemma v_2_0 : dFQ96 3 (13 : Fin 96) = 0 := row_3 2
private lemma v_2_1 : dFQ96 5 (13 : Fin 96) = 0 := row_5 2
private lemma v_2_2 : dFQ96 7 (13 : Fin 96) = 0 := row_7 2
private lemma v_2_3 : dFQ96 9 (13 : Fin 96) = 0 := row_9 2
private lemma v_2_4 : dFQ96 11 (13 : Fin 96) = 1 := row_11 2
private lemma v_2_5 : dFQ96 13 (13 : Fin 96) = 0 := row_13 2
private lemma v_2_6 : dFQ96 15 (13 : Fin 96) = 0 := row_15 2
private lemma v_2_7 : dFQ96 17 (13 : Fin 96) = -1 := row_17 2
private lemma v_2_8 : dFQ96 19 (13 : Fin 96) = 0 := row_19 2
private lemma v_2_9 : dFQ96 23 (13 : Fin 96) = 0 := row_23 2
private lemma v_2_10 : dFQ96 25 (13 : Fin 96) = 0 := row_25 2
private lemma v_2_11 : dFQ96 27 (13 : Fin 96) = 0 := row_27 2
private lemma v_2_12 : dFQ96 33 (13 : Fin 96) = 0 := row_33 2
private lemma v_2_13 : dFQ96 39 (13 : Fin 96) = 0 := row_39 2
private lemma v_2_14 : dFQ96 43 (13 : Fin 96) = 0 := row_43 2
private lemma v_2_15 : dFQ96 49 (13 : Fin 96) = -1 := row_49 2
private lemma v_2_16 : dFQ96 51 (13 : Fin 96) = 0 := row_51 2
private lemma v_2_17 : dFQ96 55 (13 : Fin 96) = 0 := row_55 2
private lemma v_2_18 : dFQ96 57 (13 : Fin 96) = 0 := row_57 2
private lemma v_2_19 : dFQ96 59 (13 : Fin 96) = 0 := row_59 2
private lemma v_2_20 : dFQ96 65 (13 : Fin 96) = 1 := row_65 2
private lemma v_2_21 : dFQ96 67 (13 : Fin 96) = 0 := row_67 2
private lemma v_2_22 : dFQ96 73 (13 : Fin 96) = -1 := row_73 2
private lemma v_2_23 : dFQ96 87 (13 : Fin 96) = 0 := row_87 2
private lemma v_2_24 : dFQ96 99 (13 : Fin 96) = 0 := row_99 2
private lemma v_2_25 : dFQ96 115 (13 : Fin 96) = 0 := row_115 2
private lemma v_2_26 : dFQ96 121 (13 : Fin 96) = 0 := row_121 2
private lemma v_2_27 : dFQ96 123 (13 : Fin 96) = 0 := row_123 2
private lemma v_2_28 : dFQ96 147 (13 : Fin 96) = 0 := row_147 2
private lemma v_2_29 : dFQ96 217 (13 : Fin 96) = 0 := row_217 2
private lemma v_2_30 : dFQ96 249 (13 : Fin 96) = 0 := row_249 2
-- 自由座標 3（96 維索引 15）
private lemma v_3_0 : dFQ96 3 (15 : Fin 96) = 0 := row_3 3
private lemma v_3_1 : dFQ96 5 (15 : Fin 96) = 0 := row_5 3
private lemma v_3_2 : dFQ96 7 (15 : Fin 96) = 0 := row_7 3
private lemma v_3_3 : dFQ96 9 (15 : Fin 96) = 0 := row_9 3
private lemma v_3_4 : dFQ96 11 (15 : Fin 96) = 0 := row_11 3
private lemma v_3_5 : dFQ96 13 (15 : Fin 96) = 0 := row_13 3
private lemma v_3_6 : dFQ96 15 (15 : Fin 96) = 0 := row_15 3
private lemma v_3_7 : dFQ96 17 (15 : Fin 96) = 0 := row_17 3
private lemma v_3_8 : dFQ96 19 (15 : Fin 96) = 0 := row_19 3
private lemma v_3_9 : dFQ96 23 (15 : Fin 96) = 0 := row_23 3
private lemma v_3_10 : dFQ96 25 (15 : Fin 96) = 0 := row_25 3
private lemma v_3_11 : dFQ96 27 (15 : Fin 96) = 1 := row_27 3
private lemma v_3_12 : dFQ96 33 (15 : Fin 96) = 0 := row_33 3
private lemma v_3_13 : dFQ96 39 (15 : Fin 96) = 0 := row_39 3
private lemma v_3_14 : dFQ96 43 (15 : Fin 96) = 0 := row_43 3
private lemma v_3_15 : dFQ96 49 (15 : Fin 96) = 0 := row_49 3
private lemma v_3_16 : dFQ96 51 (15 : Fin 96) = 0 := row_51 3
private lemma v_3_17 : dFQ96 55 (15 : Fin 96) = 0 := row_55 3
private lemma v_3_18 : dFQ96 57 (15 : Fin 96) = 0 := row_57 3
private lemma v_3_19 : dFQ96 59 (15 : Fin 96) = 0 := row_59 3
private lemma v_3_20 : dFQ96 65 (15 : Fin 96) = 0 := row_65 3
private lemma v_3_21 : dFQ96 67 (15 : Fin 96) = 0 := row_67 3
private lemma v_3_22 : dFQ96 73 (15 : Fin 96) = 0 := row_73 3
private lemma v_3_23 : dFQ96 87 (15 : Fin 96) = 0 := row_87 3
private lemma v_3_24 : dFQ96 99 (15 : Fin 96) = 0 := row_99 3
private lemma v_3_25 : dFQ96 115 (15 : Fin 96) = 0 := row_115 3
private lemma v_3_26 : dFQ96 121 (15 : Fin 96) = 0 := row_121 3
private lemma v_3_27 : dFQ96 123 (15 : Fin 96) = 0 := row_123 3
private lemma v_3_28 : dFQ96 147 (15 : Fin 96) = 0 := row_147 3
private lemma v_3_29 : dFQ96 217 (15 : Fin 96) = 0 := row_217 3
private lemma v_3_30 : dFQ96 249 (15 : Fin 96) = 0 := row_249 3
-- 自由座標 4（96 維索引 26）
private lemma v_4_0 : dFQ96 3 (26 : Fin 96) = 0 := row_3 4
private lemma v_4_1 : dFQ96 5 (26 : Fin 96) = 0 := row_5 4
private lemma v_4_2 : dFQ96 7 (26 : Fin 96) = 0 := row_7 4
private lemma v_4_3 : dFQ96 9 (26 : Fin 96) = 0 := row_9 4
private lemma v_4_4 : dFQ96 11 (26 : Fin 96) = 1 := row_11 4
private lemma v_4_5 : dFQ96 13 (26 : Fin 96) = 0 := row_13 4
private lemma v_4_6 : dFQ96 15 (26 : Fin 96) = 0 := row_15 4
private lemma v_4_7 : dFQ96 17 (26 : Fin 96) = -1 := row_17 4
private lemma v_4_8 : dFQ96 19 (26 : Fin 96) = 0 := row_19 4
private lemma v_4_9 : dFQ96 23 (26 : Fin 96) = 0 := row_23 4
private lemma v_4_10 : dFQ96 25 (26 : Fin 96) = 0 := row_25 4
private lemma v_4_11 : dFQ96 27 (26 : Fin 96) = 0 := row_27 4
private lemma v_4_12 : dFQ96 33 (26 : Fin 96) = -1 := row_33 4
private lemma v_4_13 : dFQ96 39 (26 : Fin 96) = 0 := row_39 4
private lemma v_4_14 : dFQ96 43 (26 : Fin 96) = 1 := row_43 4
private lemma v_4_15 : dFQ96 49 (26 : Fin 96) = 0 := row_49 4
private lemma v_4_16 : dFQ96 51 (26 : Fin 96) = 0 := row_51 4
private lemma v_4_17 : dFQ96 55 (26 : Fin 96) = 0 := row_55 4
private lemma v_4_18 : dFQ96 57 (26 : Fin 96) = 0 := row_57 4
private lemma v_4_19 : dFQ96 59 (26 : Fin 96) = 0 := row_59 4
private lemma v_4_20 : dFQ96 65 (26 : Fin 96) = -1 := row_65 4
private lemma v_4_21 : dFQ96 67 (26 : Fin 96) = 0 := row_67 4
private lemma v_4_22 : dFQ96 73 (26 : Fin 96) = -1 := row_73 4
private lemma v_4_23 : dFQ96 87 (26 : Fin 96) = 0 := row_87 4
private lemma v_4_24 : dFQ96 99 (26 : Fin 96) = 0 := row_99 4
private lemma v_4_25 : dFQ96 115 (26 : Fin 96) = 0 := row_115 4
private lemma v_4_26 : dFQ96 121 (26 : Fin 96) = 0 := row_121 4
private lemma v_4_27 : dFQ96 123 (26 : Fin 96) = 0 := row_123 4
private lemma v_4_28 : dFQ96 147 (26 : Fin 96) = 0 := row_147 4
private lemma v_4_29 : dFQ96 217 (26 : Fin 96) = 0 := row_217 4
private lemma v_4_30 : dFQ96 249 (26 : Fin 96) = 0 := row_249 4
-- 自由座標 5（96 維索引 29）
private lemma v_5_0 : dFQ96 3 (29 : Fin 96) = 0 := row_3 5
private lemma v_5_1 : dFQ96 5 (29 : Fin 96) = 0 := row_5 5
private lemma v_5_2 : dFQ96 7 (29 : Fin 96) = 0 := row_7 5
private lemma v_5_3 : dFQ96 9 (29 : Fin 96) = 0 := row_9 5
private lemma v_5_4 : dFQ96 11 (29 : Fin 96) = 0 := row_11 5
private lemma v_5_5 : dFQ96 13 (29 : Fin 96) = 0 := row_13 5
private lemma v_5_6 : dFQ96 15 (29 : Fin 96) = 0 := row_15 5
private lemma v_5_7 : dFQ96 17 (29 : Fin 96) = 0 := row_17 5
private lemma v_5_8 : dFQ96 19 (29 : Fin 96) = 0 := row_19 5
private lemma v_5_9 : dFQ96 23 (29 : Fin 96) = 0 := row_23 5
private lemma v_5_10 : dFQ96 25 (29 : Fin 96) = 0 := row_25 5
private lemma v_5_11 : dFQ96 27 (29 : Fin 96) = 0 := row_27 5
private lemma v_5_12 : dFQ96 33 (29 : Fin 96) = 0 := row_33 5
private lemma v_5_13 : dFQ96 39 (29 : Fin 96) = 0 := row_39 5
private lemma v_5_14 : dFQ96 43 (29 : Fin 96) = 0 := row_43 5
private lemma v_5_15 : dFQ96 49 (29 : Fin 96) = 0 := row_49 5
private lemma v_5_16 : dFQ96 51 (29 : Fin 96) = 0 := row_51 5
private lemma v_5_17 : dFQ96 55 (29 : Fin 96) = 0 := row_55 5
private lemma v_5_18 : dFQ96 57 (29 : Fin 96) = 0 := row_57 5
private lemma v_5_19 : dFQ96 59 (29 : Fin 96) = 0 := row_59 5
private lemma v_5_20 : dFQ96 65 (29 : Fin 96) = 0 := row_65 5
private lemma v_5_21 : dFQ96 67 (29 : Fin 96) = 0 := row_67 5
private lemma v_5_22 : dFQ96 73 (29 : Fin 96) = 0 := row_73 5
private lemma v_5_23 : dFQ96 87 (29 : Fin 96) = 0 := row_87 5
private lemma v_5_24 : dFQ96 99 (29 : Fin 96) = 0 := row_99 5
private lemma v_5_25 : dFQ96 115 (29 : Fin 96) = 0 := row_115 5
private lemma v_5_26 : dFQ96 121 (29 : Fin 96) = 0 := row_121 5
private lemma v_5_27 : dFQ96 123 (29 : Fin 96) = 1 := row_123 5
private lemma v_5_28 : dFQ96 147 (29 : Fin 96) = 0 := row_147 5
private lemma v_5_29 : dFQ96 217 (29 : Fin 96) = 0 := row_217 5
private lemma v_5_30 : dFQ96 249 (29 : Fin 96) = 0 := row_249 5
-- 自由座標 6（96 維索引 30）
private lemma v_6_0 : dFQ96 3 (30 : Fin 96) = 0 := row_3 6
private lemma v_6_1 : dFQ96 5 (30 : Fin 96) = 0 := row_5 6
private lemma v_6_2 : dFQ96 7 (30 : Fin 96) = 0 := row_7 6
private lemma v_6_3 : dFQ96 9 (30 : Fin 96) = -1 := row_9 6
private lemma v_6_4 : dFQ96 11 (30 : Fin 96) = 0 := row_11 6
private lemma v_6_5 : dFQ96 13 (30 : Fin 96) = 0 := row_13 6
private lemma v_6_6 : dFQ96 15 (30 : Fin 96) = 0 := row_15 6
private lemma v_6_7 : dFQ96 17 (30 : Fin 96) = 0 := row_17 6
private lemma v_6_8 : dFQ96 19 (30 : Fin 96) = 0 := row_19 6
private lemma v_6_9 : dFQ96 23 (30 : Fin 96) = 0 := row_23 6
private lemma v_6_10 : dFQ96 25 (30 : Fin 96) = 0 := row_25 6
private lemma v_6_11 : dFQ96 27 (30 : Fin 96) = 2 := row_27 6
private lemma v_6_12 : dFQ96 33 (30 : Fin 96) = 0 := row_33 6
private lemma v_6_13 : dFQ96 39 (30 : Fin 96) = 0 := row_39 6
private lemma v_6_14 : dFQ96 43 (30 : Fin 96) = 0 := row_43 6
private lemma v_6_15 : dFQ96 49 (30 : Fin 96) = 1 := row_49 6
private lemma v_6_16 : dFQ96 51 (30 : Fin 96) = 0 := row_51 6
private lemma v_6_17 : dFQ96 55 (30 : Fin 96) = 0 := row_55 6
private lemma v_6_18 : dFQ96 57 (30 : Fin 96) = 0 := row_57 6
private lemma v_6_19 : dFQ96 59 (30 : Fin 96) = 0 := row_59 6
private lemma v_6_20 : dFQ96 65 (30 : Fin 96) = 0 := row_65 6
private lemma v_6_21 : dFQ96 67 (30 : Fin 96) = 0 := row_67 6
private lemma v_6_22 : dFQ96 73 (30 : Fin 96) = -1 := row_73 6
private lemma v_6_23 : dFQ96 87 (30 : Fin 96) = 0 := row_87 6
private lemma v_6_24 : dFQ96 99 (30 : Fin 96) = 1 := row_99 6
private lemma v_6_25 : dFQ96 115 (30 : Fin 96) = 0 := row_115 6
private lemma v_6_26 : dFQ96 121 (30 : Fin 96) = 0 := row_121 6
private lemma v_6_27 : dFQ96 123 (30 : Fin 96) = 0 := row_123 6
private lemma v_6_28 : dFQ96 147 (30 : Fin 96) = 0 := row_147 6
private lemma v_6_29 : dFQ96 217 (30 : Fin 96) = 0 := row_217 6
private lemma v_6_30 : dFQ96 249 (30 : Fin 96) = 0 := row_249 6
-- 自由座標 7（96 維索引 31）
private lemma v_7_0 : dFQ96 3 (31 : Fin 96) = 0 := row_3 7
private lemma v_7_1 : dFQ96 5 (31 : Fin 96) = 0 := row_5 7
private lemma v_7_2 : dFQ96 7 (31 : Fin 96) = 0 := row_7 7
private lemma v_7_3 : dFQ96 9 (31 : Fin 96) = 0 := row_9 7
private lemma v_7_4 : dFQ96 11 (31 : Fin 96) = 0 := row_11 7
private lemma v_7_5 : dFQ96 13 (31 : Fin 96) = 0 := row_13 7
private lemma v_7_6 : dFQ96 15 (31 : Fin 96) = 0 := row_15 7
private lemma v_7_7 : dFQ96 17 (31 : Fin 96) = 0 := row_17 7
private lemma v_7_8 : dFQ96 19 (31 : Fin 96) = 0 := row_19 7
private lemma v_7_9 : dFQ96 23 (31 : Fin 96) = 0 := row_23 7
private lemma v_7_10 : dFQ96 25 (31 : Fin 96) = -1 := row_25 7
private lemma v_7_11 : dFQ96 27 (31 : Fin 96) = 0 := row_27 7
private lemma v_7_12 : dFQ96 33 (31 : Fin 96) = 1 := row_33 7
private lemma v_7_13 : dFQ96 39 (31 : Fin 96) = 0 := row_39 7
private lemma v_7_14 : dFQ96 43 (31 : Fin 96) = 0 := row_43 7
private lemma v_7_15 : dFQ96 49 (31 : Fin 96) = 0 := row_49 7
private lemma v_7_16 : dFQ96 51 (31 : Fin 96) = 0 := row_51 7
private lemma v_7_17 : dFQ96 55 (31 : Fin 96) = 0 := row_55 7
private lemma v_7_18 : dFQ96 57 (31 : Fin 96) = -1 := row_57 7
private lemma v_7_19 : dFQ96 59 (31 : Fin 96) = 1 := row_59 7
private lemma v_7_20 : dFQ96 65 (31 : Fin 96) = 0 := row_65 7
private lemma v_7_21 : dFQ96 67 (31 : Fin 96) = 1 := row_67 7
private lemma v_7_22 : dFQ96 73 (31 : Fin 96) = 0 := row_73 7
private lemma v_7_23 : dFQ96 87 (31 : Fin 96) = 0 := row_87 7
private lemma v_7_24 : dFQ96 99 (31 : Fin 96) = 0 := row_99 7
private lemma v_7_25 : dFQ96 115 (31 : Fin 96) = 0 := row_115 7
private lemma v_7_26 : dFQ96 121 (31 : Fin 96) = -1 := row_121 7
private lemma v_7_27 : dFQ96 123 (31 : Fin 96) = 1 := row_123 7
private lemma v_7_28 : dFQ96 147 (31 : Fin 96) = 0 := row_147 7
private lemma v_7_29 : dFQ96 217 (31 : Fin 96) = -1 := row_217 7
private lemma v_7_30 : dFQ96 249 (31 : Fin 96) = -1 := row_249 7
-- 自由座標 8（96 維索引 32）
private lemma v_8_0 : dFQ96 3 (32 : Fin 96) = 2 := row_3 8
private lemma v_8_1 : dFQ96 5 (32 : Fin 96) = -1 := row_5 8
private lemma v_8_2 : dFQ96 7 (32 : Fin 96) = 0 := row_7 8
private lemma v_8_3 : dFQ96 9 (32 : Fin 96) = -1 := row_9 8
private lemma v_8_4 : dFQ96 11 (32 : Fin 96) = 1 := row_11 8
private lemma v_8_5 : dFQ96 13 (32 : Fin 96) = 2 := row_13 8
private lemma v_8_6 : dFQ96 15 (32 : Fin 96) = 0 := row_15 8
private lemma v_8_7 : dFQ96 17 (32 : Fin 96) = -1 := row_17 8
private lemma v_8_8 : dFQ96 19 (32 : Fin 96) = 0 := row_19 8
private lemma v_8_9 : dFQ96 23 (32 : Fin 96) = 0 := row_23 8
private lemma v_8_10 : dFQ96 25 (32 : Fin 96) = -1 := row_25 8
private lemma v_8_11 : dFQ96 27 (32 : Fin 96) = 1 := row_27 8
private lemma v_8_12 : dFQ96 33 (32 : Fin 96) = 0 := row_33 8
private lemma v_8_13 : dFQ96 39 (32 : Fin 96) = 0 := row_39 8
private lemma v_8_14 : dFQ96 43 (32 : Fin 96) = 1 := row_43 8
private lemma v_8_15 : dFQ96 49 (32 : Fin 96) = 1 := row_49 8
private lemma v_8_16 : dFQ96 51 (32 : Fin 96) = 0 := row_51 8
private lemma v_8_17 : dFQ96 55 (32 : Fin 96) = 0 := row_55 8
private lemma v_8_18 : dFQ96 57 (32 : Fin 96) = -1 := row_57 8
private lemma v_8_19 : dFQ96 59 (32 : Fin 96) = 1 := row_59 8
private lemma v_8_20 : dFQ96 65 (32 : Fin 96) = 0 := row_65 8
private lemma v_8_21 : dFQ96 67 (32 : Fin 96) = 2 := row_67 8
private lemma v_8_22 : dFQ96 73 (32 : Fin 96) = -1 := row_73 8
private lemma v_8_23 : dFQ96 87 (32 : Fin 96) = 0 := row_87 8
private lemma v_8_24 : dFQ96 99 (32 : Fin 96) = 3 := row_99 8
private lemma v_8_25 : dFQ96 115 (32 : Fin 96) = 0 := row_115 8
private lemma v_8_26 : dFQ96 121 (32 : Fin 96) = -1 := row_121 8
private lemma v_8_27 : dFQ96 123 (32 : Fin 96) = 1 := row_123 8
private lemma v_8_28 : dFQ96 147 (32 : Fin 96) = 0 := row_147 8
private lemma v_8_29 : dFQ96 217 (32 : Fin 96) = -1 := row_217 8
private lemma v_8_30 : dFQ96 249 (32 : Fin 96) = -1 := row_249 8
-- 自由座標 9（96 維索引 40）
private lemma v_9_0 : dFQ96 3 (40 : Fin 96) = 0 := row_3 9
private lemma v_9_1 : dFQ96 5 (40 : Fin 96) = 0 := row_5 9
private lemma v_9_2 : dFQ96 7 (40 : Fin 96) = 0 := row_7 9
private lemma v_9_3 : dFQ96 9 (40 : Fin 96) = 0 := row_9 9
private lemma v_9_4 : dFQ96 11 (40 : Fin 96) = 0 := row_11 9
private lemma v_9_5 : dFQ96 13 (40 : Fin 96) = 0 := row_13 9
private lemma v_9_6 : dFQ96 15 (40 : Fin 96) = 0 := row_15 9
private lemma v_9_7 : dFQ96 17 (40 : Fin 96) = 0 := row_17 9
private lemma v_9_8 : dFQ96 19 (40 : Fin 96) = 0 := row_19 9
private lemma v_9_9 : dFQ96 23 (40 : Fin 96) = 0 := row_23 9
private lemma v_9_10 : dFQ96 25 (40 : Fin 96) = 0 := row_25 9
private lemma v_9_11 : dFQ96 27 (40 : Fin 96) = 0 := row_27 9
private lemma v_9_12 : dFQ96 33 (40 : Fin 96) = 0 := row_33 9
private lemma v_9_13 : dFQ96 39 (40 : Fin 96) = 0 := row_39 9
private lemma v_9_14 : dFQ96 43 (40 : Fin 96) = 0 := row_43 9
private lemma v_9_15 : dFQ96 49 (40 : Fin 96) = 0 := row_49 9
private lemma v_9_16 : dFQ96 51 (40 : Fin 96) = 0 := row_51 9
private lemma v_9_17 : dFQ96 55 (40 : Fin 96) = 0 := row_55 9
private lemma v_9_18 : dFQ96 57 (40 : Fin 96) = 0 := row_57 9
private lemma v_9_19 : dFQ96 59 (40 : Fin 96) = 1 := row_59 9
private lemma v_9_20 : dFQ96 65 (40 : Fin 96) = 0 := row_65 9
private lemma v_9_21 : dFQ96 67 (40 : Fin 96) = 0 := row_67 9
private lemma v_9_22 : dFQ96 73 (40 : Fin 96) = 0 := row_73 9
private lemma v_9_23 : dFQ96 87 (40 : Fin 96) = 0 := row_87 9
private lemma v_9_24 : dFQ96 99 (40 : Fin 96) = 0 := row_99 9
private lemma v_9_25 : dFQ96 115 (40 : Fin 96) = 0 := row_115 9
private lemma v_9_26 : dFQ96 121 (40 : Fin 96) = 0 := row_121 9
private lemma v_9_27 : dFQ96 123 (40 : Fin 96) = 1 := row_123 9
private lemma v_9_28 : dFQ96 147 (40 : Fin 96) = 0 := row_147 9
private lemma v_9_29 : dFQ96 217 (40 : Fin 96) = 0 := row_217 9
private lemma v_9_30 : dFQ96 249 (40 : Fin 96) = 0 := row_249 9
-- 自由座標 10（96 維索引 42）
private lemma v_10_0 : dFQ96 3 (42 : Fin 96) = 0 := row_3 10
private lemma v_10_1 : dFQ96 5 (42 : Fin 96) = 0 := row_5 10
private lemma v_10_2 : dFQ96 7 (42 : Fin 96) = 0 := row_7 10
private lemma v_10_3 : dFQ96 9 (42 : Fin 96) = 0 := row_9 10
private lemma v_10_4 : dFQ96 11 (42 : Fin 96) = 0 := row_11 10
private lemma v_10_5 : dFQ96 13 (42 : Fin 96) = 0 := row_13 10
private lemma v_10_6 : dFQ96 15 (42 : Fin 96) = 0 := row_15 10
private lemma v_10_7 : dFQ96 17 (42 : Fin 96) = 0 := row_17 10
private lemma v_10_8 : dFQ96 19 (42 : Fin 96) = 0 := row_19 10
private lemma v_10_9 : dFQ96 23 (42 : Fin 96) = 0 := row_23 10
private lemma v_10_10 : dFQ96 25 (42 : Fin 96) = 0 := row_25 10
private lemma v_10_11 : dFQ96 27 (42 : Fin 96) = 0 := row_27 10
private lemma v_10_12 : dFQ96 33 (42 : Fin 96) = 0 := row_33 10
private lemma v_10_13 : dFQ96 39 (42 : Fin 96) = 0 := row_39 10
private lemma v_10_14 : dFQ96 43 (42 : Fin 96) = 0 := row_43 10
private lemma v_10_15 : dFQ96 49 (42 : Fin 96) = 0 := row_49 10
private lemma v_10_16 : dFQ96 51 (42 : Fin 96) = 0 := row_51 10
private lemma v_10_17 : dFQ96 55 (42 : Fin 96) = 0 := row_55 10
private lemma v_10_18 : dFQ96 57 (42 : Fin 96) = -1 := row_57 10
private lemma v_10_19 : dFQ96 59 (42 : Fin 96) = 0 := row_59 10
private lemma v_10_20 : dFQ96 65 (42 : Fin 96) = 0 := row_65 10
private lemma v_10_21 : dFQ96 67 (42 : Fin 96) = 0 := row_67 10
private lemma v_10_22 : dFQ96 73 (42 : Fin 96) = 0 := row_73 10
private lemma v_10_23 : dFQ96 87 (42 : Fin 96) = 0 := row_87 10
private lemma v_10_24 : dFQ96 99 (42 : Fin 96) = 0 := row_99 10
private lemma v_10_25 : dFQ96 115 (42 : Fin 96) = 0 := row_115 10
private lemma v_10_26 : dFQ96 121 (42 : Fin 96) = 0 := row_121 10
private lemma v_10_27 : dFQ96 123 (42 : Fin 96) = 1 := row_123 10
private lemma v_10_28 : dFQ96 147 (42 : Fin 96) = 0 := row_147 10
private lemma v_10_29 : dFQ96 217 (42 : Fin 96) = -1 := row_217 10
private lemma v_10_30 : dFQ96 249 (42 : Fin 96) = 0 := row_249 10
-- 自由座標 11（96 維索引 44）
private lemma v_11_0 : dFQ96 3 (44 : Fin 96) = 0 := row_3 11
private lemma v_11_1 : dFQ96 5 (44 : Fin 96) = 0 := row_5 11
private lemma v_11_2 : dFQ96 7 (44 : Fin 96) = 0 := row_7 11
private lemma v_11_3 : dFQ96 9 (44 : Fin 96) = 0 := row_9 11
private lemma v_11_4 : dFQ96 11 (44 : Fin 96) = 0 := row_11 11
private lemma v_11_5 : dFQ96 13 (44 : Fin 96) = 0 := row_13 11
private lemma v_11_6 : dFQ96 15 (44 : Fin 96) = 0 := row_15 11
private lemma v_11_7 : dFQ96 17 (44 : Fin 96) = 0 := row_17 11
private lemma v_11_8 : dFQ96 19 (44 : Fin 96) = 0 := row_19 11
private lemma v_11_9 : dFQ96 23 (44 : Fin 96) = 0 := row_23 11
private lemma v_11_10 : dFQ96 25 (44 : Fin 96) = -1 := row_25 11
private lemma v_11_11 : dFQ96 27 (44 : Fin 96) = 0 := row_27 11
private lemma v_11_12 : dFQ96 33 (44 : Fin 96) = 1 := row_33 11
private lemma v_11_13 : dFQ96 39 (44 : Fin 96) = 0 := row_39 11
private lemma v_11_14 : dFQ96 43 (44 : Fin 96) = 0 := row_43 11
private lemma v_11_15 : dFQ96 49 (44 : Fin 96) = -1 := row_49 11
private lemma v_11_16 : dFQ96 51 (44 : Fin 96) = 0 := row_51 11
private lemma v_11_17 : dFQ96 55 (44 : Fin 96) = 0 := row_55 11
private lemma v_11_18 : dFQ96 57 (44 : Fin 96) = 0 := row_57 11
private lemma v_11_19 : dFQ96 59 (44 : Fin 96) = 1 := row_59 11
private lemma v_11_20 : dFQ96 65 (44 : Fin 96) = 1 := row_65 11
private lemma v_11_21 : dFQ96 67 (44 : Fin 96) = 1 := row_67 11
private lemma v_11_22 : dFQ96 73 (44 : Fin 96) = 0 := row_73 11
private lemma v_11_23 : dFQ96 87 (44 : Fin 96) = 0 := row_87 11
private lemma v_11_24 : dFQ96 99 (44 : Fin 96) = 0 := row_99 11
private lemma v_11_25 : dFQ96 115 (44 : Fin 96) = 0 := row_115 11
private lemma v_11_26 : dFQ96 121 (44 : Fin 96) = 0 := row_121 11
private lemma v_11_27 : dFQ96 123 (44 : Fin 96) = 0 := row_123 11
private lemma v_11_28 : dFQ96 147 (44 : Fin 96) = 0 := row_147 11
private lemma v_11_29 : dFQ96 217 (44 : Fin 96) = -1 := row_217 11
private lemma v_11_30 : dFQ96 249 (44 : Fin 96) = 0 := row_249 11
-- 自由座標 12（96 維索引 45）
private lemma v_12_0 : dFQ96 3 (45 : Fin 96) = 0 := row_3 12
private lemma v_12_1 : dFQ96 5 (45 : Fin 96) = 0 := row_5 12
private lemma v_12_2 : dFQ96 7 (45 : Fin 96) = 0 := row_7 12
private lemma v_12_3 : dFQ96 9 (45 : Fin 96) = 0 := row_9 12
private lemma v_12_4 : dFQ96 11 (45 : Fin 96) = 0 := row_11 12
private lemma v_12_5 : dFQ96 13 (45 : Fin 96) = 0 := row_13 12
private lemma v_12_6 : dFQ96 15 (45 : Fin 96) = 0 := row_15 12
private lemma v_12_7 : dFQ96 17 (45 : Fin 96) = 0 := row_17 12
private lemma v_12_8 : dFQ96 19 (45 : Fin 96) = 0 := row_19 12
private lemma v_12_9 : dFQ96 23 (45 : Fin 96) = 0 := row_23 12
private lemma v_12_10 : dFQ96 25 (45 : Fin 96) = 0 := row_25 12
private lemma v_12_11 : dFQ96 27 (45 : Fin 96) = 0 := row_27 12
private lemma v_12_12 : dFQ96 33 (45 : Fin 96) = 0 := row_33 12
private lemma v_12_13 : dFQ96 39 (45 : Fin 96) = 0 := row_39 12
private lemma v_12_14 : dFQ96 43 (45 : Fin 96) = 0 := row_43 12
private lemma v_12_15 : dFQ96 49 (45 : Fin 96) = 0 := row_49 12
private lemma v_12_16 : dFQ96 51 (45 : Fin 96) = 0 := row_51 12
private lemma v_12_17 : dFQ96 55 (45 : Fin 96) = 0 := row_55 12
private lemma v_12_18 : dFQ96 57 (45 : Fin 96) = -1 := row_57 12
private lemma v_12_19 : dFQ96 59 (45 : Fin 96) = 0 := row_59 12
private lemma v_12_20 : dFQ96 65 (45 : Fin 96) = 0 := row_65 12
private lemma v_12_21 : dFQ96 67 (45 : Fin 96) = 0 := row_67 12
private lemma v_12_22 : dFQ96 73 (45 : Fin 96) = 0 := row_73 12
private lemma v_12_23 : dFQ96 87 (45 : Fin 96) = 0 := row_87 12
private lemma v_12_24 : dFQ96 99 (45 : Fin 96) = 0 := row_99 12
private lemma v_12_25 : dFQ96 115 (45 : Fin 96) = 0 := row_115 12
private lemma v_12_26 : dFQ96 121 (45 : Fin 96) = -1 := row_121 12
private lemma v_12_27 : dFQ96 123 (45 : Fin 96) = 1 := row_123 12
private lemma v_12_28 : dFQ96 147 (45 : Fin 96) = 0 := row_147 12
private lemma v_12_29 : dFQ96 217 (45 : Fin 96) = 0 := row_217 12
private lemma v_12_30 : dFQ96 249 (45 : Fin 96) = -1 := row_249 12
-- 自由座標 13（96 維索引 46）
private lemma v_13_0 : dFQ96 3 (46 : Fin 96) = 0 := row_3 13
private lemma v_13_1 : dFQ96 5 (46 : Fin 96) = 0 := row_5 13
private lemma v_13_2 : dFQ96 7 (46 : Fin 96) = 0 := row_7 13
private lemma v_13_3 : dFQ96 9 (46 : Fin 96) = 0 := row_9 13
private lemma v_13_4 : dFQ96 11 (46 : Fin 96) = 0 := row_11 13
private lemma v_13_5 : dFQ96 13 (46 : Fin 96) = 0 := row_13 13
private lemma v_13_6 : dFQ96 15 (46 : Fin 96) = 0 := row_15 13
private lemma v_13_7 : dFQ96 17 (46 : Fin 96) = 0 := row_17 13
private lemma v_13_8 : dFQ96 19 (46 : Fin 96) = 0 := row_19 13
private lemma v_13_9 : dFQ96 23 (46 : Fin 96) = 0 := row_23 13
private lemma v_13_10 : dFQ96 25 (46 : Fin 96) = 0 := row_25 13
private lemma v_13_11 : dFQ96 27 (46 : Fin 96) = 0 := row_27 13
private lemma v_13_12 : dFQ96 33 (46 : Fin 96) = 0 := row_33 13
private lemma v_13_13 : dFQ96 39 (46 : Fin 96) = 0 := row_39 13
private lemma v_13_14 : dFQ96 43 (46 : Fin 96) = 0 := row_43 13
private lemma v_13_15 : dFQ96 49 (46 : Fin 96) = 0 := row_49 13
private lemma v_13_16 : dFQ96 51 (46 : Fin 96) = 0 := row_51 13
private lemma v_13_17 : dFQ96 55 (46 : Fin 96) = 0 := row_55 13
private lemma v_13_18 : dFQ96 57 (46 : Fin 96) = 0 := row_57 13
private lemma v_13_19 : dFQ96 59 (46 : Fin 96) = 0 := row_59 13
private lemma v_13_20 : dFQ96 65 (46 : Fin 96) = 0 := row_65 13
private lemma v_13_21 : dFQ96 67 (46 : Fin 96) = 0 := row_67 13
private lemma v_13_22 : dFQ96 73 (46 : Fin 96) = 0 := row_73 13
private lemma v_13_23 : dFQ96 87 (46 : Fin 96) = 0 := row_87 13
private lemma v_13_24 : dFQ96 99 (46 : Fin 96) = 0 := row_99 13
private lemma v_13_25 : dFQ96 115 (46 : Fin 96) = 0 := row_115 13
private lemma v_13_26 : dFQ96 121 (46 : Fin 96) = -1 := row_121 13
private lemma v_13_27 : dFQ96 123 (46 : Fin 96) = 0 := row_123 13
private lemma v_13_28 : dFQ96 147 (46 : Fin 96) = 0 := row_147 13
private lemma v_13_29 : dFQ96 217 (46 : Fin 96) = 0 := row_217 13
private lemma v_13_30 : dFQ96 249 (46 : Fin 96) = -1 := row_249 13
-- 自由座標 14（96 維索引 47）
private lemma v_14_0 : dFQ96 3 (47 : Fin 96) = 0 := row_3 14
private lemma v_14_1 : dFQ96 5 (47 : Fin 96) = 0 := row_5 14
private lemma v_14_2 : dFQ96 7 (47 : Fin 96) = 0 := row_7 14
private lemma v_14_3 : dFQ96 9 (47 : Fin 96) = 0 := row_9 14
private lemma v_14_4 : dFQ96 11 (47 : Fin 96) = 0 := row_11 14
private lemma v_14_5 : dFQ96 13 (47 : Fin 96) = 0 := row_13 14
private lemma v_14_6 : dFQ96 15 (47 : Fin 96) = 0 := row_15 14
private lemma v_14_7 : dFQ96 17 (47 : Fin 96) = 0 := row_17 14
private lemma v_14_8 : dFQ96 19 (47 : Fin 96) = 0 := row_19 14
private lemma v_14_9 : dFQ96 23 (47 : Fin 96) = 0 := row_23 14
private lemma v_14_10 : dFQ96 25 (47 : Fin 96) = 0 := row_25 14
private lemma v_14_11 : dFQ96 27 (47 : Fin 96) = 0 := row_27 14
private lemma v_14_12 : dFQ96 33 (47 : Fin 96) = 0 := row_33 14
private lemma v_14_13 : dFQ96 39 (47 : Fin 96) = 0 := row_39 14
private lemma v_14_14 : dFQ96 43 (47 : Fin 96) = 0 := row_43 14
private lemma v_14_15 : dFQ96 49 (47 : Fin 96) = 0 := row_49 14
private lemma v_14_16 : dFQ96 51 (47 : Fin 96) = 0 := row_51 14
private lemma v_14_17 : dFQ96 55 (47 : Fin 96) = 0 := row_55 14
private lemma v_14_18 : dFQ96 57 (47 : Fin 96) = 0 := row_57 14
private lemma v_14_19 : dFQ96 59 (47 : Fin 96) = 0 := row_59 14
private lemma v_14_20 : dFQ96 65 (47 : Fin 96) = 0 := row_65 14
private lemma v_14_21 : dFQ96 67 (47 : Fin 96) = 0 := row_67 14
private lemma v_14_22 : dFQ96 73 (47 : Fin 96) = 0 := row_73 14
private lemma v_14_23 : dFQ96 87 (47 : Fin 96) = 0 := row_87 14
private lemma v_14_24 : dFQ96 99 (47 : Fin 96) = 0 := row_99 14
private lemma v_14_25 : dFQ96 115 (47 : Fin 96) = 0 := row_115 14
private lemma v_14_26 : dFQ96 121 (47 : Fin 96) = 0 := row_121 14
private lemma v_14_27 : dFQ96 123 (47 : Fin 96) = 0 := row_123 14
private lemma v_14_28 : dFQ96 147 (47 : Fin 96) = 0 := row_147 14
private lemma v_14_29 : dFQ96 217 (47 : Fin 96) = 0 := row_217 14
private lemma v_14_30 : dFQ96 249 (47 : Fin 96) = -1 := row_249 14
-- 自由座標 15（96 維索引 56）
private lemma v_15_0 : dFQ96 3 (56 : Fin 96) = 0 := row_3 15
private lemma v_15_1 : dFQ96 5 (56 : Fin 96) = 0 := row_5 15
private lemma v_15_2 : dFQ96 7 (56 : Fin 96) = 0 := row_7 15
private lemma v_15_3 : dFQ96 9 (56 : Fin 96) = 0 := row_9 15
private lemma v_15_4 : dFQ96 11 (56 : Fin 96) = 0 := row_11 15
private lemma v_15_5 : dFQ96 13 (56 : Fin 96) = 0 := row_13 15
private lemma v_15_6 : dFQ96 15 (56 : Fin 96) = 0 := row_15 15
private lemma v_15_7 : dFQ96 17 (56 : Fin 96) = 0 := row_17 15
private lemma v_15_8 : dFQ96 19 (56 : Fin 96) = 0 := row_19 15
private lemma v_15_9 : dFQ96 23 (56 : Fin 96) = 0 := row_23 15
private lemma v_15_10 : dFQ96 25 (56 : Fin 96) = 0 := row_25 15
private lemma v_15_11 : dFQ96 27 (56 : Fin 96) = 0 := row_27 15
private lemma v_15_12 : dFQ96 33 (56 : Fin 96) = 0 := row_33 15
private lemma v_15_13 : dFQ96 39 (56 : Fin 96) = 0 := row_39 15
private lemma v_15_14 : dFQ96 43 (56 : Fin 96) = 0 := row_43 15
private lemma v_15_15 : dFQ96 49 (56 : Fin 96) = 0 := row_49 15
private lemma v_15_16 : dFQ96 51 (56 : Fin 96) = 0 := row_51 15
private lemma v_15_17 : dFQ96 55 (56 : Fin 96) = 0 := row_55 15
private lemma v_15_18 : dFQ96 57 (56 : Fin 96) = 0 := row_57 15
private lemma v_15_19 : dFQ96 59 (56 : Fin 96) = 0 := row_59 15
private lemma v_15_20 : dFQ96 65 (56 : Fin 96) = 0 := row_65 15
private lemma v_15_21 : dFQ96 67 (56 : Fin 96) = 0 := row_67 15
private lemma v_15_22 : dFQ96 73 (56 : Fin 96) = 0 := row_73 15
private lemma v_15_23 : dFQ96 87 (56 : Fin 96) = 1 := row_87 15
private lemma v_15_24 : dFQ96 99 (56 : Fin 96) = 0 := row_99 15
private lemma v_15_25 : dFQ96 115 (56 : Fin 96) = 0 := row_115 15
private lemma v_15_26 : dFQ96 121 (56 : Fin 96) = 0 := row_121 15
private lemma v_15_27 : dFQ96 123 (56 : Fin 96) = 0 := row_123 15
private lemma v_15_28 : dFQ96 147 (56 : Fin 96) = 0 := row_147 15
private lemma v_15_29 : dFQ96 217 (56 : Fin 96) = 0 := row_217 15
private lemma v_15_30 : dFQ96 249 (56 : Fin 96) = 0 := row_249 15
-- 自由座標 16（96 維索引 58）
private lemma v_16_0 : dFQ96 3 (58 : Fin 96) = 0 := row_3 16
private lemma v_16_1 : dFQ96 5 (58 : Fin 96) = 0 := row_5 16
private lemma v_16_2 : dFQ96 7 (58 : Fin 96) = 0 := row_7 16
private lemma v_16_3 : dFQ96 9 (58 : Fin 96) = 0 := row_9 16
private lemma v_16_4 : dFQ96 11 (58 : Fin 96) = 0 := row_11 16
private lemma v_16_5 : dFQ96 13 (58 : Fin 96) = 0 := row_13 16
private lemma v_16_6 : dFQ96 15 (58 : Fin 96) = 0 := row_15 16
private lemma v_16_7 : dFQ96 17 (58 : Fin 96) = 0 := row_17 16
private lemma v_16_8 : dFQ96 19 (58 : Fin 96) = 0 := row_19 16
private lemma v_16_9 : dFQ96 23 (58 : Fin 96) = 1 := row_23 16
private lemma v_16_10 : dFQ96 25 (58 : Fin 96) = 0 := row_25 16
private lemma v_16_11 : dFQ96 27 (58 : Fin 96) = 0 := row_27 16
private lemma v_16_12 : dFQ96 33 (58 : Fin 96) = 0 := row_33 16
private lemma v_16_13 : dFQ96 39 (58 : Fin 96) = 0 := row_39 16
private lemma v_16_14 : dFQ96 43 (58 : Fin 96) = 0 := row_43 16
private lemma v_16_15 : dFQ96 49 (58 : Fin 96) = 0 := row_49 16
private lemma v_16_16 : dFQ96 51 (58 : Fin 96) = 0 := row_51 16
private lemma v_16_17 : dFQ96 55 (58 : Fin 96) = 0 := row_55 16
private lemma v_16_18 : dFQ96 57 (58 : Fin 96) = 0 := row_57 16
private lemma v_16_19 : dFQ96 59 (58 : Fin 96) = 0 := row_59 16
private lemma v_16_20 : dFQ96 65 (58 : Fin 96) = 0 := row_65 16
private lemma v_16_21 : dFQ96 67 (58 : Fin 96) = -1 := row_67 16
private lemma v_16_22 : dFQ96 73 (58 : Fin 96) = 0 := row_73 16
private lemma v_16_23 : dFQ96 87 (58 : Fin 96) = 1 := row_87 16
private lemma v_16_24 : dFQ96 99 (58 : Fin 96) = -1 := row_99 16
private lemma v_16_25 : dFQ96 115 (58 : Fin 96) = 0 := row_115 16
private lemma v_16_26 : dFQ96 121 (58 : Fin 96) = 0 := row_121 16
private lemma v_16_27 : dFQ96 123 (58 : Fin 96) = 0 := row_123 16
private lemma v_16_28 : dFQ96 147 (58 : Fin 96) = 0 := row_147 16
private lemma v_16_29 : dFQ96 217 (58 : Fin 96) = 1 := row_217 16
private lemma v_16_30 : dFQ96 249 (58 : Fin 96) = 0 := row_249 16
-- 自由座標 17（96 維索引 61）
private lemma v_17_0 : dFQ96 3 (61 : Fin 96) = 0 := row_3 17
private lemma v_17_1 : dFQ96 5 (61 : Fin 96) = 0 := row_5 17
private lemma v_17_2 : dFQ96 7 (61 : Fin 96) = 0 := row_7 17
private lemma v_17_3 : dFQ96 9 (61 : Fin 96) = 0 := row_9 17
private lemma v_17_4 : dFQ96 11 (61 : Fin 96) = 0 := row_11 17
private lemma v_17_5 : dFQ96 13 (61 : Fin 96) = 0 := row_13 17
private lemma v_17_6 : dFQ96 15 (61 : Fin 96) = 0 := row_15 17
private lemma v_17_7 : dFQ96 17 (61 : Fin 96) = 0 := row_17 17
private lemma v_17_8 : dFQ96 19 (61 : Fin 96) = 0 := row_19 17
private lemma v_17_9 : dFQ96 23 (61 : Fin 96) = 1 := row_23 17
private lemma v_17_10 : dFQ96 25 (61 : Fin 96) = 0 := row_25 17
private lemma v_17_11 : dFQ96 27 (61 : Fin 96) = 0 := row_27 17
private lemma v_17_12 : dFQ96 33 (61 : Fin 96) = 0 := row_33 17
private lemma v_17_13 : dFQ96 39 (61 : Fin 96) = 0 := row_39 17
private lemma v_17_14 : dFQ96 43 (61 : Fin 96) = 0 := row_43 17
private lemma v_17_15 : dFQ96 49 (61 : Fin 96) = 0 := row_49 17
private lemma v_17_16 : dFQ96 51 (61 : Fin 96) = 0 := row_51 17
private lemma v_17_17 : dFQ96 55 (61 : Fin 96) = 0 := row_55 17
private lemma v_17_18 : dFQ96 57 (61 : Fin 96) = 0 := row_57 17
private lemma v_17_19 : dFQ96 59 (61 : Fin 96) = 0 := row_59 17
private lemma v_17_20 : dFQ96 65 (61 : Fin 96) = 0 := row_65 17
private lemma v_17_21 : dFQ96 67 (61 : Fin 96) = 0 := row_67 17
private lemma v_17_22 : dFQ96 73 (61 : Fin 96) = 0 := row_73 17
private lemma v_17_23 : dFQ96 87 (61 : Fin 96) = 0 := row_87 17
private lemma v_17_24 : dFQ96 99 (61 : Fin 96) = -1 := row_99 17
private lemma v_17_25 : dFQ96 115 (61 : Fin 96) = 0 := row_115 17
private lemma v_17_26 : dFQ96 121 (61 : Fin 96) = 0 := row_121 17
private lemma v_17_27 : dFQ96 123 (61 : Fin 96) = 0 := row_123 17
private lemma v_17_28 : dFQ96 147 (61 : Fin 96) = -1 := row_147 17
private lemma v_17_29 : dFQ96 217 (61 : Fin 96) = 1 := row_217 17
private lemma v_17_30 : dFQ96 249 (61 : Fin 96) = 0 := row_249 17
-- 自由座標 18（96 維索引 63）
private lemma v_18_0 : dFQ96 3 (63 : Fin 96) = 0 := row_3 18
private lemma v_18_1 : dFQ96 5 (63 : Fin 96) = 0 := row_5 18
private lemma v_18_2 : dFQ96 7 (63 : Fin 96) = 0 := row_7 18
private lemma v_18_3 : dFQ96 9 (63 : Fin 96) = 0 := row_9 18
private lemma v_18_4 : dFQ96 11 (63 : Fin 96) = 0 := row_11 18
private lemma v_18_5 : dFQ96 13 (63 : Fin 96) = 0 := row_13 18
private lemma v_18_6 : dFQ96 15 (63 : Fin 96) = 0 := row_15 18
private lemma v_18_7 : dFQ96 17 (63 : Fin 96) = 0 := row_17 18
private lemma v_18_8 : dFQ96 19 (63 : Fin 96) = 0 := row_19 18
private lemma v_18_9 : dFQ96 23 (63 : Fin 96) = 0 := row_23 18
private lemma v_18_10 : dFQ96 25 (63 : Fin 96) = 0 := row_25 18
private lemma v_18_11 : dFQ96 27 (63 : Fin 96) = 0 := row_27 18
private lemma v_18_12 : dFQ96 33 (63 : Fin 96) = 0 := row_33 18
private lemma v_18_13 : dFQ96 39 (63 : Fin 96) = 0 := row_39 18
private lemma v_18_14 : dFQ96 43 (63 : Fin 96) = 0 := row_43 18
private lemma v_18_15 : dFQ96 49 (63 : Fin 96) = 0 := row_49 18
private lemma v_18_16 : dFQ96 51 (63 : Fin 96) = 0 := row_51 18
private lemma v_18_17 : dFQ96 55 (63 : Fin 96) = 1 := row_55 18
private lemma v_18_18 : dFQ96 57 (63 : Fin 96) = 0 := row_57 18
private lemma v_18_19 : dFQ96 59 (63 : Fin 96) = 0 := row_59 18
private lemma v_18_20 : dFQ96 65 (63 : Fin 96) = 0 := row_65 18
private lemma v_18_21 : dFQ96 67 (63 : Fin 96) = 0 := row_67 18
private lemma v_18_22 : dFQ96 73 (63 : Fin 96) = 0 := row_73 18
private lemma v_18_23 : dFQ96 87 (63 : Fin 96) = 0 := row_87 18
private lemma v_18_24 : dFQ96 99 (63 : Fin 96) = 0 := row_99 18
private lemma v_18_25 : dFQ96 115 (63 : Fin 96) = 0 := row_115 18
private lemma v_18_26 : dFQ96 121 (63 : Fin 96) = 0 := row_121 18
private lemma v_18_27 : dFQ96 123 (63 : Fin 96) = 0 := row_123 18
private lemma v_18_28 : dFQ96 147 (63 : Fin 96) = 0 := row_147 18
private lemma v_18_29 : dFQ96 217 (63 : Fin 96) = 1 := row_217 18
private lemma v_18_30 : dFQ96 249 (63 : Fin 96) = 0 := row_249 18
-- 自由座標 19（96 維索引 74）
private lemma v_19_0 : dFQ96 3 (74 : Fin 96) = 0 := row_3 19
private lemma v_19_1 : dFQ96 5 (74 : Fin 96) = 0 := row_5 19
private lemma v_19_2 : dFQ96 7 (74 : Fin 96) = 0 := row_7 19
private lemma v_19_3 : dFQ96 9 (74 : Fin 96) = 0 := row_9 19
private lemma v_19_4 : dFQ96 11 (74 : Fin 96) = 0 := row_11 19
private lemma v_19_5 : dFQ96 13 (74 : Fin 96) = 0 := row_13 19
private lemma v_19_6 : dFQ96 15 (74 : Fin 96) = 0 := row_15 19
private lemma v_19_7 : dFQ96 17 (74 : Fin 96) = 0 := row_17 19
private lemma v_19_8 : dFQ96 19 (74 : Fin 96) = 0 := row_19 19
private lemma v_19_9 : dFQ96 23 (74 : Fin 96) = 1 := row_23 19
private lemma v_19_10 : dFQ96 25 (74 : Fin 96) = 0 := row_25 19
private lemma v_19_11 : dFQ96 27 (74 : Fin 96) = 0 := row_27 19
private lemma v_19_12 : dFQ96 33 (74 : Fin 96) = 0 := row_33 19
private lemma v_19_13 : dFQ96 39 (74 : Fin 96) = 0 := row_39 19
private lemma v_19_14 : dFQ96 43 (74 : Fin 96) = 0 := row_43 19
private lemma v_19_15 : dFQ96 49 (74 : Fin 96) = 0 := row_49 19
private lemma v_19_16 : dFQ96 51 (74 : Fin 96) = 0 := row_51 19
private lemma v_19_17 : dFQ96 55 (74 : Fin 96) = 0 := row_55 19
private lemma v_19_18 : dFQ96 57 (74 : Fin 96) = 0 := row_57 19
private lemma v_19_19 : dFQ96 59 (74 : Fin 96) = 0 := row_59 19
private lemma v_19_20 : dFQ96 65 (74 : Fin 96) = 0 := row_65 19
private lemma v_19_21 : dFQ96 67 (74 : Fin 96) = -1 := row_67 19
private lemma v_19_22 : dFQ96 73 (74 : Fin 96) = 0 := row_73 19
private lemma v_19_23 : dFQ96 87 (74 : Fin 96) = 1 := row_87 19
private lemma v_19_24 : dFQ96 99 (74 : Fin 96) = 0 := row_99 19
private lemma v_19_25 : dFQ96 115 (74 : Fin 96) = 0 := row_115 19
private lemma v_19_26 : dFQ96 121 (74 : Fin 96) = 0 := row_121 19
private lemma v_19_27 : dFQ96 123 (74 : Fin 96) = 0 := row_123 19
private lemma v_19_28 : dFQ96 147 (74 : Fin 96) = -1 := row_147 19
private lemma v_19_29 : dFQ96 217 (74 : Fin 96) = 1 := row_217 19
private lemma v_19_30 : dFQ96 249 (74 : Fin 96) = 0 := row_249 19
-- 自由座標 20（96 維索引 77）
private lemma v_20_0 : dFQ96 3 (77 : Fin 96) = 0 := row_3 20
private lemma v_20_1 : dFQ96 5 (77 : Fin 96) = 0 := row_5 20
private lemma v_20_2 : dFQ96 7 (77 : Fin 96) = 1 := row_7 20
private lemma v_20_3 : dFQ96 9 (77 : Fin 96) = 0 := row_9 20
private lemma v_20_4 : dFQ96 11 (77 : Fin 96) = -1 := row_11 20
private lemma v_20_5 : dFQ96 13 (77 : Fin 96) = 0 := row_13 20
private lemma v_20_6 : dFQ96 15 (77 : Fin 96) = 1 := row_15 20
private lemma v_20_7 : dFQ96 17 (77 : Fin 96) = 0 := row_17 20
private lemma v_20_8 : dFQ96 19 (77 : Fin 96) = 0 := row_19 20
private lemma v_20_9 : dFQ96 23 (77 : Fin 96) = -1 := row_23 20
private lemma v_20_10 : dFQ96 25 (77 : Fin 96) = 0 := row_25 20
private lemma v_20_11 : dFQ96 27 (77 : Fin 96) = -1 := row_27 20
private lemma v_20_12 : dFQ96 33 (77 : Fin 96) = 0 := row_33 20
private lemma v_20_13 : dFQ96 39 (77 : Fin 96) = 1 := row_39 20
private lemma v_20_14 : dFQ96 43 (77 : Fin 96) = -1 := row_43 20
private lemma v_20_15 : dFQ96 49 (77 : Fin 96) = 0 := row_49 20
private lemma v_20_16 : dFQ96 51 (77 : Fin 96) = 0 := row_51 20
private lemma v_20_17 : dFQ96 55 (77 : Fin 96) = -1 := row_55 20
private lemma v_20_18 : dFQ96 57 (77 : Fin 96) = 1 := row_57 20
private lemma v_20_19 : dFQ96 59 (77 : Fin 96) = -1 := row_59 20
private lemma v_20_20 : dFQ96 65 (77 : Fin 96) = 0 := row_65 20
private lemma v_20_21 : dFQ96 67 (77 : Fin 96) = 0 := row_67 20
private lemma v_20_22 : dFQ96 73 (77 : Fin 96) = 1 := row_73 20
private lemma v_20_23 : dFQ96 87 (77 : Fin 96) = -1 := row_87 20
private lemma v_20_24 : dFQ96 99 (77 : Fin 96) = 0 := row_99 20
private lemma v_20_25 : dFQ96 115 (77 : Fin 96) = 1 := row_115 20
private lemma v_20_26 : dFQ96 121 (77 : Fin 96) = 2 := row_121 20
private lemma v_20_27 : dFQ96 123 (77 : Fin 96) = -1 := row_123 20
private lemma v_20_28 : dFQ96 147 (77 : Fin 96) = 1 := row_147 20
private lemma v_20_29 : dFQ96 217 (77 : Fin 96) = 0 := row_217 20
private lemma v_20_30 : dFQ96 249 (77 : Fin 96) = 2 := row_249 20
-- 自由座標 21（96 維索引 78）
private lemma v_21_0 : dFQ96 3 (78 : Fin 96) = 0 := row_3 21
private lemma v_21_1 : dFQ96 5 (78 : Fin 96) = 0 := row_5 21
private lemma v_21_2 : dFQ96 7 (78 : Fin 96) = 0 := row_7 21
private lemma v_21_3 : dFQ96 9 (78 : Fin 96) = 0 := row_9 21
private lemma v_21_4 : dFQ96 11 (78 : Fin 96) = 0 := row_11 21
private lemma v_21_5 : dFQ96 13 (78 : Fin 96) = 0 := row_13 21
private lemma v_21_6 : dFQ96 15 (78 : Fin 96) = 0 := row_15 21
private lemma v_21_7 : dFQ96 17 (78 : Fin 96) = 0 := row_17 21
private lemma v_21_8 : dFQ96 19 (78 : Fin 96) = -1 := row_19 21
private lemma v_21_9 : dFQ96 23 (78 : Fin 96) = 0 := row_23 21
private lemma v_21_10 : dFQ96 25 (78 : Fin 96) = 1 := row_25 21
private lemma v_21_11 : dFQ96 27 (78 : Fin 96) = 0 := row_27 21
private lemma v_21_12 : dFQ96 33 (78 : Fin 96) = 0 := row_33 21
private lemma v_21_13 : dFQ96 39 (78 : Fin 96) = -1 := row_39 21
private lemma v_21_14 : dFQ96 43 (78 : Fin 96) = 0 := row_43 21
private lemma v_21_15 : dFQ96 49 (78 : Fin 96) = 0 := row_49 21
private lemma v_21_16 : dFQ96 51 (78 : Fin 96) = 1 := row_51 21
private lemma v_21_17 : dFQ96 55 (78 : Fin 96) = 2 := row_55 21
private lemma v_21_18 : dFQ96 57 (78 : Fin 96) = 0 := row_57 21
private lemma v_21_19 : dFQ96 59 (78 : Fin 96) = 0 := row_59 21
private lemma v_21_20 : dFQ96 65 (78 : Fin 96) = 0 := row_65 21
private lemma v_21_21 : dFQ96 67 (78 : Fin 96) = 0 := row_67 21
private lemma v_21_22 : dFQ96 73 (78 : Fin 96) = 0 := row_73 21
private lemma v_21_23 : dFQ96 87 (78 : Fin 96) = 0 := row_87 21
private lemma v_21_24 : dFQ96 99 (78 : Fin 96) = 0 := row_99 21
private lemma v_21_25 : dFQ96 115 (78 : Fin 96) = 0 := row_115 21
private lemma v_21_26 : dFQ96 121 (78 : Fin 96) = 0 := row_121 21
private lemma v_21_27 : dFQ96 123 (78 : Fin 96) = 0 := row_123 21
private lemma v_21_28 : dFQ96 147 (78 : Fin 96) = -1 := row_147 21
private lemma v_21_29 : dFQ96 217 (78 : Fin 96) = 1 := row_217 21
private lemma v_21_30 : dFQ96 249 (78 : Fin 96) = 0 := row_249 21
-- 自由座標 22（96 維索引 79）
private lemma v_22_0 : dFQ96 3 (79 : Fin 96) = 0 := row_3 22
private lemma v_22_1 : dFQ96 5 (79 : Fin 96) = 0 := row_5 22
private lemma v_22_2 : dFQ96 7 (79 : Fin 96) = 0 := row_7 22
private lemma v_22_3 : dFQ96 9 (79 : Fin 96) = 0 := row_9 22
private lemma v_22_4 : dFQ96 11 (79 : Fin 96) = 0 := row_11 22
private lemma v_22_5 : dFQ96 13 (79 : Fin 96) = 0 := row_13 22
private lemma v_22_6 : dFQ96 15 (79 : Fin 96) = 0 := row_15 22
private lemma v_22_7 : dFQ96 17 (79 : Fin 96) = 0 := row_17 22
private lemma v_22_8 : dFQ96 19 (79 : Fin 96) = 0 := row_19 22
private lemma v_22_9 : dFQ96 23 (79 : Fin 96) = 0 := row_23 22
private lemma v_22_10 : dFQ96 25 (79 : Fin 96) = 0 := row_25 22
private lemma v_22_11 : dFQ96 27 (79 : Fin 96) = 0 := row_27 22
private lemma v_22_12 : dFQ96 33 (79 : Fin 96) = 0 := row_33 22
private lemma v_22_13 : dFQ96 39 (79 : Fin 96) = 0 := row_39 22
private lemma v_22_14 : dFQ96 43 (79 : Fin 96) = 0 := row_43 22
private lemma v_22_15 : dFQ96 49 (79 : Fin 96) = 0 := row_49 22
private lemma v_22_16 : dFQ96 51 (79 : Fin 96) = -1 := row_51 22
private lemma v_22_17 : dFQ96 55 (79 : Fin 96) = 0 := row_55 22
private lemma v_22_18 : dFQ96 57 (79 : Fin 96) = 0 := row_57 22
private lemma v_22_19 : dFQ96 59 (79 : Fin 96) = 0 := row_59 22
private lemma v_22_20 : dFQ96 65 (79 : Fin 96) = 0 := row_65 22
private lemma v_22_21 : dFQ96 67 (79 : Fin 96) = 0 := row_67 22
private lemma v_22_22 : dFQ96 73 (79 : Fin 96) = 0 := row_73 22
private lemma v_22_23 : dFQ96 87 (79 : Fin 96) = 0 := row_87 22
private lemma v_22_24 : dFQ96 99 (79 : Fin 96) = 0 := row_99 22
private lemma v_22_25 : dFQ96 115 (79 : Fin 96) = -1 := row_115 22
private lemma v_22_26 : dFQ96 121 (79 : Fin 96) = 0 := row_121 22
private lemma v_22_27 : dFQ96 123 (79 : Fin 96) = 0 := row_123 22
private lemma v_22_28 : dFQ96 147 (79 : Fin 96) = 0 := row_147 22
private lemma v_22_29 : dFQ96 217 (79 : Fin 96) = 0 := row_217 22
private lemma v_22_30 : dFQ96 249 (79 : Fin 96) = 0 := row_249 22
-- 自由座標 23（96 維索引 80）
private lemma v_23_0 : dFQ96 3 (80 : Fin 96) = 0 := row_3 23
private lemma v_23_1 : dFQ96 5 (80 : Fin 96) = 0 := row_5 23
private lemma v_23_2 : dFQ96 7 (80 : Fin 96) = 0 := row_7 23
private lemma v_23_3 : dFQ96 9 (80 : Fin 96) = 0 := row_9 23
private lemma v_23_4 : dFQ96 11 (80 : Fin 96) = 0 := row_11 23
private lemma v_23_5 : dFQ96 13 (80 : Fin 96) = -1 := row_13 23
private lemma v_23_6 : dFQ96 15 (80 : Fin 96) = 0 := row_15 23
private lemma v_23_7 : dFQ96 17 (80 : Fin 96) = 1 := row_17 23
private lemma v_23_8 : dFQ96 19 (80 : Fin 96) = 1 := row_19 23
private lemma v_23_9 : dFQ96 23 (80 : Fin 96) = 0 := row_23 23
private lemma v_23_10 : dFQ96 25 (80 : Fin 96) = 0 := row_25 23
private lemma v_23_11 : dFQ96 27 (80 : Fin 96) = 0 := row_27 23
private lemma v_23_12 : dFQ96 33 (80 : Fin 96) = 0 := row_33 23
private lemma v_23_13 : dFQ96 39 (80 : Fin 96) = 0 := row_39 23
private lemma v_23_14 : dFQ96 43 (80 : Fin 96) = 0 := row_43 23
private lemma v_23_15 : dFQ96 49 (80 : Fin 96) = 0 := row_49 23
private lemma v_23_16 : dFQ96 51 (80 : Fin 96) = 1 := row_51 23
private lemma v_23_17 : dFQ96 55 (80 : Fin 96) = 0 := row_55 23
private lemma v_23_18 : dFQ96 57 (80 : Fin 96) = 0 := row_57 23
private lemma v_23_19 : dFQ96 59 (80 : Fin 96) = 0 := row_59 23
private lemma v_23_20 : dFQ96 65 (80 : Fin 96) = 0 := row_65 23
private lemma v_23_21 : dFQ96 67 (80 : Fin 96) = 0 := row_67 23
private lemma v_23_22 : dFQ96 73 (80 : Fin 96) = 0 := row_73 23
private lemma v_23_23 : dFQ96 87 (80 : Fin 96) = 0 := row_87 23
private lemma v_23_24 : dFQ96 99 (80 : Fin 96) = 0 := row_99 23
private lemma v_23_25 : dFQ96 115 (80 : Fin 96) = 1 := row_115 23
private lemma v_23_26 : dFQ96 121 (80 : Fin 96) = 0 := row_121 23
private lemma v_23_27 : dFQ96 123 (80 : Fin 96) = 0 := row_123 23
private lemma v_23_28 : dFQ96 147 (80 : Fin 96) = 1 := row_147 23
private lemma v_23_29 : dFQ96 217 (80 : Fin 96) = 0 := row_217 23
private lemma v_23_30 : dFQ96 249 (80 : Fin 96) = 0 := row_249 23
-- 自由座標 24（96 維索引 88）
private lemma v_24_0 : dFQ96 3 (88 : Fin 96) = 0 := row_3 24
private lemma v_24_1 : dFQ96 5 (88 : Fin 96) = 0 := row_5 24
private lemma v_24_2 : dFQ96 7 (88 : Fin 96) = 1 := row_7 24
private lemma v_24_3 : dFQ96 9 (88 : Fin 96) = 0 := row_9 24
private lemma v_24_4 : dFQ96 11 (88 : Fin 96) = -1 := row_11 24
private lemma v_24_5 : dFQ96 13 (88 : Fin 96) = 0 := row_13 24
private lemma v_24_6 : dFQ96 15 (88 : Fin 96) = 1 := row_15 24
private lemma v_24_7 : dFQ96 17 (88 : Fin 96) = 0 := row_17 24
private lemma v_24_8 : dFQ96 19 (88 : Fin 96) = 0 := row_19 24
private lemma v_24_9 : dFQ96 23 (88 : Fin 96) = -1 := row_23 24
private lemma v_24_10 : dFQ96 25 (88 : Fin 96) = 0 := row_25 24
private lemma v_24_11 : dFQ96 27 (88 : Fin 96) = 0 := row_27 24
private lemma v_24_12 : dFQ96 33 (88 : Fin 96) = 0 := row_33 24
private lemma v_24_13 : dFQ96 39 (88 : Fin 96) = 0 := row_39 24
private lemma v_24_14 : dFQ96 43 (88 : Fin 96) = -2 := row_43 24
private lemma v_24_15 : dFQ96 49 (88 : Fin 96) = 0 := row_49 24
private lemma v_24_16 : dFQ96 51 (88 : Fin 96) = 0 := row_51 24
private lemma v_24_17 : dFQ96 55 (88 : Fin 96) = 0 := row_55 24
private lemma v_24_18 : dFQ96 57 (88 : Fin 96) = 2 := row_57 24
private lemma v_24_19 : dFQ96 59 (88 : Fin 96) = 0 := row_59 24
private lemma v_24_20 : dFQ96 65 (88 : Fin 96) = 0 := row_65 24
private lemma v_24_21 : dFQ96 67 (88 : Fin 96) = 0 := row_67 24
private lemma v_24_22 : dFQ96 73 (88 : Fin 96) = 0 := row_73 24
private lemma v_24_23 : dFQ96 87 (88 : Fin 96) = -2 := row_87 24
private lemma v_24_24 : dFQ96 99 (88 : Fin 96) = 0 := row_99 24
private lemma v_24_25 : dFQ96 115 (88 : Fin 96) = 2 := row_115 24
private lemma v_24_26 : dFQ96 121 (88 : Fin 96) = 1 := row_121 24
private lemma v_24_27 : dFQ96 123 (88 : Fin 96) = 0 := row_123 24
private lemma v_24_28 : dFQ96 147 (88 : Fin 96) = 0 := row_147 24
private lemma v_24_29 : dFQ96 217 (88 : Fin 96) = 0 := row_217 24
private lemma v_24_30 : dFQ96 249 (88 : Fin 96) = 1 := row_249 24
-- 自由座標 25（96 維索引 89）
private lemma v_25_0 : dFQ96 3 (89 : Fin 96) = 0 := row_3 25
private lemma v_25_1 : dFQ96 5 (89 : Fin 96) = 0 := row_5 25
private lemma v_25_2 : dFQ96 7 (89 : Fin 96) = 0 := row_7 25
private lemma v_25_3 : dFQ96 9 (89 : Fin 96) = 0 := row_9 25
private lemma v_25_4 : dFQ96 11 (89 : Fin 96) = 0 := row_11 25
private lemma v_25_5 : dFQ96 13 (89 : Fin 96) = 0 := row_13 25
private lemma v_25_6 : dFQ96 15 (89 : Fin 96) = 0 := row_15 25
private lemma v_25_7 : dFQ96 17 (89 : Fin 96) = 0 := row_17 25
private lemma v_25_8 : dFQ96 19 (89 : Fin 96) = 0 := row_19 25
private lemma v_25_9 : dFQ96 23 (89 : Fin 96) = 0 := row_23 25
private lemma v_25_10 : dFQ96 25 (89 : Fin 96) = 0 := row_25 25
private lemma v_25_11 : dFQ96 27 (89 : Fin 96) = -1 := row_27 25
private lemma v_25_12 : dFQ96 33 (89 : Fin 96) = 0 := row_33 25
private lemma v_25_13 : dFQ96 39 (89 : Fin 96) = 1 := row_39 25
private lemma v_25_14 : dFQ96 43 (89 : Fin 96) = 0 := row_43 25
private lemma v_25_15 : dFQ96 49 (89 : Fin 96) = 0 := row_49 25
private lemma v_25_16 : dFQ96 51 (89 : Fin 96) = 0 := row_51 25
private lemma v_25_17 : dFQ96 55 (89 : Fin 96) = -1 := row_55 25
private lemma v_25_18 : dFQ96 57 (89 : Fin 96) = 0 := row_57 25
private lemma v_25_19 : dFQ96 59 (89 : Fin 96) = -1 := row_59 25
private lemma v_25_20 : dFQ96 65 (89 : Fin 96) = 0 := row_65 25
private lemma v_25_21 : dFQ96 67 (89 : Fin 96) = 0 := row_67 25
private lemma v_25_22 : dFQ96 73 (89 : Fin 96) = 1 := row_73 25
private lemma v_25_23 : dFQ96 87 (89 : Fin 96) = 0 := row_87 25
private lemma v_25_24 : dFQ96 99 (89 : Fin 96) = 0 := row_99 25
private lemma v_25_25 : dFQ96 115 (89 : Fin 96) = 0 := row_115 25
private lemma v_25_26 : dFQ96 121 (89 : Fin 96) = 1 := row_121 25
private lemma v_25_27 : dFQ96 123 (89 : Fin 96) = -1 := row_123 25
private lemma v_25_28 : dFQ96 147 (89 : Fin 96) = 1 := row_147 25
private lemma v_25_29 : dFQ96 217 (89 : Fin 96) = 0 := row_217 25
private lemma v_25_30 : dFQ96 249 (89 : Fin 96) = 1 := row_249 25
-- 自由座標 26（96 維索引 90）
private lemma v_26_0 : dFQ96 3 (90 : Fin 96) = -1 := row_3 26
private lemma v_26_1 : dFQ96 5 (90 : Fin 96) = 0 := row_5 26
private lemma v_26_2 : dFQ96 7 (90 : Fin 96) = 1 := row_7 26
private lemma v_26_3 : dFQ96 9 (90 : Fin 96) = 0 := row_9 26
private lemma v_26_4 : dFQ96 11 (90 : Fin 96) = -1 := row_11 26
private lemma v_26_5 : dFQ96 13 (90 : Fin 96) = -1 := row_13 26
private lemma v_26_6 : dFQ96 15 (90 : Fin 96) = 0 := row_15 26
private lemma v_26_7 : dFQ96 17 (90 : Fin 96) = 1 := row_17 26
private lemma v_26_8 : dFQ96 19 (90 : Fin 96) = -1 := row_19 26
private lemma v_26_9 : dFQ96 23 (90 : Fin 96) = 1 := row_23 26
private lemma v_26_10 : dFQ96 25 (90 : Fin 96) = 1 := row_25 26
private lemma v_26_11 : dFQ96 27 (90 : Fin 96) = -2 := row_27 26
private lemma v_26_12 : dFQ96 33 (90 : Fin 96) = 0 := row_33 26
private lemma v_26_13 : dFQ96 39 (90 : Fin 96) = 1 := row_39 26
private lemma v_26_14 : dFQ96 43 (90 : Fin 96) = -1 := row_43 26
private lemma v_26_15 : dFQ96 49 (90 : Fin 96) = 0 := row_49 26
private lemma v_26_16 : dFQ96 51 (90 : Fin 96) = 0 := row_51 26
private lemma v_26_17 : dFQ96 55 (90 : Fin 96) = 0 := row_55 26
private lemma v_26_18 : dFQ96 57 (90 : Fin 96) = 1 := row_57 26
private lemma v_26_19 : dFQ96 59 (90 : Fin 96) = -1 := row_59 26
private lemma v_26_20 : dFQ96 65 (90 : Fin 96) = 0 := row_65 26
private lemma v_26_21 : dFQ96 67 (90 : Fin 96) = -1 := row_67 26
private lemma v_26_22 : dFQ96 73 (90 : Fin 96) = 1 := row_73 26
private lemma v_26_23 : dFQ96 87 (90 : Fin 96) = 1 := row_87 26
private lemma v_26_24 : dFQ96 99 (90 : Fin 96) = -1 := row_99 26
private lemma v_26_25 : dFQ96 115 (90 : Fin 96) = -1 := row_115 26
private lemma v_26_26 : dFQ96 121 (90 : Fin 96) = 2 := row_121 26
private lemma v_26_27 : dFQ96 123 (90 : Fin 96) = -1 := row_123 26
private lemma v_26_28 : dFQ96 147 (90 : Fin 96) = 0 := row_147 26
private lemma v_26_29 : dFQ96 217 (90 : Fin 96) = 1 := row_217 26
private lemma v_26_30 : dFQ96 249 (90 : Fin 96) = 1 := row_249 26
-- 自由座標 27（96 維索引 92）
private lemma v_27_0 : dFQ96 3 (92 : Fin 96) = 0 := row_3 27
private lemma v_27_1 : dFQ96 5 (92 : Fin 96) = 0 := row_5 27
private lemma v_27_2 : dFQ96 7 (92 : Fin 96) = 0 := row_7 27
private lemma v_27_3 : dFQ96 9 (92 : Fin 96) = 0 := row_9 27
private lemma v_27_4 : dFQ96 11 (92 : Fin 96) = 0 := row_11 27
private lemma v_27_5 : dFQ96 13 (92 : Fin 96) = 0 := row_13 27
private lemma v_27_6 : dFQ96 15 (92 : Fin 96) = 0 := row_15 27
private lemma v_27_7 : dFQ96 17 (92 : Fin 96) = 0 := row_17 27
private lemma v_27_8 : dFQ96 19 (92 : Fin 96) = 0 := row_19 27
private lemma v_27_9 : dFQ96 23 (92 : Fin 96) = 0 := row_23 27
private lemma v_27_10 : dFQ96 25 (92 : Fin 96) = 0 := row_25 27
private lemma v_27_11 : dFQ96 27 (92 : Fin 96) = 0 := row_27 27
private lemma v_27_12 : dFQ96 33 (92 : Fin 96) = 0 := row_33 27
private lemma v_27_13 : dFQ96 39 (92 : Fin 96) = 0 := row_39 27
private lemma v_27_14 : dFQ96 43 (92 : Fin 96) = 0 := row_43 27
private lemma v_27_15 : dFQ96 49 (92 : Fin 96) = 0 := row_49 27
private lemma v_27_16 : dFQ96 51 (92 : Fin 96) = -1 := row_51 27
private lemma v_27_17 : dFQ96 55 (92 : Fin 96) = 0 := row_55 27
private lemma v_27_18 : dFQ96 57 (92 : Fin 96) = 0 := row_57 27
private lemma v_27_19 : dFQ96 59 (92 : Fin 96) = 0 := row_59 27
private lemma v_27_20 : dFQ96 65 (92 : Fin 96) = 0 := row_65 27
private lemma v_27_21 : dFQ96 67 (92 : Fin 96) = 0 := row_67 27
private lemma v_27_22 : dFQ96 73 (92 : Fin 96) = 0 := row_73 27
private lemma v_27_23 : dFQ96 87 (92 : Fin 96) = 0 := row_87 27
private lemma v_27_24 : dFQ96 99 (92 : Fin 96) = -1 := row_99 27
private lemma v_27_25 : dFQ96 115 (92 : Fin 96) = 0 := row_115 27
private lemma v_27_26 : dFQ96 121 (92 : Fin 96) = 0 := row_121 27
private lemma v_27_27 : dFQ96 123 (92 : Fin 96) = 0 := row_123 27
private lemma v_27_28 : dFQ96 147 (92 : Fin 96) = 0 := row_147 27
private lemma v_27_29 : dFQ96 217 (92 : Fin 96) = 0 := row_217 27
private lemma v_27_30 : dFQ96 249 (92 : Fin 96) = 0 := row_249 27
-- 自由座標 28（96 維索引 93）
private lemma v_28_0 : dFQ96 3 (93 : Fin 96) = 0 := row_3 28
private lemma v_28_1 : dFQ96 5 (93 : Fin 96) = 0 := row_5 28
private lemma v_28_2 : dFQ96 7 (93 : Fin 96) = 0 := row_7 28
private lemma v_28_3 : dFQ96 9 (93 : Fin 96) = 0 := row_9 28
private lemma v_28_4 : dFQ96 11 (93 : Fin 96) = 0 := row_11 28
private lemma v_28_5 : dFQ96 13 (93 : Fin 96) = 0 := row_13 28
private lemma v_28_6 : dFQ96 15 (93 : Fin 96) = 0 := row_15 28
private lemma v_28_7 : dFQ96 17 (93 : Fin 96) = 0 := row_17 28
private lemma v_28_8 : dFQ96 19 (93 : Fin 96) = 0 := row_19 28
private lemma v_28_9 : dFQ96 23 (93 : Fin 96) = 0 := row_23 28
private lemma v_28_10 : dFQ96 25 (93 : Fin 96) = 0 := row_25 28
private lemma v_28_11 : dFQ96 27 (93 : Fin 96) = 0 := row_27 28
private lemma v_28_12 : dFQ96 33 (93 : Fin 96) = 0 := row_33 28
private lemma v_28_13 : dFQ96 39 (93 : Fin 96) = 0 := row_39 28
private lemma v_28_14 : dFQ96 43 (93 : Fin 96) = 0 := row_43 28
private lemma v_28_15 : dFQ96 49 (93 : Fin 96) = 0 := row_49 28
private lemma v_28_16 : dFQ96 51 (93 : Fin 96) = 0 := row_51 28
private lemma v_28_17 : dFQ96 55 (93 : Fin 96) = 0 := row_55 28
private lemma v_28_18 : dFQ96 57 (93 : Fin 96) = 0 := row_57 28
private lemma v_28_19 : dFQ96 59 (93 : Fin 96) = 0 := row_59 28
private lemma v_28_20 : dFQ96 65 (93 : Fin 96) = 0 := row_65 28
private lemma v_28_21 : dFQ96 67 (93 : Fin 96) = 0 := row_67 28
private lemma v_28_22 : dFQ96 73 (93 : Fin 96) = 0 := row_73 28
private lemma v_28_23 : dFQ96 87 (93 : Fin 96) = 0 := row_87 28
private lemma v_28_24 : dFQ96 99 (93 : Fin 96) = 0 := row_99 28
private lemma v_28_25 : dFQ96 115 (93 : Fin 96) = -1 := row_115 28
private lemma v_28_26 : dFQ96 121 (93 : Fin 96) = 0 := row_121 28
private lemma v_28_27 : dFQ96 123 (93 : Fin 96) = 0 := row_123 28
private lemma v_28_28 : dFQ96 147 (93 : Fin 96) = 0 := row_147 28
private lemma v_28_29 : dFQ96 217 (93 : Fin 96) = 0 := row_217 28
private lemma v_28_30 : dFQ96 249 (93 : Fin 96) = 0 := row_249 28
-- 自由座標 29（96 維索引 94）
private lemma v_29_0 : dFQ96 3 (94 : Fin 96) = 0 := row_3 29
private lemma v_29_1 : dFQ96 5 (94 : Fin 96) = 0 := row_5 29
private lemma v_29_2 : dFQ96 7 (94 : Fin 96) = -1 := row_7 29
private lemma v_29_3 : dFQ96 9 (94 : Fin 96) = 1 := row_9 29
private lemma v_29_4 : dFQ96 11 (94 : Fin 96) = 0 := row_11 29
private lemma v_29_5 : dFQ96 13 (94 : Fin 96) = 0 := row_13 29
private lemma v_29_6 : dFQ96 15 (94 : Fin 96) = 0 := row_15 29
private lemma v_29_7 : dFQ96 17 (94 : Fin 96) = 0 := row_17 29
private lemma v_29_8 : dFQ96 19 (94 : Fin 96) = 1 := row_19 29
private lemma v_29_9 : dFQ96 23 (94 : Fin 96) = -1 := row_23 29
private lemma v_29_10 : dFQ96 25 (94 : Fin 96) = 0 := row_25 29
private lemma v_29_11 : dFQ96 27 (94 : Fin 96) = 0 := row_27 29
private lemma v_29_12 : dFQ96 33 (94 : Fin 96) = 0 := row_33 29
private lemma v_29_13 : dFQ96 39 (94 : Fin 96) = 0 := row_39 29
private lemma v_29_14 : dFQ96 43 (94 : Fin 96) = 0 := row_43 29
private lemma v_29_15 : dFQ96 49 (94 : Fin 96) = 0 := row_49 29
private lemma v_29_16 : dFQ96 51 (94 : Fin 96) = 0 := row_51 29
private lemma v_29_17 : dFQ96 55 (94 : Fin 96) = -1 := row_55 29
private lemma v_29_18 : dFQ96 57 (94 : Fin 96) = 0 := row_57 29
private lemma v_29_19 : dFQ96 59 (94 : Fin 96) = -1 := row_59 29
private lemma v_29_20 : dFQ96 65 (94 : Fin 96) = 0 := row_65 29
private lemma v_29_21 : dFQ96 67 (94 : Fin 96) = 0 := row_67 29
private lemma v_29_22 : dFQ96 73 (94 : Fin 96) = 1 := row_73 29
private lemma v_29_23 : dFQ96 87 (94 : Fin 96) = -1 := row_87 29
private lemma v_29_24 : dFQ96 99 (94 : Fin 96) = 0 := row_99 29
private lemma v_29_25 : dFQ96 115 (94 : Fin 96) = 0 := row_115 29
private lemma v_29_26 : dFQ96 121 (94 : Fin 96) = 0 := row_121 29
private lemma v_29_27 : dFQ96 123 (94 : Fin 96) = -1 := row_123 29
private lemma v_29_28 : dFQ96 147 (94 : Fin 96) = 1 := row_147 29
private lemma v_29_29 : dFQ96 217 (94 : Fin 96) = 0 := row_217 29
private lemma v_29_30 : dFQ96 249 (94 : Fin 96) = 1 := row_249 29
-- 自由座標 30（96 維索引 95）
private lemma v_30_0 : dFQ96 3 (95 : Fin 96) = 0 := row_3 30
private lemma v_30_1 : dFQ96 5 (95 : Fin 96) = 0 := row_5 30
private lemma v_30_2 : dFQ96 7 (95 : Fin 96) = 0 := row_7 30
private lemma v_30_3 : dFQ96 9 (95 : Fin 96) = 0 := row_9 30
private lemma v_30_4 : dFQ96 11 (95 : Fin 96) = 0 := row_11 30
private lemma v_30_5 : dFQ96 13 (95 : Fin 96) = 0 := row_13 30
private lemma v_30_6 : dFQ96 15 (95 : Fin 96) = -1 := row_15 30
private lemma v_30_7 : dFQ96 17 (95 : Fin 96) = 0 := row_17 30
private lemma v_30_8 : dFQ96 19 (95 : Fin 96) = 0 := row_19 30
private lemma v_30_9 : dFQ96 23 (95 : Fin 96) = 0 := row_23 30
private lemma v_30_10 : dFQ96 25 (95 : Fin 96) = 0 := row_25 30
private lemma v_30_11 : dFQ96 27 (95 : Fin 96) = 0 := row_27 30
private lemma v_30_12 : dFQ96 33 (95 : Fin 96) = 0 := row_33 30
private lemma v_30_13 : dFQ96 39 (95 : Fin 96) = 0 := row_39 30
private lemma v_30_14 : dFQ96 43 (95 : Fin 96) = 0 := row_43 30
private lemma v_30_15 : dFQ96 49 (95 : Fin 96) = 0 := row_49 30
private lemma v_30_16 : dFQ96 51 (95 : Fin 96) = 0 := row_51 30
private lemma v_30_17 : dFQ96 55 (95 : Fin 96) = 0 := row_55 30
private lemma v_30_18 : dFQ96 57 (95 : Fin 96) = 0 := row_57 30
private lemma v_30_19 : dFQ96 59 (95 : Fin 96) = 0 := row_59 30
private lemma v_30_20 : dFQ96 65 (95 : Fin 96) = 0 := row_65 30
private lemma v_30_21 : dFQ96 67 (95 : Fin 96) = 0 := row_67 30
private lemma v_30_22 : dFQ96 73 (95 : Fin 96) = 0 := row_73 30
private lemma v_30_23 : dFQ96 87 (95 : Fin 96) = 0 := row_87 30
private lemma v_30_24 : dFQ96 99 (95 : Fin 96) = 0 := row_99 30
private lemma v_30_25 : dFQ96 115 (95 : Fin 96) = 0 := row_115 30
private lemma v_30_26 : dFQ96 121 (95 : Fin 96) = 0 := row_121 30
private lemma v_30_27 : dFQ96 123 (95 : Fin 96) = -1 := row_123 30
private lemma v_30_28 : dFQ96 147 (95 : Fin 96) = 0 := row_147 30
private lemma v_30_29 : dFQ96 217 (95 : Fin 96) = 0 := row_217 30
private lemma v_30_30 : dFQ96 249 (95 : Fin 96) = 0 := row_249 30

/-! ## §86 Fin 31 求和展開 -/

/-- `Fin 31` 上的和展開成 31 項、索引為字面數字。
（直接用 `Fin.sum_univ_succ` 會留下 `Fin.succ` 形式，
`linear_combination` 的 ring 正規化會把它們當成不同原子。） -/
private lemma sum_fin_31 (f : Fin 31 → ℚ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 +
      f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 +
      f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 := by
  simp [Fin.sum_univ_succ]
  ring

/-! ## §87 線性獨立 -/

set_option maxHeartbeats 1600000 in
/-- **31 條 dFW96 線性獨立**。判準：投影到 §81 那 31 個自由座標的 31×31 矩陣
可逆（行列式 = 1，么模）。每個係數 `g i` 由錨定的整數逆矩陣 `B` 給出顯式組合
`g i = Σₜ B[t][i]·hₜ`（一行 `linear_combination`，不經 `linarith` 搜尋）。 -/
theorem dFW96_linearIndependent : LinearIndependent ℚ dFW96 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e : ∀ j : Fin 96,
      g 0 * dFQ96 3 j + g 1 * dFQ96 5 j + g 2 * dFQ96 7 j + g 3 * dFQ96 9 j + g 4 * dFQ96 11 j +
        g 5 * dFQ96 13 j + g 6 * dFQ96 15 j + g 7 * dFQ96 17 j + g 8 * dFQ96 19 j +
        g 9 * dFQ96 23 j + g 10 * dFQ96 25 j + g 11 * dFQ96 27 j + g 12 * dFQ96 33 j +
        g 13 * dFQ96 39 j + g 14 * dFQ96 43 j + g 15 * dFQ96 49 j + g 16 * dFQ96 51 j +
        g 17 * dFQ96 55 j + g 18 * dFQ96 57 j + g 19 * dFQ96 59 j + g 20 * dFQ96 65 j +
        g 21 * dFQ96 67 j + g 22 * dFQ96 73 j + g 23 * dFQ96 87 j + g 24 * dFQ96 99 j +
        g 25 * dFQ96 115 j + g 26 * dFQ96 121 j + g 27 * dFQ96 123 j + g 28 * dFQ96 147 j +
        g 29 * dFQ96 217 j + g 30 * dFQ96 249 j = 0 := by
    intro j
    have h := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [sum_fin_31] at h
    exact h
  have h0 := e (8 : Fin 96)
  have h1 := e (10 : Fin 96)
  have h2 := e (13 : Fin 96)
  have h3 := e (15 : Fin 96)
  have h4 := e (26 : Fin 96)
  have h5 := e (29 : Fin 96)
  have h6 := e (30 : Fin 96)
  have h7 := e (31 : Fin 96)
  have h8 := e (32 : Fin 96)
  have h9 := e (40 : Fin 96)
  have h10 := e (42 : Fin 96)
  have h11 := e (44 : Fin 96)
  have h12 := e (45 : Fin 96)
  have h13 := e (46 : Fin 96)
  have h14 := e (47 : Fin 96)
  have h15 := e (56 : Fin 96)
  have h16 := e (58 : Fin 96)
  have h17 := e (61 : Fin 96)
  have h18 := e (63 : Fin 96)
  have h19 := e (74 : Fin 96)
  have h20 := e (77 : Fin 96)
  have h21 := e (78 : Fin 96)
  have h22 := e (79 : Fin 96)
  have h23 := e (80 : Fin 96)
  have h24 := e (88 : Fin 96)
  have h25 := e (89 : Fin 96)
  have h26 := e (90 : Fin 96)
  have h27 := e (92 : Fin 96)
  have h28 := e (93 : Fin 96)
  have h29 := e (94 : Fin 96)
  have h30 := e (95 : Fin 96)
  rw [v_0_0, v_0_1, v_0_2, v_0_3, v_0_4, v_0_5, v_0_6, v_0_7, v_0_8, v_0_9, v_0_10, v_0_11, v_0_12,
    v_0_13, v_0_14, v_0_15, v_0_16, v_0_17, v_0_18, v_0_19, v_0_20, v_0_21, v_0_22, v_0_23,
    v_0_24, v_0_25, v_0_26, v_0_27, v_0_28, v_0_29, v_0_30] at h0
  rw [v_1_0, v_1_1, v_1_2, v_1_3, v_1_4, v_1_5, v_1_6, v_1_7, v_1_8, v_1_9, v_1_10, v_1_11, v_1_12,
    v_1_13, v_1_14, v_1_15, v_1_16, v_1_17, v_1_18, v_1_19, v_1_20, v_1_21, v_1_22, v_1_23,
    v_1_24, v_1_25, v_1_26, v_1_27, v_1_28, v_1_29, v_1_30] at h1
  rw [v_2_0, v_2_1, v_2_2, v_2_3, v_2_4, v_2_5, v_2_6, v_2_7, v_2_8, v_2_9, v_2_10, v_2_11, v_2_12,
    v_2_13, v_2_14, v_2_15, v_2_16, v_2_17, v_2_18, v_2_19, v_2_20, v_2_21, v_2_22, v_2_23,
    v_2_24, v_2_25, v_2_26, v_2_27, v_2_28, v_2_29, v_2_30] at h2
  rw [v_3_0, v_3_1, v_3_2, v_3_3, v_3_4, v_3_5, v_3_6, v_3_7, v_3_8, v_3_9, v_3_10, v_3_11, v_3_12,
    v_3_13, v_3_14, v_3_15, v_3_16, v_3_17, v_3_18, v_3_19, v_3_20, v_3_21, v_3_22, v_3_23,
    v_3_24, v_3_25, v_3_26, v_3_27, v_3_28, v_3_29, v_3_30] at h3
  rw [v_4_0, v_4_1, v_4_2, v_4_3, v_4_4, v_4_5, v_4_6, v_4_7, v_4_8, v_4_9, v_4_10, v_4_11, v_4_12,
    v_4_13, v_4_14, v_4_15, v_4_16, v_4_17, v_4_18, v_4_19, v_4_20, v_4_21, v_4_22, v_4_23,
    v_4_24, v_4_25, v_4_26, v_4_27, v_4_28, v_4_29, v_4_30] at h4
  rw [v_5_0, v_5_1, v_5_2, v_5_3, v_5_4, v_5_5, v_5_6, v_5_7, v_5_8, v_5_9, v_5_10, v_5_11, v_5_12,
    v_5_13, v_5_14, v_5_15, v_5_16, v_5_17, v_5_18, v_5_19, v_5_20, v_5_21, v_5_22, v_5_23,
    v_5_24, v_5_25, v_5_26, v_5_27, v_5_28, v_5_29, v_5_30] at h5
  rw [v_6_0, v_6_1, v_6_2, v_6_3, v_6_4, v_6_5, v_6_6, v_6_7, v_6_8, v_6_9, v_6_10, v_6_11, v_6_12,
    v_6_13, v_6_14, v_6_15, v_6_16, v_6_17, v_6_18, v_6_19, v_6_20, v_6_21, v_6_22, v_6_23,
    v_6_24, v_6_25, v_6_26, v_6_27, v_6_28, v_6_29, v_6_30] at h6
  rw [v_7_0, v_7_1, v_7_2, v_7_3, v_7_4, v_7_5, v_7_6, v_7_7, v_7_8, v_7_9, v_7_10, v_7_11, v_7_12,
    v_7_13, v_7_14, v_7_15, v_7_16, v_7_17, v_7_18, v_7_19, v_7_20, v_7_21, v_7_22, v_7_23,
    v_7_24, v_7_25, v_7_26, v_7_27, v_7_28, v_7_29, v_7_30] at h7
  rw [v_8_0, v_8_1, v_8_2, v_8_3, v_8_4, v_8_5, v_8_6, v_8_7, v_8_8, v_8_9, v_8_10, v_8_11, v_8_12,
    v_8_13, v_8_14, v_8_15, v_8_16, v_8_17, v_8_18, v_8_19, v_8_20, v_8_21, v_8_22, v_8_23,
    v_8_24, v_8_25, v_8_26, v_8_27, v_8_28, v_8_29, v_8_30] at h8
  rw [v_9_0, v_9_1, v_9_2, v_9_3, v_9_4, v_9_5, v_9_6, v_9_7, v_9_8, v_9_9, v_9_10, v_9_11, v_9_12,
    v_9_13, v_9_14, v_9_15, v_9_16, v_9_17, v_9_18, v_9_19, v_9_20, v_9_21, v_9_22, v_9_23,
    v_9_24, v_9_25, v_9_26, v_9_27, v_9_28, v_9_29, v_9_30] at h9
  rw [v_10_0, v_10_1, v_10_2, v_10_3, v_10_4, v_10_5, v_10_6, v_10_7, v_10_8, v_10_9, v_10_10,
    v_10_11, v_10_12, v_10_13, v_10_14, v_10_15, v_10_16, v_10_17, v_10_18, v_10_19, v_10_20,
    v_10_21, v_10_22, v_10_23, v_10_24, v_10_25, v_10_26, v_10_27, v_10_28, v_10_29, v_10_30] at h10
  rw [v_11_0, v_11_1, v_11_2, v_11_3, v_11_4, v_11_5, v_11_6, v_11_7, v_11_8, v_11_9, v_11_10,
    v_11_11, v_11_12, v_11_13, v_11_14, v_11_15, v_11_16, v_11_17, v_11_18, v_11_19, v_11_20,
    v_11_21, v_11_22, v_11_23, v_11_24, v_11_25, v_11_26, v_11_27, v_11_28, v_11_29, v_11_30] at h11
  rw [v_12_0, v_12_1, v_12_2, v_12_3, v_12_4, v_12_5, v_12_6, v_12_7, v_12_8, v_12_9, v_12_10,
    v_12_11, v_12_12, v_12_13, v_12_14, v_12_15, v_12_16, v_12_17, v_12_18, v_12_19, v_12_20,
    v_12_21, v_12_22, v_12_23, v_12_24, v_12_25, v_12_26, v_12_27, v_12_28, v_12_29, v_12_30] at h12
  rw [v_13_0, v_13_1, v_13_2, v_13_3, v_13_4, v_13_5, v_13_6, v_13_7, v_13_8, v_13_9, v_13_10,
    v_13_11, v_13_12, v_13_13, v_13_14, v_13_15, v_13_16, v_13_17, v_13_18, v_13_19, v_13_20,
    v_13_21, v_13_22, v_13_23, v_13_24, v_13_25, v_13_26, v_13_27, v_13_28, v_13_29, v_13_30] at h13
  rw [v_14_0, v_14_1, v_14_2, v_14_3, v_14_4, v_14_5, v_14_6, v_14_7, v_14_8, v_14_9, v_14_10,
    v_14_11, v_14_12, v_14_13, v_14_14, v_14_15, v_14_16, v_14_17, v_14_18, v_14_19, v_14_20,
    v_14_21, v_14_22, v_14_23, v_14_24, v_14_25, v_14_26, v_14_27, v_14_28, v_14_29, v_14_30] at h14
  rw [v_15_0, v_15_1, v_15_2, v_15_3, v_15_4, v_15_5, v_15_6, v_15_7, v_15_8, v_15_9, v_15_10,
    v_15_11, v_15_12, v_15_13, v_15_14, v_15_15, v_15_16, v_15_17, v_15_18, v_15_19, v_15_20,
    v_15_21, v_15_22, v_15_23, v_15_24, v_15_25, v_15_26, v_15_27, v_15_28, v_15_29, v_15_30] at h15
  rw [v_16_0, v_16_1, v_16_2, v_16_3, v_16_4, v_16_5, v_16_6, v_16_7, v_16_8, v_16_9, v_16_10,
    v_16_11, v_16_12, v_16_13, v_16_14, v_16_15, v_16_16, v_16_17, v_16_18, v_16_19, v_16_20,
    v_16_21, v_16_22, v_16_23, v_16_24, v_16_25, v_16_26, v_16_27, v_16_28, v_16_29, v_16_30] at h16
  rw [v_17_0, v_17_1, v_17_2, v_17_3, v_17_4, v_17_5, v_17_6, v_17_7, v_17_8, v_17_9, v_17_10,
    v_17_11, v_17_12, v_17_13, v_17_14, v_17_15, v_17_16, v_17_17, v_17_18, v_17_19, v_17_20,
    v_17_21, v_17_22, v_17_23, v_17_24, v_17_25, v_17_26, v_17_27, v_17_28, v_17_29, v_17_30] at h17
  rw [v_18_0, v_18_1, v_18_2, v_18_3, v_18_4, v_18_5, v_18_6, v_18_7, v_18_8, v_18_9, v_18_10,
    v_18_11, v_18_12, v_18_13, v_18_14, v_18_15, v_18_16, v_18_17, v_18_18, v_18_19, v_18_20,
    v_18_21, v_18_22, v_18_23, v_18_24, v_18_25, v_18_26, v_18_27, v_18_28, v_18_29, v_18_30] at h18
  rw [v_19_0, v_19_1, v_19_2, v_19_3, v_19_4, v_19_5, v_19_6, v_19_7, v_19_8, v_19_9, v_19_10,
    v_19_11, v_19_12, v_19_13, v_19_14, v_19_15, v_19_16, v_19_17, v_19_18, v_19_19, v_19_20,
    v_19_21, v_19_22, v_19_23, v_19_24, v_19_25, v_19_26, v_19_27, v_19_28, v_19_29, v_19_30] at h19
  rw [v_20_0, v_20_1, v_20_2, v_20_3, v_20_4, v_20_5, v_20_6, v_20_7, v_20_8, v_20_9, v_20_10,
    v_20_11, v_20_12, v_20_13, v_20_14, v_20_15, v_20_16, v_20_17, v_20_18, v_20_19, v_20_20,
    v_20_21, v_20_22, v_20_23, v_20_24, v_20_25, v_20_26, v_20_27, v_20_28, v_20_29, v_20_30] at h20
  rw [v_21_0, v_21_1, v_21_2, v_21_3, v_21_4, v_21_5, v_21_6, v_21_7, v_21_8, v_21_9, v_21_10,
    v_21_11, v_21_12, v_21_13, v_21_14, v_21_15, v_21_16, v_21_17, v_21_18, v_21_19, v_21_20,
    v_21_21, v_21_22, v_21_23, v_21_24, v_21_25, v_21_26, v_21_27, v_21_28, v_21_29, v_21_30] at h21
  rw [v_22_0, v_22_1, v_22_2, v_22_3, v_22_4, v_22_5, v_22_6, v_22_7, v_22_8, v_22_9, v_22_10,
    v_22_11, v_22_12, v_22_13, v_22_14, v_22_15, v_22_16, v_22_17, v_22_18, v_22_19, v_22_20,
    v_22_21, v_22_22, v_22_23, v_22_24, v_22_25, v_22_26, v_22_27, v_22_28, v_22_29, v_22_30] at h22
  rw [v_23_0, v_23_1, v_23_2, v_23_3, v_23_4, v_23_5, v_23_6, v_23_7, v_23_8, v_23_9, v_23_10,
    v_23_11, v_23_12, v_23_13, v_23_14, v_23_15, v_23_16, v_23_17, v_23_18, v_23_19, v_23_20,
    v_23_21, v_23_22, v_23_23, v_23_24, v_23_25, v_23_26, v_23_27, v_23_28, v_23_29, v_23_30] at h23
  rw [v_24_0, v_24_1, v_24_2, v_24_3, v_24_4, v_24_5, v_24_6, v_24_7, v_24_8, v_24_9, v_24_10,
    v_24_11, v_24_12, v_24_13, v_24_14, v_24_15, v_24_16, v_24_17, v_24_18, v_24_19, v_24_20,
    v_24_21, v_24_22, v_24_23, v_24_24, v_24_25, v_24_26, v_24_27, v_24_28, v_24_29, v_24_30] at h24
  rw [v_25_0, v_25_1, v_25_2, v_25_3, v_25_4, v_25_5, v_25_6, v_25_7, v_25_8, v_25_9, v_25_10,
    v_25_11, v_25_12, v_25_13, v_25_14, v_25_15, v_25_16, v_25_17, v_25_18, v_25_19, v_25_20,
    v_25_21, v_25_22, v_25_23, v_25_24, v_25_25, v_25_26, v_25_27, v_25_28, v_25_29, v_25_30] at h25
  rw [v_26_0, v_26_1, v_26_2, v_26_3, v_26_4, v_26_5, v_26_6, v_26_7, v_26_8, v_26_9, v_26_10,
    v_26_11, v_26_12, v_26_13, v_26_14, v_26_15, v_26_16, v_26_17, v_26_18, v_26_19, v_26_20,
    v_26_21, v_26_22, v_26_23, v_26_24, v_26_25, v_26_26, v_26_27, v_26_28, v_26_29, v_26_30] at h26
  rw [v_27_0, v_27_1, v_27_2, v_27_3, v_27_4, v_27_5, v_27_6, v_27_7, v_27_8, v_27_9, v_27_10,
    v_27_11, v_27_12, v_27_13, v_27_14, v_27_15, v_27_16, v_27_17, v_27_18, v_27_19, v_27_20,
    v_27_21, v_27_22, v_27_23, v_27_24, v_27_25, v_27_26, v_27_27, v_27_28, v_27_29, v_27_30] at h27
  rw [v_28_0, v_28_1, v_28_2, v_28_3, v_28_4, v_28_5, v_28_6, v_28_7, v_28_8, v_28_9, v_28_10,
    v_28_11, v_28_12, v_28_13, v_28_14, v_28_15, v_28_16, v_28_17, v_28_18, v_28_19, v_28_20,
    v_28_21, v_28_22, v_28_23, v_28_24, v_28_25, v_28_26, v_28_27, v_28_28, v_28_29, v_28_30] at h28
  rw [v_29_0, v_29_1, v_29_2, v_29_3, v_29_4, v_29_5, v_29_6, v_29_7, v_29_8, v_29_9, v_29_10,
    v_29_11, v_29_12, v_29_13, v_29_14, v_29_15, v_29_16, v_29_17, v_29_18, v_29_19, v_29_20,
    v_29_21, v_29_22, v_29_23, v_29_24, v_29_25, v_29_26, v_29_27, v_29_28, v_29_29, v_29_30] at h29
  rw [v_30_0, v_30_1, v_30_2, v_30_3, v_30_4, v_30_5, v_30_6, v_30_7, v_30_8, v_30_9, v_30_10,
    v_30_11, v_30_12, v_30_13, v_30_14, v_30_15, v_30_16, v_30_17, v_30_18, v_30_19, v_30_20,
    v_30_21, v_30_22, v_30_23, v_30_24, v_30_25, v_30_26, v_30_27, v_30_28, v_30_29, v_30_30] at h30
  have g0 : g 0 = 0 := by
    linear_combination -h0 - 2 * h1 - h2 + h3 + 3 * h4 + 2 * h5 - 2 * h7 + h9 + h10 + 3 * h11 + h12 + 3 * h13
      + h14 - h18 + 2 * h19 + h20 + 2 * h21 + 2 * h22 + h23 + 2 * h25 - h26 + h27 + h28 + h30
  have g1 : g 1 = 0 := by
    linear_combination -h0 - h1 + h3 + h5 - h6 - h8 - h11 - 2 * h12 + h13 + h17 - h19 + h20 + 3 * h22 - h24 + h25
      - 2 * h26 - 3 * h27 - 2 * h28 - 2 * h29
  have g2 : g 2 = 0 := by
    linear_combination h1 + h2 + h3 - 2 * h4 - h6 + 2 * h7 - h9 - h10 - 3 * h11 - 2 * h12 - h13 - h14 - h15 - h19
      + h20 - h21 - h24 - 2 * h25 - h27 - h28 - h29
  have g3 : g 3 = 0 := by
    linear_combination -h0 - h1 + 2 * h3 + h4 + h5 - h6 - h12 + h13 - h15 + h20 + h22 - h24 - h25 - h27 - 2 * h28
  have g4 : g 4 = 0 := by
    linear_combination h1 + h2 + h3 - 2 * h4 - h5 - h6 + 2 * h7 - h9 - 2 * h10 - 3 * h11 - h12 - 3 * h13 - h14
      - h15 - h16 - h17 - h20 - h21 - 2 * h22 + h27 + h28 - h29 - h30
  have g5 : g 5 = 0 := by
    linear_combination h0 + h1 + h2 - 3 * h4 - 2 * h5 - h6 + h7 - h9 - h10 - 3 * h11 - h12 - 3 * h13 - h14 + h18
      - 2 * h19 - h20 - 2 * h21 - 2 * h22 - h23 - h25 - h27 - h29 - h30
  have g6 : g 6 = 0 := by
    linear_combination -h5 - h30
  have g7 : g 7 = 0 := by
    linear_combination h3 - h4 - h5 - h6 - h9 - 2 * h10 - h11 + h12 - 3 * h13 - h14 - h15 - h16 - h17 - h20 - h21
      - 2 * h22 + h27 + h28 - h29 - h30
  have g8 : g 8 = 0 := by
    linear_combination h0 + h1 + h2 - h3 - 2 * h4 - h5 + h7 + h10 - 2 * h11 - 2 * h12 + h15 + h17 + h18 - h19
      - h21 - h25 - h27
  have g9 : g 9 = 0 := by
    linear_combination h10 - h12 + h13 + h16 + h17 - h19 + 2 * h22 - 2 * h27 - 2 * h28
  have g10 : g 10 = 0 := by
    linear_combination h0 + h2 - h4 - h5 + h9 + h10 - h11 - h12 + h13 + h15 + h17 - h19 + h22 - h27 - h28
  have g11 : g 11 = 0 := by
    linear_combination h3
  have g12 : g 12 = 0 := by
    linear_combination h0 + h2 - h4 + h7 - h11 - h12
  have g13 : g 13 = 0 := by
    linear_combination -h1 + h3 + h4 - h7 + h9 + h10 + h11 + 2 * h13 - h16 + h18 + h19 - h22 + h25 + h27 + h28
  have g14 : g 14 = 0 := by
    linear_combination h5 - h12 + h13 - h15 + h20 - h24 - h25 - h28
  have g15 : g 15 = 0 := by
    linear_combination -h0 + h5 + h7 - h11 - 2 * h12 + h13 - h15 + h20 - h24 - h25 - h28
  have g16 : g 16 = 0 := by
    linear_combination -h22 + h28
  have g17 : g 17 = 0 := by
    linear_combination h10 - h12 + h13 + h18
  have g18 : g 18 = 0 := by
    linear_combination h5 - h12 + h13
  have g19 : g 19 = 0 := by
    linear_combination -h5 + h9
  have g20 : g 20 = 0 := by
    linear_combination -h0 + h5 - h12 + h13 - h15 + h20 - h24 - h25 - h28
  have g21 : g 21 = 0 := by
    linear_combination h15 + h17 - h19 + h22 - h27 - h28
  have g22 : g 22 = 0 := by
    linear_combination h1 - h4 + h7 - h11 - h12
  have g23 : g 23 = 0 := by
    linear_combination h15
  have g24 : g 24 = 0 := by
    linear_combination h22 - h27 - h28
  have g25 : g 25 = 0 := by
    linear_combination -h28
  have g26 : g 26 = 0 := by
    linear_combination -h13 + h14
  have g27 : g 27 = 0 := by
    linear_combination h5
  have g28 : g 28 = 0 := by
    linear_combination h16 - h19 + h22 - h27 - h28
  have g29 : g 29 = 0 := by
    linear_combination -h10 + h12 - h13
  have g30 : g 30 = 0 := by
    linear_combination -h14
  intro i
  fin_cases i <;> assumption

/-! ## §88 下界與維度定理 -/

/-- 每條見證向量都在 `dFQ96` 的值域裡（定義即然）。 -/
theorem dFW96_mem_range (i : Fin 31) : dFW96 i ∈ Set.range dFQ96 := ⟨wit31 i, rfl⟩

/-- **下界**：`31 ≤ dim span(dFQ96)`。 -/
theorem thirtyone_le_finrank_span_dFQ96 :
    31 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ96)) := by
  have hcard : Module.finrank ℚ (Submodule.span ℚ (Set.range dFW96)) = 31 := by
    simpa using finrank_span_eq_card dFW96_linearIndependent
  have hle : Submodule.span ℚ (Set.range dFW96) ≤ Submodule.span ℚ (Set.range dFQ96) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact dFW96_mem_range i)
  calc (31 : ℕ) = Module.finrank ℚ (Submodule.span ℚ (Set.range dFW96)) := hcard.symm
    _ ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ96)) := Submodule.finrank_mono hle

/-- **維度定理**：Level 3 雙模式有效差分生成空間恰為 **31 維**（96 維中）。

這是 HandOver「維度精確化 (Dimensionality)」第二條主張的形式化：
上界來自 65 條差分層泛函（`finrank_span_dFQ96_le`，§79–81），
下界來自 31 條具體見證的線性獨立（`thirtyone_le_finrank_span_dFQ96`）。
與 Level 2 的 `Flow.finrank_span_dFQ_eq_ten` 對應；A-3 至此收官。 -/
theorem finrank_span_dFQ96_eq_31 :
    Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ96)) = 31 :=
  le_antisymm finrank_span_dFQ96_le thirtyone_le_finrank_span_dFQ96

end CollatzFST.L3
