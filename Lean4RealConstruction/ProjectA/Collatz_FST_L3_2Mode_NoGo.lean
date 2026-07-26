/-
# Level 3 + 雙模式狀態條件勢能不可行性定理（**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_L3_2Mode_Recon.lean`
（規格與憑證皆經對方書面確認採用）。

## 主定理

`no_go_level3_2mode_potential`：Level 3（2 步歷史記憶，48 維特徵）加上
狀態條件雙模式（θ₀ ⊕ θ₁，96 維皆非負）——「有限狀態 + 線性平攤」的最強配置——
**仍不能**在 W₂₀ 的每一單步 Todd 軌跡上嚴格下降。

`no_go_level3_2mode_affine_potential`（仿射版，ROADMAP A-2）：勢能升級為
V_m(x) = β_m + θ_mᵀ F3(x)（β₀ β₁ 不受非負限制）仍不可行——
憑證滿足模式流量平衡，β 項在 Farkas 組合中自動抵消，同一組 λ 直接收掉。
`no_global_odd_level3_2mode_potential`（全稱版，ROADMAP A-1）：同敘述對全體奇數
x > 1 成立——由 W₂₀ ⊆ 奇數 ∩ (1, ∞) a fortiori 得出，三條主定理形式一致。

## 憑證（我方精確整數版，對方已採用）

W₂₀ = 修復版（159 → 59）；λ = (397, 1499, 1734, 2571, 1197, 800, 1046, 2027,
1387, 2648, 3051, 2373, 160, 1734, 1947, 428, 2005, 1846, 1850, 1046)，
Σλ = 31746；組合 S 的 27 個正座標（θ₀ 側 15、θ₁ 側 12）為矛盾的算術基礎。

## 證明骨架

20 條 `Todd_x`（`padicValNat_two_pow_mul`）＋ 40 條 `F3_n` 求值（`decide`）＋
模式引理由 F3 字面值一步導出＋ `if_pos`/`if_neg` 消分支＋
組合恆等式 `key`（96 變數、約 1920 個乘積項，`ring` 收掉，heartbeats 已調高）＋
二十項嚴格負 vs 二十七項非負：0 ≤ −31746 矛盾。

模式語義接地：`mode_bit_endpoints3` 證 40 端點皆滿足 F3[16] + F3[33] = 1
（Level 3 出口唯一性，`boundary_step_unique` 的推廣投影）。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_2Mode_Recon

namespace CollatzFST.L3

open CollatzFST

/-! ## §44 48 分量線性形式 -/

/-- θ ⬝ v（48 分量顯式展開；非 48 長度時取 0）。 -/
def dot48 (θ : Fin 48 → ℚ) : List ℤ → ℚ
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: a20 :: a21 :: a22 :: a23 :: a24 :: a25 :: a26 :: a27 :: a28 :: a29 :: a30 :: a31 :: a32 :: a33 :: a34 :: a35 :: a36 :: a37 :: a38 :: a39 :: a40 :: a41 :: a42 :: a43 :: a44 :: a45 :: a46 :: a47 :: [] =>
      θ 0 * (a0 : ℚ)
      + θ 1 * (a1 : ℚ)
      + θ 2 * (a2 : ℚ)
      + θ 3 * (a3 : ℚ)
      + θ 4 * (a4 : ℚ)
      + θ 5 * (a5 : ℚ)
      + θ 6 * (a6 : ℚ)
      + θ 7 * (a7 : ℚ)
      + θ 8 * (a8 : ℚ)
      + θ 9 * (a9 : ℚ)
      + θ 10 * (a10 : ℚ)
      + θ 11 * (a11 : ℚ)
      + θ 12 * (a12 : ℚ)
      + θ 13 * (a13 : ℚ)
      + θ 14 * (a14 : ℚ)
      + θ 15 * (a15 : ℚ)
      + θ 16 * (a16 : ℚ)
      + θ 17 * (a17 : ℚ)
      + θ 18 * (a18 : ℚ)
      + θ 19 * (a19 : ℚ)
      + θ 20 * (a20 : ℚ)
      + θ 21 * (a21 : ℚ)
      + θ 22 * (a22 : ℚ)
      + θ 23 * (a23 : ℚ)
      + θ 24 * (a24 : ℚ)
      + θ 25 * (a25 : ℚ)
      + θ 26 * (a26 : ℚ)
      + θ 27 * (a27 : ℚ)
      + θ 28 * (a28 : ℚ)
      + θ 29 * (a29 : ℚ)
      + θ 30 * (a30 : ℚ)
      + θ 31 * (a31 : ℚ)
      + θ 32 * (a32 : ℚ)
      + θ 33 * (a33 : ℚ)
      + θ 34 * (a34 : ℚ)
      + θ 35 * (a35 : ℚ)
      + θ 36 * (a36 : ℚ)
      + θ 37 * (a37 : ℚ)
      + θ 38 * (a38 : ℚ)
      + θ 39 * (a39 : ℚ)
      + θ 40 * (a40 : ℚ)
      + θ 41 * (a41 : ℚ)
      + θ 42 * (a42 : ℚ)
      + θ 43 * (a43 : ℚ)
      + θ 44 * (a44 : ℚ)
      + θ 45 * (a45 : ℚ)
      + θ 46 * (a46 : ℚ)
      + θ 47 * (a47 : ℚ)
  | _ => 0

/-! ## §45 Todd 值 -/

lemma Todd_25 : Todd 25 = 19 := by
  have hv : padicValNat 2 (3 * 25 + 1) = 2 := by
    rw [show (3 * 25 + 1 : ℕ) = 2 ^ 2 * 19 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_81 : Todd 81 = 61 := by
  have hv : padicValNat 2 (3 * 81 + 1) = 2 := by
    rw [show (3 * 81 + 1 : ℕ) = 2 ^ 2 * 61 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_59 : Todd 59 = 89 := by
  have hv : padicValNat 2 (3 * 59 + 1) = 1 := by
    rw [show (3 * 59 + 1 : ℕ) = 2 ^ 1 * 89 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_175 : Todd 175 = 263 := by
  have hv : padicValNat 2 (3 * 175 + 1) = 1 := by
    rw [show (3 * 175 + 1 : ℕ) = 2 ^ 1 * 263 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_251 : Todd 251 = 377 := by
  have hv : padicValNat 2 (3 * 251 + 1) = 1 := by
    rw [show (3 * 251 + 1 : ℕ) = 2 ^ 1 * 377 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_449 : Todd 449 = 337 := by
  have hv : padicValNat 2 (3 * 449 + 1) = 2 := by
    rw [show (3 * 449 + 1 : ℕ) = 2 ^ 2 * 337 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_473 : Todd 473 = 355 := by
  have hv : padicValNat 2 (3 * 473 + 1) = 2 := by
    rw [show (3 * 473 + 1 : ℕ) = 2 ^ 2 * 355 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_523 : Todd 523 = 785 := by
  have hv : padicValNat 2 (3 * 523 + 1) = 1 := by
    rw [show (3 * 523 + 1 : ℕ) = 2 ^ 1 * 785 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_537 : Todd 537 = 403 := by
  have hv : padicValNat 2 (3 * 537 + 1) = 2 := by
    rw [show (3 * 537 + 1 : ℕ) = 2 ^ 2 * 403 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_591 : Todd 591 = 887 := by
  have hv : padicValNat 2 (3 * 591 + 1) = 1 := by
    rw [show (3 * 591 + 1 : ℕ) = 2 ^ 1 * 887 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_623 : Todd 623 = 935 := by
  have hv : padicValNat 2 (3 * 623 + 1) = 1 := by
    rw [show (3 * 623 + 1 : ℕ) = 2 ^ 1 * 935 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_679 : Todd 679 = 1019 := by
  have hv : padicValNat 2 (3 * 679 + 1) = 1 := by
    rw [show (3 * 679 + 1 : ℕ) = 2 ^ 1 * 1019 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_683 : Todd 683 = 1025 := by
  have hv : padicValNat 2 (3 * 683 + 1) = 1 := by
    rw [show (3 * 683 + 1 : ℕ) = 2 ^ 1 * 1025 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_713 : Todd 713 = 535 := by
  have hv : padicValNat 2 (3 * 713 + 1) = 2 := by
    rw [show (3 * 713 + 1 : ℕ) = 2 ^ 2 * 535 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_745 : Todd 745 = 559 := by
  have hv : padicValNat 2 (3 * 745 + 1) = 2 := by
    rw [show (3 * 745 + 1 : ℕ) = 2 ^ 2 * 559 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_783 : Todd 783 = 1175 := by
  have hv : padicValNat 2 (3 * 783 + 1) = 1 := by
    rw [show (3 * 783 + 1 : ℕ) = 2 ^ 1 * 1175 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_839 : Todd 839 = 1259 := by
  have hv : padicValNat 2 (3 * 839 + 1) = 1 := by
    rw [show (3 * 839 + 1 : ℕ) = 2 ^ 1 * 1259 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_891 : Todd 891 = 1337 := by
  have hv : padicValNat 2 (3 * 891 + 1) = 1 := by
    rw [show (3 * 891 + 1 : ℕ) = 2 ^ 1 * 1337 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_903 : Todd 903 = 1355 := by
  have hv : padicValNat 2 (3 * 903 + 1) = 1 := by
    rw [show (3 * 903 + 1 : ℕ) = 2 ^ 1 * 1355 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_971 : Todd 971 = 1457 := by
  have hv : padicValNat 2 (3 * 971 + 1) = 1 := by
    rw [show (3 * 971 + 1 : ℕ) = 2 ^ 1 * 1457 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num

/-! ## §46 F3 求值與模式引理 -/

lemma F3_25 : F3 25 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by decide
lemma F3_19 : F3 19 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by decide
lemma F3_81 : F3 81 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
lemma F3_61 : F3 61 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1] := by decide
lemma F3_59 : F3 59 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0] := by decide
lemma F3_89 : F3 89 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0] := by decide
lemma F3_175 : F3 175 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 1] := by decide
lemma F3_263 : F3 263 = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0] := by decide
lemma F3_251 : F3 251 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 2] := by decide
lemma F3_377 : F3 377 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0] := by decide
lemma F3_449 : F3 449 = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0] := by decide
lemma F3_337 : F3 337 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
lemma F3_473 : F3 473 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0] := by decide
lemma F3_355 : F3 355 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0] := by decide
lemma F3_523 : F3 523 = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0] := by decide
lemma F3_785 : F3 785 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by decide
lemma F3_537 : F3 537 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by decide
lemma F3_403 : F3 403 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] := by decide
lemma F3_591 : F3 591 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1] := by decide
lemma F3_887 : F3 887 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 2, 0] := by decide
lemma F3_623 : F3 623 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1] := by decide
lemma F3_935 : F3 935 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0] := by decide
lemma F3_679 : F3 679 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0] := by decide
lemma F3_1019 : F3 1019 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 4] := by decide
lemma F3_683 : F3 683 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0] := by decide
lemma F3_1025 : F3 1025 = [0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
lemma F3_713 : F3 713 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0] := by decide
lemma F3_535 : F3 535 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0] := by decide
lemma F3_745 : F3 745 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0] := by decide
lemma F3_559 : F3 559 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1] := by decide
lemma F3_783 : F3 783 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1] := by decide
lemma F3_1175 : F3 1175 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0] := by decide
lemma F3_839 : F3 839 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0] := by decide
lemma F3_1259 : F3 1259 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0] := by decide
lemma F3_891 : F3 891 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 1] := by decide
lemma F3_1337 : F3 1337 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0] := by decide
lemma F3_903 : F3 903 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0] := by decide
lemma F3_1355 : F3 1355 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0] := by decide
lemma F3_971 : F3 971 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0] := by decide
lemma F3_1457 : F3 1457 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0] := by decide

lemma hm_25 : ¬ (F3 25).getD 33 0 = 1 := by rw [F3_25]; decide
lemma hm_19 : (F3 19).getD 33 0 = 1 := by rw [F3_19]; decide
lemma hm_81 : ¬ (F3 81).getD 33 0 = 1 := by rw [F3_81]; decide
lemma hm_61 : (F3 61).getD 33 0 = 1 := by rw [F3_61]; decide
lemma hm_59 : (F3 59).getD 33 0 = 1 := by rw [F3_59]; decide
lemma hm_89 : ¬ (F3 89).getD 33 0 = 1 := by rw [F3_89]; decide
lemma hm_175 : (F3 175).getD 33 0 = 1 := by rw [F3_175]; decide
lemma hm_263 : (F3 263).getD 33 0 = 1 := by rw [F3_263]; decide
lemma hm_251 : (F3 251).getD 33 0 = 1 := by rw [F3_251]; decide
lemma hm_377 : ¬ (F3 377).getD 33 0 = 1 := by rw [F3_377]; decide
lemma hm_449 : ¬ (F3 449).getD 33 0 = 1 := by rw [F3_449]; decide
lemma hm_337 : ¬ (F3 337).getD 33 0 = 1 := by rw [F3_337]; decide
lemma hm_473 : ¬ (F3 473).getD 33 0 = 1 := by rw [F3_473]; decide
lemma hm_355 : (F3 355).getD 33 0 = 1 := by rw [F3_355]; decide
lemma hm_523 : (F3 523).getD 33 0 = 1 := by rw [F3_523]; decide
lemma hm_785 : ¬ (F3 785).getD 33 0 = 1 := by rw [F3_785]; decide
lemma hm_537 : ¬ (F3 537).getD 33 0 = 1 := by rw [F3_537]; decide
lemma hm_403 : (F3 403).getD 33 0 = 1 := by rw [F3_403]; decide
lemma hm_591 : (F3 591).getD 33 0 = 1 := by rw [F3_591]; decide
lemma hm_887 : (F3 887).getD 33 0 = 1 := by rw [F3_887]; decide
lemma hm_623 : (F3 623).getD 33 0 = 1 := by rw [F3_623]; decide
lemma hm_935 : (F3 935).getD 33 0 = 1 := by rw [F3_935]; decide
lemma hm_679 : (F3 679).getD 33 0 = 1 := by rw [F3_679]; decide
lemma hm_1019 : (F3 1019).getD 33 0 = 1 := by rw [F3_1019]; decide
lemma hm_683 : (F3 683).getD 33 0 = 1 := by rw [F3_683]; decide
lemma hm_1025 : ¬ (F3 1025).getD 33 0 = 1 := by rw [F3_1025]; decide
lemma hm_713 : ¬ (F3 713).getD 33 0 = 1 := by rw [F3_713]; decide
lemma hm_535 : (F3 535).getD 33 0 = 1 := by rw [F3_535]; decide
lemma hm_745 : ¬ (F3 745).getD 33 0 = 1 := by rw [F3_745]; decide
lemma hm_559 : (F3 559).getD 33 0 = 1 := by rw [F3_559]; decide
lemma hm_783 : (F3 783).getD 33 0 = 1 := by rw [F3_783]; decide
lemma hm_1175 : (F3 1175).getD 33 0 = 1 := by rw [F3_1175]; decide
lemma hm_839 : (F3 839).getD 33 0 = 1 := by rw [F3_839]; decide
lemma hm_1259 : (F3 1259).getD 33 0 = 1 := by rw [F3_1259]; decide
lemma hm_891 : (F3 891).getD 33 0 = 1 := by rw [F3_891]; decide
lemma hm_1337 : ¬ (F3 1337).getD 33 0 = 1 := by rw [F3_1337]; decide
lemma hm_903 : (F3 903).getD 33 0 = 1 := by rw [F3_903]; decide
lemma hm_1355 : (F3 1355).getD 33 0 = 1 := by rw [F3_1355]; decide
lemma hm_971 : (F3 971).getD 33 0 = 1 := by rw [F3_971]; decide
lemma hm_1457 : ¬ (F3 1457).getD 33 0 = 1 := by rw [F3_1457]; decide

/-- Level 3 出口唯一性（40 端點）：F3[16] + F3[33] = 1。 -/
lemma mode_bit_endpoints3 :
    ∀ n ∈ ([25, 19, 81, 61, 59, 89, 175, 263, 251, 377, 449, 337, 473, 355, 523, 785, 537, 403, 591, 887, 623, 935, 679, 1019, 683, 1025, 713, 535, 745, 559, 783, 1175, 839, 1259, 891, 1337, 903, 1355, 971, 1457] : List ℕ), (F3 n).getD 16 0 + (F3 n).getD 33 0 = 1 := by
  decide

/-! ## §47 主定理 -/

private lemma addneg {a b : ℚ} (ha : a < 0) (hb : b < 0) : a + b < 0 := by
  have h := add_lt_add ha hb
  simpa using h

set_option maxHeartbeats 1600000 in
/-- **主定理（照確認規格）**：不存在兩組非負權重使 Level 3 雙模式勢能在
W₂₀ 的每一步皆嚴格下降。 -/
theorem no_go_level3_2mode_potential :
    ¬ ∃ (θ₀ θ₁ : Fin 48 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W20,
        (if (F3 (Todd x)).getD 33 0 = 1 then dot48 θ₁ (F3 (Todd x)) else dot48 θ₀ (F3 (Todd x)))
          - (if (F3 x).getD 33 0 = 1 then dot48 θ₁ (F3 x) else dot48 θ₀ (F3 x)) < 0 := by
  rintro ⟨θ₀, θ₁, hθ₀, hθ₁, hdesc⟩
  have h1 := hdesc 25 (by decide)
  have h2 := hdesc 81 (by decide)
  have h3 := hdesc 59 (by decide)
  have h4 := hdesc 175 (by decide)
  have h5 := hdesc 251 (by decide)
  have h6 := hdesc 449 (by decide)
  have h7 := hdesc 473 (by decide)
  have h8 := hdesc 523 (by decide)
  have h9 := hdesc 537 (by decide)
  have h10 := hdesc 591 (by decide)
  have h11 := hdesc 623 (by decide)
  have h12 := hdesc 679 (by decide)
  have h13 := hdesc 683 (by decide)
  have h14 := hdesc 713 (by decide)
  have h15 := hdesc 745 (by decide)
  have h16 := hdesc 783 (by decide)
  have h17 := hdesc 839 (by decide)
  have h18 := hdesc 891 (by decide)
  have h19 := hdesc 903 (by decide)
  have h20 := hdesc 971 (by decide)
  rw [Todd_25, if_pos hm_19, if_neg hm_25] at h1
  rw [Todd_81, if_pos hm_61, if_neg hm_81] at h2
  rw [Todd_59, if_neg hm_89, if_pos hm_59] at h3
  rw [Todd_175, if_pos hm_263, if_pos hm_175] at h4
  rw [Todd_251, if_neg hm_377, if_pos hm_251] at h5
  rw [Todd_449, if_neg hm_337, if_neg hm_449] at h6
  rw [Todd_473, if_pos hm_355, if_neg hm_473] at h7
  rw [Todd_523, if_neg hm_785, if_pos hm_523] at h8
  rw [Todd_537, if_pos hm_403, if_neg hm_537] at h9
  rw [Todd_591, if_pos hm_887, if_pos hm_591] at h10
  rw [Todd_623, if_pos hm_935, if_pos hm_623] at h11
  rw [Todd_679, if_pos hm_1019, if_pos hm_679] at h12
  rw [Todd_683, if_neg hm_1025, if_pos hm_683] at h13
  rw [Todd_713, if_pos hm_535, if_neg hm_713] at h14
  rw [Todd_745, if_pos hm_559, if_neg hm_745] at h15
  rw [Todd_783, if_pos hm_1175, if_pos hm_783] at h16
  rw [Todd_839, if_pos hm_1259, if_pos hm_839] at h17
  rw [Todd_891, if_neg hm_1337, if_pos hm_891] at h18
  rw [Todd_903, if_pos hm_1355, if_pos hm_903] at h19
  rw [Todd_971, if_neg hm_1457, if_pos hm_971] at h20
  have t1 : (397 : ℚ) * (dot48 θ₁ (F3 19) - dot48 θ₀ (F3 25)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h1
  have t2 : (1499 : ℚ) * (dot48 θ₁ (F3 61) - dot48 θ₀ (F3 81)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h2
  have t3 : (1734 : ℚ) * (dot48 θ₀ (F3 89) - dot48 θ₁ (F3 59)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h3
  have t4 : (2571 : ℚ) * (dot48 θ₁ (F3 263) - dot48 θ₁ (F3 175)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h4
  have t5 : (1197 : ℚ) * (dot48 θ₀ (F3 377) - dot48 θ₁ (F3 251)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h5
  have t6 : (800 : ℚ) * (dot48 θ₀ (F3 337) - dot48 θ₀ (F3 449)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h6
  have t7 : (1046 : ℚ) * (dot48 θ₁ (F3 355) - dot48 θ₀ (F3 473)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h7
  have t8 : (2027 : ℚ) * (dot48 θ₀ (F3 785) - dot48 θ₁ (F3 523)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h8
  have t9 : (1387 : ℚ) * (dot48 θ₁ (F3 403) - dot48 θ₀ (F3 537)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h9
  have t10 : (2648 : ℚ) * (dot48 θ₁ (F3 887) - dot48 θ₁ (F3 591)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h10
  have t11 : (3051 : ℚ) * (dot48 θ₁ (F3 935) - dot48 θ₁ (F3 623)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h11
  have t12 : (2373 : ℚ) * (dot48 θ₁ (F3 1019) - dot48 θ₁ (F3 679)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h12
  have t13 : (160 : ℚ) * (dot48 θ₀ (F3 1025) - dot48 θ₁ (F3 683)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h13
  have t14 : (1734 : ℚ) * (dot48 θ₁ (F3 535) - dot48 θ₀ (F3 713)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h14
  have t15 : (1947 : ℚ) * (dot48 θ₁ (F3 559) - dot48 θ₀ (F3 745)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h15
  have t16 : (428 : ℚ) * (dot48 θ₁ (F3 1175) - dot48 θ₁ (F3 783)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h16
  have t17 : (2005 : ℚ) * (dot48 θ₁ (F3 1259) - dot48 θ₁ (F3 839)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h17
  have t18 : (1846 : ℚ) * (dot48 θ₀ (F3 1337) - dot48 θ₁ (F3 891)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h18
  have t19 : (1850 : ℚ) * (dot48 θ₁ (F3 1355) - dot48 θ₁ (F3 903)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h19
  have t20 : (1046 : ℚ) * (dot48 θ₀ (F3 1457) - dot48 θ₁ (F3 971)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h20
  have hlt : (397 : ℚ) * (dot48 θ₁ (F3 19) - dot48 θ₀ (F3 25))
      + (1499 : ℚ) * (dot48 θ₁ (F3 61) - dot48 θ₀ (F3 81))
      + (1734 : ℚ) * (dot48 θ₀ (F3 89) - dot48 θ₁ (F3 59))
      + (2571 : ℚ) * (dot48 θ₁ (F3 263) - dot48 θ₁ (F3 175))
      + (1197 : ℚ) * (dot48 θ₀ (F3 377) - dot48 θ₁ (F3 251))
      + (800 : ℚ) * (dot48 θ₀ (F3 337) - dot48 θ₀ (F3 449))
      + (1046 : ℚ) * (dot48 θ₁ (F3 355) - dot48 θ₀ (F3 473))
      + (2027 : ℚ) * (dot48 θ₀ (F3 785) - dot48 θ₁ (F3 523))
      + (1387 : ℚ) * (dot48 θ₁ (F3 403) - dot48 θ₀ (F3 537))
      + (2648 : ℚ) * (dot48 θ₁ (F3 887) - dot48 θ₁ (F3 591))
      + (3051 : ℚ) * (dot48 θ₁ (F3 935) - dot48 θ₁ (F3 623))
      + (2373 : ℚ) * (dot48 θ₁ (F3 1019) - dot48 θ₁ (F3 679))
      + (160 : ℚ) * (dot48 θ₀ (F3 1025) - dot48 θ₁ (F3 683))
      + (1734 : ℚ) * (dot48 θ₁ (F3 535) - dot48 θ₀ (F3 713))
      + (1947 : ℚ) * (dot48 θ₁ (F3 559) - dot48 θ₀ (F3 745))
      + (428 : ℚ) * (dot48 θ₁ (F3 1175) - dot48 θ₁ (F3 783))
      + (2005 : ℚ) * (dot48 θ₁ (F3 1259) - dot48 θ₁ (F3 839))
      + (1846 : ℚ) * (dot48 θ₀ (F3 1337) - dot48 θ₁ (F3 891))
      + (1850 : ℚ) * (dot48 θ₁ (F3 1355) - dot48 θ₁ (F3 903))
      + (1046 : ℚ) * (dot48 θ₀ (F3 1457) - dot48 θ₁ (F3 971)) < 0 :=
    addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11) t12) t13) t14) t15) t16) t17) t18) t19) t20
  have key : (397 : ℚ) * (dot48 θ₁ (F3 19) - dot48 θ₀ (F3 25))
      + (1499 : ℚ) * (dot48 θ₁ (F3 61) - dot48 θ₀ (F3 81))
      + (1734 : ℚ) * (dot48 θ₀ (F3 89) - dot48 θ₁ (F3 59))
      + (2571 : ℚ) * (dot48 θ₁ (F3 263) - dot48 θ₁ (F3 175))
      + (1197 : ℚ) * (dot48 θ₀ (F3 377) - dot48 θ₁ (F3 251))
      + (800 : ℚ) * (dot48 θ₀ (F3 337) - dot48 θ₀ (F3 449))
      + (1046 : ℚ) * (dot48 θ₁ (F3 355) - dot48 θ₀ (F3 473))
      + (2027 : ℚ) * (dot48 θ₀ (F3 785) - dot48 θ₁ (F3 523))
      + (1387 : ℚ) * (dot48 θ₁ (F3 403) - dot48 θ₀ (F3 537))
      + (2648 : ℚ) * (dot48 θ₁ (F3 887) - dot48 θ₁ (F3 591))
      + (3051 : ℚ) * (dot48 θ₁ (F3 935) - dot48 θ₁ (F3 623))
      + (2373 : ℚ) * (dot48 θ₁ (F3 1019) - dot48 θ₁ (F3 679))
      + (160 : ℚ) * (dot48 θ₀ (F3 1025) - dot48 θ₁ (F3 683))
      + (1734 : ℚ) * (dot48 θ₁ (F3 535) - dot48 θ₀ (F3 713))
      + (1947 : ℚ) * (dot48 θ₁ (F3 559) - dot48 θ₀ (F3 745))
      + (428 : ℚ) * (dot48 θ₁ (F3 1175) - dot48 θ₁ (F3 783))
      + (2005 : ℚ) * (dot48 θ₁ (F3 1259) - dot48 θ₁ (F3 839))
      + (1846 : ℚ) * (dot48 θ₀ (F3 1337) - dot48 θ₁ (F3 891))
      + (1850 : ℚ) * (dot48 θ₁ (F3 1355) - dot48 θ₁ (F3 903))
      + (1046 : ℚ) * (dot48 θ₀ (F3 1457) - dot48 θ₁ (F3 971))
      = 347 * θ₀ 10
        + 112 * θ₀ 11
        + 640 * θ₀ 13
        + 213 * θ₀ 14
        + 539 * θ₀ 24
        + 101 * θ₀ 26
        + 539 * θ₀ 27
        + 296 * θ₀ 29
        + 112 * θ₀ 30
        + 296 * θ₀ 40
        + 145 * θ₀ 42
        + 151 * θ₀ 43
        + 243 * θ₀ 44
        + 296 * θ₀ 45
        + 151 * θ₀ 46
        + 544 * θ₁ 8
        + 988 * θ₁ 10
        + 155 * θ₁ 13
        + 1499 * θ₁ 17
        + 155 * θ₁ 24
        + 155 * θ₁ 27
        + 155 * θ₁ 29
        + 1499 * θ₁ 32
        + 155 * θ₁ 40
        + 155 * θ₁ 43
        + 155 * θ₁ 45
        + 155 * θ₁ 46 := by
    rw [F3_25, F3_19, F3_81, F3_61, F3_59, F3_89, F3_175, F3_263, F3_251, F3_377, F3_449, F3_337, F3_473, F3_355, F3_523, F3_785, F3_537, F3_403, F3_591, F3_887, F3_623, F3_935, F3_679, F3_1019, F3_683, F3_1025, F3_713, F3_535, F3_745, F3_559, F3_783, F3_1175, F3_839, F3_1259, F3_891, F3_1337, F3_903, F3_1355, F3_971, F3_1457]
    simp only [dot48]
    push_cast
    ring
  rw [key] at hlt
  have hge : (0 : ℚ) ≤ 347 * θ₀ 10
        + 112 * θ₀ 11
        + 640 * θ₀ 13
        + 213 * θ₀ 14
        + 539 * θ₀ 24
        + 101 * θ₀ 26
        + 539 * θ₀ 27
        + 296 * θ₀ 29
        + 112 * θ₀ 30
        + 296 * θ₀ 40
        + 145 * θ₀ 42
        + 151 * θ₀ 43
        + 243 * θ₀ 44
        + 296 * θ₀ 45
        + 151 * θ₀ 46
        + 544 * θ₁ 8
        + 988 * θ₁ 10
        + 155 * θ₁ 13
        + 1499 * θ₁ 17
        + 155 * θ₁ 24
        + 155 * θ₁ 27
        + 155 * θ₁ 29
        + 1499 * θ₁ 32
        + 155 * θ₁ 40
        + 155 * θ₁ 43
        + 155 * θ₁ 45
        + 155 * θ₁ 46 :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hθ₀ 10)) (mul_nonneg (by norm_num) (hθ₀ 11))) (mul_nonneg (by norm_num) (hθ₀ 13))) (mul_nonneg (by norm_num) (hθ₀ 14))) (mul_nonneg (by norm_num) (hθ₀ 24))) (mul_nonneg (by norm_num) (hθ₀ 26))) (mul_nonneg (by norm_num) (hθ₀ 27))) (mul_nonneg (by norm_num) (hθ₀ 29))) (mul_nonneg (by norm_num) (hθ₀ 30))) (mul_nonneg (by norm_num) (hθ₀ 40))) (mul_nonneg (by norm_num) (hθ₀ 42))) (mul_nonneg (by norm_num) (hθ₀ 43))) (mul_nonneg (by norm_num) (hθ₀ 44))) (mul_nonneg (by norm_num) (hθ₀ 45))) (mul_nonneg (by norm_num) (hθ₀ 46))) (mul_nonneg (by norm_num) (hθ₁ 8))) (mul_nonneg (by norm_num) (hθ₁ 10))) (mul_nonneg (by norm_num) (hθ₁ 13))) (mul_nonneg (by norm_num) (hθ₁ 17))) (mul_nonneg (by norm_num) (hθ₁ 24))) (mul_nonneg (by norm_num) (hθ₁ 27))) (mul_nonneg (by norm_num) (hθ₁ 29))) (mul_nonneg (by norm_num) (hθ₁ 32))) (mul_nonneg (by norm_num) (hθ₁ 40))) (mul_nonneg (by norm_num) (hθ₁ 43))) (mul_nonneg (by norm_num) (hθ₁ 45))) (mul_nonneg (by norm_num) (hθ₁ 46))
  exact absurd hlt (not_lt.mpr hge)

set_option maxHeartbeats 1600000 in
/-- **仿射版主定理**（ROADMAP A-2；HandOver「仿射截距強健性 (Affine Offsets)」條款）：
Level 3 勢能升級為 V_m(x) = β_m + θ_mᵀ F3(x)，截距 `β₀ β₁` **不受非負限制**（可正可負），
非負權重的雙模式仿射勢能仍不能在 W₂₀ 的每一步嚴格下降。

證明骨架與 `no_go_level3_2mode_potential` 完全相同（同一組 λ、同批 `Todd_*`/`hm_*` 引理、
同樣的 `if_pos`/`if_neg`）：憑證滿足模式流量平衡 Σλ(e_{m(y)} − e_{m(x)}) = [0, 0]
（`tools/certificates.py` 重算驗證），β 項在 Farkas 組合中自動抵消，
組合恆等式 `key` 的右端不變。 -/
theorem no_go_level3_2mode_affine_potential :
    ¬ ∃ (β₀ β₁ : ℚ) (θ₀ θ₁ : Fin 48 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W20,
        (if (F3 (Todd x)).getD 33 0 = 1 then β₁ + dot48 θ₁ (F3 (Todd x))
                                        else β₀ + dot48 θ₀ (F3 (Todd x)))
          - (if (F3 x).getD 33 0 = 1 then β₁ + dot48 θ₁ (F3 x) else β₀ + dot48 θ₀ (F3 x)) < 0 := by
  rintro ⟨β₀, β₁, θ₀, θ₁, hθ₀, hθ₁, hdesc⟩
  have h1 := hdesc 25 (by decide)
  have h2 := hdesc 81 (by decide)
  have h3 := hdesc 59 (by decide)
  have h4 := hdesc 175 (by decide)
  have h5 := hdesc 251 (by decide)
  have h6 := hdesc 449 (by decide)
  have h7 := hdesc 473 (by decide)
  have h8 := hdesc 523 (by decide)
  have h9 := hdesc 537 (by decide)
  have h10 := hdesc 591 (by decide)
  have h11 := hdesc 623 (by decide)
  have h12 := hdesc 679 (by decide)
  have h13 := hdesc 683 (by decide)
  have h14 := hdesc 713 (by decide)
  have h15 := hdesc 745 (by decide)
  have h16 := hdesc 783 (by decide)
  have h17 := hdesc 839 (by decide)
  have h18 := hdesc 891 (by decide)
  have h19 := hdesc 903 (by decide)
  have h20 := hdesc 971 (by decide)
  rw [Todd_25, if_pos hm_19, if_neg hm_25] at h1
  rw [Todd_81, if_pos hm_61, if_neg hm_81] at h2
  rw [Todd_59, if_neg hm_89, if_pos hm_59] at h3
  rw [Todd_175, if_pos hm_263, if_pos hm_175] at h4
  rw [Todd_251, if_neg hm_377, if_pos hm_251] at h5
  rw [Todd_449, if_neg hm_337, if_neg hm_449] at h6
  rw [Todd_473, if_pos hm_355, if_neg hm_473] at h7
  rw [Todd_523, if_neg hm_785, if_pos hm_523] at h8
  rw [Todd_537, if_pos hm_403, if_neg hm_537] at h9
  rw [Todd_591, if_pos hm_887, if_pos hm_591] at h10
  rw [Todd_623, if_pos hm_935, if_pos hm_623] at h11
  rw [Todd_679, if_pos hm_1019, if_pos hm_679] at h12
  rw [Todd_683, if_neg hm_1025, if_pos hm_683] at h13
  rw [Todd_713, if_pos hm_535, if_neg hm_713] at h14
  rw [Todd_745, if_pos hm_559, if_neg hm_745] at h15
  rw [Todd_783, if_pos hm_1175, if_pos hm_783] at h16
  rw [Todd_839, if_pos hm_1259, if_pos hm_839] at h17
  rw [Todd_891, if_neg hm_1337, if_pos hm_891] at h18
  rw [Todd_903, if_pos hm_1355, if_pos hm_903] at h19
  rw [Todd_971, if_neg hm_1457, if_pos hm_971] at h20
  have t1 : (397 : ℚ) * ((β₁ + dot48 θ₁ (F3 19)) - (β₀ + dot48 θ₀ (F3 25))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h1
  have t2 : (1499 : ℚ) * ((β₁ + dot48 θ₁ (F3 61)) - (β₀ + dot48 θ₀ (F3 81))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h2
  have t3 : (1734 : ℚ) * ((β₀ + dot48 θ₀ (F3 89)) - (β₁ + dot48 θ₁ (F3 59))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h3
  have t4 : (2571 : ℚ) * ((β₁ + dot48 θ₁ (F3 263)) - (β₁ + dot48 θ₁ (F3 175))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h4
  have t5 : (1197 : ℚ) * ((β₀ + dot48 θ₀ (F3 377)) - (β₁ + dot48 θ₁ (F3 251))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h5
  have t6 : (800 : ℚ) * ((β₀ + dot48 θ₀ (F3 337)) - (β₀ + dot48 θ₀ (F3 449))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h6
  have t7 : (1046 : ℚ) * ((β₁ + dot48 θ₁ (F3 355)) - (β₀ + dot48 θ₀ (F3 473))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h7
  have t8 : (2027 : ℚ) * ((β₀ + dot48 θ₀ (F3 785)) - (β₁ + dot48 θ₁ (F3 523))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h8
  have t9 : (1387 : ℚ) * ((β₁ + dot48 θ₁ (F3 403)) - (β₀ + dot48 θ₀ (F3 537))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h9
  have t10 : (2648 : ℚ) * ((β₁ + dot48 θ₁ (F3 887)) - (β₁ + dot48 θ₁ (F3 591))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h10
  have t11 : (3051 : ℚ) * ((β₁ + dot48 θ₁ (F3 935)) - (β₁ + dot48 θ₁ (F3 623))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h11
  have t12 : (2373 : ℚ) * ((β₁ + dot48 θ₁ (F3 1019)) - (β₁ + dot48 θ₁ (F3 679))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h12
  have t13 : (160 : ℚ) * ((β₀ + dot48 θ₀ (F3 1025)) - (β₁ + dot48 θ₁ (F3 683))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h13
  have t14 : (1734 : ℚ) * ((β₁ + dot48 θ₁ (F3 535)) - (β₀ + dot48 θ₀ (F3 713))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h14
  have t15 : (1947 : ℚ) * ((β₁ + dot48 θ₁ (F3 559)) - (β₀ + dot48 θ₀ (F3 745))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h15
  have t16 : (428 : ℚ) * ((β₁ + dot48 θ₁ (F3 1175)) - (β₁ + dot48 θ₁ (F3 783))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h16
  have t17 : (2005 : ℚ) * ((β₁ + dot48 θ₁ (F3 1259)) - (β₁ + dot48 θ₁ (F3 839))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h17
  have t18 : (1846 : ℚ) * ((β₀ + dot48 θ₀ (F3 1337)) - (β₁ + dot48 θ₁ (F3 891))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h18
  have t19 : (1850 : ℚ) * ((β₁ + dot48 θ₁ (F3 1355)) - (β₁ + dot48 θ₁ (F3 903))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h19
  have t20 : (1046 : ℚ) * ((β₀ + dot48 θ₀ (F3 1457)) - (β₁ + dot48 θ₁ (F3 971))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h20
  have hlt : (397 : ℚ) * ((β₁ + dot48 θ₁ (F3 19)) - (β₀ + dot48 θ₀ (F3 25)))
      + (1499 : ℚ) * ((β₁ + dot48 θ₁ (F3 61)) - (β₀ + dot48 θ₀ (F3 81)))
      + (1734 : ℚ) * ((β₀ + dot48 θ₀ (F3 89)) - (β₁ + dot48 θ₁ (F3 59)))
      + (2571 : ℚ) * ((β₁ + dot48 θ₁ (F3 263)) - (β₁ + dot48 θ₁ (F3 175)))
      + (1197 : ℚ) * ((β₀ + dot48 θ₀ (F3 377)) - (β₁ + dot48 θ₁ (F3 251)))
      + (800 : ℚ) * ((β₀ + dot48 θ₀ (F3 337)) - (β₀ + dot48 θ₀ (F3 449)))
      + (1046 : ℚ) * ((β₁ + dot48 θ₁ (F3 355)) - (β₀ + dot48 θ₀ (F3 473)))
      + (2027 : ℚ) * ((β₀ + dot48 θ₀ (F3 785)) - (β₁ + dot48 θ₁ (F3 523)))
      + (1387 : ℚ) * ((β₁ + dot48 θ₁ (F3 403)) - (β₀ + dot48 θ₀ (F3 537)))
      + (2648 : ℚ) * ((β₁ + dot48 θ₁ (F3 887)) - (β₁ + dot48 θ₁ (F3 591)))
      + (3051 : ℚ) * ((β₁ + dot48 θ₁ (F3 935)) - (β₁ + dot48 θ₁ (F3 623)))
      + (2373 : ℚ) * ((β₁ + dot48 θ₁ (F3 1019)) - (β₁ + dot48 θ₁ (F3 679)))
      + (160 : ℚ) * ((β₀ + dot48 θ₀ (F3 1025)) - (β₁ + dot48 θ₁ (F3 683)))
      + (1734 : ℚ) * ((β₁ + dot48 θ₁ (F3 535)) - (β₀ + dot48 θ₀ (F3 713)))
      + (1947 : ℚ) * ((β₁ + dot48 θ₁ (F3 559)) - (β₀ + dot48 θ₀ (F3 745)))
      + (428 : ℚ) * ((β₁ + dot48 θ₁ (F3 1175)) - (β₁ + dot48 θ₁ (F3 783)))
      + (2005 : ℚ) * ((β₁ + dot48 θ₁ (F3 1259)) - (β₁ + dot48 θ₁ (F3 839)))
      + (1846 : ℚ) * ((β₀ + dot48 θ₀ (F3 1337)) - (β₁ + dot48 θ₁ (F3 891)))
      + (1850 : ℚ) * ((β₁ + dot48 θ₁ (F3 1355)) - (β₁ + dot48 θ₁ (F3 903)))
      + (1046 : ℚ) * ((β₀ + dot48 θ₀ (F3 1457)) - (β₁ + dot48 θ₁ (F3 971))) < 0 :=
    addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11) t12) t13) t14) t15) t16) t17) t18) t19) t20
  have key : (397 : ℚ) * ((β₁ + dot48 θ₁ (F3 19)) - (β₀ + dot48 θ₀ (F3 25)))
      + (1499 : ℚ) * ((β₁ + dot48 θ₁ (F3 61)) - (β₀ + dot48 θ₀ (F3 81)))
      + (1734 : ℚ) * ((β₀ + dot48 θ₀ (F3 89)) - (β₁ + dot48 θ₁ (F3 59)))
      + (2571 : ℚ) * ((β₁ + dot48 θ₁ (F3 263)) - (β₁ + dot48 θ₁ (F3 175)))
      + (1197 : ℚ) * ((β₀ + dot48 θ₀ (F3 377)) - (β₁ + dot48 θ₁ (F3 251)))
      + (800 : ℚ) * ((β₀ + dot48 θ₀ (F3 337)) - (β₀ + dot48 θ₀ (F3 449)))
      + (1046 : ℚ) * ((β₁ + dot48 θ₁ (F3 355)) - (β₀ + dot48 θ₀ (F3 473)))
      + (2027 : ℚ) * ((β₀ + dot48 θ₀ (F3 785)) - (β₁ + dot48 θ₁ (F3 523)))
      + (1387 : ℚ) * ((β₁ + dot48 θ₁ (F3 403)) - (β₀ + dot48 θ₀ (F3 537)))
      + (2648 : ℚ) * ((β₁ + dot48 θ₁ (F3 887)) - (β₁ + dot48 θ₁ (F3 591)))
      + (3051 : ℚ) * ((β₁ + dot48 θ₁ (F3 935)) - (β₁ + dot48 θ₁ (F3 623)))
      + (2373 : ℚ) * ((β₁ + dot48 θ₁ (F3 1019)) - (β₁ + dot48 θ₁ (F3 679)))
      + (160 : ℚ) * ((β₀ + dot48 θ₀ (F3 1025)) - (β₁ + dot48 θ₁ (F3 683)))
      + (1734 : ℚ) * ((β₁ + dot48 θ₁ (F3 535)) - (β₀ + dot48 θ₀ (F3 713)))
      + (1947 : ℚ) * ((β₁ + dot48 θ₁ (F3 559)) - (β₀ + dot48 θ₀ (F3 745)))
      + (428 : ℚ) * ((β₁ + dot48 θ₁ (F3 1175)) - (β₁ + dot48 θ₁ (F3 783)))
      + (2005 : ℚ) * ((β₁ + dot48 θ₁ (F3 1259)) - (β₁ + dot48 θ₁ (F3 839)))
      + (1846 : ℚ) * ((β₀ + dot48 θ₀ (F3 1337)) - (β₁ + dot48 θ₁ (F3 891)))
      + (1850 : ℚ) * ((β₁ + dot48 θ₁ (F3 1355)) - (β₁ + dot48 θ₁ (F3 903)))
      + (1046 : ℚ) * ((β₀ + dot48 θ₀ (F3 1457)) - (β₁ + dot48 θ₁ (F3 971)))
      = 347 * θ₀ 10
        + 112 * θ₀ 11
        + 640 * θ₀ 13
        + 213 * θ₀ 14
        + 539 * θ₀ 24
        + 101 * θ₀ 26
        + 539 * θ₀ 27
        + 296 * θ₀ 29
        + 112 * θ₀ 30
        + 296 * θ₀ 40
        + 145 * θ₀ 42
        + 151 * θ₀ 43
        + 243 * θ₀ 44
        + 296 * θ₀ 45
        + 151 * θ₀ 46
        + 544 * θ₁ 8
        + 988 * θ₁ 10
        + 155 * θ₁ 13
        + 1499 * θ₁ 17
        + 155 * θ₁ 24
        + 155 * θ₁ 27
        + 155 * θ₁ 29
        + 1499 * θ₁ 32
        + 155 * θ₁ 40
        + 155 * θ₁ 43
        + 155 * θ₁ 45
        + 155 * θ₁ 46 := by
    rw [F3_25, F3_19, F3_81, F3_61, F3_59, F3_89, F3_175, F3_263, F3_251, F3_377, F3_449, F3_337, F3_473, F3_355, F3_523, F3_785, F3_537, F3_403, F3_591, F3_887, F3_623, F3_935, F3_679, F3_1019, F3_683, F3_1025, F3_713, F3_535, F3_745, F3_559, F3_783, F3_1175, F3_839, F3_1259, F3_891, F3_1337, F3_903, F3_1355, F3_971, F3_1457]
    simp only [dot48]
    push_cast
    ring
  rw [key] at hlt
  have hge : (0 : ℚ) ≤ 347 * θ₀ 10
        + 112 * θ₀ 11
        + 640 * θ₀ 13
        + 213 * θ₀ 14
        + 539 * θ₀ 24
        + 101 * θ₀ 26
        + 539 * θ₀ 27
        + 296 * θ₀ 29
        + 112 * θ₀ 30
        + 296 * θ₀ 40
        + 145 * θ₀ 42
        + 151 * θ₀ 43
        + 243 * θ₀ 44
        + 296 * θ₀ 45
        + 151 * θ₀ 46
        + 544 * θ₁ 8
        + 988 * θ₁ 10
        + 155 * θ₁ 13
        + 1499 * θ₁ 17
        + 155 * θ₁ 24
        + 155 * θ₁ 27
        + 155 * θ₁ 29
        + 1499 * θ₁ 32
        + 155 * θ₁ 40
        + 155 * θ₁ 43
        + 155 * θ₁ 45
        + 155 * θ₁ 46 :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hθ₀ 10)) (mul_nonneg (by norm_num) (hθ₀ 11))) (mul_nonneg (by norm_num) (hθ₀ 13))) (mul_nonneg (by norm_num) (hθ₀ 14))) (mul_nonneg (by norm_num) (hθ₀ 24))) (mul_nonneg (by norm_num) (hθ₀ 26))) (mul_nonneg (by norm_num) (hθ₀ 27))) (mul_nonneg (by norm_num) (hθ₀ 29))) (mul_nonneg (by norm_num) (hθ₀ 30))) (mul_nonneg (by norm_num) (hθ₀ 40))) (mul_nonneg (by norm_num) (hθ₀ 42))) (mul_nonneg (by norm_num) (hθ₀ 43))) (mul_nonneg (by norm_num) (hθ₀ 44))) (mul_nonneg (by norm_num) (hθ₀ 45))) (mul_nonneg (by norm_num) (hθ₀ 46))) (mul_nonneg (by norm_num) (hθ₁ 8))) (mul_nonneg (by norm_num) (hθ₁ 10))) (mul_nonneg (by norm_num) (hθ₁ 13))) (mul_nonneg (by norm_num) (hθ₁ 17))) (mul_nonneg (by norm_num) (hθ₁ 24))) (mul_nonneg (by norm_num) (hθ₁ 27))) (mul_nonneg (by norm_num) (hθ₁ 29))) (mul_nonneg (by norm_num) (hθ₁ 32))) (mul_nonneg (by norm_num) (hθ₁ 40))) (mul_nonneg (by norm_num) (hθ₁ 43))) (mul_nonneg (by norm_num) (hθ₁ 45))) (mul_nonneg (by norm_num) (hθ₁ 46))
  exact absurd hlt (not_lt.mpr hge)
lemma W20_odd : ∀ x ∈ W20, x % 2 = 1 := by decide

lemma W20_gt_one : ∀ x ∈ W20, 1 < x := by decide

/-- **全稱版**（與 `LP.no_global_odd_ranking`、`TwoMode.no_global_odd_2mode_potential`
同形式；ROADMAP A-1）：不存在兩組非負權重使 Level 3 雙模式勢能對**每個奇數 `x > 1`**
的單次加速迭代皆嚴格下降——由 W₂₀ ⊆ 奇數 ∩ (1, ∞) a fortiori 得出。
量詞排除 `x = 1` 對應 HandOver「非平凡量詞 (The Trivial Trap)」條款。 -/
theorem no_global_odd_level3_2mode_potential :
    ¬ ∃ (θ₀ θ₁ : Fin 48 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x : ℕ, x % 2 = 1 → 1 < x →
        (if (F3 (Todd x)).getD 33 0 = 1 then dot48 θ₁ (F3 (Todd x)) else dot48 θ₀ (F3 (Todd x)))
          - (if (F3 x).getD 33 0 = 1 then dot48 θ₁ (F3 x) else dot48 θ₀ (F3 x)) < 0 := by
  rintro ⟨θ₀, θ₁, hθ₀, hθ₁, h⟩
  exact no_go_level3_2mode_potential
    ⟨θ₀, θ₁, hθ₀, hθ₁, fun x hx => h x (W20_odd x hx) (W20_gt_one x hx)⟩

/-! ## §48 回歸驗證 -/

section Verification

#eval cert3.all fun p => p.1 ∈ W20
#eval W20.all fun x => x % 2 == 1

end Verification

end CollatzFST.L3
