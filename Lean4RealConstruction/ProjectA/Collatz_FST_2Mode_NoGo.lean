/-
# 雙模式狀態條件勢能不可行性定理（**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_2Mode_Recon.lean`
（規格驗證）與 `Collatz_FST_NoLinearRanking.lean`（複用 `dot`）。

## 主定理

`no_go_2mode_potential`：Level 2 特徵空間引入狀態條件切換
（模式觀測量 m(x) = F(x)[5]，即 K→S 出口的凝聚/碎裂二分）後，
36 維（θ₀ ⊕ θ₁ 皆非負）的雙模式勢能**仍不能**在 W₁₂ 的每一步嚴格下降。

`no_go_2mode_affine_potential`（仿射版，ROADMAP A-2）：勢能升級為
V_m(x) = β_m + θ_mᵀ F(x)（β₀ β₁ 不受非負限制）仍不可行——
憑證滿足模式流量平衡，β 項在 Farkas 組合中自動抵消，同一組 λ 直接收掉。

## 證明骨架

* 12 條 `Todd_x`（v₂ = 2,2,2,1,1,2,1,1,2,1,1,1，`padicValNat_two_pow_mul`）。
* 24 條 `F_n` 求值（`decide`，digits kernel 展開）；模式引理 `hm_n` 由
  F 字面值一步導出（getD 於字面串列上化簡）。
* 模式分支以 `if_pos`/`if_neg` 消去後，12 條假設化為
  `dot θ_{mₑ} (F y) − dot θ_{mₛ} (F x) < 0`。
* 組合恆等式 `key`：Σ λᵢ·(…) = 36·θ₀₍₁₁₎+36·θ₀₍₁₅₎+36·θ₀₍₁₆₎+36·θ₀₍₁₇₎
  + 94·θ₁₍₇₎+522·θ₁₍₈₎+527·θ₁₍₉₎+621·θ₁₍₁₂₎，由 `ring` 於 36 變數上收掉
  （λ = (72,936,864,1107,1502,900,588,326,648,162,163,558)，Σ = 7826）。
* 十二項嚴格負 vs 八項非負：0 ≤ −7826 矛盾。

## 模式語義的接地

m ∈ {0,1} 非假設：`mode_bit_endpoints` 證 24 端點皆滿足
F[2] + F[5] = 1——`boundary_step_unique`（K→S 邊界步唯一）的特徵層投影。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_2Mode_Recon
import Lean4RealConstruction.ProjectA.Collatz_FST_NoLinearRanking

namespace CollatzFST.TwoMode

open CollatzFST
open CollatzFST.LP (dot)

/-! ## §38 Todd 值 -/

lemma Todd_25 : Todd 25 = 19 := by
  have hv : padicValNat 2 (3 * 25 + 1) = 2 := by
    rw [show (3 * 25 + 1 : ℕ) = 2 ^ 2 * 19 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_161 : Todd 161 = 121 := by
  have hv : padicValNat 2 (3 * 161 + 1) = 2 := by
    rw [show (3 * 161 + 1 : ℕ) = 2 ^ 2 * 121 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_353 : Todd 353 = 265 := by
  have hv : padicValNat 2 (3 * 353 + 1) = 2 := by
    rw [show (3 * 353 + 1 : ℕ) = 2 ^ 2 * 265 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_391 : Todd 391 = 587 := by
  have hv : padicValNat 2 (3 * 391 + 1) = 1 := by
    rw [show (3 * 391 + 1 : ℕ) = 2 ^ 1 * 587 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_471 : Todd 471 = 707 := by
  have hv : padicValNat 2 (3 * 471 + 1) = 1 := by
    rw [show (3 * 471 + 1 : ℕ) = 2 ^ 1 * 707 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_481 : Todd 481 = 361 := by
  have hv : padicValNat 2 (3 * 481 + 1) = 2 := by
    rw [show (3 * 481 + 1 : ℕ) = 2 ^ 2 * 361 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_583 : Todd 583 = 875 := by
  have hv : padicValNat 2 (3 * 583 + 1) = 1 := by
    rw [show (3 * 583 + 1 : ℕ) = 2 ^ 1 * 875 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_663 : Todd 663 = 995 := by
  have hv : padicValNat 2 (3 * 663 + 1) = 1 := by
    rw [show (3 * 663 + 1 : ℕ) = 2 ^ 1 * 995 by norm_num]
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
lemma Todd_683 : Todd 683 = 1025 := by
  have hv : padicValNat 2 (3 * 683 + 1) = 1 := by
    rw [show (3 * 683 + 1 : ℕ) = 2 ^ 1 * 1025 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_711 : Todd 711 = 1067 := by
  have hv : padicValNat 2 (3 * 711 + 1) = 1 := by
    rw [show (3 * 711 + 1 : ℕ) = 2 ^ 1 * 1067 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_779 : Todd 779 = 1169 := by
  have hv : padicValNat 2 (3 * 779 + 1) = 1 := by
    rw [show (3 * 779 + 1 : ℕ) = 2 ^ 1 * 1169 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num

/-! ## §39 F 求值與模式引理 -/

lemma F_25 : F 25 = [0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0] := by decide
lemma F_19 : F 19 = [0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0] := by decide
lemma F_161 : F 161 = [0, 0, 1, 1, 1, 0, 1, 1, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0] := by decide
lemma F_121 : F 121 = [0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1] := by decide
lemma F_353 : F 353 = [0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 2, 0, 0, 0] := by decide
lemma F_265 : F 265 = [0, 0, 1, 1, 1, 0, 2, 1, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0] := by decide
lemma F_391 : F 391 = [0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 2, 0, 0, 1, 1, 0, 1, 1] := by decide
lemma F_587 : F 587 = [0, 0, 0, 1, 0, 1, 0, 1, 2, 1, 1, 1, 2, 0, 1, 0, 1, 0] := by decide
lemma F_471 : F 471 = [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 1, 1, 2, 2] := by decide
lemma F_707 : F 707 = [0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0] := by decide
lemma F_481 : F 481 = [0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1] := by decide
lemma F_361 : F 361 = [0, 0, 1, 1, 1, 0, 0, 0, 0, 2, 1, 1, 1, 1, 2, 0, 0, 0] := by decide
lemma F_583 : F 583 = [0, 0, 0, 1, 0, 1, 0, 2, 3, 0, 1, 0, 2, 0, 0, 0, 1, 1] := by decide
lemma F_875 : F 875 = [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 3, 0, 0, 1, 2, 3, 0] := by decide
lemma F_663 : F 663 = [0, 0, 0, 1, 0, 1, 0, 0, 1, 2, 1, 1, 2, 0, 1, 0, 1, 1] := by decide
lemma F_995 : F 995 = [0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 2, 2] := by decide
lemma F_681 : F 681 = [0, 0, 1, 1, 1, 0, 0, 0, 1, 4, 0, 0, 4, 0, 0, 0, 0, 0] := by decide
lemma F_511 : F 511 = [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 7] := by decide
lemma F_683 : F 683 = [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 4, 0, 0, 4, 0, 1, 0] := by decide
lemma F_1025 : F 1025 = [0, 0, 1, 1, 1, 0, 6, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by decide
lemma F_711 : F 711 = [0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 2, 1, 0, 1, 2, 0, 1, 1] := by decide
lemma F_1067 : F 1067 = [0, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 0] := by decide
lemma F_779 : F 779 = [0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0] := by decide
lemma F_1169 : F 1169 = [0, 0, 1, 1, 1, 0, 0, 3, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0] := by decide

lemma hm_25 : ¬ (F 25).getD 5 0 = 1 := by rw [F_25]; decide
lemma hm_19 : (F 19).getD 5 0 = 1 := by rw [F_19]; decide
lemma hm_161 : ¬ (F 161).getD 5 0 = 1 := by rw [F_161]; decide
lemma hm_121 : ¬ (F 121).getD 5 0 = 1 := by rw [F_121]; decide
lemma hm_353 : ¬ (F 353).getD 5 0 = 1 := by rw [F_353]; decide
lemma hm_265 : ¬ (F 265).getD 5 0 = 1 := by rw [F_265]; decide
lemma hm_391 : (F 391).getD 5 0 = 1 := by rw [F_391]; decide
lemma hm_587 : (F 587).getD 5 0 = 1 := by rw [F_587]; decide
lemma hm_471 : (F 471).getD 5 0 = 1 := by rw [F_471]; decide
lemma hm_707 : (F 707).getD 5 0 = 1 := by rw [F_707]; decide
lemma hm_481 : ¬ (F 481).getD 5 0 = 1 := by rw [F_481]; decide
lemma hm_361 : ¬ (F 361).getD 5 0 = 1 := by rw [F_361]; decide
lemma hm_583 : (F 583).getD 5 0 = 1 := by rw [F_583]; decide
lemma hm_875 : (F 875).getD 5 0 = 1 := by rw [F_875]; decide
lemma hm_663 : (F 663).getD 5 0 = 1 := by rw [F_663]; decide
lemma hm_995 : (F 995).getD 5 0 = 1 := by rw [F_995]; decide
lemma hm_681 : ¬ (F 681).getD 5 0 = 1 := by rw [F_681]; decide
lemma hm_511 : (F 511).getD 5 0 = 1 := by rw [F_511]; decide
lemma hm_683 : (F 683).getD 5 0 = 1 := by rw [F_683]; decide
lemma hm_1025 : ¬ (F 1025).getD 5 0 = 1 := by rw [F_1025]; decide
lemma hm_711 : (F 711).getD 5 0 = 1 := by rw [F_711]; decide
lemma hm_1067 : (F 1067).getD 5 0 = 1 := by rw [F_1067]; decide
lemma hm_779 : (F 779).getD 5 0 = 1 := by rw [F_779]; decide
lemma hm_1169 : ¬ (F 1169).getD 5 0 = 1 := by rw [F_1169]; decide

/-- 模式為位元（`boundary_step_unique` 的特徵層投影，24 端點）。 -/
lemma mode_bit_endpoints :
    ∀ n ∈ (cert.flatMap fun t => [t.1, t.2.1]),
      (F n).getD 2 0 + (F n).getD 5 0 = 1 := by decide

/-! ## §40 主定理 -/

private lemma addneg {a b : ℚ} (ha : a < 0) (hb : b < 0) : a + b < 0 := by
  have h := add_lt_add ha hb
  simpa using h

/-- **主定理（照定案敘述）**：不存在兩組非負權重使雙模式勢能在 W₁₂ 的
每一步皆嚴格下降。 -/
theorem no_go_2mode_potential :
    ¬ ∃ (θ₀ θ₁ : Fin 18 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W12,
        (if (F (Todd x)).getD 5 0 = 1 then dot θ₁ (F (Todd x)) else dot θ₀ (F (Todd x)))
          - (if (F x).getD 5 0 = 1 then dot θ₁ (F x) else dot θ₀ (F x)) < 0 := by
  rintro ⟨θ₀, θ₁, hθ₀, hθ₁, hdesc⟩
  have h1 := hdesc 25 (by decide)
  have h2 := hdesc 161 (by decide)
  have h3 := hdesc 353 (by decide)
  have h4 := hdesc 391 (by decide)
  have h5 := hdesc 471 (by decide)
  have h6 := hdesc 481 (by decide)
  have h7 := hdesc 583 (by decide)
  have h8 := hdesc 663 (by decide)
  have h9 := hdesc 681 (by decide)
  have h10 := hdesc 683 (by decide)
  have h11 := hdesc 711 (by decide)
  have h12 := hdesc 779 (by decide)
  rw [Todd_25, if_pos hm_19, if_neg hm_25] at h1
  rw [Todd_161, if_neg hm_121, if_neg hm_161] at h2
  rw [Todd_353, if_neg hm_265, if_neg hm_353] at h3
  rw [Todd_391, if_pos hm_587, if_pos hm_391] at h4
  rw [Todd_471, if_pos hm_707, if_pos hm_471] at h5
  rw [Todd_481, if_neg hm_361, if_neg hm_481] at h6
  rw [Todd_583, if_pos hm_875, if_pos hm_583] at h7
  rw [Todd_663, if_pos hm_995, if_pos hm_663] at h8
  rw [Todd_681, if_pos hm_511, if_neg hm_681] at h9
  rw [Todd_683, if_neg hm_1025, if_pos hm_683] at h10
  rw [Todd_711, if_pos hm_1067, if_pos hm_711] at h11
  rw [Todd_779, if_neg hm_1169, if_pos hm_779] at h12
  have t1 : (72 : ℚ) * (dot θ₁ (F 19) - dot θ₀ (F 25)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h1
  have t2 : (936 : ℚ) * (dot θ₀ (F 121) - dot θ₀ (F 161)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h2
  have t3 : (864 : ℚ) * (dot θ₀ (F 265) - dot θ₀ (F 353)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h3
  have t4 : (1107 : ℚ) * (dot θ₁ (F 587) - dot θ₁ (F 391)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h4
  have t5 : (1502 : ℚ) * (dot θ₁ (F 707) - dot θ₁ (F 471)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h5
  have t6 : (900 : ℚ) * (dot θ₀ (F 361) - dot θ₀ (F 481)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h6
  have t7 : (588 : ℚ) * (dot θ₁ (F 875) - dot θ₁ (F 583)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h7
  have t8 : (326 : ℚ) * (dot θ₁ (F 995) - dot θ₁ (F 663)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h8
  have t9 : (648 : ℚ) * (dot θ₁ (F 511) - dot θ₀ (F 681)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h9
  have t10 : (162 : ℚ) * (dot θ₀ (F 1025) - dot θ₁ (F 683)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h10
  have t11 : (163 : ℚ) * (dot θ₁ (F 1067) - dot θ₁ (F 711)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h11
  have t12 : (558 : ℚ) * (dot θ₀ (F 1169) - dot θ₁ (F 779)) < 0 := mul_neg_of_pos_of_neg (by norm_num) h12
  have hlt : (72 : ℚ) * (dot θ₁ (F 19) - dot θ₀ (F 25))
      + (936 : ℚ) * (dot θ₀ (F 121) - dot θ₀ (F 161))
      + (864 : ℚ) * (dot θ₀ (F 265) - dot θ₀ (F 353))
      + (1107 : ℚ) * (dot θ₁ (F 587) - dot θ₁ (F 391))
      + (1502 : ℚ) * (dot θ₁ (F 707) - dot θ₁ (F 471))
      + (900 : ℚ) * (dot θ₀ (F 361) - dot θ₀ (F 481))
      + (588 : ℚ) * (dot θ₁ (F 875) - dot θ₁ (F 583))
      + (326 : ℚ) * (dot θ₁ (F 995) - dot θ₁ (F 663))
      + (648 : ℚ) * (dot θ₁ (F 511) - dot θ₀ (F 681))
      + (162 : ℚ) * (dot θ₀ (F 1025) - dot θ₁ (F 683))
      + (163 : ℚ) * (dot θ₁ (F 1067) - dot θ₁ (F 711))
      + (558 : ℚ) * (dot θ₀ (F 1169) - dot θ₁ (F 779)) < 0 :=
    addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11) t12
  have key : (72 : ℚ) * (dot θ₁ (F 19) - dot θ₀ (F 25))
      + (936 : ℚ) * (dot θ₀ (F 121) - dot θ₀ (F 161))
      + (864 : ℚ) * (dot θ₀ (F 265) - dot θ₀ (F 353))
      + (1107 : ℚ) * (dot θ₁ (F 587) - dot θ₁ (F 391))
      + (1502 : ℚ) * (dot θ₁ (F 707) - dot θ₁ (F 471))
      + (900 : ℚ) * (dot θ₀ (F 361) - dot θ₀ (F 481))
      + (588 : ℚ) * (dot θ₁ (F 875) - dot θ₁ (F 583))
      + (326 : ℚ) * (dot θ₁ (F 995) - dot θ₁ (F 663))
      + (648 : ℚ) * (dot θ₁ (F 511) - dot θ₀ (F 681))
      + (162 : ℚ) * (dot θ₀ (F 1025) - dot θ₁ (F 683))
      + (163 : ℚ) * (dot θ₁ (F 1067) - dot θ₁ (F 711))
      + (558 : ℚ) * (dot θ₀ (F 1169) - dot θ₁ (F 779))
      = 36 * θ₀ 11 + 36 * θ₀ 15 + 36 * θ₀ 16 + 36 * θ₀ 17 + 94 * θ₁ 7 + 522 * θ₁ 8 + 527 * θ₁ 9 + 621 * θ₁ 12 := by
    rw [F_25, F_19, F_161, F_121, F_353, F_265, F_391, F_587, F_471, F_707, F_481, F_361, F_583, F_875, F_663, F_995, F_681, F_511, F_683, F_1025, F_711, F_1067, F_779, F_1169]
    simp only [dot]
    push_cast
    ring
  rw [key] at hlt
  have hge : (0 : ℚ) ≤ 36 * θ₀ 11 + 36 * θ₀ 15 + 36 * θ₀ 16 + 36 * θ₀ 17 + 94 * θ₁ 7 + 522 * θ₁ 8 + 527 * θ₁ 9 + 621 * θ₁ 12 :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hθ₀ 11)) (mul_nonneg (by norm_num) (hθ₀ 15))) (mul_nonneg (by norm_num) (hθ₀ 16))) (mul_nonneg (by norm_num) (hθ₀ 17))) (mul_nonneg (by norm_num) (hθ₁ 7))) (mul_nonneg (by norm_num) (hθ₁ 8))) (mul_nonneg (by norm_num) (hθ₁ 9))) (mul_nonneg (by norm_num) (hθ₁ 12))
  exact absurd hlt (not_lt.mpr hge)

/-- **仿射版主定理**（ROADMAP A-2；HandOver「仿射截距強健性 (Affine Offsets)」條款）：
勢能升級為 V_m(x) = β_m + θ_mᵀ F(x)，截距 `β₀ β₁` **不受非負限制**（可正可負），
非負權重的雙模式仿射勢能仍不能在 W₁₂ 的每一步嚴格下降。

證明骨架與 `no_go_2mode_potential` 完全相同（同一組 λ、同批 `Todd_*`/`hm_*` 引理、
同樣的 `if_pos`/`if_neg`）：憑證滿足模式流量平衡 Σλ(e_{m(y)} − e_{m(x)}) = [0, 0]
（`tools/certificates.py` 重算驗證），β 項在 Farkas 組合中自動抵消，
組合恆等式 `key` 的右端不變。 -/
theorem no_go_2mode_affine_potential :
    ¬ ∃ (β₀ β₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W12,
        (if (F (Todd x)).getD 5 0 = 1 then β₁ + dot θ₁ (F (Todd x))
                                       else β₀ + dot θ₀ (F (Todd x)))
          - (if (F x).getD 5 0 = 1 then β₁ + dot θ₁ (F x) else β₀ + dot θ₀ (F x)) < 0 := by
  rintro ⟨β₀, β₁, θ₀, θ₁, hθ₀, hθ₁, hdesc⟩
  have h1 := hdesc 25 (by decide)
  have h2 := hdesc 161 (by decide)
  have h3 := hdesc 353 (by decide)
  have h4 := hdesc 391 (by decide)
  have h5 := hdesc 471 (by decide)
  have h6 := hdesc 481 (by decide)
  have h7 := hdesc 583 (by decide)
  have h8 := hdesc 663 (by decide)
  have h9 := hdesc 681 (by decide)
  have h10 := hdesc 683 (by decide)
  have h11 := hdesc 711 (by decide)
  have h12 := hdesc 779 (by decide)
  rw [Todd_25, if_pos hm_19, if_neg hm_25] at h1
  rw [Todd_161, if_neg hm_121, if_neg hm_161] at h2
  rw [Todd_353, if_neg hm_265, if_neg hm_353] at h3
  rw [Todd_391, if_pos hm_587, if_pos hm_391] at h4
  rw [Todd_471, if_pos hm_707, if_pos hm_471] at h5
  rw [Todd_481, if_neg hm_361, if_neg hm_481] at h6
  rw [Todd_583, if_pos hm_875, if_pos hm_583] at h7
  rw [Todd_663, if_pos hm_995, if_pos hm_663] at h8
  rw [Todd_681, if_pos hm_511, if_neg hm_681] at h9
  rw [Todd_683, if_neg hm_1025, if_pos hm_683] at h10
  rw [Todd_711, if_pos hm_1067, if_pos hm_711] at h11
  rw [Todd_779, if_neg hm_1169, if_pos hm_779] at h12
  have t1 : (72 : ℚ) * ((β₁ + dot θ₁ (F 19)) - (β₀ + dot θ₀ (F 25))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h1
  have t2 : (936 : ℚ) * ((β₀ + dot θ₀ (F 121)) - (β₀ + dot θ₀ (F 161))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h2
  have t3 : (864 : ℚ) * ((β₀ + dot θ₀ (F 265)) - (β₀ + dot θ₀ (F 353))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h3
  have t4 : (1107 : ℚ) * ((β₁ + dot θ₁ (F 587)) - (β₁ + dot θ₁ (F 391))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h4
  have t5 : (1502 : ℚ) * ((β₁ + dot θ₁ (F 707)) - (β₁ + dot θ₁ (F 471))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h5
  have t6 : (900 : ℚ) * ((β₀ + dot θ₀ (F 361)) - (β₀ + dot θ₀ (F 481))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h6
  have t7 : (588 : ℚ) * ((β₁ + dot θ₁ (F 875)) - (β₁ + dot θ₁ (F 583))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h7
  have t8 : (326 : ℚ) * ((β₁ + dot θ₁ (F 995)) - (β₁ + dot θ₁ (F 663))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h8
  have t9 : (648 : ℚ) * ((β₁ + dot θ₁ (F 511)) - (β₀ + dot θ₀ (F 681))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h9
  have t10 : (162 : ℚ) * ((β₀ + dot θ₀ (F 1025)) - (β₁ + dot θ₁ (F 683))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h10
  have t11 : (163 : ℚ) * ((β₁ + dot θ₁ (F 1067)) - (β₁ + dot θ₁ (F 711))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h11
  have t12 : (558 : ℚ) * ((β₀ + dot θ₀ (F 1169)) - (β₁ + dot θ₁ (F 779))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h12
  have hlt : (72 : ℚ) * ((β₁ + dot θ₁ (F 19)) - (β₀ + dot θ₀ (F 25)))
      + (936 : ℚ) * ((β₀ + dot θ₀ (F 121)) - (β₀ + dot θ₀ (F 161)))
      + (864 : ℚ) * ((β₀ + dot θ₀ (F 265)) - (β₀ + dot θ₀ (F 353)))
      + (1107 : ℚ) * ((β₁ + dot θ₁ (F 587)) - (β₁ + dot θ₁ (F 391)))
      + (1502 : ℚ) * ((β₁ + dot θ₁ (F 707)) - (β₁ + dot θ₁ (F 471)))
      + (900 : ℚ) * ((β₀ + dot θ₀ (F 361)) - (β₀ + dot θ₀ (F 481)))
      + (588 : ℚ) * ((β₁ + dot θ₁ (F 875)) - (β₁ + dot θ₁ (F 583)))
      + (326 : ℚ) * ((β₁ + dot θ₁ (F 995)) - (β₁ + dot θ₁ (F 663)))
      + (648 : ℚ) * ((β₁ + dot θ₁ (F 511)) - (β₀ + dot θ₀ (F 681)))
      + (162 : ℚ) * ((β₀ + dot θ₀ (F 1025)) - (β₁ + dot θ₁ (F 683)))
      + (163 : ℚ) * ((β₁ + dot θ₁ (F 1067)) - (β₁ + dot θ₁ (F 711)))
      + (558 : ℚ) * ((β₀ + dot θ₀ (F 1169)) - (β₁ + dot θ₁ (F 779))) < 0 :=
    addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11) t12
  have key : (72 : ℚ) * ((β₁ + dot θ₁ (F 19)) - (β₀ + dot θ₀ (F 25)))
      + (936 : ℚ) * ((β₀ + dot θ₀ (F 121)) - (β₀ + dot θ₀ (F 161)))
      + (864 : ℚ) * ((β₀ + dot θ₀ (F 265)) - (β₀ + dot θ₀ (F 353)))
      + (1107 : ℚ) * ((β₁ + dot θ₁ (F 587)) - (β₁ + dot θ₁ (F 391)))
      + (1502 : ℚ) * ((β₁ + dot θ₁ (F 707)) - (β₁ + dot θ₁ (F 471)))
      + (900 : ℚ) * ((β₀ + dot θ₀ (F 361)) - (β₀ + dot θ₀ (F 481)))
      + (588 : ℚ) * ((β₁ + dot θ₁ (F 875)) - (β₁ + dot θ₁ (F 583)))
      + (326 : ℚ) * ((β₁ + dot θ₁ (F 995)) - (β₁ + dot θ₁ (F 663)))
      + (648 : ℚ) * ((β₁ + dot θ₁ (F 511)) - (β₀ + dot θ₀ (F 681)))
      + (162 : ℚ) * ((β₀ + dot θ₀ (F 1025)) - (β₁ + dot θ₁ (F 683)))
      + (163 : ℚ) * ((β₁ + dot θ₁ (F 1067)) - (β₁ + dot θ₁ (F 711)))
      + (558 : ℚ) * ((β₀ + dot θ₀ (F 1169)) - (β₁ + dot θ₁ (F 779)))
      = 36 * θ₀ 11 + 36 * θ₀ 15 + 36 * θ₀ 16 + 36 * θ₀ 17 + 94 * θ₁ 7 + 522 * θ₁ 8 + 527 * θ₁ 9 + 621 * θ₁ 12 := by
    rw [F_25, F_19, F_161, F_121, F_353, F_265, F_391, F_587, F_471, F_707, F_481, F_361, F_583, F_875, F_663, F_995, F_681, F_511, F_683, F_1025, F_711, F_1067, F_779, F_1169]
    simp only [dot]
    push_cast
    ring
  rw [key] at hlt
  have hge : (0 : ℚ) ≤ 36 * θ₀ 11 + 36 * θ₀ 15 + 36 * θ₀ 16 + 36 * θ₀ 17 + 94 * θ₁ 7 + 522 * θ₁ 8 + 527 * θ₁ 9 + 621 * θ₁ 12 :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hθ₀ 11)) (mul_nonneg (by norm_num) (hθ₀ 15))) (mul_nonneg (by norm_num) (hθ₀ 16))) (mul_nonneg (by norm_num) (hθ₀ 17))) (mul_nonneg (by norm_num) (hθ₁ 7))) (mul_nonneg (by norm_num) (hθ₁ 8))) (mul_nonneg (by norm_num) (hθ₁ 9))) (mul_nonneg (by norm_num) (hθ₁ 12))
  exact absurd hlt (not_lt.mpr hge)

/-! ## §41 回歸驗證 -/

section Verification

#eval cert.all fun t => Todd t.1 == t.2.1
#eval F 25 == [0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0]
#eval F 19 == [0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0]
#eval F 161 == [0, 0, 1, 1, 1, 0, 1, 1, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0]
#eval F 121 == [0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1]
#eval cert.all fun t => (F t.1).getD 5 0 == t.2.2.2.1 && (F t.2.1).getD 5 0 == t.2.2.2.2

end Verification

end CollatzFST.TwoMode
