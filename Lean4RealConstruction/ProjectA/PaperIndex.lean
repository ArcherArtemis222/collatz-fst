/-
# PaperIndex：論文定理重述層（A-4）

本檔由 tools/gen_paper_index.py 從 paper/registry.yaml 生成——**不要手改**。
CI 以 regeneration + `git diff --exit-code` 強制逐位一致（guard.yml certs job）。

每條 `Paper.<id>` 的型別是 registry 的人工快照，`:= @<原定理>` 由 kernel
檢查快照與原定理相容。原定理被改到不相容 ⇒ 本檔編譯失敗 ⇒ 修 registry，
該 PR 標【敘述變更】（AGENTS §2.6 [statement change]）。
-/
import Lean4RealConstruction.Core.Collatz_FST_Ext
import Lean4RealConstruction.Core.Collatz_FST_Level2
import Lean4RealConstruction.Core.Collatz_FST_Statements
import Lean4RealConstruction.ProjectA.Collatz_FST_2Mode_NoGo
import Lean4RealConstruction.ProjectA.Collatz_FST_DimLower
import Lean4RealConstruction.ProjectA.Collatz_FST_Flow
import Lean4RealConstruction.ProjectA.Collatz_FST_FlowDelta
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_2Mode_NoGo
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_Delta
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_DimLower
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_Flow
import Lean4RealConstruction.ProjectA.Collatz_FST_NoLinearRanking

-- 本檔只有型別重述（無證明項），binder 名逐字承自原敘述、純屬文件；
-- unusedVariables 對重述層無意義，全檔關閉。
set_option linter.unusedVariables false

namespace Paper

open CollatzFST

/-- Paper ref: boundary-step-unique（`CollatzFST.boundary_step_unique`） -/
theorem boundary_step_unique :
    ∀ (x : ℕ),
      (microTrace2 (1, Phase.K, 0) (extIn x)).countP
          (fun t => t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1) = 1 :=
  @CollatzFST.boundary_step_unique

/-- Paper ref: dim-l2-eq-10（`CollatzFST.Flow.finrank_span_dFQ_eq_ten`） -/
theorem dim_l2_eq_10 :
    Module.finrank ℚ (Submodule.span ℚ (Set.range Flow.dFQ)) = 10 :=
  @CollatzFST.Flow.finrank_span_dFQ_eq_ten

/-- Paper ref: dim-l3-eq-31（`CollatzFST.L3.finrank_span_dFQ96_eq_31`） -/
theorem dim_l3_eq_31 :
    Module.finrank ℚ (Submodule.span ℚ (Set.range L3.dFQ96)) = 31 :=
  @CollatzFST.L3.finrank_span_dFQ96_eq_31

/-- Paper ref: flow-2k0-alternating（`CollatzFST.Flow.dF_flow_2K0`） -/
theorem flow_2k0_alternating :
    ∀ (x : ℕ), (LP.ΔF x).getD 3 0 = (LP.ΔF x).getD 4 0 + (LP.ΔF x).getD 5 0 :=
  @CollatzFST.Flow.dF_flow_2K0

/-- Paper ref: flow-kirchhoff-l2（`CollatzFST.Flow.kirchhoff_occ2`） -/
theorem flow_kirchhoff_l2 :
    ∀ (g : ℕ × Phase × ℕ) {s : ℕ × Phase × ℕ} (hs : s ∈ S8)
        {w : List ℕ} (hw : ∀ b ∈ w, b < 2),
      ((Flow.inEdges g).map (fun e => occ2 s w e)).sum + (if s = g then 1 else 0)
        = occ2 s w (g, 0) + occ2 s w (g, 1) + (if run2 s w = g then 1 else 0) :=
  @CollatzFST.Flow.kirchhoff_occ2

/-- Paper ref: fstart-l3-crossblock（`CollatzFST.L3.dF96_fstart`） -/
theorem fstart_l3_crossblock :
    ∀ (x : ℕ),
      (L3.dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
          - L3.dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
          - L3.dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1))
        + (L3.dF96 x 1 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
          - L3.dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
          - L3.dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1)) = 0 :=
  @CollatzFST.L3.dF96_fstart

/-- Paper ref: mode-bit-sum-l3（`CollatzFST.L3.occ3_mode_bit_sum`） -/
theorem mode_bit_sum_l3 :
    ∀ (x : ℕ),
      L3.occ3 (1, Phase.K, 0, 0) (extIn x) (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
        + L3.occ3 (1, Phase.K, 0, 0) (extIn x) (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 1 :=
  @CollatzFST.L3.occ3_mode_bit_sum

/-- Paper ref: nogo-l2-2mode-affine（`CollatzFST.TwoMode.no_go_2mode_affine_potential`） -/
theorem nogo_l2_2mode_affine :
    ¬ ∃ (β₀ β₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ TwoMode.W12,
        (if (TwoMode.F (Todd x)).getD 5 0 = 1 then β₁ + LP.dot θ₁ (TwoMode.F (Todd x))
                                       else β₀ + LP.dot θ₀ (TwoMode.F (Todd x)))
          - (if (TwoMode.F x).getD 5 0 = 1 then β₁ + LP.dot θ₁ (TwoMode.F x) else β₀ + LP.dot θ₀ (TwoMode.F x)) < 0 :=
  @CollatzFST.TwoMode.no_go_2mode_affine_potential

/-- Paper ref: nogo-l2-2mode-universal（`CollatzFST.TwoMode.no_global_odd_2mode_potential`） -/
theorem nogo_l2_2mode_universal :
    ¬ ∃ (θ₀ θ₁ : Fin 18 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x : ℕ, x % 2 = 1 → 1 < x →
        (if (TwoMode.F (Todd x)).getD 5 0 = 1 then LP.dot θ₁ (TwoMode.F (Todd x)) else LP.dot θ₀ (TwoMode.F (Todd x)))
          - (if (TwoMode.F x).getD 5 0 = 1 then LP.dot θ₁ (TwoMode.F x) else LP.dot θ₀ (TwoMode.F x)) < 0 :=
  @CollatzFST.TwoMode.no_global_odd_2mode_potential

/-- Paper ref: nogo-l2-2mode-witness（`CollatzFST.TwoMode.no_go_2mode_potential`） -/
theorem nogo_l2_2mode_witness :
    ¬ ∃ (θ₀ θ₁ : Fin 18 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ TwoMode.W12,
        (if (TwoMode.F (Todd x)).getD 5 0 = 1 then LP.dot θ₁ (TwoMode.F (Todd x)) else LP.dot θ₀ (TwoMode.F (Todd x)))
          - (if (TwoMode.F x).getD 5 0 = 1 then LP.dot θ₁ (TwoMode.F x) else LP.dot θ₀ (TwoMode.F x)) < 0 :=
  @CollatzFST.TwoMode.no_go_2mode_potential

/-- Paper ref: nogo-l2-single-universal（`CollatzFST.LP.no_global_odd_ranking`） -/
theorem nogo_l2_single_universal :
    ¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧
      ∀ x : ℕ, x % 2 = 1 → 1 < x → LP.dot θ (LP.ΔF x) < 0 :=
  @CollatzFST.LP.no_global_odd_ranking

/-- Paper ref: nogo-l2-single-witness（`CollatzFST.LP.no_nonneg_linear_ranking`） -/
theorem nogo_l2_single_witness :
    ¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧ ∀ x ∈ LP.W₁₀, LP.dot θ (LP.ΔF x) < 0 :=
  @CollatzFST.LP.no_nonneg_linear_ranking

/-- Paper ref: nogo-l3-2mode-affine（`CollatzFST.L3.no_go_level3_2mode_affine_potential`） -/
theorem nogo_l3_2mode_affine :
    ¬ ∃ (β₀ β₁ : ℚ) (θ₀ θ₁ : Fin 48 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ L3.W20,
        (if (L3.F3 (Todd x)).getD 33 0 = 1 then β₁ + L3.dot48 θ₁ (L3.F3 (Todd x))
                                        else β₀ + L3.dot48 θ₀ (L3.F3 (Todd x)))
          - (if (L3.F3 x).getD 33 0 = 1 then β₁ + L3.dot48 θ₁ (L3.F3 x) else β₀ + L3.dot48 θ₀ (L3.F3 x)) < 0 :=
  @CollatzFST.L3.no_go_level3_2mode_affine_potential

/-- Paper ref: nogo-l3-2mode-universal（`CollatzFST.L3.no_global_odd_level3_2mode_potential`） -/
theorem nogo_l3_2mode_universal :
    ¬ ∃ (θ₀ θ₁ : Fin 48 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x : ℕ, x % 2 = 1 → 1 < x →
        (if (L3.F3 (Todd x)).getD 33 0 = 1 then L3.dot48 θ₁ (L3.F3 (Todd x)) else L3.dot48 θ₀ (L3.F3 (Todd x)))
          - (if (L3.F3 x).getD 33 0 = 1 then L3.dot48 θ₁ (L3.F3 x) else L3.dot48 θ₀ (L3.F3 x)) < 0 :=
  @CollatzFST.L3.no_global_odd_level3_2mode_potential

/-- Paper ref: nogo-l3-2mode-witness（`CollatzFST.L3.no_go_level3_2mode_potential`） -/
theorem nogo_l3_2mode_witness :
    ¬ ∃ (θ₀ θ₁ : Fin 48 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ L3.W20,
        (if (L3.F3 (Todd x)).getD 33 0 = 1 then L3.dot48 θ₁ (L3.F3 (Todd x)) else L3.dot48 θ₀ (L3.F3 (Todd x)))
          - (if (L3.F3 x).getD 33 0 = 1 then L3.dot48 θ₁ (L3.F3 x) else L3.dot48 θ₀ (L3.F3 x)) < 0 :=
  @CollatzFST.L3.no_go_level3_2mode_potential

/-- Paper ref: terminal-l2（`CollatzFST.Flow.run2_extIn_terminal`） -/
theorem terminal_l2 :
    ∀ (x : ℕ),
      run2 (1, Phase.K, 0) (extIn x) = ((0 : ℕ), Phase.S, (0 : ℕ))
        ∨ run2 (1, Phase.K, 0) (extIn x) = ((0 : ℕ), Phase.S, (1 : ℕ)) :=
  @CollatzFST.Flow.run2_extIn_terminal

/-- Paper ref: terminal-l3（`CollatzFST.L3.run3_extIn_terminal`） -/
theorem terminal_l3 :
    ∀ (x : ℕ),
      L3.run3 (1, Phase.K, 0, 0) (extIn x) = ((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ))
        ∨ L3.run3 (1, Phase.K, 0, 0) (extIn x) = ((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) :=
  @CollatzFST.L3.run3_extIn_terminal

/-- Paper ref: todd-eq-dropwhile（`CollatzFST.Todd_eq_dropWhile`） -/
theorem todd_eq_dropwhile :
    ∀ (x : ℕ), Nat.ofDigits 2 ((transduce x).dropWhile (· = 0)) = Todd x :=
  @CollatzFST.Todd_eq_dropWhile

/-- Paper ref: transducer-soundness（`CollatzFST.ofDigits_transduce`） -/
theorem transducer_soundness :
    ∀ (x : ℕ), Nat.ofDigits 2 (transduce x) = 3 * x + 1 :=
  @CollatzFST.ofDigits_transduce

/-- Paper ref: transducer-split（`CollatzFST.transduce_split`） -/
theorem transducer_split :
    ∀ (x : ℕ),
      transduce x
        = List.replicate (padicValNat 2 (3 * x + 1)) 0 ++ (transduce x).dropWhile (· = 0) :=
  @CollatzFST.transduce_split

/-- Paper ref: valuation-alt-prefix（`CollatzFST.padicValNat_eq_altPrefixLen`） -/
theorem valuation_alt_prefix :
    ∀ (x : ℕ), padicValNat 2 (3 * x + 1) = altPrefixLen x :=
  @CollatzFST.padicValNat_eq_altPrefixLen

end Paper
