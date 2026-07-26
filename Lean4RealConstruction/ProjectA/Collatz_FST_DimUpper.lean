/-
# 上界：`dim span(ΔF) ≤ 10`（ROADMAP A-3 第六步）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_FlowDelta.lean`（§53–54）。

## 這一步在做什麼

§53–54 已經有 9 條對**所有** x 成立的 `LP.ΔF` 線性關係（秩 8）。本檔把它們打包成
子模敘述，直接讀出上界——**不需要任何新的數學**，只是把已有的東西說出口：

1. `Sol`：9 條關係切出的解空間（`relMap` 的核，自動是 ℚ-子模）。
2. `dFQ_mem_Sol`：每個 `ΔF x` 都落在 `Sol` 裡（就是那 9 條）。
3. `pick`：選出 10 個**自由座標** `{2,3,6,7,8,9,10,11,15,17}`。
4. `pick_injective_on_Sol`：`pick` 限制到 `Sol` 上是單射——因為另外 8 個座標
   可以由自由座標重建（見下表），自由座標全零就迫使整個向量為零。
5. 於是 `finrank Sol ≤ finrank (Fin 10 → ℚ) = 10`，再由 `span ≤ Sol` 得到結論。

## 8 個被決定的座標怎麼重建（由 9 條解出，`tools/a3_functionals.py` 對帳）

| 座標 | 公式 |
|---|---|
| `v 0` | `0` |
| `v 1` | `0` |
| `v 4` | `v 2 + v 3` |
| `v 5` | `-v 2` |
| `v 12` | `v 7 + v 9 - v 10 - v 2` |
| `v 13` | `v 10 + v 2` |
| `v 14` | `v 10 + v 11 + v 2 - v 15` |
| `v 16` | `v 15 - v 2` |

注意 `v 5 = -v 2` 是 `dF_flow_1K0` 與 `dF_flow_2K0` 兩條相減的結果
（`v 4 = v 2 + v 3` 與 `v 3 = v 4 + v 5` ⇒ `v 2 + v 5 = 0`），
也是「9 條秩只有 8」的具體體現：`dF_flow_terminal_merged` 被其餘 8 條蘊含。

## 不在本檔範圍

**下界（≥ 10）**：要挑 10 個具體 `ΔF xᵢ` 證線性獨立（`W₁₀` 可用）。
兩件事分開做，故維度定理 `dim span(ΔF) = 10` 也留待下一步。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_FlowDelta
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace CollatzFST.Flow

open CollatzFST

/-! ## §56 ΔF 的 ℚ 座標向量與解空間 -/

/-- `ΔF x` 的 ℚ 座標向量（18 維）。 -/
def dFQ (x : ℕ) : Fin 18 → ℚ := fun i => ((LP.ΔF x).getD i 0 : ℚ)

/-- 把 §53–54 的 9 條關係寫成一個線性映射；其核就是解空間。 -/
def relMap : (Fin 18 → ℚ) →ₗ[ℚ] (Fin 9 → ℚ) where
  toFun v := ![v 0, v 1,
    v 4 - v 2 - v 3,
    v 3 - v 4 - v 5,
    v 14 + v 16 - v 10 - v 11,
    v 7 + v 9 - v 12 - v 13,
    v 11 + v 13 - v 14 - v 15,
    v 5 + v 15 - v 16,
    v 2 + v 10 + v 12 - v 7 - v 9]
  map_add' a b := by funext k; fin_cases k <;> simp <;> ring
  map_smul' c a := by funext k; fin_cases k <;> simp <;> ring

/-- 9 條關係切出的解空間。 -/
def Sol : Submodule ℚ (Fin 18 → ℚ) := LinearMap.ker relMap

lemma mem_Sol_iff (v : Fin 18 → ℚ) :
    v ∈ Sol ↔ v 0 = 0 ∧ v 1 = 0 ∧ v 4 - v 2 - v 3 = 0 ∧ v 3 - v 4 - v 5 = 0
      ∧ v 14 + v 16 - v 10 - v 11 = 0 ∧ v 7 + v 9 - v 12 - v 13 = 0
      ∧ v 11 + v 13 - v 14 - v 15 = 0 ∧ v 5 + v 15 - v 16 = 0
      ∧ v 2 + v 10 + v 12 - v 7 - v 9 = 0 := by
  constructor
  · intro h
    have h' : ∀ k, relMap v k = 0 := fun k => congrFun h k
    exact ⟨h' 0, h' 1, h' 2, h' 3, h' 4, h' 5, h' 6, h' 7, h' 8⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
    show relMap v = 0
    funext k
    fin_cases k <;> assumption

/-! ## §57 每個 ΔF 都落在解空間裡（就是 §53–54 的 9 條） -/

/-- §53–54 的 9 條，換成 `dFQ`（`Fin 18` 索引、ℚ 值）的說法。
`show` 把 `Fin` 座標的 coercion 攤成 ℕ 字面值（`rfl` 級），`exact_mod_cast` 過 ℤ→ℚ。

刻意不用 `simp`／`norm_num`：`FlowDelta` 的 18 條座標橋掛了 `@[simp]`，
一旦讓預設 simp set 上場，目標會被展開成 18 個 `occ2` 之差而變得無法閱讀。 -/
theorem dFQ_mem_Sol (x : ℕ) : dFQ x ∈ Sol := by
  have q0 : dFQ x 0 = 0 := by
    show ((LP.ΔF x).getD 0 0 : ℚ) = 0
    exact_mod_cast dF_zero_0 x
  have q1 : dFQ x 1 = 0 := by
    show ((LP.ΔF x).getD 1 0 : ℚ) = 0
    exact_mod_cast dF_zero_1 x
  have q2 : dFQ x 4 = dFQ x 2 + dFQ x 3 := by
    show ((LP.ΔF x).getD 4 0 : ℚ) = ((LP.ΔF x).getD 2 0 : ℚ) + ((LP.ΔF x).getD 3 0 : ℚ)
    exact_mod_cast dF_flow_1K0 x
  have q3 : dFQ x 3 = dFQ x 4 + dFQ x 5 := by
    show ((LP.ΔF x).getD 3 0 : ℚ) = ((LP.ΔF x).getD 4 0 : ℚ) + ((LP.ΔF x).getD 5 0 : ℚ)
    exact_mod_cast dF_flow_2K0 x
  have q4 : dFQ x 14 + dFQ x 16 = dFQ x 10 + dFQ x 11 := by
    show ((LP.ΔF x).getD 14 0 : ℚ) + ((LP.ΔF x).getD 16 0 : ℚ)
      = ((LP.ΔF x).getD 10 0 : ℚ) + ((LP.ΔF x).getD 11 0 : ℚ)
    exact_mod_cast dF_flow_1S0 x
  have q5 : dFQ x 7 + dFQ x 9 = dFQ x 12 + dFQ x 13 := by
    show ((LP.ΔF x).getD 7 0 : ℚ) + ((LP.ΔF x).getD 9 0 : ℚ)
      = ((LP.ΔF x).getD 12 0 : ℚ) + ((LP.ΔF x).getD 13 0 : ℚ)
    exact_mod_cast dF_flow_1S1 x
  have q6 : dFQ x 11 + dFQ x 13 = dFQ x 14 + dFQ x 15 := by
    show ((LP.ΔF x).getD 11 0 : ℚ) + ((LP.ΔF x).getD 13 0 : ℚ)
      = ((LP.ΔF x).getD 14 0 : ℚ) + ((LP.ΔF x).getD 15 0 : ℚ)
    exact_mod_cast dF_flow_2S0 x
  have q7 : dFQ x 5 + dFQ x 15 = dFQ x 16 := by
    show ((LP.ΔF x).getD 5 0 : ℚ) + ((LP.ΔF x).getD 15 0 : ℚ)
      = ((LP.ΔF x).getD 16 0 : ℚ)
    exact_mod_cast dF_flow_2S1 x
  have q8 : dFQ x 2 + dFQ x 10 + dFQ x 12 = dFQ x 7 + dFQ x 9 := by
    show ((LP.ΔF x).getD 2 0 : ℚ) + ((LP.ΔF x).getD 10 0 : ℚ) + ((LP.ΔF x).getD 12 0 : ℚ)
      = ((LP.ΔF x).getD 7 0 : ℚ) + ((LP.ΔF x).getD 9 0 : ℚ)
    exact_mod_cast dF_flow_terminal_merged x
  rw [mem_Sol_iff]
  refine ⟨q0, q1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## §58 自由座標的選取在解空間上是單射 -/

/-- 10 個自由座標。 -/
def freeIdx : Fin 10 → Fin 18 := ![2, 3, 6, 7, 8, 9, 10, 11, 15, 17]

/-- 選出那 10 個座標的線性映射。 -/
def pick : (Fin 18 → ℚ) →ₗ[ℚ] (Fin 10 → ℚ) := LinearMap.funLeft ℚ ℚ freeIdx

/-- **關鍵**：解空間上，10 個自由座標全零迫使整個向量為零
（其餘 8 個座標由檔頭那張表重建）。 -/
theorem pick_injective_on_Sol : Function.Injective (pick.domRestrict Sol) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨v, hv⟩ hker
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := (mem_Sol_iff v).mp hv
  have hz : ∀ j : Fin 10, v (freeIdx j) = 0 := fun j => congrFun hker j
  -- `freeIdx j` 對字面 j 是 `rfl` 級化約，故 defeq 直接取用，不必動 simp
  have f2 : v 2 = 0 := hz 0
  have f3 : v 3 = 0 := hz 1
  have f7 : v 7 = 0 := hz 3
  have f9 : v 9 = 0 := hz 5
  have f10 : v 10 = 0 := hz 6
  have f11 : v 11 = 0 := hz 7
  have f15 : v 15 = 0 := hz 8
  -- 8 個被決定的座標（檔頭那張表）
  have g0 : v 0 = 0 := h0
  have g1 : v 1 = 0 := h1
  have g4 : v 4 = 0 := by linarith
  have g5 : v 5 = 0 := by linarith
  have g13 : v 13 = 0 := by linarith
  have g16 : v 16 = 0 := by linarith
  have g14 : v 14 = 0 := by linarith
  have g12 : v 12 = 0 := by linarith
  -- 剩下兩個自由座標本身
  have f6 : v 6 = 0 := hz 2
  have f8 : v 8 = 0 := hz 4
  have f17 : v 17 = 0 := hz 9
  apply Subtype.ext
  funext i
  fin_cases i
  · exact g0
  · exact g1
  · exact f2
  · exact f3
  · exact g4
  · exact g5
  · exact f6
  · exact f7
  · exact f8
  · exact f9
  · exact f10
  · exact f11
  · exact g12
  · exact g13
  · exact g14
  · exact f15
  · exact g16
  · exact f17

/-! ## §59 上界 -/

theorem finrank_Sol_le_ten : Module.finrank ℚ Sol ≤ 10 := by
  have h := LinearMap.finrank_le_finrank_of_injective pick_injective_on_Sol
  simpa using h

/-- **上界定理**：`span(ΔF)` 至多 10 維。

`ΔF` 的每個值都滿足 §53–54 的 9 條線性關係（秩 8），故整個生成空間落在
18 − 8 = 10 維的解空間內。這一半不需要新數學——9 條關係就已經蘊含它。 -/
theorem finrank_span_dFQ_le_ten :
    Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ)) ≤ 10 :=
  le_trans
    (Submodule.finrank_mono
      (Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact dFQ_mem_Sol x)))
    finrank_Sol_le_ten

/-! ## §60 數值回歸（`#guard` 失敗即 build 紅） -/

section Verification

-- 自由座標選得對：10 個、互異、且都 < 18
#guard (List.finRange 10).map (fun j => (freeIdx j).val) == [2, 3, 6, 7, 8, 9, 10, 11, 15, 17]

end Verification

end CollatzFST.Flow
