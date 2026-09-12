/-
# 軌道回歸 no-go：三個 A 模板的無符號 2 見證版與 bounded-below 升級（**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_NoLinearRanking.lean`（單模式）、
`Collatz_FST_2Mode_Terminal_NoGo.lean`（#39，Level 2）與 `Collatz_FST_L3_2Mode_Terminal_NoGo.lean`
（#39，Level 3）。設計核准 2026-09-12（UPGRADE-DESIGN-REPORT；路線 S、裁決點 D1–D12）。

## 主張

Todd 軌道 **1787 → 2681 → 2011** 在兩步後回到**統計不可分辨**的狀態：
`F 2011 = F 1787`、`F3 2011 = F3 1787`，且終態相同（`run2`／`run3` 讀完 `extIn` 的狀態）。
於是任何以（佔用向量, 終態）為自變量的函數 Φ 都不能在 x = 1787 與 x = 2681 兩步同時嚴格下降
（**任意函數版**）——特別地，三個 A 模板（單模式線性、Level 2／3 terminal-affine 雙模式，
連同其仿射與純雙模式特例）去掉 `θ ≥ 0` 只需這 2 個見證；「V 有下界」升級是 a fortiori 系理，
不需要 gauge。與 A 既有定理的關係：`no_nonneg_linear_ranking` 需 θ ≥ 0 ＋ 10 見證，
#39 兩條需 θ ≥ 0 ＋ 17／26 見證；本檔 2 見證、零符號假設，見證集 `{1787, 2681}` 與
W₁₀／W12／W17／W20／W26 皆不相交。

## 內容

* **§O.1 軌道**：`Orbit.Todd_1787`、`Orbit.Todd_2681`（#39 血統 `padicValNat_two_pow_mul`）、見證集 `Orbit.W1787`。
* **§O.2 Level 2 單模式**（`LP`）：`F_2011_eq_F_1787`、`ΔF_1787`／`ΔF_2681`（互為負）、任意函數版
  `no_feature_ranking_orbit_1787`、`no_signed_linear_ranking`（`no_nonneg_linear_ranking` 去掉 θ ≥ 0）、
  `no_linear_ranking_bounded_below`、全稱版 `no_global_odd_signed_ranking`。
* **§O.3 Level 2 terminal-affine 雙模式**（`TwoMode`）：模板 `V2`（#39 表達式抽成定義；#39 主定理以
  `V2` 重述為 rfl 級定理）、`run2_2011_eq_run2_1787`、任意函數版、`no_go_2mode_terminal_signed`、
  `no_go_2mode_terminal_bounded_below`、全稱版、仿射（A-2）與純雙模式特例。
* **§O.4 Level 3**（`L3`）：同上以 `V3`／`F3`／`run3`／`dot48`。
* **§O.V 電池**：Todd 鏈、兩層相等式、字面（`tools/certificates.py --orbit` 的錨）、模式位、終態。

## 機制（觀察，不入定理）

2011 的位元串是 1787 的位元串把機器態 (2,S,1) 錨定的兩個閉走行對調：`111`（三個自環）與
`011`（(2,S,1) →0→ (1,S,0) →1→ (2,S,0) →1→ (2,S,1)）——佔用統計對「同錨閉走行的置換」不變，
Todd 動力學恰好在兩步內實現了這個置換（B 座標 `featList 1787 = [7,13,16,9,15, 17,17,17,16,9,15, 16,8]`、
`featList 2011 = [7,13,16,9,15, 16,9,15,17,17,17, 16,8]`；`tools/search/orbit_census.py` §2）。
這是 ROADMAP-B B5「狀態對齊＋語境封閉」的最小實例，比 B3c 的對立對 (25, 315)（同一閉走行插進
兩條走行）更強：同一條軌道回到不可分辨的統計態。x < 2¹⁶ 的軌道回歸 Level 2 有 21 個、Level 3 有 2 個
（1787、3577），最小皆 1787。

## 技術註記

1. 全檔**零歸納、零 `maxHeartbeats` 調整**；核心是四條 kernel `decide` 相等式（兩層 F 與終態）。
2. 三個模板定理都是任意函數版的實例（Φ 取模板本身）；為了可讀性各以直接改寫（`rw` ＋ `linarith`）證明。
3. 與 gauge 路線的關係：設計階段的探測顯示，模式追蹤乘積上的邊粒度雙平衡 LP（指令 R1）在池
   奇數 < 4000 上可行，但聚合 ≡ 0 的**無符號** LP 亦可行，最強形即本檔軌道——B1.5 structured gauge 的
   Collatz 消費在現有三模板上沒有非平凡實例（ROADMAP-B B1.5 收口句與覆活判準）。
4. 錨：`tools/certificates.py --orbit`（A 側 `F2`／`F3`／`run2`／`run3` 重算、Lean 字面雙向對帳、
   小普查、負向測試；CI certs job 既有一步）；大普查（x < 2¹⁶）、機制與 R1 LP 資料：
   `tools/search/orbit_census.py`（不進 CI）。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_2Mode_Terminal_NoGo
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_2Mode_Terminal_NoGo

namespace CollatzFST

/-! ## §O.1 軌道 1787 → 2681 → 2011 -/

namespace Orbit

/-- `3·1787 + 1 = 5362 = 2 · 2681`。 -/
lemma Todd_1787 : Todd 1787 = 2681 := by
  have hv : padicValNat 2 (3 * 1787 + 1) = 1 := by
    rw [show (3 * 1787 + 1 : ℕ) = 2 ^ 1 * 2681 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num

/-- `3·2681 + 1 = 8044 = 4 · 2011`。 -/
lemma Todd_2681 : Todd 2681 = 2011 := by
  have hv : padicValNat 2 (3 * 2681 + 1) = 2 := by
    rw [show (3 * 2681 + 1 : ℕ) = 2 ^ 2 * 2011 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num

/-- 兩步見證集：軌道的前兩點（`Todd 1787 = 2681`、`Todd 2681 = 2011`）。 -/
def W1787 : List ℕ := [1787, 2681]

lemma W1787_odd : ∀ x ∈ W1787, x % 2 = 1 := by decide

lemma W1787_gt_one : ∀ x ∈ W1787, 1 < x := by decide

/-- 見證集成員的逐點展開（全稱版 a fortiori 用）。 -/
lemma mem_W1787 {x : ℕ} (hx : x ∈ W1787) : x = 1787 ∨ x = 2681 := by
  simp only [W1787, List.mem_cons, List.not_mem_nil, or_false] at hx
  exact hx

end Orbit

/-! ## §O.2 Level 2 單模式（`LP.F`／`LP.ΔF`／`LP.dot`） -/

namespace LP

/-- **軌道回歸（特徵層）**：`F (T² 1787) = F 1787`（kernel `decide`，兩條 `extIn` 走行）。 -/
lemma F_2011_eq_F_1787 : F 2011 = F 1787 := by decide

/-- 可見形：`ΔF 1787 = F 2681 − F 1787`。 -/
lemma ΔF_1787 : ΔF 1787 = [0, 0, 1, 0, 1, -1, 0, 0, 1, 3, 0, -2, 2, 1, 0, -1, -2, -2] := by
  unfold ΔF
  rw [Orbit.Todd_1787]
  decide

/-- `ΔF 2681 = F 2011 − F 2681 = F 1787 − F 2681 = −ΔF 1787`（軌道回歸的差分形）。 -/
lemma ΔF_2681 : ΔF 2681 = [0, 0, -1, 0, -1, 1, 0, 0, -1, -3, 0, 2, -2, -1, 0, 1, 2, 2] := by
  unfold ΔF
  rw [Orbit.Todd_2681, F_2011_eq_F_1787]
  decide

/-- **任意函數版（單模式）**：任何以佔用向量 `F x` 為自變量的函數都不能在 1787、2681 兩步
同時嚴格下降（`F (Todd 2681) = F 1787`）。 -/
theorem no_feature_ranking_orbit_1787 :
    ¬ ∃ Φ : List ℤ → ℚ, Φ (F (Todd 1787)) < Φ (F 1787) ∧ Φ (F (Todd 2681)) < Φ (F 2681) := by
  rintro ⟨Φ, h1, h2⟩
  rw [Orbit.Todd_1787] at h1
  rw [Orbit.Todd_2681, F_2011_eq_F_1787] at h2
  linarith

/-- **無符號線性 ranking 不存在（2 見證）**：`no_nonneg_linear_ranking` 去掉 `θ ≥ 0`、見證集換為
`W1787`。證明 = `ΔF 1787 + ΔF 2681 = 0` ＋ `linarith`。 -/
theorem no_signed_linear_ranking :
    ¬ ∃ θ : Fin 18 → ℚ, ∀ x ∈ Orbit.W1787, dot θ (ΔF x) < 0 := by
  rintro ⟨θ, h⟩
  have h1 := h 1787 (by decide)
  have h2 := h 2681 (by decide)
  have key : dot θ (ΔF 1787) + dot θ (ΔF 2681) = 0 := by
    rw [ΔF_1787, ΔF_2681]
    simp only [dot]
    push_cast
    ring
  linarith

/-- **bounded-below 升級（a fortiori）**：`θᵀF` 在奇數上有下界 ∧ 兩步嚴格下降 ⟹ 矛盾——
下界假設多餘（ROADMAP-B B1「直接紅利」在單模式的最終形）。 -/
theorem no_linear_ranking_bounded_below :
    ¬ ∃ θ : Fin 18 → ℚ,
      (∃ B : ℚ, ∀ x : ℕ, x % 2 = 1 → B ≤ dot θ (F x)) ∧
      ∀ x ∈ Orbit.W1787, dot θ (ΔF x) < 0 :=
  fun ⟨θ, _, h⟩ => no_signed_linear_ranking ⟨θ, h⟩

/-- 全稱版（∀ 奇 x > 1）：`no_global_odd_ranking` 去掉 `θ ≥ 0`。 -/
theorem no_global_odd_signed_ranking :
    ¬ ∃ θ : Fin 18 → ℚ, ∀ x : ℕ, x % 2 = 1 → 1 < x → dot θ (ΔF x) < 0 := by
  rintro ⟨θ, h⟩
  exact no_signed_linear_ranking
    ⟨θ, fun x hx => h x (Orbit.W1787_odd x hx) (Orbit.W1787_gt_one x hx)⟩

end LP

/-! ## §O.3 Level 2 terminal-affine 雙模式（#39 模板） -/

namespace TwoMode

open CollatzFST.LP (dot)

/-- terminal-affine 雙模式模板（#39 主定理內的表達式抽成定義）：
`V(x) = β_{m(x), t(x)} + θ_{m(x)}ᵀ F(x)`，`m(x) = (F x).getD 5 0`、`t(x)` = 終末位。 -/
def V2 (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ) (x : ℕ) : ℚ :=
  if (F x).getD 5 0 = 1
    then (if (run2 (1, Phase.K, 0) (extIn x)).2.2 = 1 then β₁₁ else β₁₀) + dot θ₁ (F x)
    else (if (run2 (1, Phase.K, 0) (extIn x)).2.2 = 1 then β₀₁ else β₀₀) + dot θ₀ (F x)

/-- #39 主定理以 `V2` 重述（定義展開後逐字同形；讓「同一模板」在 kernel 可見）。 -/
theorem no_go_2mode_terminal_affine_potential_V2 :
    ¬ ∃ (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W17, V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ (Todd x) - V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ x < 0 :=
  no_go_2mode_terminal_affine_potential

/-- 軌道回歸（特徵層，`TwoMode.F`）。 -/
lemma F_2011_eq_F_1787 : F 2011 = F 1787 := by decide

/-- 軌道回歸（終態）：`run2` 讀完 `extIn 2011` 與 `extIn 1787` 的狀態相同（皆為 `(0,S,1)`）。 -/
lemma run2_2011_eq_run2_1787 :
    run2 (1, Phase.K, 0) (extIn 2011) = run2 (1, Phase.K, 0) (extIn 1787) := by decide

/-- 可見形（電池與 `certificates.py --orbit` 的錨）。 -/
lemma F_1787 : F 1787 = [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 3, 3] := by decide

lemma F_2681 : F 2681 = [0, 0, 1, 1, 1, 0, 0, 0, 1, 3, 1, 0, 2, 1, 0, 1, 1, 1] := by decide

/-- 模式：1787 走 (2,K,0)-b1 出口（m = 1）、2681 走 (1,K,0)-b0 出口（m = 0）。 -/
lemma hm_1787 : (F 1787).getD 5 0 = 1 := by rw [F_1787]; decide

lemma hm_2681 : ¬ (F 2681).getD 5 0 = 1 := by rw [F_2681]; decide

/-- **任意函數版**：任何以 (佔用向量, 終態) 為自變量的函數 Φ 都不能在 1787、2681 兩步同時嚴格下降
（`T² 1787 = 2011` 與 1787 在特徵層與終態不可分辨）。三個模板定理皆為此定理的實例（Φ 取模板）。 -/
theorem no_feature_ranking_orbit_1787 :
    ¬ ∃ Φ : List ℤ → (ℕ × Phase × ℕ) → ℚ,
      Φ (F (Todd 1787)) (run2 (1, Phase.K, 0) (extIn (Todd 1787)))
        < Φ (F 1787) (run2 (1, Phase.K, 0) (extIn 1787)) ∧
      Φ (F (Todd 2681)) (run2 (1, Phase.K, 0) (extIn (Todd 2681)))
        < Φ (F 2681) (run2 (1, Phase.K, 0) (extIn 2681)) := by
  rintro ⟨Φ, h1, h2⟩
  rw [Orbit.Todd_1787] at h1
  rw [Orbit.Todd_2681, F_2011_eq_F_1787, run2_2011_eq_run2_1787] at h2
  linarith

/-- 軌道回歸（模板層）：`V2 … 2011 = V2 … 1787` 對任意參數。 -/
lemma V2_2011_eq_V2_1787 (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ) :
    V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ 2011 = V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ 1787 := by
  unfold V2
  rw [F_2011_eq_F_1787, run2_2011_eq_run2_1787]

/-- **無符號 terminal-affine 雙模式 no-go（2 見證；本檔頭條）**：#39 的模板去掉 `θ ≥ 0`
（β_{m,t} 仍無符號約束），見證集換為 `W1787`。 -/
theorem no_go_2mode_terminal_signed :
    ¬ ∃ (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ),
      ∀ x ∈ Orbit.W1787,
        V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ (Todd x) - V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ x < 0 := by
  rintro ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, h⟩
  have h1 := h 1787 (by decide)
  have h2 := h 2681 (by decide)
  rw [Orbit.Todd_1787] at h1
  rw [Orbit.Todd_2681, V2_2011_eq_V2_1787] at h2
  linarith

/-- **bounded-below 升級（a fortiori；任務 (2) 的目標敘述）**：V 在奇數上有一致下界 ∧ 在 `W1787`
兩步嚴格下降 ⟹ 矛盾——下界假設多餘，gauge 不需要。語言域取全體奇數（含 x = 1；與「奇 x > 1」
等價：單一值不影響有界性）。 -/
theorem no_go_2mode_terminal_bounded_below :
    ¬ ∃ (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ),
      (∃ B : ℚ, ∀ x : ℕ, x % 2 = 1 → B ≤ V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ x) ∧
      ∀ x ∈ Orbit.W1787,
        V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ (Todd x) - V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ x < 0 :=
  fun ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, _, h⟩ =>
    no_go_2mode_terminal_signed ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, h⟩

/-- 全稱版（∀ 奇 x > 1；a fortiori）。 -/
theorem no_global_odd_2mode_terminal_signed :
    ¬ ∃ (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ),
      ∀ x : ℕ, x % 2 = 1 → 1 < x →
        V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ (Todd x) - V2 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ x < 0 := by
  rintro ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, h⟩
  exact no_go_2mode_terminal_signed
    ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, fun x hx => h x (Orbit.W1787_odd x hx) (Orbit.W1787_gt_one x hx)⟩

/-- 仿射特例（A-2 模板 `β_m + θ_mᵀF` 去掉 `θ ≥ 0`）：`V2` 取 β₀₀ = β₀₁ = β₀、β₁₀ = β₁₁ = β₁。 -/
theorem no_go_2mode_affine_signed :
    ¬ ∃ (β₀ β₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ),
      ∀ x ∈ Orbit.W1787,
        (if (F (Todd x)).getD 5 0 = 1 then β₁ + dot θ₁ (F (Todd x))
                                       else β₀ + dot θ₀ (F (Todd x)))
          - (if (F x).getD 5 0 = 1 then β₁ + dot θ₁ (F x) else β₀ + dot θ₀ (F x)) < 0 := by
  rintro ⟨β₀, β₁, θ₀, θ₁, h⟩
  refine no_go_2mode_terminal_signed ⟨β₀, β₀, β₁, β₁, θ₀, θ₁, fun x hx => ?_⟩
  simpa only [V2, ite_self] using h x hx

/-- 純雙模式特例（`no_go_2mode_potential` 的模板去掉 `θ ≥ 0`）：`V2` 取 β ≡ 0。 -/
theorem no_go_2mode_signed :
    ¬ ∃ (θ₀ θ₁ : Fin 18 → ℚ),
      ∀ x ∈ Orbit.W1787,
        (if (F (Todd x)).getD 5 0 = 1 then dot θ₁ (F (Todd x)) else dot θ₀ (F (Todd x)))
          - (if (F x).getD 5 0 = 1 then dot θ₁ (F x) else dot θ₀ (F x)) < 0 := by
  rintro ⟨θ₀, θ₁, h⟩
  refine no_go_2mode_terminal_signed ⟨0, 0, 0, 0, θ₀, θ₁, fun x hx => ?_⟩
  simpa only [V2, ite_self, zero_add] using h x hx

end TwoMode

/-! ## §O.4 Level 3 terminal-affine 雙模式（#39 L3 模板；同一軌道） -/

namespace L3

/-- Level 3 terminal-affine 雙模式模板（#39 L3 主定理內的表達式抽成定義）：
`m(x) = (F3 x).getD 33 0`、`t(x)` = 終態第三分量。 -/
def V3 (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 48 → ℚ) (x : ℕ) : ℚ :=
  if (F3 x).getD 33 0 = 1
    then (if (run3 (1, Phase.K, 0, 0) (extIn x)).2.2.1 = 1 then β₁₁ else β₁₀) + dot48 θ₁ (F3 x)
    else (if (run3 (1, Phase.K, 0, 0) (extIn x)).2.2.1 = 1 then β₀₁ else β₀₀) + dot48 θ₀ (F3 x)

/-- #39 L3 主定理以 `V3` 重述（rfl 級）。 -/
theorem no_go_level3_2mode_terminal_affine_potential_V3 :
    ¬ ∃ (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 48 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W26, V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ (Todd x) - V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ x < 0 :=
  no_go_level3_2mode_terminal_affine_potential

/-- 軌道回歸（Level 3 特徵層，48 維）。 -/
lemma F3_2011_eq_F3_1787 : F3 2011 = F3 1787 := by decide

/-- 軌道回歸（Level 3 終態）：皆為 `(0,S,0,1)`。 -/
lemma run3_2011_eq_run3_1787 :
    run3 (1, Phase.K, 0, 0) (extIn 2011) = run3 (1, Phase.K, 0, 0) (extIn 1787) := by decide

/-- 可見形（電池與錨）。 -/
lemma F3_1787 : F3 1787 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 2] := by decide

lemma F3_2681 : F3 2681 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0] := by decide

lemma hm3_1787 : (F3 1787).getD 33 0 = 1 := by rw [F3_1787]; decide

lemma hm3_2681 : ¬ (F3 2681).getD 33 0 = 1 := by rw [F3_2681]; decide

/-- **任意函數版（Level 3）**。 -/
theorem no_feature3_ranking_orbit_1787 :
    ¬ ∃ Φ : List ℤ → (ℕ × Phase × ℕ × ℕ) → ℚ,
      Φ (F3 (Todd 1787)) (run3 (1, Phase.K, 0, 0) (extIn (Todd 1787)))
        < Φ (F3 1787) (run3 (1, Phase.K, 0, 0) (extIn 1787)) ∧
      Φ (F3 (Todd 2681)) (run3 (1, Phase.K, 0, 0) (extIn (Todd 2681)))
        < Φ (F3 2681) (run3 (1, Phase.K, 0, 0) (extIn 2681)) := by
  rintro ⟨Φ, h1, h2⟩
  rw [Orbit.Todd_1787] at h1
  rw [Orbit.Todd_2681, F3_2011_eq_F3_1787, run3_2011_eq_run3_1787] at h2
  linarith

/-- 軌道回歸（模板層）。 -/
lemma V3_2011_eq_V3_1787 (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 48 → ℚ) :
    V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ 2011 = V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ 1787 := by
  unfold V3
  rw [F3_2011_eq_F3_1787, run3_2011_eq_run3_1787]

/-- **無符號 Level 3 terminal-affine 雙模式 no-go（2 見證）**。 -/
theorem no_go_level3_2mode_terminal_signed :
    ¬ ∃ (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 48 → ℚ),
      ∀ x ∈ Orbit.W1787,
        V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ (Todd x) - V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ x < 0 := by
  rintro ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, h⟩
  have h1 := h 1787 (by decide)
  have h2 := h 2681 (by decide)
  rw [Orbit.Todd_1787] at h1
  rw [Orbit.Todd_2681, V3_2011_eq_V3_1787] at h2
  linarith

/-- **bounded-below 升級（Level 3；a fortiori）**。 -/
theorem no_go_level3_2mode_terminal_bounded_below :
    ¬ ∃ (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 48 → ℚ),
      (∃ B : ℚ, ∀ x : ℕ, x % 2 = 1 → B ≤ V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ x) ∧
      ∀ x ∈ Orbit.W1787,
        V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ (Todd x) - V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ x < 0 :=
  fun ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, _, h⟩ =>
    no_go_level3_2mode_terminal_signed ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, h⟩

/-- 全稱版（∀ 奇 x > 1；a fortiori）。 -/
theorem no_global_odd_level3_2mode_terminal_signed :
    ¬ ∃ (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 48 → ℚ),
      ∀ x : ℕ, x % 2 = 1 → 1 < x →
        V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ (Todd x) - V3 β₀₀ β₀₁ β₁₀ β₁₁ θ₀ θ₁ x < 0 := by
  rintro ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, h⟩
  exact no_go_level3_2mode_terminal_signed
    ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, fun x hx => h x (Orbit.W1787_odd x hx) (Orbit.W1787_gt_one x hx)⟩

/-- 仿射特例（Level 3 A-2 模板去掉 `θ ≥ 0`）。 -/
theorem no_go_level3_2mode_affine_signed :
    ¬ ∃ (β₀ β₁ : ℚ) (θ₀ θ₁ : Fin 48 → ℚ),
      ∀ x ∈ Orbit.W1787,
        (if (F3 (Todd x)).getD 33 0 = 1 then β₁ + dot48 θ₁ (F3 (Todd x))
                                        else β₀ + dot48 θ₀ (F3 (Todd x)))
          - (if (F3 x).getD 33 0 = 1 then β₁ + dot48 θ₁ (F3 x) else β₀ + dot48 θ₀ (F3 x)) < 0 := by
  rintro ⟨β₀, β₁, θ₀, θ₁, h⟩
  refine no_go_level3_2mode_terminal_signed ⟨β₀, β₀, β₁, β₁, θ₀, θ₁, fun x hx => ?_⟩
  simpa only [V3, ite_self] using h x hx

/-- 純雙模式特例（`no_go_level3_2mode_potential` 的模板去掉 `θ ≥ 0`）。 -/
theorem no_go_level3_2mode_signed :
    ¬ ∃ (θ₀ θ₁ : Fin 48 → ℚ),
      ∀ x ∈ Orbit.W1787,
        (if (F3 (Todd x)).getD 33 0 = 1 then dot48 θ₁ (F3 (Todd x)) else dot48 θ₀ (F3 (Todd x)))
          - (if (F3 x).getD 33 0 = 1 then dot48 θ₁ (F3 x) else dot48 θ₀ (F3 x)) < 0 := by
  rintro ⟨θ₀, θ₁, h⟩
  refine no_go_level3_2mode_terminal_signed ⟨0, 0, 0, 0, θ₀, θ₁, fun x hx => ?_⟩
  simpa only [V3, ite_self, zero_add] using h x hx

end L3

/-! ## §O.V 數據驗證（全部應輸出 `true`）

字面即 `tools/certificates.py --orbit` 的錨（`LEAN_ORBIT_*`）。 -/

section Verification

-- 1 Todd 鏈
#eval [1787, 2681].map Todd == [2681, 2011]
-- 2–3 兩層特徵回歸
#eval TwoMode.F 2011 == TwoMode.F 1787
#eval L3.F3 2011 == L3.F3 1787
-- 4–5 兩層終態回歸
#eval run2 (1, Phase.K, 0) (extIn 2011) == run2 (1, Phase.K, 0) (extIn 1787)
#eval L3.run3 (1, Phase.K, 0, 0) (extIn 2011) == L3.run3 (1, Phase.K, 0, 0) (extIn 1787)
-- 6–9 字面（錨）
#eval TwoMode.F 1787 == [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 3, 3]
#eval TwoMode.F 2681 == [0, 0, 1, 1, 1, 0, 0, 0, 1, 3, 1, 0, 2, 1, 0, 1, 1, 1]
#eval L3.F3 1787 == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 2]
#eval L3.F3 2681 == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0]
-- 10–11 模式位（兩層一致：1787 ↦ 1、2681 ↦ 0）
#eval (TwoMode.F 1787).getD 5 0 == 1 && (TwoMode.F 2681).getD 5 0 == 0
#eval (L3.F3 1787).getD 33 0 == 1 && (L3.F3 2681).getD 33 0 == 0
-- 12–13 終態
#eval run2 (1, Phase.K, 0) (extIn 1787) == (0, Phase.S, 1) && run2 (1, Phase.K, 0) (extIn 2681) == (0, Phase.S, 0)
#eval L3.run3 (1, Phase.K, 0, 0) (extIn 1787) == (0, Phase.S, 0, 1) && L3.run3 (1, Phase.K, 0, 0) (extIn 2681) == (0, Phase.S, 1, 0)
-- 14 單模式差分互為負（LP.ΔF）
#eval (LP.ΔF 1787).zipWith (· + ·) (LP.ΔF 2681) == List.replicate 18 0
-- 15 見證集在域內、與既有見證集不相交
#eval Orbit.W1787.all (fun x => x % 2 == 1 && 1 < x)
  && Orbit.W1787.all (fun x => !(LP.W₁₀.contains x) && !(TwoMode.W12.contains x)
      && !(TwoMode.W17.contains x) && !(L3.W20.contains x) && !(L3.W26.contains x))
-- 16 單步不回歸（軌道回歸是兩步現象）
#eval TwoMode.F 2681 != TwoMode.F 1787 && L3.F3 2681 != L3.F3 1787

end Verification

end CollatzFST
