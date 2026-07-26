/-
# 下界與維度定理：`dim span(ΔF) = 10`（ROADMAP A-3 第七步，A-3 收尾）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_DimUpper.lean`（§56–59）。

## 這一步在做什麼

上界 `≤ 10` 已由 9 條流守恆關係給出（`finrank_span_dFQ_le_ten`）。剩下的是下界：
挑 10 個具體的 `ΔF xᵢ` 證線性獨立。見證集直接用現成的
`W₁₀ = [231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511]`——
也就是 `no_nonneg_linear_ranking` 那組 Farkas 見證，不必另外搜。

判準的關鍵是**投影到 §58 那 10 個自由座標** `{2,3,6,7,8,9,10,11,15,17}`：
在那 10 個座標上，10 條 `ΔF` 構成的 10×10 矩陣可逆，於是 10 條在 18 維裡也獨立
（任何線性映射都保持相依關係，故投影後獨立 ⇒ 原本獨立）。

這正是 `pick` 的複用：`pick_injective_on_Sol` 說那組座標在解空間上不丟資訊，
所以「投影後仍獨立」不是巧合——`ΔF` 全落在 `Sol` 裡，投影是單射。

## 那個 31 不是巧合（Cramer）

10×10 矩陣的行列式是 **31**，與 Farkas 憑證的 `Σλ·ΔF = 31·e₇`（見
`Collatz_FST_NoLinearRanking.lean` §35）是同一個 31，而且有原因：

λ 垂直於 9 個「被湮滅」的座標列，故在相差尺度下唯一；由 Cramer，
**λ = adj(A_free) 的第 2 列**（實測完全吻合 `[100, 64, 119, 51, 56, 183, 164, 18, 191, 78]`），
而 `31 = det(A_free)`。該列 gcd = 1（本原），所以最小整數尺度必然就是 `|det| = 31`
——這也回答了「為什麼 `t = 31` 剛好解回整數」。

驗算與一般形式（含雙模式、gcd ≠ 1 的情形）見 `docs/ROADMAP-A.md` A-4 與
`python3 tools/certificates.py --cramer`。注意 `Σλ = 1024` **不是**行列式。

## 主定理

`finrank_span_dFQ_eq_ten : Module.finrank ℚ (span ℚ (Set.range dFQ)) = 10`

即 HandOver「Level 2 差分空間 = 精確的 10 維有理線性子空間」的形式化。

## 注意：不要在本檔用 `simp` / `norm_num` 碰 `LP.ΔF x`

`FlowDelta` 的 18 條座標橋掛在全域 simp set 上。本檔的做法是**先**用
`LP.ΔF_231` 等把 `LP.ΔF` 換成字面串列——換完之後式子裡沒有 `LP.ΔF` 了，
座標橋無從匹配，`norm_num` 才安全。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_DimUpper

namespace CollatzFST.Flow

open CollatzFST

/-! ## §61 W₁₀ 的 10 條 ΔF 的 ℚ 座標字面值

每條都由 `Collatz_FST_NoLinearRanking.lean` §34 已證的 `LP.ΔF_xxx` 直接得出。 -/

lemma dFQ_231 : dFQ 231 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 3, 0, -1, 2, 0, 0, -1] := by
  funext j; simp only [dFQ, LP.ΔF_231]; fin_cases j <;> norm_num
lemma dFQ_323 : dFQ 323 = ![0, 0, 1, 1, 2, -1, -1, -1, -2, 0, 0, 0, -2, 1, 0, 1, 0, 1] := by
  funext j; simp only [dFQ, LP.ΔF_323]; fin_cases j <;> norm_num
lemma dFQ_403 : dFQ 403 = ![0, 0, 0, 1, 1, 0, 0, -1, 0, 0, -1, 1, 0, -1, 0, 0, 0, 1] := by
  funext j; simp only [dFQ, LP.ΔF_403]; fin_cases j <;> norm_num
lemma dFQ_551 : dFQ 551 = ![0, 0, 0, 0, 0, 0, -1, -1, -2, 0, 1, 1, -2, 1, 1, 1, 1, 0] := by
  funext j; simp only [dFQ, LP.ΔF_551]; fin_cases j <;> norm_num
lemma dFQ_681 : dFQ 681 = ![0, 0, -1, 0, -1, 1, 0, 0, -1, -4, 1, 0, -4, 0, 0, 0, 1, 7] := by
  funext j; simp only [dFQ, LP.ΔF_681]; fin_cases j <;> norm_num
lemma dFQ_877 : dFQ 877 = ![0, 0, 1, -1, 0, -1, 0, 1, 2, 2, -1, -2, 3, 0, 0, -2, -3, 0] := by
  funext j; simp only [dFQ, LP.ΔF_877]; fin_cases j <;> norm_num
lemma dFQ_983 : dFQ 983 = ![0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, -1, 0, 1, 0, 0, 0, -3] := by
  funext j; simp only [dFQ, LP.ΔF_983]; fin_cases j <;> norm_num
lemma dFQ_1079 : dFQ 1079 = ![0, 0, 0, 0, 0, 0, -1, 0, -1, 2, 1, -1, 1, 1, 1, -1, -1, -1] := by
  funext j; simp only [dFQ, LP.ΔF_1079]; fin_cases j <;> norm_num
lemma dFQ_1305 : dFQ 1305 = ![0, 0, -1, 0, -1, 1, 0, -1, -2, 0, 1, 0, -1, 0, -1, 1, 2, 1] := by
  funext j; simp only [dFQ, LP.ΔF_1305]; fin_cases j <;> norm_num
lemma dFQ_1511 : dFQ 1511 = ![0, 0, 0, 0, 0, 0, 0, 1, 2, -1, -1, 1, 1, -1, -1, 1, 1, -2] := by
  funext j; simp only [dFQ, LP.ΔF_1511]; fin_cases j <;> norm_num

/-- `W₁₀` 的 10 條 ΔF（ℚ 版），依 `W₁₀` 的順序。 -/
def dFW : Fin 10 → (Fin 18 → ℚ) :=
  ![dFQ 231, dFQ 323, dFQ 403, dFQ 551, dFQ 681,
    dFQ 877, dFQ 983, dFQ 1079, dFQ 1305, dFQ 1511]

/-! ## §62 下界：10 條線性獨立 -/

/-- `Fin 10` 上的和展開成 10 項、索引為字面數字。
（Mathlib 只到 `Fin.succ_one_eq_two`，直接用 `Fin.sum_univ_succ` 會留下
`Fin.succ 2` 之類的形式，`linarith` 會把它們當成不同原子。） -/
private lemma sum_fin_ten (f : Fin 10 → ℚ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp [Fin.sum_univ_succ]; ring

/-- **10 條 ΔF 線性獨立**。證法：假設有零組合，逐一取 §58 那 10 個自由座標
（`{2,3,6,7,8,9,10,11,15,17}`）得到 10 條係數方程；該 10×10 矩陣可逆
（行列式 31），故每個係數為零。 -/
theorem dFW_linearIndependent : LinearIndependent ℚ dFW := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e : ∀ j : Fin 18, ∑ i : Fin 10, g i * dFW i j = 0 := by
    intro j
    have h := congrFun hg j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have h2 := e 2
  have h3 := e 3
  have h6 := e 6
  have h7 := e 7
  have h8 := e 8
  have h9 := e 9
  have h10 := e 10
  have h11 := e 11
  have h15 := e 15
  have h17 := e 17
  rw [sum_fin_ten] at h2 h3 h6 h7 h8 h9 h10 h11 h15 h17
  -- `dFQ_xxx` 把每條換成字面向量後，式子裡已經沒有 `LP.ΔF`，
  -- 座標橋（`FlowDelta` 的 18 條 `@[simp]`）無從匹配，此時全域 `simp` 是安全的。
  simp [dFW, dFQ_231, dFQ_323, dFQ_403, dFQ_551, dFQ_681, dFQ_877, dFQ_983,
    dFQ_1079, dFQ_1305, dFQ_1511] at h2 h3 h6 h7 h8 h9 h10 h11 h15 h17
  have g0 : g 0 = 0 := by linarith
  have g1 : g 1 = 0 := by linarith
  have g2 : g 2 = 0 := by linarith
  have g3 : g 3 = 0 := by linarith
  have g4 : g 4 = 0 := by linarith
  have g5 : g 5 = 0 := by linarith
  have g6 : g 6 = 0 := by linarith
  have g7 : g 7 = 0 := by linarith
  have g8 : g 8 = 0 := by linarith
  have g9 : g 9 = 0 := by linarith
  intro i
  fin_cases i <;> assumption

theorem dFW_mem_range (i : Fin 10) : dFW i ∈ Set.range dFQ := by
  fin_cases i
  · exact ⟨231, rfl⟩
  · exact ⟨323, rfl⟩
  · exact ⟨403, rfl⟩
  · exact ⟨551, rfl⟩
  · exact ⟨681, rfl⟩
  · exact ⟨877, rfl⟩
  · exact ⟨983, rfl⟩
  · exact ⟨1079, rfl⟩
  · exact ⟨1305, rfl⟩
  · exact ⟨1511, rfl⟩

/-- **下界**：`10 ≤ dim span(ΔF)`。 -/
theorem ten_le_finrank_span_dFQ :
    10 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ)) := by
  have hcard : Module.finrank ℚ (Submodule.span ℚ (Set.range dFW)) = 10 := by
    simpa using finrank_span_eq_card dFW_linearIndependent
  have hle : Submodule.span ℚ (Set.range dFW) ≤ Submodule.span ℚ (Set.range dFQ) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact dFW_mem_range i)
  calc (10 : ℕ) = Module.finrank ℚ (Submodule.span ℚ (Set.range dFW)) := hcard.symm
    _ ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ)) := Submodule.finrank_mono hle

/-! ## §63 維度定理 -/

/-- **維度定理**：Level 2 特徵差分空間恰為 **10 維**有理線性子空間。

這是 HandOver「維度精確化 (Dimensionality)」第一條主張的形式化：
上界來自 9 條 Kirchhoff 流守恆關係（秩 8，`finrank_span_dFQ_le_ten`），
下界來自 `W₁₀` 的 10 條 ΔF 線性獨立（`ten_le_finrank_span_dFQ`）。 -/
theorem finrank_span_dFQ_eq_ten :
    Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ)) = 10 :=
  le_antisymm finrank_span_dFQ_le_ten ten_le_finrank_span_dFQ

/-! ## §64 數值回歸（`#guard` 失敗即 build 紅）

釘住上面 10 條字面值：它們是本檔唯一手抄的數字。 -/

section Verification

#guard (LP.W₁₀.map LP.ΔF) ==
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 3, 0, -1, 2, 0, 0, -1],
   [0, 0, 1, 1, 2, -1, -1, -1, -2, 0, 0, 0, -2, 1, 0, 1, 0, 1],
   [0, 0, 0, 1, 1, 0, 0, -1, 0, 0, -1, 1, 0, -1, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, -1, -1, -2, 0, 1, 1, -2, 1, 1, 1, 1, 0],
   [0, 0, -1, 0, -1, 1, 0, 0, -1, -4, 1, 0, -4, 0, 0, 0, 1, 7],
   [0, 0, 1, -1, 0, -1, 0, 1, 2, 2, -1, -2, 3, 0, 0, -2, -3, 0],
   [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, -1, 0, 1, 0, 0, 0, -3],
   [0, 0, 0, 0, 0, 0, -1, 0, -1, 2, 1, -1, 1, 1, 1, -1, -1, -1],
   [0, 0, -1, 0, -1, 1, 0, -1, -2, 0, 1, 0, -1, 0, -1, 1, 2, 1],
   [0, 0, 0, 0, 0, 0, 0, 1, 2, -1, -1, 1, 1, -1, -1, 1, 1, -2]]

end Verification

end CollatzFST.Flow
