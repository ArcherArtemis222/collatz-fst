/-
# 差分層泛函：A-3 上界的 9 條關係落到 `LP.ΔF` 上（ROADMAP A-3 第五步）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_Flow.lean`（§51）
與 `Collatz_FST_NoLinearRanking.lean`（`LP.KEYS` / `LP.F` / `LP.ΔF`）。

## 這一步在做什麼

§51 的 `kirchhoff_occ2_extIn_clean` / `_merged` 是「對每個 x 的常數關係」，
形狀是 `Σ occ2(入邊) + [初始指示] = Σ occ2(出邊)`。要變成 `LP.ΔF` 上的泛函，
對 `x` 與 `Todd x` 各用一次再相減——**初始指示兩邊相同，於是對消**，
剩下純粹的 ΔF 座標線性恆等式。

`Todd x` 不需要任何奇偶假設：§51 的兩條對 `∀ x : ℕ` 成立
（`extIn_bits` 對所有 ℕ 都給位元界，終末狀態定理也是全稱的），
所以本檔的 9 條同樣對**所有** x 成立，不限奇數。

## 9 條關係的清單（秩 8；座標用 0-based，ROADMAP 的 e-記法是 1-based，差 1）

| 來源 | 差分層恆等式 |
|---|---|
| 死狀態 (0,K,0) b=0 | `ΔF₀ = 0` |
| 死狀態 (0,K,0) b=1 | `ΔF₁ = 0` |
| flow (1,K,0) | `ΔF₄ = ΔF₂ + ΔF₃` |
| flow (2,K,0) | `ΔF₃ = ΔF₄ + ΔF₅` ← 即 ROADMAP 舊表的「K 區交錯 e₄ = e₅ + e₆」 |
| flow (1,S,0) | `ΔF₁₄ + ΔF₁₆ = ΔF₁₀ + ΔF₁₁` |
| flow (1,S,1) | `ΔF₇ + ΔF₉ = ΔF₁₂ + ΔF₁₃` |
| flow (2,S,0) | `ΔF₁₁ + ΔF₁₃ = ΔF₁₄ + ΔF₁₅` |
| flow (2,S,1) | `ΔF₅ + ΔF₁₅ = ΔF₁₆`（兩側的 ΔF₁₇ 已對消） |
| flow 合併終末 | `ΔF₂ + ΔF₁₀ + ΔF₁₂ = ΔF₇ + ΔF₉`（ΔF₆、ΔF₈ 已對消） |

死狀態 2 條 + 流守恆 7 條，秩 8 = 18 − dim span(ΔF)，由
`tools/a3_functionals.py` 精確有理秩驗算（該腳本在 CI 每次 push 跑）。
「K 區交錯」那條在此可以看得很清楚：它就是狀態 (2,K,0) 的流守恆，
不是額外需要的引理。

## 不在本檔範圍

把這 9 條打包成係數向量並論證秩 = 8、下界的 10×10 行列式、
以及維度定理本身（`dim span(ΔF) = 10`）。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_SimpAttr
import Lean4RealConstruction.ProjectA.Collatz_FST_Flow
import Lean4RealConstruction.ProjectA.Collatz_FST_NoLinearRanking

namespace CollatzFST.Flow

open CollatzFST

/-! ## §52 座標橋：ΔF 的每一格就是端點 `occ2` 之差

`LP.KEYS` 是閉項，故 `LP.F x` 化約成 18 元字面串列、`LP.ΔF x` 化約成逐格相減，
每條橋都是 `rfl`。有了它們，§51 的 ℕ 等式與 ΔF 的 ℤ 座標可以直接交給 `omega`。

這 18 條掛在**具名** simp set `coord_bridge`（宣告見 `Collatz_FST_SimpAttr.lean`），
**不參與全域 simp**：要展開時明確寫 `simp [coord_bridge]`，不想展開時
`simp` / `norm_num` 碰不到它們。原本掛全域 `@[simp]` 的版本會讓任何用到 `simp`
的證明突然多出 18 個 `occ2` 差的算式——`DimUpper` 與 `DimLower` 兩個 PR 都為此
繞過 `simp`，第二次繞道就是該改的訊號。 -/

/-- 端點特徵：`E x k = occ2 (1,K,0) (extIn x) k`（取 ℤ 值）。 -/
def E (x : ℕ) (k : (ℕ × Phase × ℕ) × ℕ) : ℤ := (occ2 (1, Phase.K, 0) (extIn x) k : ℤ)

@[coord_bridge] lemma dF_00 (x : ℕ) : (LP.ΔF x).getD 0 0
    = E (Todd x) (((0 : ℕ), Phase.K, (0 : ℕ)), 0) - E x (((0 : ℕ), Phase.K, (0 : ℕ)), 0) := rfl
@[coord_bridge] lemma dF_01 (x : ℕ) : (LP.ΔF x).getD 1 0
    = E (Todd x) (((0 : ℕ), Phase.K, (0 : ℕ)), 1) - E x (((0 : ℕ), Phase.K, (0 : ℕ)), 1) := rfl
@[coord_bridge] lemma dF_02 (x : ℕ) : (LP.ΔF x).getD 2 0
    = E (Todd x) (((1 : ℕ), Phase.K, (0 : ℕ)), 0) - E x (((1 : ℕ), Phase.K, (0 : ℕ)), 0) := rfl
@[coord_bridge] lemma dF_03 (x : ℕ) : (LP.ΔF x).getD 3 0
    = E (Todd x) (((1 : ℕ), Phase.K, (0 : ℕ)), 1) - E x (((1 : ℕ), Phase.K, (0 : ℕ)), 1) := rfl
@[coord_bridge] lemma dF_04 (x : ℕ) : (LP.ΔF x).getD 4 0
    = E (Todd x) (((2 : ℕ), Phase.K, (0 : ℕ)), 0) - E x (((2 : ℕ), Phase.K, (0 : ℕ)), 0) := rfl
@[coord_bridge] lemma dF_05 (x : ℕ) : (LP.ΔF x).getD 5 0
    = E (Todd x) (((2 : ℕ), Phase.K, (0 : ℕ)), 1) - E x (((2 : ℕ), Phase.K, (0 : ℕ)), 1) := rfl
@[coord_bridge] lemma dF_06 (x : ℕ) : (LP.ΔF x).getD 6 0
    = E (Todd x) (((0 : ℕ), Phase.S, (0 : ℕ)), 0) - E x (((0 : ℕ), Phase.S, (0 : ℕ)), 0) := rfl
@[coord_bridge] lemma dF_07 (x : ℕ) : (LP.ΔF x).getD 7 0
    = E (Todd x) (((0 : ℕ), Phase.S, (0 : ℕ)), 1) - E x (((0 : ℕ), Phase.S, (0 : ℕ)), 1) := rfl
@[coord_bridge] lemma dF_08 (x : ℕ) : (LP.ΔF x).getD 8 0
    = E (Todd x) (((0 : ℕ), Phase.S, (1 : ℕ)), 0) - E x (((0 : ℕ), Phase.S, (1 : ℕ)), 0) := rfl
@[coord_bridge] lemma dF_09 (x : ℕ) : (LP.ΔF x).getD 9 0
    = E (Todd x) (((0 : ℕ), Phase.S, (1 : ℕ)), 1) - E x (((0 : ℕ), Phase.S, (1 : ℕ)), 1) := rfl
@[coord_bridge] lemma dF_10 (x : ℕ) : (LP.ΔF x).getD 10 0
    = E (Todd x) (((1 : ℕ), Phase.S, (0 : ℕ)), 0) - E x (((1 : ℕ), Phase.S, (0 : ℕ)), 0) := rfl
@[coord_bridge] lemma dF_11 (x : ℕ) : (LP.ΔF x).getD 11 0
    = E (Todd x) (((1 : ℕ), Phase.S, (0 : ℕ)), 1) - E x (((1 : ℕ), Phase.S, (0 : ℕ)), 1) := rfl
@[coord_bridge] lemma dF_12 (x : ℕ) : (LP.ΔF x).getD 12 0
    = E (Todd x) (((1 : ℕ), Phase.S, (1 : ℕ)), 0) - E x (((1 : ℕ), Phase.S, (1 : ℕ)), 0) := rfl
@[coord_bridge] lemma dF_13 (x : ℕ) : (LP.ΔF x).getD 13 0
    = E (Todd x) (((1 : ℕ), Phase.S, (1 : ℕ)), 1) - E x (((1 : ℕ), Phase.S, (1 : ℕ)), 1) := rfl
@[coord_bridge] lemma dF_14 (x : ℕ) : (LP.ΔF x).getD 14 0
    = E (Todd x) (((2 : ℕ), Phase.S, (0 : ℕ)), 0) - E x (((2 : ℕ), Phase.S, (0 : ℕ)), 0) := rfl
@[coord_bridge] lemma dF_15 (x : ℕ) : (LP.ΔF x).getD 15 0
    = E (Todd x) (((2 : ℕ), Phase.S, (0 : ℕ)), 1) - E x (((2 : ℕ), Phase.S, (0 : ℕ)), 1) := rfl
@[coord_bridge] lemma dF_16 (x : ℕ) : (LP.ΔF x).getD 16 0
    = E (Todd x) (((2 : ℕ), Phase.S, (1 : ℕ)), 0) - E x (((2 : ℕ), Phase.S, (1 : ℕ)), 0) := rfl
@[coord_bridge] lemma dF_17 (x : ℕ) : (LP.ΔF x).getD 17 0
    = E (Todd x) (((2 : ℕ), Phase.S, (1 : ℕ)), 1) - E x (((2 : ℕ), Phase.S, (1 : ℕ)), 1) := rfl

/-! ## §53 死狀態的 2 條 -/

/-- 死狀態 `(0,K,0)`（`occ2_deadState`）在差分層仍是零。 -/
theorem dF_deadState_zero (x : ℕ) (b : ℕ) :
    E (Todd x) (((0 : ℕ), Phase.K, (0 : ℕ)), b) - E x (((0 : ℕ), Phase.K, (0 : ℕ)), b) = 0 := by
  unfold E
  rw [occ2_deadState, occ2_deadState]
  simp

theorem dF_zero_0 (x : ℕ) : (LP.ΔF x).getD 0 0 = 0 := by
  rw [dF_00]; exact dF_deadState_zero x 0

theorem dF_zero_1 (x : ℕ) : (LP.ΔF x).getD 1 0 = 0 := by
  rw [dF_01]; exact dF_deadState_zero x 1

/-! ## §54 流守恆的 7 條

每條都是同一個機械步驟：§51 的關係在 `x` 與 `Todd x` 各取一次
（`_clean` 的兩個 `≠` 由 `decide`），把 `inEdges` 的字面值與 `map`/`sum` 攤開，
座標橋把目標換成同一批 `E` 原子，`omega` 收尾（初始指示在相減時對消）。 -/

/-- 狀態 (1,K,0) 的流守恆（它同時是初始狀態，初始指示 1 在相減時對消）。 -/
theorem dF_flow_1K0 (x : ℕ) : (LP.ΔF x).getD 4 0 = (LP.ΔF x).getD 2 0 + (LP.ΔF x).getD 3 0 := by
  have hx := kirchhoff_occ2_extIn_clean x ((1 : ℕ), Phase.K, (0 : ℕ)) (by decide) (by decide)
  have hy := kirchhoff_occ2_extIn_clean (Todd x) ((1 : ℕ), Phase.K, (0 : ℕ)) (by decide) (by decide)
  simp only [show inEdges ((1 : ℕ), Phase.K, (0 : ℕ)) = [(((2 : ℕ), Phase.K, (0 : ℕ)), 0)] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hx hy
  simp only [coord_bridge, E]
  omega

/-- 狀態 (2,K,0) 的流守恆。**這就是 ROADMAP 舊表的「K 區交錯 e₄ = e₅ + e₆」**
（1-based e₄/e₅/e₆ = 0-based 3/4/5），可見它不是額外需要的引理。 -/
theorem dF_flow_2K0 (x : ℕ) : (LP.ΔF x).getD 3 0 = (LP.ΔF x).getD 4 0 + (LP.ΔF x).getD 5 0 := by
  have hx := kirchhoff_occ2_extIn_clean x ((2 : ℕ), Phase.K, (0 : ℕ)) (by decide) (by decide)
  have hy := kirchhoff_occ2_extIn_clean (Todd x) ((2 : ℕ), Phase.K, (0 : ℕ)) (by decide) (by decide)
  simp only [show inEdges ((2 : ℕ), Phase.K, (0 : ℕ)) = [(((1 : ℕ), Phase.K, (0 : ℕ)), 1)] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_neg (by decide : ¬
      (((1 : ℕ), Phase.K, (0 : ℕ)) = ((2 : ℕ), Phase.K, (0 : ℕ))))] at hx hy
  simp only [coord_bridge, E]
  omega

/-- 狀態 (1,S,0) 的流守恆。 -/
theorem dF_flow_1S0 (x : ℕ) :
    (LP.ΔF x).getD 14 0 + (LP.ΔF x).getD 16 0
      = (LP.ΔF x).getD 10 0 + (LP.ΔF x).getD 11 0 := by
  have hx := kirchhoff_occ2_extIn_clean x ((1 : ℕ), Phase.S, (0 : ℕ)) (by decide) (by decide)
  have hy := kirchhoff_occ2_extIn_clean (Todd x) ((1 : ℕ), Phase.S, (0 : ℕ)) (by decide) (by decide)
  simp only [show inEdges ((1 : ℕ), Phase.S, (0 : ℕ))
      = [(((2 : ℕ), Phase.S, (0 : ℕ)), 0), (((2 : ℕ), Phase.S, (1 : ℕ)), 0)] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_neg (by decide : ¬
      (((1 : ℕ), Phase.K, (0 : ℕ)) = ((1 : ℕ), Phase.S, (0 : ℕ))))] at hx hy
  simp only [coord_bridge, E]
  omega

/-- 狀態 (1,S,1) 的流守恆。 -/
theorem dF_flow_1S1 (x : ℕ) :
    (LP.ΔF x).getD 7 0 + (LP.ΔF x).getD 9 0
      = (LP.ΔF x).getD 12 0 + (LP.ΔF x).getD 13 0 := by
  have hx := kirchhoff_occ2_extIn_clean x ((1 : ℕ), Phase.S, (1 : ℕ)) (by decide) (by decide)
  have hy := kirchhoff_occ2_extIn_clean (Todd x) ((1 : ℕ), Phase.S, (1 : ℕ)) (by decide) (by decide)
  simp only [show inEdges ((1 : ℕ), Phase.S, (1 : ℕ))
      = [(((0 : ℕ), Phase.S, (0 : ℕ)), 1), (((0 : ℕ), Phase.S, (1 : ℕ)), 1)] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_neg (by decide : ¬
      (((1 : ℕ), Phase.K, (0 : ℕ)) = ((1 : ℕ), Phase.S, (1 : ℕ))))] at hx hy
  simp only [coord_bridge, E]
  omega

/-- 狀態 (2,S,0) 的流守恆。 -/
theorem dF_flow_2S0 (x : ℕ) :
    (LP.ΔF x).getD 11 0 + (LP.ΔF x).getD 13 0
      = (LP.ΔF x).getD 14 0 + (LP.ΔF x).getD 15 0 := by
  have hx := kirchhoff_occ2_extIn_clean x ((2 : ℕ), Phase.S, (0 : ℕ)) (by decide) (by decide)
  have hy := kirchhoff_occ2_extIn_clean (Todd x) ((2 : ℕ), Phase.S, (0 : ℕ)) (by decide) (by decide)
  simp only [show inEdges ((2 : ℕ), Phase.S, (0 : ℕ))
      = [(((1 : ℕ), Phase.S, (0 : ℕ)), 1), (((1 : ℕ), Phase.S, (1 : ℕ)), 1)] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_neg (by decide : ¬
      (((1 : ℕ), Phase.K, (0 : ℕ)) = ((2 : ℕ), Phase.S, (0 : ℕ))))] at hx hy
  simp only [coord_bridge, E]
  omega

/-- 狀態 (2,S,1) 的流守恆（自環使兩側各有一個 ΔF₁₇，已對消）。 -/
theorem dF_flow_2S1 (x : ℕ) :
    (LP.ΔF x).getD 5 0 + (LP.ΔF x).getD 15 0 = (LP.ΔF x).getD 16 0 := by
  have hx := kirchhoff_occ2_extIn_clean x ((2 : ℕ), Phase.S, (1 : ℕ)) (by decide) (by decide)
  have hy := kirchhoff_occ2_extIn_clean (Todd x) ((2 : ℕ), Phase.S, (1 : ℕ)) (by decide) (by decide)
  simp only [show inEdges ((2 : ℕ), Phase.S, (1 : ℕ))
      = [(((2 : ℕ), Phase.K, (0 : ℕ)), 1), (((2 : ℕ), Phase.S, (0 : ℕ)), 1),
         (((2 : ℕ), Phase.S, (1 : ℕ)), 1)] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_neg (by decide : ¬
      (((1 : ℕ), Phase.K, (0 : ℕ)) = ((2 : ℕ), Phase.S, (1 : ℕ))))] at hx hy
  simp only [coord_bridge, E]
  omega

/-- 兩個可能終末合併的流守恆（第 7 條）。ΔF₆、ΔF₈ 在兩側對消，
合併後的終末指示 1 也在相減時對消。 -/
theorem dF_flow_terminal_merged (x : ℕ) :
    (LP.ΔF x).getD 2 0 + (LP.ΔF x).getD 10 0 + (LP.ΔF x).getD 12 0
      = (LP.ΔF x).getD 7 0 + (LP.ΔF x).getD 9 0 := by
  have hx := kirchhoff_occ2_extIn_merged x
  have hy := kirchhoff_occ2_extIn_merged (Todd x)
  simp only [show inEdges ((0 : ℕ), Phase.S, (0 : ℕ))
      = [(((0 : ℕ), Phase.S, (0 : ℕ)), 0), (((0 : ℕ), Phase.S, (1 : ℕ)), 0)] from rfl,
    show inEdges ((0 : ℕ), Phase.S, (1 : ℕ))
      = [(((1 : ℕ), Phase.K, (0 : ℕ)), 0), (((1 : ℕ), Phase.S, (0 : ℕ)), 0),
         (((1 : ℕ), Phase.S, (1 : ℕ)), 0)] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hx hy
  simp only [coord_bridge, E]
  omega

/-! ## §55 數值回歸（`#guard` 失敗即 build 紅）

上面 9 條都是對所有 x 的定理；這裡是它們的數值錨，
掃 x < 240（含 0、1 與偶數，因為這些恆等式與奇偶無關）。 -/

section Verification

#guard (List.range 240).all fun x =>
  let d := LP.ΔF x
  (d.getD 0 0 == 0) && (d.getD 1 0 == 0)
    && (d.getD 4 0 == d.getD 2 0 + d.getD 3 0)
    && (d.getD 3 0 == d.getD 4 0 + d.getD 5 0)
    && (d.getD 14 0 + d.getD 16 0 == d.getD 10 0 + d.getD 11 0)
    && (d.getD 7 0 + d.getD 9 0 == d.getD 12 0 + d.getD 13 0)
    && (d.getD 11 0 + d.getD 13 0 == d.getD 14 0 + d.getD 15 0)
    && (d.getD 5 0 + d.getD 15 0 == d.getD 16 0)
    && (d.getD 2 0 + d.getD 10 0 + d.getD 12 0 == d.getD 7 0 + d.getD 9 0)

end Verification

end CollatzFST.Flow
