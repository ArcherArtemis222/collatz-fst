/-
# Kirchhoff 流守恆：microTrace2 的出入計數歸納引理（ROADMAP A-3 第一步）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Core/Collatz_FST_Level2.lean`。

## 定位（HandOver「維度精確化 (Dimensionality)」條款的技術基座）

HandOver 主張 Level 2 差分空間是精確的 **10 維**有理線性子空間；其上界（≤ 10）
要對**所有**奇數 x 證明 8 條線性泛函在 ΔF x 上為零，其中四條是 Kirchhoff
流守恆（ROADMAP A-3 的泛函對照表）。本檔把守恆律落地為 trace 層的歸納引理：

  對任意狀態 g：入流(g) + [初始 = g] = 出流(g) + [終末 = g]

其中出流(g) = trace 上**起點**為 g 的步數，入流(g) = trace 上**落點**
（`step2` 後）為 g 的步數。ROADMAP A-3 稱此為「核心技術債」並建議
獨立成 PR——本檔即該 PR，**不含**後續的逐狀態泛函實例化與維度定理。

## 本檔內容

* `microTrace2_flow_conservation`：核心歸納引理（對 w 歸納、s 全稱；
  每筆轉移 (s, b) 同時是 s 的出流與 step2 s b 的入流，逐步對消）。
* `state_outflow_eq_occ2`：出流與 18 維特徵的橋——對 0/1 字，
  出流(g) = occ2 (g,0) + occ2 (g,1)（`F` 的兩個分量之和）。
* `flow_conservation_extIn`：canonical 起點 (1, K, 0) 與 extIn x 的實例，
  後續 PR 逐狀態展開泛函時直接引用。
-/
import Lean4RealConstruction.Core.Collatz_FST_Level2

namespace CollatzFST.Flow

open CollatzFST

/-- **Kirchhoff 流守恆（trace 層）**：對任意目標狀態 g，
「落點為 g」的步數 + 初始指示 = 「起點為 g」的步數 + 終末指示。
對 w 歸納：頭步 (s, b) 是 s 的出流、step2 s b 的入流，與歸納假設逐步對消。 -/
theorem microTrace2_flow_conservation (g : ℕ × Phase × ℕ) :
    ∀ (w : List ℕ) (s : ℕ × Phase × ℕ),
      (microTrace2 s w).countP (fun t => step2 t.1 t.2 == g)
          + (if s = g then 1 else 0)
        = (microTrace2 s w).countP (fun t => t.1 == g)
          + (if run2 s w = g then 1 else 0) := by
  intro w
  induction w with
  | nil =>
      intro s
      simp only [microTrace2, List.countP_nil, run2_nil]
  | cons b bs ih =>
      intro s
      have hih := ih (step2 s b)
      rw [show microTrace2 s (b :: bs) = (s, b) :: microTrace2 (step2 s b) bs from rfl,
        List.countP_cons, List.countP_cons, run2_cons]
      simp only [beq_iff_eq] at hih ⊢
      split_ifs at hih ⊢ <;> omega

/-- **出流與特徵的橋**：對 0/1 字，狀態 g 的出流恰為兩個佔用特徵之和
occ2 (g, 0) + occ2 (g, 1)（即 18 維特徵 `F` 中 g 的兩個分量）。 -/
theorem state_outflow_eq_occ2 (g : ℕ × Phase × ℕ) :
    ∀ (w : List ℕ) (s : ℕ × Phase × ℕ), (∀ b ∈ w, b < 2) →
      (microTrace2 s w).countP (fun t => t.1 == g)
        = occ2 s w (g, 0) + occ2 s w (g, 1) := by
  intro w
  induction w with
  | nil =>
      intro s _
      rfl
  | cons b bs ih =>
      intro s hw
      have hb : b < 2 := hw b (List.mem_cons_self ..)
      have hih := ih (step2 s b) (fun y hy => hw y (List.mem_cons_of_mem _ hy))
      unfold occ2 at hih ⊢
      rw [show microTrace2 s (b :: bs) = (s, b) :: microTrace2 (step2 s b) bs from rfl,
        List.countP_cons, List.count_cons, List.count_cons, hih]
      by_cases hgs : s = g
      · subst hgs
        interval_cases b <;> simp <;> omega
      · have h0 : ¬ ((s, b) = ((g, 0) : (ℕ × Phase × ℕ) × ℕ)) :=
          fun h => hgs (congrArg Prod.fst h)
        have h1 : ¬ ((s, b) = ((g, 1) : (ℕ × Phase × ℕ) × ℕ)) :=
          fun h => hgs (congrArg Prod.fst h)
        simp only [beq_iff_eq, if_neg hgs, if_neg h0, if_neg h1]
        omega

/-- canonical 起點 (1, K, 0) 讀 extIn x 的流守恆實例（後續逐狀態泛函直接引用）。 -/
theorem flow_conservation_extIn (x : ℕ) (g : ℕ × Phase × ℕ) :
    (microTrace2 (1, Phase.K, 0) (extIn x)).countP (fun t => step2 t.1 t.2 == g)
        + (if ((1 : ℕ), Phase.K, (0 : ℕ)) = g then 1 else 0)
      = (microTrace2 (1, Phase.K, 0) (extIn x)).countP (fun t => t.1 == g)
        + (if run2 (1, Phase.K, 0) (extIn x) = g then 1 else 0) :=
  microTrace2_flow_conservation g (extIn x) _

/-! ## 數據驗證（回歸；全部應輸出 `true`） -/

section Verification

-- 流守恆：S8 全狀態 × x < 120
#eval (List.range 120).all fun x =>
  S8.all fun g =>
    (microTrace2 (1, Phase.K, 0) (extIn x)).countP (fun t => step2 t.1 t.2 == g)
        + (if ((1 : ℕ), Phase.K, (0 : ℕ)) = g then 1 else 0)
      == (microTrace2 (1, Phase.K, 0) (extIn x)).countP (fun t => t.1 == g)
        + (if run2 (1, Phase.K, 0) (extIn x) = g then 1 else 0)

-- 出流橋：S8 全狀態 × x < 120
#eval (List.range 120).all fun x =>
  S8.all fun g =>
    (microTrace2 (1, Phase.K, 0) (extIn x)).countP (fun t => t.1 == g)
      == occ2 (1, Phase.K, 0) (extIn x) (g, 0) + occ2 (1, Phase.K, 0) (extIn x) (g, 1)

end Verification

end CollatzFST.Flow
