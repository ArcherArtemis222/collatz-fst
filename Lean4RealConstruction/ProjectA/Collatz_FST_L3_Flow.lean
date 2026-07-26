/-
# Level 3 的 Kirchhoff 流守恆（ROADMAP A-3 Level 3 第一步）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_L3_2Mode_Recon.lean`
（`step3` / `microTrace3` / `occ3` / `KEYS3` / `F3`）與 `Collatz_FST_Flow.lean`
（借用通用計數引理 `Flow.countP_eq_sum_count`）。

## 這一步在做什麼

把 Level 2 那條「流守恆 → 差分層泛函 → 解空間上界 → 具體見證下界」的路
搬到 Level 3。本檔是第一段：可達性閉包 + 流守恆 + 出入流接上特徵。

`tools/l3_recon.py`（CI 每次 push 跑）已經先把數字釘死，本檔的定義必須與它對得上：

| | Level 2 | Level 3 |
|---|---|---|
| 可達狀態 / 邊 | 8 / 16 | **14 / 28** |
| 恆死座標 | 2（18 維裡） | **20**（48 維裡） |
| 終末狀態 | 2 | **2**：`(0,S,0,1)`、`(0,S,1,0)` |
| 流守恆可用 | 6 乾淨 + 1 合併 = 7 | **12 + 1 = 13** |

**不需要 `x % 2 = 1` 假設**：Level 3 的維度結論（單模式 16、雙模式 31）對
奇數與全部 x 都成立，`tools/l3_recon.py` 有對帳。所以本檔沿用 `Flow.lean`
的「對所有 x」寫法。

**不需要動 `Core/`**：Level 3 的狀態機定義都已在 ProjectA 裡。

## 本檔內容

* `run3`：讀完一個字之後的狀態（Level 2 的 `run2` 在 Core，Level 3 這邊自備）。
* `S14` / `S14_closed` / `run3_mem_S14`：14 個可達狀態與閉包（`S8` 的類比）。
* `microTrace3_flow_conservation`：入流(g) + [初始=g] = 出流(g) + [終末=g]。
* `state_outflow_eq_occ3`、`inflow_eq_sum_occ3`：兩側都接上 48 維佔用特徵
  （入流用 28 條可達邊的關聯結構，由 `step3` 就地算出）。
* `kirchhoff_occ3` / `kirchhoff_occ3_extIn`：特徵層的 Kirchhoff 關係。

## 不在本檔範圍

終末狀態定理（需要「讀完 `Nat.digits 2 x` 後進位 ∈ {1,2}」這條新引理）、
13 條可用關係、差分層、以及維度上下界。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_2Mode_Recon
import Lean4RealConstruction.ProjectA.Collatz_FST_Flow

namespace CollatzFST.L3

open CollatzFST

/-! ## §65 讀完一個字之後的狀態 -/

/-- Level 3 的 `run`：從狀態 `s` 讀完 `w` 後的狀態。 -/
def run3 : (ℕ × Phase × ℕ × ℕ) → List ℕ → (ℕ × Phase × ℕ × ℕ)
  | s, [] => s
  | s, b :: bs => run3 (step3 s b) bs

@[simp] lemma run3_nil (s) : run3 s [] = s := rfl
lemma run3_cons (s b bs) : run3 s (b :: bs) = run3 (step3 s b) bs := rfl

/-! ## §66 可達狀態：14 個（`S8` 的 Level 3 類比）

順序照 `S8` 的慣例：先 K 側 2 個，再 S 側 12 個。 -/

/-- 14 個可達狀態（48 維裡另外 20 個座標的狀態恆不出現）。 -/
def S14 : List (ℕ × Phase × ℕ × ℕ) :=
  [(1, .K, 0, 0), (2, .K, 0, 0),
   (0, .S, 0, 0), (0, .S, 0, 1), (0, .S, 1, 0), (0, .S, 1, 1),
   (1, .S, 0, 0), (1, .S, 0, 1), (1, .S, 1, 0), (1, .S, 1, 1),
   (2, .S, 0, 0), (2, .S, 0, 1), (2, .S, 1, 0), (2, .S, 1, 1)]

lemma S14_length : S14.length = 14 := by decide

theorem S14_closed : ∀ s ∈ S14, ∀ b < 2, step3 s b ∈ S14 := by decide

theorem run3_mem_S14 {w : List ℕ} (hw : ∀ b ∈ w, b < 2) :
    run3 (1, Phase.K, 0, 0) w ∈ S14 := by
  suffices h : ∀ (w : List ℕ), (∀ b ∈ w, b < 2) → ∀ s ∈ S14, run3 s w ∈ S14 by
    exact h w hw _ (by decide)
  intro w
  induction w with
  | nil => intro _ s hs; exact hs
  | cons b bs ih =>
      intro hw s hs
      rw [run3_cons]
      exact ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _
        (S14_closed s hs b (hw b (List.mem_cons_self ..)))

/-- trace 的每一筆都是 `S14` 狀態配上一個位元。 -/
theorem microTrace3_mem_S14 : ∀ (w : List ℕ) (s : ℕ × Phase × ℕ × ℕ), s ∈ S14 →
    (∀ b ∈ w, b < 2) → ∀ t ∈ microTrace3 s w, t.1 ∈ S14 ∧ t.2 < 2 := by
  intro w
  induction w with
  | nil => intro _ _ _ t ht; cases ht
  | cons b bs ih =>
      intro s hs hw t ht
      have hb : b < 2 := hw b (List.mem_cons_self ..)
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨hs, hb⟩
      · exact ih (step3 s b) (S14_closed s hs b hb)
          (fun y hy => hw y (List.mem_cons_of_mem _ hy)) t ht'

/-! ## §67 流守恆 -/

/-- **Kirchhoff 流守恆（Level 3，trace 層）**：對任意目標狀態 g，
「落點為 g」的步數 + 初始指示 = 「起點為 g」的步數 + 終末指示。
證法與 `Flow.microTrace2_flow_conservation` 逐字相同。 -/
theorem microTrace3_flow_conservation (g : ℕ × Phase × ℕ × ℕ) :
    ∀ (w : List ℕ) (s : ℕ × Phase × ℕ × ℕ),
      (microTrace3 s w).countP (fun t => step3 t.1 t.2 == g)
          + (if s = g then 1 else 0)
        = (microTrace3 s w).countP (fun t => t.1 == g)
          + (if run3 s w = g then 1 else 0) := by
  intro w
  induction w with
  | nil =>
      intro s
      simp only [microTrace3, List.countP_nil, run3_nil]
  | cons b bs ih =>
      intro s
      have hih := ih (step3 s b)
      rw [show microTrace3 s (b :: bs) = (s, b) :: microTrace3 (step3 s b) bs from rfl,
        List.countP_cons, List.countP_cons, run3_cons]
      simp only [beq_iff_eq] at hih ⊢
      split_ifs at hih ⊢ <;> omega

/-- **出流與特徵的橋**：狀態 g 的出流 = occ3 (g, 0) + occ3 (g, 1)。 -/
theorem state_outflow_eq_occ3 (g : ℕ × Phase × ℕ × ℕ) :
    ∀ (w : List ℕ) (s : ℕ × Phase × ℕ × ℕ), (∀ b ∈ w, b < 2) →
      (microTrace3 s w).countP (fun t => t.1 == g)
        = occ3 s w (g, 0) + occ3 s w (g, 1) := by
  intro w
  induction w with
  | nil => intro s _; rfl
  | cons b bs ih =>
      intro s hw
      have hb : b < 2 := hw b (List.mem_cons_self ..)
      have hih := ih (step3 s b) (fun y hy => hw y (List.mem_cons_of_mem _ hy))
      unfold occ3 at hih ⊢
      rw [show microTrace3 s (b :: bs) = (s, b) :: microTrace3 (step3 s b) bs from rfl,
        List.countP_cons, List.count_cons, List.count_cons, hih]
      by_cases hgs : s = g
      · subst hgs
        interval_cases b <;> simp <;> omega
      · have h0 : ¬ ((s, b) = ((g, 0) : (ℕ × Phase × ℕ × ℕ) × ℕ)) :=
          fun h => hgs (congrArg Prod.fst h)
        have h1 : ¬ ((s, b) = ((g, 1) : (ℕ × Phase × ℕ × ℕ) × ℕ)) :=
          fun h => hgs (congrArg Prod.fst h)
        simp only [beq_iff_eq, if_neg hgs, if_neg h0, if_neg h1]
        omega

/-! ## §68 入流分解：28 條可達邊的關聯結構

邊表不是外部資料：`inEdges3` 由 `step3` 就地 `filter` 算出。
通用計數引理直接借 `Flow.countP_eq_sum_count`（它是對 `BEq` + `LawfulBEq` 泛化的）。 -/

/-- 28 條轉移邊：14 個可達狀態 × 2 個輸入位元。 -/
def allEdges3 : List ((ℕ × Phase × ℕ × ℕ) × ℕ) := S14.flatMap fun h => [(h, 0), (h, 1)]

lemma allEdges3_nodup : allEdges3.Nodup := by decide

/-- 落點為 `g` 的入邊。 -/
def inEdges3 (g : ℕ × Phase × ℕ × ℕ) : List ((ℕ × Phase × ℕ × ℕ) × ℕ) :=
  allEdges3.filter fun e => step3 e.1 e.2 == g

lemma mem_allEdges3 {s : ℕ × Phase × ℕ × ℕ} {b : ℕ} (h1 : s ∈ S14) (h2 : b < 2) :
    (s, b) ∈ allEdges3 := by
  rw [allEdges3, List.mem_flatMap]
  exact ⟨s, h1, by interval_cases b <;> simp⟩

/-- **入流分解**：落點為 `g` 的步數 = 所有入邊的佔用特徵之和。 -/
theorem inflow_eq_sum_occ3 (g : ℕ × Phase × ℕ × ℕ) {s : ℕ × Phase × ℕ × ℕ}
    (hs : s ∈ S14) {w : List ℕ} (hw : ∀ b ∈ w, b < 2) :
    (microTrace3 s w).countP (fun t => step3 t.1 t.2 == g)
      = ((inEdges3 g).map (fun e => occ3 s w e)).sum := by
  have h := Flow.countP_eq_sum_count
    (fun e : (ℕ × Phase × ℕ × ℕ) × ℕ => step3 e.1 e.2 == g)
    allEdges3 allEdges3_nodup (microTrace3 s w) fun t ht => by
      obtain ⟨h1, h2⟩ := microTrace3_mem_S14 w s hs hw t ht
      exact mem_allEdges3 h1 h2
  simpa [inEdges3, occ3] using h

/-- **Kirchhoff 泛函（Level 3，純特徵層）**：兩側都只由 `occ3` 與端點指示構成。 -/
theorem kirchhoff_occ3 (g : ℕ × Phase × ℕ × ℕ) {s : ℕ × Phase × ℕ × ℕ} (hs : s ∈ S14)
    {w : List ℕ} (hw : ∀ b ∈ w, b < 2) :
    ((inEdges3 g).map (fun e => occ3 s w e)).sum + (if s = g then 1 else 0)
      = occ3 s w (g, 0) + occ3 s w (g, 1) + (if run3 s w = g then 1 else 0) := by
  rw [← inflow_eq_sum_occ3 g hs hw, ← state_outflow_eq_occ3 g w s hw]
  exact microTrace3_flow_conservation g w s

/-- canonical 起點 (1, K, 0, 0) 讀 `extIn x` 的特徵層實例。 -/
theorem kirchhoff_occ3_extIn (x : ℕ) (g : ℕ × Phase × ℕ × ℕ) :
    ((inEdges3 g).map (fun e => occ3 (1, Phase.K, 0, 0) (extIn x) e)).sum
        + (if ((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)) = g then 1 else 0)
      = occ3 (1, Phase.K, 0, 0) (extIn x) (g, 0)
        + occ3 (1, Phase.K, 0, 0) (extIn x) (g, 1)
        + (if run3 (1, Phase.K, 0, 0) (extIn x) = g then 1 else 0) :=
  kirchhoff_occ3 g (by decide) (extIn_bits x)

/-! ## §69 數值回歸（`#guard` 失敗即 build 紅）

與 `tools/l3_recon.py` 的 `LEAN_L3_*` 常數對帳。 -/

section Verification

-- 可達狀態 14 個、可達邊 28 條
#guard S14.length == 14
#guard allEdges3.length == 28
#guard (S14.map fun g => (inEdges3 g).length).sum == 28

-- 48 維裡恆死的座標 = 20（狀態不在 S14 的那些 key）
#guard (KEYS3.filter fun k => !(S14.contains k.1)).length == 20

-- 流守恆：S14 全狀態 × x < 60
#guard (List.range 60).all fun x =>
  S14.all fun g =>
    (microTrace3 (1, Phase.K, 0, 0) (extIn x)).countP (fun t => step3 t.1 t.2 == g)
        + (if ((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)) = g then 1 else 0)
      == (microTrace3 (1, Phase.K, 0, 0) (extIn x)).countP (fun t => t.1 == g)
        + (if run3 (1, Phase.K, 0, 0) (extIn x) = g then 1 else 0)

-- 出流橋與入流分解：S14 全狀態 × x < 60
#guard (List.range 60).all fun x =>
  S14.all fun g =>
    (microTrace3 (1, Phase.K, 0, 0) (extIn x)).countP (fun t => t.1 == g)
      == occ3 (1, Phase.K, 0, 0) (extIn x) (g, 0) + occ3 (1, Phase.K, 0, 0) (extIn x) (g, 1)

#guard (List.range 60).all fun x =>
  S14.all fun g =>
    (microTrace3 (1, Phase.K, 0, 0) (extIn x)).countP (fun t => step3 t.1 t.2 == g)
      == ((inEdges3 g).map fun e => occ3 (1, Phase.K, 0, 0) (extIn x) e).sum

-- 終末狀態恆落在 {(0,S,0,1), (0,S,1,0)}（**2 個**，不是 3 個；下一步的定理化目標）。
-- 涵蓋 x = 0、x = 1 與偶數：該性質與奇偶無關。
#guard (List.range 240).all fun x =>
  run3 (1, Phase.K, 0, 0) (extIn x)
    ∈ [((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), (0, Phase.S, 1, 0)]

end Verification

end CollatzFST.L3
