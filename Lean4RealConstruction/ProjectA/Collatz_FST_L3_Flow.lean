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

* `runCarry_digits_mem`（§70）：讀完 `Nat.digits 2 x` 後進位 ∈ {1,2}。
* `run3_extIn_terminal`：終末狀態恆為 `(0,S,0,1)` 或 `(0,S,1,0)`（**2 個**）。
* `kirchhoff_occ3_extIn_clean`（12 條）／`_merged`（1 條）：13 條可用關係。

## 為什麼 Level 2 的收尾技巧在這裡失效

Level 2 靠「終末進位 = 0 + `run2_mem_S8` + `decide`」就收掉，因為 `S8` 裡進位為 0
的狀態只有兩個。Level 3 不行：`S14` 裡進位為 0 的有**四個**
（`(0,S,0,0)`、`(0,S,0,1)`、`(0,S,1,0)`、`(0,S,1,1)`），而且 `(0,S,0,0)` 確實可達
（只是不會當終末）。所以需要 §70 那條進位引理，把「讀完 digits 後進位 ∈ {1,2}」
接上「兩個哨兵零把 (c, ·) 打成 (0, S, c%2, (c/2)%2)」。

兩條路線都探針過：**靠「digits 最後一位 = 1」的路一次就過**；
靠算術（進位 = (3x+1) >> len）那條在最後的 `omega` 卡住——`2^L · c` 是非線性項，
還要對 `c` 分情況。故採前者。

## 不在本檔範圍

差分層、以及維度上下界。
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

/-! ## §70 終末狀態 -/

lemma run3_append : ∀ (u v : List ℕ) (s : ℕ × Phase × ℕ × ℕ),
    run3 s (u ++ v) = run3 (run3 s u) v := by
  intro u
  induction u with
  | nil => intro v s; rfl
  | cons b bs ih => intro v s; rw [List.cons_append, run3_cons, run3_cons, ih]

/-- Level 3 的進位分量就是 Level 1 的 `runCarry`（`run2_fst` 的類比）。 -/
lemma run3_fst (c : ℕ) (P : Phase) (h₂ h₁ : ℕ) (w : List ℕ) :
    (run3 (c, P, h₂, h₁) w).1 = runCarry w c := by
  induction w generalizing c P h₂ h₁ with
  | nil => rfl
  | cons b bs ih => rw [run3_cons]; exact ih _ _ _ _

/-- **讀完 `Nat.digits 2 x` 後進位 ∈ {1,2}**。

`x ≠ 0` 時 digits 非空且最後一位（MSB）為 1，故最後一步是
`nextCarry c 1 = (3 + c) / 2`，配合前段進位 `< 3` 得 1 或 2；
`x = 0` 時 digits 為空，進位保持初始值 1。 -/
lemma runCarry_digits_mem (x : ℕ) :
    runCarry (Nat.digits 2 x) 1 = 1 ∨ runCarry (Nat.digits 2 x) 1 = 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · left; rfl
  · have hne : Nat.digits 2 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hx
    have hlast : (Nat.digits 2 x).getLast hne = 1 := by
      have h0 := Nat.getLast_digit_ne_zero 2 hx
      have hlt : (Nat.digits 2 x).getLast hne < 2 :=
        Nat.digits_lt_base (by norm_num) (List.getLast_mem hne)
      omega
    have hsplit : Nat.digits 2 x = (Nat.digits 2 x).dropLast ++ [1] := by
      rw [← hlast]; exact (List.dropLast_concat_getLast hne).symm
    have hc : runCarry (Nat.digits 2 x).dropLast 1 < 3 :=
      run_carry_lt_three (by norm_num) (fun b hb =>
        Nat.digits_lt_base (by norm_num) (List.dropLast_subset _ hb))
    rw [hsplit, t_append, t_single]
    unfold nextCarry
    omega

/-- **終末狀態定理（Level 3）**：讀完 `extIn x` 後的狀態恆為
`(0,S,0,1)` 或 `(0,S,1,0)`——**2 個**，不是 4 個。對**所有** x 成立（不需奇偶假設）。

`(0,S,0,0)` 雖然可達，卻永遠不會是終末：那需要讀完 digits 後進位為 0，而 §70 說不可能。 -/
theorem run3_extIn_terminal (x : ℕ) :
    run3 (1, Phase.K, 0, 0) (extIn x) = ((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ))
      ∨ run3 (1, Phase.K, 0, 0) (extIn x) = ((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) := by
  have hdig : ∀ b ∈ Nat.digits 2 x, b < 2 := fun b hb =>
    Nat.digits_lt_base (by norm_num) hb
  have hmem : run3 (1, Phase.K, 0, 0) (Nat.digits 2 x) ∈ S14 := run3_mem_S14 hdig
  have hcar : (run3 (1, Phase.K, 0, 0) (Nat.digits 2 x)).1 = 1
      ∨ (run3 (1, Phase.K, 0, 0) (Nat.digits 2 x)).1 = 2 := by
    rw [run3_fst]; exact runCarry_digits_mem x
  have key : ∀ s ∈ S14, (s.1 = 1 ∨ s.1 = 2) →
      run3 s [0, 0] = ((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ))
        ∨ run3 s [0, 0] = ((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) := by decide
  rw [show extIn x = Nat.digits 2 x ++ [0, 0] from rfl, run3_append]
  exact key _ hmem hcar

/-! ## §71 13 條可用關係（12 乾淨 + 1 合併） -/

/-- 非終末狀態的**乾淨流守恆**（12 條）：終末指示恆為 0。 -/
theorem kirchhoff_occ3_extIn_clean (x : ℕ) (g : ℕ × Phase × ℕ × ℕ)
    (h0 : g ≠ ((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)))
    (h1 : g ≠ ((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ))) :
    ((inEdges3 g).map (fun e => occ3 (1, Phase.K, 0, 0) (extIn x) e)).sum
        + (if ((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)) = g then 1 else 0)
      = occ3 (1, Phase.K, 0, 0) (extIn x) (g, 0)
        + occ3 (1, Phase.K, 0, 0) (extIn x) (g, 1) := by
  have hne : run3 (1, Phase.K, 0, 0) (extIn x) ≠ g := by
    rcases run3_extIn_terminal x with h | h <;> rw [h] <;> exact fun hh => by
      first | exact h0 hh.symm | exact h1 hh.symm
  rw [kirchhoff_occ3_extIn x g, if_neg hne, Nat.add_zero]

/-- 兩個可能終末的**合併流守恆**（第 13 條）：兩個終末指示相加恆為 1。 -/
theorem kirchhoff_occ3_extIn_merged (x : ℕ) :
    ((inEdges3 ((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ))).map
          (fun e => occ3 (1, Phase.K, 0, 0) (extIn x) e)).sum
        + ((inEdges3 ((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ))).map
            (fun e => occ3 (1, Phase.K, 0, 0) (extIn x) e)).sum
      = (occ3 (1, Phase.K, 0, 0) (extIn x) (((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0)
          + occ3 (1, Phase.K, 0, 0) (extIn x) (((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1))
        + (occ3 (1, Phase.K, 0, 0) (extIn x) (((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0)
            + occ3 (1, Phase.K, 0, 0) (extIn x) (((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1))
        + 1 := by
  have e0 := kirchhoff_occ3_extIn x ((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ))
  have e1 := kirchhoff_occ3_extIn x ((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ))
  have hi0 : ¬ (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ))
      = ((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ))) := by decide
  have hi1 : ¬ (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ))
      = ((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ))) := by decide
  rw [if_neg hi0, Nat.add_zero] at e0
  rw [if_neg hi1, Nat.add_zero] at e1
  have hsum : (if run3 (1, Phase.K, 0, 0) (extIn x)
        = ((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)) then 1 else 0)
      + (if run3 (1, Phase.K, 0, 0) (extIn x)
        = ((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) then 1 else 0) = 1 := by
    rcases run3_extIn_terminal x with h | h <;> rw [h] <;> decide
  omega

/-! ## §72 模式位元恆等式的全稱版

`L3.mode_bit_endpoints3`（在 `Collatz_FST_L3_2Mode_NoGo.lean`）只用 `decide` 證了
40 個端點的 `F3[16] + F3[33] = 1`。雙模式的第 65 條泛函
（`θ₀[16] + θ₁[33] = 0`，見 `tools/l3_recon.py`）需要**全稱版**。

不必新證：`F3[16] + F3[33]` 就是「**起點在 K 相位且輸出 1** 的步數」——
`S14` 的 K 側只有 `(1,K,0,0)` 與 `(2,K,0,0)`，而從 `(1,K,0,0)` 輸出 1 ⟺ 讀 0、
從 `(2,K,0,0)` 輸出 1 ⟺ 讀 1，恰好就是 `KEYS3` 的第 16 與第 33 個 key。
而那個步數由 Core 的 `boundary_step_unique` 給定為 1；Level 3 的 trace 投影到
Level 2（忘掉 `h₂`）即可套用。 -/

/-- Level 3 的 trace 投影到 Level 1 的 trace（`microTrace2_proj` 的類比）。
狀態 `(c, P, h₂, h₁)` 對應 Level 2 的 `(c, P, h₁)`：`step3` 的 `h₁' = outBit`
與 `step2` 的 `d_prev' = outBit` 是同一件事。 -/
theorem microTrace3_proj : ∀ (w : List ℕ) (c : ℕ) (P : Phase) (h₂ h₁ : ℕ),
    (microTrace3 (c, P, h₂, h₁) w).map (fun t => (t.1.1, t.1.2.1, t.2))
      = microTraceP (c, P) w := by
  intro w
  induction w with
  | nil => intro c P h₂ h₁; rfl
  | cons b bs ih =>
      intro c P h₂ h₁
      show ((c, P, b) : ℕ × Phase × ℕ) :: (microTrace3 (step3 (c, P, h₂, h₁) b) bs).map _
          = (c, P, b) :: microTraceP (nextCarry c b, phaseStep P (outBit c b)) bs
      show _ :: (microTrace3 (nextCarry c b, phaseStep P (outBit c b), h₁, outBit c b) bs).map _
          = _
      rw [ih]

/-- **模式位元恆等式（全稱版）**：對**所有** x，
`F3[16] + F3[33] = 1`，即 `occ3 ((1,K,0,0), 0) + occ3 ((2,K,0,0), 1) = 1`。

這是 `mode_bit_endpoints3` 從 40 個端點推廣到全稱，也是雙模式第 65 條泛函
`θ₀[16] + θ₁[33] = 0` 的來源（`F3[16] = 1 − m`、`F3[33] = m`）。 -/
theorem occ3_mode_bit_sum (x : ℕ) :
    occ3 (1, Phase.K, 0, 0) (extIn x) (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
      + occ3 (1, Phase.K, 0, 0) (extIn x) (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 1 := by
  -- ① 那個和 = trace 上「起點在 K 且輸出 1」的步數
  have hsum : (microTrace3 (1, Phase.K, 0, 0) (extIn x)).countP
        (fun t => t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1)
      = occ3 (1, Phase.K, 0, 0) (extIn x) (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
        + occ3 (1, Phase.K, 0, 0) (extIn x) (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) := by
    have h := Flow.countP_eq_sum_count
      (fun e : (ℕ × Phase × ℕ × ℕ) × ℕ => e.1.2.1 == Phase.K && outBit e.1.1 e.2 == 1)
      allEdges3 allEdges3_nodup (microTrace3 (1, Phase.K, 0, 0) (extIn x)) fun t ht => by
        obtain ⟨h1, h2⟩ := microTrace3_mem_S14 (extIn x) _ (by decide) (extIn_bits x) t ht
        exact mem_allEdges3 h1 h2
    rw [h, show allEdges3.filter
        (fun e : (ℕ × Phase × ℕ × ℕ) × ℕ => e.1.2.1 == Phase.K && outBit e.1.1 e.2 == 1)
      = [(((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0),
         (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1)] from by decide]
    simp [occ3]
  -- ② 投影到 Level 1 後，那個步數由 boundary_step_unique 給定為 1
  rw [← hsum, show (microTrace3 (1, Phase.K, 0, 0) (extIn x)).countP
        (fun t => t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1)
      = (microTraceP (1, Phase.K) (extIn x)).countP
          (fun t => t.2.1 == Phase.K && outBit t.1 t.2.2 == 1) from by
    rw [← microTrace3_proj (extIn x) 1 Phase.K 0 0, List.countP_map]; rfl]
  -- Core 的 boundary_step_unique 是對 microTrace2 敘述的，同樣投影過去
  have hb := boundary_step_unique x
  rwa [show (microTrace2 (1, Phase.K, 0) (extIn x)).countP
        (fun t => t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1)
      = (microTraceP (1, Phase.K) (extIn x)).countP
          (fun t => t.2.1 == Phase.K && outBit t.1 t.2.2 == 1) from by
    rw [← microTrace2_proj (extIn x) 1 Phase.K 0, List.countP_map]; rfl] at hb

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

-- 模式位元恆等式（§72 全稱定理的數值錨；亦即 F3[16] + F3[33] = 1）
#guard (List.range 240).all fun x =>
  occ3 (1, Phase.K, 0, 0) (extIn x) (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
    + occ3 (1, Phase.K, 0, 0) (extIn x) (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) == 1

end Verification

end CollatzFST.L3
