/-
# Kirchhoff 流守恆：出入流的特徵層形式（ROADMAP A-3 第一、二步）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Core/Collatz_FST_Level2.lean`。

## 定位（HandOver「維度精確化 (Dimensionality)」條款的技術基座）

HandOver 主張 Level 2 差分空間是精確的 **10 維**有理線性子空間；其上界（≤ 10）
要對**所有**奇數 x 證明 8 條線性泛函在 ΔF x 上為零，主體就是 Kirchhoff
流守恆。本檔把守恆律落地為 trace 層的歸納引理：

  對任意狀態 g：入流(g) + [初始 = g] = 出流(g) + [終末 = g]

其中出流(g) = trace 上**起點**為 g 的步數，入流(g) = trace 上**落點**
（`step2` 後）為 g 的步數。ROADMAP A-3 稱此為「核心技術債」。
本檔**不含**維度定理本身（`span(ΔF)` 的上下界），那是後續 PR。

## 本檔內容

* `microTrace2_flow_conservation`：核心歸納引理（對 w 歸納、s 全稱；
  每筆轉移 (s, b) 同時是 s 的出流與 step2 s b 的入流，逐步對消）。
* `state_outflow_eq_occ2`：出流與 18 維特徵的橋——對 0/1 字，
  出流(g) = occ2 (g,0) + occ2 (g,1)（`F` 的兩個分量之和）。
* `flow_conservation_extIn`：canonical 起點 (1, K, 0) 與 extIn x 的實例。
* `inflow_eq_sum_occ2`（§50）：入流 = Σ_{(h,b) : step2 h b = g} occ2 (h, b)，
  16 條轉移邊的關聯結構；至此兩側都是 18 維特徵上的線性泛函。
* `kirchhoff_occ2` / `kirchhoff_occ2_extIn`：合併後的特徵層 Kirchhoff 關係。
* `runCarry_extIn`、`run2_extIn_terminal`（§51）：終末進位為 0，故終末狀態
  對**所有** x 恆落在 {(0,S,0), (0,S,1)}。
* `kirchhoff_occ2_extIn_clean`（6 條）／`kirchhoff_occ2_extIn_merged`（1 條）：
  終末指示消去後，A-3 上界要用的 7 條常數關係。

## 上界所需泛函（已用精確有理秩驗算，見 `tools/a3_functionals.py`）

死狀態 2 條 + 流守恆可用 7 條（秩 6）＝ 秩 8 ＝ 18 − dim span(ΔF) = 18 − 10，**完備**。
ROADMAP 舊表列的 `boundary_step_unique`（e₃+e₆=1）與 K 區交錯（e₄=e₅+e₆）
落在上述列空間內，是被蘊含的推論，**不需要另證**。

流守恆是 8 條（每個可達狀態一條），其中：8 條之和恆為零故至多 7 條獨立；
又因終末狀態恆落在 (0,S,0)/(0,S,1) 兩者之一（§51 `run2_extIn_terminal`），
這兩條的端點指示在 ΔF 上不個別對消，**須相加合併**成一條（合併後指示恆為 1）。
6 條乾淨 + 1 條合併 = 7 條，秩 6——即 §51 的 `_clean` 與 `_merged`。
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

/-! ## §50 入流分解：關聯結構落到特徵層

出流已由 `state_outflow_eq_occ2` 接上特徵；入流 `countP (step2 t.1 t.2 == g)` 還不是
`occ2` 的線性組合。本節補上

  in-flow(g) = Σ_{(h, b) : step2 h b = g} occ2 s w (h, b)

即把 8 狀態 × 2 位元 = **16 條轉移邊**的關聯結構寫進 Lean。邊表不是外部資料：
`inEdges` 由 `step2` 就地 `filter` 算出，`#guard` 只檢查它的結構性質。 -/

/-- 通用計數引理：若串列元素都落在無重複的有限集 `E` 裡，
則 `countP p` 等於 `E` 中滿足 `p` 的元素各自出現次數之和。 -/
private lemma count_filter_of_nodup {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) (a : α) :
    ∀ E : List α, E.Nodup → a ∈ E → (E.filter p).count a = if p a then 1 else 0 := by
  intro E
  induction E with
  | nil => intro _ ha; exact absurd ha (List.not_mem_nil)
  | cons e es ih =>
      intro hnd ha
      obtain ⟨hne, hes⟩ := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp ha with rfl | ha'
      · have hnot : a ∉ es.filter p := fun h => hne (List.mem_of_mem_filter h)
        by_cases hp : p a = true <;>
          simp [hp, List.count_eq_zero_of_not_mem hnot]
      · have hea : e ≠ a := fun h => hne (h ▸ ha')
        by_cases hp : p e = true <;>
          simp [hp, hea, ih hes ha']

private lemma sum_map_indicator {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ F : List α, (F.map (fun e => if a == e then 1 else 0)).sum = F.count a := by
  intro F
  induction F with
  | nil => rfl
  | cons e es ih =>
      rw [List.map_cons, List.sum_cons, ih, List.count_cons, BEq.comm (a := e)]
      omega

private lemma sum_map_count_cons {α : Type} [BEq α] [LawfulBEq α] (a : α) (l : List α)
    (F : List α) : (F.map (fun e => (a :: l).count e)).sum
      = (F.map (fun e => l.count e)).sum + F.count a := by
  rw [← sum_map_indicator a F]
  induction F with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, List.count_cons]
      omega

/-- `countP` 的有限集分解：`l.countP p = Σ_{e ∈ E, p e} l.count e`。 -/
theorem countP_eq_sum_count {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) (E : List α)
    (hE : E.Nodup) : ∀ l : List α, (∀ a ∈ l, a ∈ E) →
      l.countP p = ((E.filter p).map (fun e => l.count e)).sum := by
  intro l
  induction l with
  | nil => simp
  | cons a as ih =>
      intro h
      have ha : a ∈ E := h a (List.mem_cons_self ..)
      rw [List.countP_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy)),
        sum_map_count_cons, count_filter_of_nodup p a E hE ha]

/-- 16 條轉移邊：8 個可達狀態（`S8`）× 2 個輸入位元。 -/
def allEdges : List ((ℕ × Phase × ℕ) × ℕ) := S8.flatMap fun h => [(h, 0), (h, 1)]

lemma allEdges_nodup : allEdges.Nodup := by decide

/-- 落點為 `g` 的入邊。關聯結構由 `step2` 就地算出，非外部表格。 -/
def inEdges (g : ℕ × Phase × ℕ) : List ((ℕ × Phase × ℕ) × ℕ) :=
  allEdges.filter fun e => step2 e.1 e.2 == g

/-- trace 的每一筆都是 `S8` 狀態配上一個位元。 -/
theorem microTrace2_mem_S8 : ∀ (w : List ℕ) (s : ℕ × Phase × ℕ), s ∈ S8 → (∀ b ∈ w, b < 2) →
    ∀ t ∈ microTrace2 s w, t.1 ∈ S8 ∧ t.2 < 2 := by
  intro w
  induction w with
  | nil => intro _ _ _ t ht; cases ht
  | cons b bs ih =>
      intro s hs hw t ht
      have hb : b < 2 := hw b (List.mem_cons_self ..)
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨hs, hb⟩
      · exact ih (step2 s b) (S8_closed s hs b hb)
          (fun y hy => hw y (List.mem_cons_of_mem _ hy)) t ht'

lemma mem_allEdges {s : ℕ × Phase × ℕ} {b : ℕ} (h1 : s ∈ S8) (h2 : b < 2) :
    (s, b) ∈ allEdges := by
  rw [allEdges, List.mem_flatMap]
  exact ⟨s, h1, by interval_cases b <;> simp⟩

/-- **入流分解**：落點為 `g` 的步數 = 所有入邊的佔用特徵之和。
這使入流也成為 18 維特徵上的線性泛函。 -/
theorem inflow_eq_sum_occ2 (g : ℕ × Phase × ℕ) {s : ℕ × Phase × ℕ} (hs : s ∈ S8)
    {w : List ℕ} (hw : ∀ b ∈ w, b < 2) :
    (microTrace2 s w).countP (fun t => step2 t.1 t.2 == g)
      = ((inEdges g).map (fun e => occ2 s w e)).sum := by
  have h := countP_eq_sum_count (fun e : (ℕ × Phase × ℕ) × ℕ => step2 e.1 e.2 == g)
    allEdges allEdges_nodup (microTrace2 s w) fun t ht => by
      obtain ⟨h1, h2⟩ := microTrace2_mem_S8 w s hs hw t ht
      exact mem_allEdges h1 h2
  simpa [inEdges, occ2] using h

/-- **Kirchhoff 泛函（純特徵層）**：兩側都只由 `occ2` 與端點指示構成，
即 18 維特徵上的一條線性關係。A-3 上界的可用形式。 -/
theorem kirchhoff_occ2 (g : ℕ × Phase × ℕ) {s : ℕ × Phase × ℕ} (hs : s ∈ S8)
    {w : List ℕ} (hw : ∀ b ∈ w, b < 2) :
    ((inEdges g).map (fun e => occ2 s w e)).sum + (if s = g then 1 else 0)
      = occ2 s w (g, 0) + occ2 s w (g, 1) + (if run2 s w = g then 1 else 0) := by
  rw [← inflow_eq_sum_occ2 g hs hw, ← state_outflow_eq_occ2 g w s hw]
  exact microTrace2_flow_conservation g w s

/-- canonical 起點 (1, K, 0) 讀 `extIn x` 的特徵層實例。 -/
theorem kirchhoff_occ2_extIn (x : ℕ) (g : ℕ × Phase × ℕ) :
    ((inEdges g).map (fun e => occ2 (1, Phase.K, 0) (extIn x) e)).sum
        + (if ((1 : ℕ), Phase.K, (0 : ℕ)) = g then 1 else 0)
      = occ2 (1, Phase.K, 0) (extIn x) (g, 0) + occ2 (1, Phase.K, 0) (extIn x) (g, 1)
        + (if run2 (1, Phase.K, 0) (extIn x) = g then 1 else 0) :=
  kirchhoff_occ2 g (by decide) (extIn_bits x)

/-! ## §51 終末狀態，與由它得出的 7 條可用流守恆

`kirchhoff_occ2_extIn` 右端還帶著終末指示 `[run2 … = g]`，它隨 x 變動，
所以還不是「對所有 x 的常數關係」。本節把終末狀態釘死：

  對**所有** x（含 0、1 與偶數），`run2 (1,K,0) (extIn x) ∈ {(0,S,0), (0,S,1)}`

於此得到 A-3 上界要用的 7 條：6 個非終末狀態各一條（終末指示恆 0），
加上兩個可能終末**合併**的一條（合併後指示恆 1）。這正是
`tools/a3_functionals.py` 算出的「7 條、秩 6」的結構來源。 -/

/-- extIn 的兩個哨兵零把進位沖到 0（進位 < 3 時，`c → c/2 → 0`）。
Core 只有這條的 `#eval`（`Collatz_FST_Monoid.lean` §16），這裡定理化。 -/
lemma runCarry_two_zeros {c : ℕ} (hc : c < 3) : runCarry [0, 0] c = 0 := by
  interval_cases c <;> decide

lemma digits_two_bits (x : ℕ) : ∀ b ∈ Nat.digits 2 x, b < 2 := fun b hb =>
  extIn_bits x b (List.mem_append_left _ hb)

/-- **讀完 extIn x 後最終進位為 0**。兩個哨兵零之前進位已受 `run_carry_lt_three`
約束在 `< 3`，兩步整除即歸零。 -/
theorem runCarry_extIn (x : ℕ) : runCarry (extIn x) 1 = 0 := by
  show runCarry (Nat.digits 2 x ++ [0, 0]) 1 = 0
  rw [t_append]
  exact runCarry_two_zeros (run_carry_lt_three (by norm_num) (digits_two_bits x))

/-- **終末狀態定理**：讀完 `extIn x` 後的 Level 2 狀態恆為 `(0,S,0)` 或 `(0,S,1)`。
對**所有** x 成立——含 `x = 0`、`x = 1` 與偶數，與奇偶無關。

兩個成分：終末進位為 0（`runCarry_extIn`）；終末落在 8 個可達狀態內
（`run2_mem_S8`）。關鍵在於 **`S8` 已經排除了死狀態 `(0,K,0)`**——這正是
「K 相位進位恆 ∈ {1,2}」那條不變量，Core 已用 `Inv` / `inv_step` / `S8_closed`
證掉（K→K 只在 `3b+c` 為偶時發生，`c=1` 只能走 `b=1`→`c=2`、`c=2` 只能走
`b=0`→`c=1`，互跳而碰不到 0；起點 `(1,K,0)` 的進位是 1）。
於是「進位 = 0」把 `S8` 的 8 個候選砍到只剩兩個 S 狀態。 -/
theorem run2_extIn_terminal (x : ℕ) :
    run2 (1, Phase.K, 0) (extIn x) = ((0 : ℕ), Phase.S, (0 : ℕ))
      ∨ run2 (1, Phase.K, 0) (extIn x) = ((0 : ℕ), Phase.S, (1 : ℕ)) := by
  have key : ∀ s ∈ S8, s.1 = 0 →
      s = ((0 : ℕ), Phase.S, (0 : ℕ)) ∨ s = ((0 : ℕ), Phase.S, (1 : ℕ)) := by decide
  exact key _ (run2_mem_S8 (extIn_bits x))
    (by rw [run2_fst]; exact runCarry_extIn x)

/-- 非終末狀態的**乾淨流守恆**（6 條）：終末指示恆為 0，
整條關係只剩 `occ2` 與初始指示，對所有 x 為同一條常數關係。 -/
theorem kirchhoff_occ2_extIn_clean (x : ℕ) (g : ℕ × Phase × ℕ)
    (h0 : g ≠ ((0 : ℕ), Phase.S, (0 : ℕ))) (h1 : g ≠ ((0 : ℕ), Phase.S, (1 : ℕ))) :
    ((inEdges g).map (fun e => occ2 (1, Phase.K, 0) (extIn x) e)).sum
        + (if ((1 : ℕ), Phase.K, (0 : ℕ)) = g then 1 else 0)
      = occ2 (1, Phase.K, 0) (extIn x) (g, 0) + occ2 (1, Phase.K, 0) (extIn x) (g, 1) := by
  have hne : run2 (1, Phase.K, 0) (extIn x) ≠ g := by
    rcases run2_extIn_terminal x with h | h <;> rw [h] <;> exact fun hh => by
      first | exact h0 hh.symm | exact h1 hh.symm
  rw [kirchhoff_occ2_extIn x g, if_neg hne, Nat.add_zero]

/-- 兩個可能終末的**合併流守恆**（第 7 條）：單獨看終末指示隨 x 變動，
相加後恆為 1（`run2_extIn_terminal` 說恰好落在其中一個），於是又成為常數關係。 -/
theorem kirchhoff_occ2_extIn_merged (x : ℕ) :
    ((inEdges ((0 : ℕ), Phase.S, (0 : ℕ))).map (fun e => occ2 (1, Phase.K, 0) (extIn x) e)).sum
        + ((inEdges ((0 : ℕ), Phase.S, (1 : ℕ))).map
            (fun e => occ2 (1, Phase.K, 0) (extIn x) e)).sum
      = (occ2 (1, Phase.K, 0) (extIn x) (((0 : ℕ), Phase.S, (0 : ℕ)), 0)
          + occ2 (1, Phase.K, 0) (extIn x) (((0 : ℕ), Phase.S, (0 : ℕ)), 1))
        + (occ2 (1, Phase.K, 0) (extIn x) (((0 : ℕ), Phase.S, (1 : ℕ)), 0)
            + occ2 (1, Phase.K, 0) (extIn x) (((0 : ℕ), Phase.S, (1 : ℕ)), 1))
        + 1 := by
  have e0 := kirchhoff_occ2_extIn x ((0 : ℕ), Phase.S, (0 : ℕ))
  have e1 := kirchhoff_occ2_extIn x ((0 : ℕ), Phase.S, (1 : ℕ))
  have hinit0 : ¬ (((1 : ℕ), Phase.K, (0 : ℕ)) = ((0 : ℕ), Phase.S, (0 : ℕ))) := by decide
  have hinit1 : ¬ (((1 : ℕ), Phase.K, (0 : ℕ)) = ((0 : ℕ), Phase.S, (1 : ℕ))) := by decide
  rw [if_neg hinit0, Nat.add_zero] at e0
  rw [if_neg hinit1, Nat.add_zero] at e1
  have hsum : (if run2 (1, Phase.K, 0) (extIn x) = ((0 : ℕ), Phase.S, (0 : ℕ)) then 1 else 0)
      + (if run2 (1, Phase.K, 0) (extIn x) = ((0 : ℕ), Phase.S, (1 : ℕ)) then 1 else 0) = 1 := by
    rcases run2_extIn_terminal x with h | h <;> rw [h] <;> decide
  omega

/-! ## 數據驗證（回歸；`#guard` 失敗即 build 紅） -/

section Verification

-- 流守恆：S8 全狀態 × x < 120
#guard (List.range 120).all fun x =>
  S8.all fun g =>
    (microTrace2 (1, Phase.K, 0) (extIn x)).countP (fun t => step2 t.1 t.2 == g)
        + (if ((1 : ℕ), Phase.K, (0 : ℕ)) = g then 1 else 0)
      == (microTrace2 (1, Phase.K, 0) (extIn x)).countP (fun t => t.1 == g)
        + (if run2 (1, Phase.K, 0) (extIn x) = g then 1 else 0)

-- 出流橋：S8 全狀態 × x < 120
#guard (List.range 120).all fun x =>
  S8.all fun g =>
    (microTrace2 (1, Phase.K, 0) (extIn x)).countP (fun t => t.1 == g)
      == occ2 (1, Phase.K, 0) (extIn x) (g, 0) + occ2 (1, Phase.K, 0) (extIn x) (g, 1)

-- 邊表結構：16 條邊、無重複、每條邊恰屬於一個狀態的入邊表
#guard allEdges.length == 16
#guard (S8.map fun g => (inEdges g).length).sum == 16

-- 入流分解：S8 全狀態 × x < 120
#guard (List.range 120).all fun x =>
  S8.all fun g =>
    (microTrace2 (1, Phase.K, 0) (extIn x)).countP (fun t => step2 t.1 t.2 == g)
      == ((inEdges g).map fun e => occ2 (1, Phase.K, 0) (extIn x) e).sum

-- 終末狀態恆落在 {(0,S,0), (0,S,1)}（下一步合併那兩條流守恆的依據）
#guard (List.range 120).all fun x =>
  run2 (1, Phase.K, 0) (extIn (2 * x + 3)) ∈ [((0 : ℕ), Phase.S, (0 : ℕ)), (0, Phase.S, 1)]

end Verification

end CollatzFST.Flow
