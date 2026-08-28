/-
# Project B 第三批：Nonnegative Reweighting Theorem——B1a
（定義層＋(1)⟹(2)＋(3)⟹(1)＋吸收恆等式＋玩具電池）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。設計核准 2026-08-28
（B1-DESIGN-REPORT；Q1–Q4 與偏差點 D1/D2/D3 全項通過）。
(2)⟹(3)（有界長最短路勢能）在 B1b 同檔追加，對本批純追加零改動。

## 內容

* **§B1.1 載體與定義層**：`CostAutomaton`——抽象確定性有理權重成本自動機
  （單一初態、接受集 `Finset`、邊權 `w`、初始常數 `α`、終權 `β`）。**零 Collatz
  內容、import 純 mathlib**（連 `Core/` 都不需要）。`evalFrom`/`wpath` 與
  望遠鏡引擎 `evalFrom_append`/`wpath_append`；witness 形的
  `Reach`/`CoReach`/`Useful`/`UsefulEdge`；三個敘述端點
  `BoundedBelow`/`CyclesNonneg`/`HasPotential`。
* **§B1.2 (1)⟹(2)**（`cyclesNonneg_of_boundedBelow`）：pump k 圈＋阿基米德。
  無需任何 Fintype——pump 見證就是 `Useful` 存在量詞裡的字（Q2）。
* **§B1.3 (3)⟹(1)**（`boundedBelow_of_hasPotential`）：望遠鏡直接界。
  亦無需 Fintype（下界的 min 在 `accept : Finset` 上取）。
* **§B1.4 吸收恆等式**（`reweight_cost`）：Johnson reweighting
  `w′ = w + h∘src − h∘dst`、`α′ = α − h(init)`、`β′ = β + h` 之下
  cost **逐字恆等**（對全體字、非只接受字；與三條蘊含正交，任意 h 都成立）。

## 技術註記（設計定案）

1. **D1**：`CyclesNonneg` 不帶 `c ≠ []`——空閉走行權重 0，兩形逐字等價，
   消費端少一個 side condition。
2. **D2**：「位於某條接受路徑上的 cycle」形式化為「錨在 useful 態的閉走行」。
   接受路徑上的 cycle 其錨點必 useful；反向 `u ++ cᵏ ++ v` 就是接受路徑
   （`cyclesNonneg_of_boundedBelow` 證明內顯式構造）。旋轉不必另計。
3. **D3**：勢能 h 不吸收 α（ROADMAP 的 super-source 版把 α 放進距離；等價，
   α 留在 `cost`／下界處讓 `potential`（B1b）與 `reweight` 介面最簡）。
4. instance 經濟學：本批三條主定理**零 Fintype 需求**；
   `[Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]` 只有 B1b 的
   (2)⟹(3) 需要。`toDFA` 是 B1b 借 mathlib `DFA.evalFrom_split` 的橋，
   先與定義層一同落地（設計 §2.1）。
5. 結論 (3) 只對 `UsefulEdge` 宣稱——從 useful 態指向死區的邊不在保證範圍
   （ROADMAP B1 措辭紀律）；死區的 h 值在 B1b 構造中任取 0。
-/
import Mathlib.Computability.DFA
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Field.Rat

namespace CollatzFST.ProjectB

/-- 抽象確定性有理權重成本自動機（ROADMAP-B B1 載體，Q1 設計定案為完全抽象）：
單一初態 `init`、確定性轉移 `step`、接受集 `accept`（`Finset`，可判定性免費）、
邊權 `w`、初始常數 `α`、終權 `β`。有限性假設不進結構體，
在用到的定理處以 instance 參數帶入（本批三條主定理都不需要）。 -/
structure CostAutomaton (Q A : Type*) where
  /-- 初始狀態。 -/
  init : Q
  /-- 確定性狀態轉移。 -/
  step : Q → A → Q
  /-- 接受集。 -/
  accept : Finset Q
  /-- 邊權。 -/
  w : Q → A → ℚ
  /-- 初始常數權重。 -/
  α : ℚ
  /-- 終權。 -/
  β : Q → ℚ

namespace CostAutomaton

variable {Q A : Type*} (M : CostAutomaton Q A)

/-! ## §B1.1 定義層 -/

/-- 走行（與 mathlib `DFA.evalFrom` 同一 `foldl`，`toDFA_evalFrom` rfl 級互通）。 -/
def evalFrom (q : Q) (u : List A) : Q := u.foldl M.step q

@[simp] lemma evalFrom_nil (q : Q) : M.evalFrom q [] = q := rfl

lemma evalFrom_cons (q : Q) (a : A) (u : List A) :
    M.evalFrom q (a :: u) = M.evalFrom (M.step q a) u := rfl

lemma evalFrom_append (q : Q) (u v : List A) :
    M.evalFrom q (u ++ v) = M.evalFrom (M.evalFrom q u) v := by
  simp [evalFrom, List.foldl_append]

/-- 底層 DFA（B1b 借 mathlib `DFA.evalFrom_split` 做鴿籠萃取的橋）。 -/
def toDFA : DFA A Q := ⟨M.step, M.init, ↑M.accept⟩

lemma toDFA_evalFrom (q : Q) (u : List A) : M.toDFA.evalFrom q u = M.evalFrom q u := rfl

/-- 路徑權重：從 q 讀 u 沿途邊權之和。 -/
def wpath : Q → List A → ℚ
  | _, [] => 0
  | q, a :: u => M.w q a + wpath (M.step q a) u

@[simp] lemma wpath_nil (q : Q) : M.wpath q [] = 0 := rfl

lemma wpath_cons (q : Q) (a : A) (u : List A) :
    M.wpath q (a :: u) = M.w q a + M.wpath (M.step q a) u := rfl

/-- 望遠鏡引擎：路徑權重對串接可加。 -/
lemma wpath_append (q : Q) (u v : List A) :
    M.wpath q (u ++ v) = M.wpath q u + M.wpath (M.evalFrom q u) v := by
  induction u generalizing q with
  | nil => simp
  | cons a t ih => simp only [List.cons_append, wpath_cons, evalFrom_cons, ih, add_assoc]

/-- 接受謂詞。 -/
def Accepts (u : List A) : Prop := M.evalFrom M.init u ∈ M.accept

/-- 成本：`α + Σ邊權 + 終權`。對全體字有定義；諸敘述只對 `Accepts` 量化。 -/
def cost (u : List A) : ℚ := M.α + M.wpath M.init u + M.β (M.evalFrom M.init u)

/-- 可達（witness 形，Q2 設計定案）。 -/
def Reach (q : Q) : Prop := ∃ u, M.evalFrom M.init u = q

/-- 可出（可從 q 走到接受態）。 -/
def CoReach (q : Q) : Prop := ∃ v, M.evalFrom q v ∈ M.accept

/-- useful 態：可達 ∧ 可出（非 co-reachable 區域由此明確排除）。 -/
def Useful (q : Q) : Prop := M.Reach q ∧ M.CoReach q

/-- useful 邊：兩端皆 useful（等價於「位於某條接受路徑上」——
`u ++ [a] ++ v` 就是接受路徑；(3) 只對 useful 邊宣稱）。 -/
def UsefulEdge (q : Q) (a : A) : Prop := M.Useful q ∧ M.Useful (M.step q a)

/-- **(1)** 接受字的成本集合有一致下界。 -/
def BoundedBelow : Prop := ∃ B : ℚ, ∀ u, M.Accepts u → B ≤ M.cost u

/-- **(2)** 每條 useful cycle（錨在 useful 態的閉走行；D2）總權重非負。
不帶 `c ≠ []`（D1：空閉走行權重 0，兩形逐字等價）。 -/
def CyclesNonneg : Prop := ∀ q c, M.Useful q → M.evalFrom q c = q → 0 ≤ M.wpath q c

/-- **(3)** 存在勢能 `h : Q → ℚ` 使每條 **useful** 邊滿足
`0 ≤ w(e) + h(src e) − h(dst e)`。 -/
def HasPotential : Prop :=
  ∃ h : Q → ℚ, ∀ q a, M.UsefulEdge q a → 0 ≤ M.w q a + h q - h (M.step q a)

/-! ## §B1.2 (1)⟹(2)：pump k 圈＋阿基米德 -/

/-- k 次重複（pump 用的證明內部件）。 -/
private def npow (c : List A) : ℕ → List A
  | 0 => []
  | k + 1 => c ++ npow c k

private lemma evalFrom_npow {q : Q} {c : List A} (hc : M.evalFrom q c = q) (k : ℕ) :
    M.evalFrom q (npow c k) = q := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show M.evalFrom q (c ++ npow c k) = q
      rw [M.evalFrom_append, hc, ih]

private lemma wpath_npow {q : Q} {c : List A} (hc : M.evalFrom q c = q) (k : ℕ) :
    M.wpath q (npow c k) = k * M.wpath q c := by
  induction k with
  | zero => simp [npow]
  | succ k ih =>
      show M.wpath q (c ++ npow c k) = _
      rw [M.wpath_append, hc, ih]
      push_cast
      ring

/-- **B1 (1)⟹(2)**（ROADMAP-B B1）：成本有一致下界 ⟹ 每條 useful cycle 總權重非負。
反設負循環：`Reach`/`CoReach` 的見證 `u`/`v` 給出接受字族 `u ++ cᵏ ++ v`
（pump 全在語言內完成），成本 = 基底 + k·(循環權)，阿基米德取 k 沖破下界。
無需任何 Fintype。 -/
theorem cyclesNonneg_of_boundedBelow (h1 : M.BoundedBelow) : M.CyclesNonneg := by
  rintro q c ⟨⟨u, hu⟩, v, hv⟩ hc
  by_contra hneg
  push_neg at hneg
  obtain ⟨B, hB⟩ := h1
  -- 終態對 k 固定
  have hrun : ∀ k : ℕ, M.evalFrom M.init (u ++ npow c k ++ v) = M.evalFrom q v := by
    intro k
    rw [M.evalFrom_append, M.evalFrom_append, hu, M.evalFrom_npow hc]
  have hacc : ∀ k : ℕ, M.Accepts (u ++ npow c k ++ v) := by
    intro k
    show M.evalFrom M.init (u ++ npow c k ++ v) ∈ M.accept
    rw [hrun k]
    exact hv
  have hw : ∀ k : ℕ, M.wpath M.init (u ++ npow c k ++ v)
      = M.wpath M.init u + k * M.wpath q c + M.wpath q v := by
    intro k
    rw [M.wpath_append, M.wpath_append, M.evalFrom_append, hu, M.evalFrom_npow hc,
      M.wpath_npow hc]
  have hcost : ∀ k : ℕ, M.cost (u ++ npow c k ++ v)
      = (M.α + M.wpath M.init u + M.wpath q v + M.β (M.evalFrom q v))
          + k * M.wpath q c := by
    intro k
    simp only [cost, hw k, hrun k]
    ring
  -- 阿基米德：取 k 使成本 < B
  set C : ℚ := M.α + M.wpath M.init u + M.wpath q v + M.β (M.evalFrom q v) with hCdef
  have hwc : (0 : ℚ) < -M.wpath q c := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((C - B) / (-M.wpath q c))
  have hmul : C - B < k * (-M.wpath q c) := (div_lt_iff₀ hwc).mp hk
  rw [mul_neg] at hmul
  have hlt : M.cost (u ++ npow c k ++ v) < B := by
    rw [hcost k]
    linarith
  exact absurd (hB _ (hacc k)) (not_le.mpr hlt)

/-! ## §B1.3 (3)⟹(1)：望遠鏡直接界 -/

/-- 望遠鏡引理（證明內部件）：接受字沿途的每條邊自動 useful——兩端的
`Reach`/`CoReach` 見證就是當前前綴／後綴（Q2 設計預期），故勢能不等式可沿字累加。 -/
private lemma potential_telescope {h : Q → ℚ}
    (hh : ∀ q a, M.UsefulEdge q a → 0 ≤ M.w q a + h q - h (M.step q a)) :
    ∀ (u : List A) (q : Q), M.Reach q → M.evalFrom q u ∈ M.accept →
      h (M.evalFrom q u) - h q ≤ M.wpath q u := by
  intro u
  induction u with
  | nil => intro q _ _; simp
  | cons a t ih =>
      intro q hq hacc
      have hacc' : M.evalFrom (M.step q a) t ∈ M.accept := hacc
      have hstep : M.Reach (M.step q a) := by
        obtain ⟨u₀, hu₀⟩ := hq
        exact ⟨u₀ ++ [a], by rw [M.evalFrom_append, hu₀]; rfl⟩
      have hedge : M.UsefulEdge q a :=
        ⟨⟨hq, ⟨a :: t, hacc⟩⟩, ⟨hstep, ⟨t, hacc'⟩⟩⟩
      have h1 := hh q a hedge
      have h2 := ih (M.step q a) hstep hacc'
      rw [M.wpath_cons, show M.evalFrom q (a :: t) = M.evalFrom (M.step q a) t from rfl]
      linarith

/-- **B1 (3)⟹(1)**（ROADMAP-B B1）：useful-edge 勢能 ⟹ 成本一致下界
`B = α − h(init) + min_{t ∈ accept} (β t + h t)`。無需 Fintype
（min 在 `accept : Finset` 上取；接受集空時任取下界，量詞空虛成立）。 -/
theorem boundedBelow_of_hasPotential (h3 : M.HasPotential) : M.BoundedBelow := by
  obtain ⟨h, hh⟩ := h3
  rcases Finset.eq_empty_or_nonempty M.accept with hemp | hne
  · exact ⟨0, fun u hu => by simp [Accepts, hemp] at hu⟩
  · refine ⟨M.α - h M.init + (M.accept.image fun t => M.β t + h t).min' (hne.image _),
      fun u hu => ?_⟩
    have hu' : M.evalFrom M.init u ∈ M.accept := hu
    have htel : h (M.evalFrom M.init u) - h M.init ≤ M.wpath M.init u :=
      M.potential_telescope hh u M.init ⟨[], rfl⟩ hu'
    have hmin : (M.accept.image fun t => M.β t + h t).min' (hne.image _)
        ≤ M.β (M.evalFrom M.init u) + h (M.evalFrom M.init u) :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ hu')
    simp only [cost]
    linarith

/-! ## §B1.4 吸收恆等式（Johnson reweighting；與三條蘊含正交） -/

/-- Johnson reweighting：`w′ = w + h∘src − h∘dst`、`α′ = α − h(init)`、
`β′ = β + h`；`init`/`step`/`accept` 原封不動。 -/
def reweight (h : Q → ℚ) : CostAutomaton Q A where
  init := M.init
  step := M.step
  accept := M.accept
  w := fun q a => M.w q a + h q - h (M.step q a)
  α := M.α - h M.init
  β := fun q => M.β q + h q

@[simp] lemma reweight_init (h : Q → ℚ) : (M.reweight h).init = M.init := rfl
@[simp] lemma reweight_step (h : Q → ℚ) (q : Q) (a : A) :
    (M.reweight h).step q a = M.step q a := rfl
@[simp] lemma reweight_accept (h : Q → ℚ) : (M.reweight h).accept = M.accept := rfl
@[simp] lemma reweight_w (h : Q → ℚ) (q : Q) (a : A) :
    (M.reweight h).w q a = M.w q a + h q - h (M.step q a) := rfl
@[simp] lemma reweight_α (h : Q → ℚ) : (M.reweight h).α = M.α - h M.init := rfl
@[simp] lemma reweight_β (h : Q → ℚ) (q : Q) : (M.reweight h).β q = M.β q + h q := rfl
@[simp] lemma reweight_evalFrom (h : Q → ℚ) (q : Q) (u : List A) :
    (M.reweight h).evalFrom q u = M.evalFrom q u := rfl

/-- 望遠鏡本體：reweighted 路徑權重 = 原路徑權重 + 端點勢能差。 -/
lemma reweight_wpath (h : Q → ℚ) (q : Q) (u : List A) :
    (M.reweight h).wpath q u = M.wpath q u + h q - h (M.evalFrom q u) := by
  induction u generalizing q with
  | nil => simp
  | cons a t ih =>
      simp only [wpath_cons, reweight_w, reweight_step, evalFrom_cons, ih]
      ring

/-- **B1 吸收恆等式**（ROADMAP-B B1）：reweighted cost 與原 cost **逐字恆等**
（對全體字、非只接受字；任意 h 都成立，與三條蘊含正交）。嚴格下降、下界、
任兩字差值的保持全是此恆等式的即時推論，由消費者（B1.5 structured gauge、B3）
就地取用，本檔不另列 API。 -/
theorem reweight_cost (h : Q → ℚ) (u : List A) : (M.reweight h).cost u = M.cost u := by
  simp only [cost, reweight_α, reweight_β, reweight_init, reweight_evalFrom,
    reweight_wpath]
  ring

end CostAutomaton

/-! ## §B1.V 數據驗證（全部應輸出 `true`）

玩具電池（B1a 份；B1b 補機算 `potential` 的項）：狀態 `Fin 3`、字母 `Fin 2`。
`Mneg` = 負例（useful 自環權 −1，(2) 失敗、pump 可見地無下界）；
`Mpos` = 正例（含負權邊但全循環非負，手寫勢能 `hpos` 非平凡）。 -/

section Verification

open CostAutomaton

/-- 負例：`0 →ₐ 1`（w 0）、`1 →ₐ 1`（自環 w −1）、`1 →_b 2`（w 0）、accept {2}
（字母 a = 0、b = 1；其餘轉移收到 2 的自環）。 -/
private def Mneg : CostAutomaton (Fin 3) (Fin 2) where
  init := 0
  step := fun q a => if q = 0 then 1 else if q = 1 then (if a = 0 then 1 else 2) else 2
  accept := {2}
  w := fun q a => if q = 1 ∧ a = 0 then -1 else 0
  α := 0
  β := fun _ => 0

-- 自環 usefulness 的具體見證：Reach 1、CoReach 1、閉走行、負權——(2) 失敗
#eval decide (Mneg.evalFrom Mneg.init [0] = 1)
#eval decide (Mneg.evalFrom 1 [1] ∈ Mneg.accept)
#eval decide (Mneg.evalFrom 1 [0] = 1)
#eval decide (Mneg.wpath 1 [0] < 0)

-- pump 可見形：cost ([0] ++ 0ᵏ ++ [1]) 對 k = 0..3 嚴格遞減（(1) 失敗的機制）
#eval ([0, 1, 2, 3] : List ℕ).all fun k =>
  decide (Mneg.cost ([0] ++ List.replicate (k + 1) 0 ++ [1])
        < Mneg.cost ([0] ++ List.replicate k 0 ++ [1]))

/-- 正例：`0 →ₐ 1`（w −2）、`1 →ₐ 0`（w 3）、`1 →_b 2`（w −1）、`0 →_b 2`（w 0）、
accept {2}。全循環非負（0→1→0 權 1、2 自環權 0），含負權邊使勢能非平凡；
α、β 取非零讓恆等式測試更有內容。 -/
private def Mpos : CostAutomaton (Fin 3) (Fin 2) where
  init := 0
  step := fun q a =>
    if q = 0 then (if a = 0 then 1 else 2)
    else if q = 1 then (if a = 0 then 0 else 2)
    else 2
  accept := {2}
  w := fun q a =>
    if q = 0 ∧ a = 0 then -2
    else if q = 1 ∧ a = 0 then 3
    else if q = 1 ∧ a = 1 then -1
    else 0
  α := 5
  β := fun q => if q = 2 then 7 else 0

/-- 手寫勢能（= 各態最短路徑權重；B1b 的 `potential` 應算出同值，屆時升級為機算）。 -/
private def hpos : Fin 3 → ℚ := fun q => if q = 0 then 0 else if q = 1 then -2 else -3

-- usefulness 見證：三個狀態各一條 Reach 與 CoReach 的具體字（本例全態 useful）
#eval decide (Mpos.evalFrom Mpos.init [] = 0) && decide (Mpos.evalFrom 0 [1] ∈ Mpos.accept)
#eval decide (Mpos.evalFrom Mpos.init [0] = 1) && decide (Mpos.evalFrom 1 [1] ∈ Mpos.accept)
#eval decide (Mpos.evalFrom Mpos.init [1] = 2) && decide (Mpos.evalFrom 2 [] ∈ Mpos.accept)

-- 三角不等式：全體邊（本例全 useful）0 ≤ w q a + h q − h (step q a)
#eval ([0, 1, 2] : List (Fin 3)).all fun q => ([0, 1] : List (Fin 2)).all fun a =>
  decide (0 ≤ Mpos.w q a + hpos q - hpos (Mpos.step q a))

-- reweight 後全邊權非負（gauge 之後「θ ≥ 0」是 WLOG 的可見形）
#eval ([0, 1, 2] : List (Fin 3)).all fun q => ([0, 1] : List (Fin 2)).all fun a =>
  decide (0 ≤ (Mpos.reweight hpos).w q a)

private def words2 : ℕ → List (List (Fin 2))
  | 0 => [[]]
  | n + 1 => (words2 n).flatMap fun w => [0 :: w, 1 :: w]

-- 吸收恆等式：長 ≤ 6 全字枚舉，reweighted cost ≡ 原 cost
#eval ((List.range 7).flatMap words2).all fun u =>
  decide ((Mpos.reweight hpos).cost u = Mpos.cost u)

-- 恆等式與 (2) 正交：負例配任意 h（借 hpos）恆等式照樣成立
#eval ((List.range 7).flatMap words2).all fun u =>
  decide ((Mneg.reweight hpos).cost u = Mneg.cost u)

end Verification

end CollatzFST.ProjectB
