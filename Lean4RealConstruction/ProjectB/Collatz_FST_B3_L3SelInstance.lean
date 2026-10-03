/-
# Project B 第九批（下）：R-B-L3——L3 雙模式 Sel 實例化（模式追蹤乘積 × 旗標；B3 三條重推收口）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。設計核准 2026-10-03
（RB-L3-DESIGN-REPORT；Q1–Q7 作答與裁決點 E1–E11 全項通過：E7 單 PR 兩檔、E3 歸納帳 5 條、E6 跨層恆等升格）。

把 A 的 Level 3 terminal-affine 雙模式模板（#39 `V3`：`V(x) = β_{m(x),t(x)} + θ_{m(x)}ᵀ F3(x)`，
m = `F3[33]`、t = 終態第三分量）誠實實例化為 B1.5 的 `SelCostAutomaton`——R-B（`Collatz_FST_B3_SelInstance.lean`，
Level 2）逐項鏡射到 B 側 L3 語義層（姊妹檔 `Collatz_FST_B3_L3Machine.lean`）之上：底層機器 = L3 機器 × B0 `extDFA`
× 旗標（`Bool`），旗標於機器態 ((2,K,0),0) 讀 1（B 座標 33）時置真、`sel = 旗標`；`w m = θ m ∘ featIdx3_B ∘ unmark`；
β 於兩終態取 `βv (sel) t`、餘 0。**零 ProjectA import**；素材全 B 自產——`F3_B 2011 = F3_B 1787` 與終末位在
B 座標重新 `decide`、終態定理由 Core 錨重推；Todd 鏈 `Todd_1787`／`Todd_2681` 與見證集 `WB1787` 取自 R-B（B0 `U` 自產，
見證 1787 是問題輸入）。至此 ROADMAP-B B3「用 B 框架重推三條 no-go」**全數收口**：L2 單模式（B3a／B3c）、
L2 雙模式（R-B）、L3 雙模式（本檔）。

**證明路線是軌道（A-5 的 1787 → 2681 → 2011），不是 gauge**：`structured_gauge` 未被使用（其 `Fintype QF3`／
`Fintype (Option ℕ)` 前提在本實例亦不成立）；(c) 的 `BoundedBelow` 形只是把「gauge 目標類（Sel 實例的
bounded-below 類）在此模板上為空」寫成 kernel 可見的形式紀錄，假設在證明中棄置（a fortiori）。

## 內容

* **§L.6 載體**：`QF3 := (L3State_B × LSt) × Bool`、`flagUpd3`／`flagStep3`／`initF3`、`βsel3`、`termStates3`、
  **`SelInst3 θ βv`**（`selF` 沿用 R-B）。
* **§L.7 走行**：`flagVal3`；兩條記帳級歸納 `evalFrom_flag3`（④，走行三分量顯式）與 `wpath_flag3`（⑤）。
* **§L.8 旗標接地**：`flagB3`、`modeB3`、`termB3`、`evalFrom_extInM3`、**`flag_iff3 : flagB3 x = true ↔ F3_B x 33 = 1`**、
  `selF_flagB3`。
* **§L.9 β 與成本橋**：`βsel3_final`、`wpath_sum3`、
  **`cost_eq_sel3 : cost (SelInst3 θ βv) (extInM x) = βv (modeB3 x) (termB3 x) + ∑ i, θ (modeB3 x) i * F3_B x i`**
  （對全體 x）、`accepts_extInM_sel3`。
* **§L.10 三層定理與隨附**：`orbit_cost_eq3`（∀ θ βv）、`no_go_sel3_signed`（無符號 2 見證）、
  `no_go_sel3_bounded_below`（`BoundedBelow` 逐字為假設）；全稱兩式 `no_go_sel3_signed_odd`／`_lang`、
  任意函數版 `no_feature_ranking_orbit3_B`。
* **§L.11 跨層恆等（E6）**：`flagB3_eq_flagB`、**`modeB3_eq_modeB`**（L3 模式 = L2 模式，全體 x）、`termB3_eq`。
* **§L.V2 電池**：字面即 `tools/b3_attest.py` §J 的錨。

## 技術註記（設計定案）

1. **E3（歸納帳）**：本檔 2 條（④ `evalFrom_flag3`、⑤ `wpath_flag3`，R-B `evalFrom_flag`／`wpath_flag` 鏡射），
   姊妹檔 3 條（① trace 閉包、② trace 投影、③ run 投影）——兩檔合計恰 5；`flag_iff3`、成本橋、三層定理、
   跨層恆等皆零歸納。
2. **E5（終末位）**：t = 較舊歷史位（#39 L3 的編碼 `(run3 …).2.2.1`，A 的 h₂ = B 的 h）：((0,S,1),0)（A (0,S,0,1)）↦ t = 0、
   ((0,S,0),1)（A (0,S,1,0)）↦ t = 1。β 只看機器分量（R-B D4），橋因此對全體 x 成立；接受集 = 兩終態 × {tail2} × Bool（4 態）。
3. R-B D1–D11 照辦：旗標 `Bool`（`Bool.or_assoc`＋`decide_or`）、參數形 `θ : Fin 2 → Fin 48 → ℚ`、`βv : Fin 2 → Fin 2 → ℚ`、
   哨兵經 `unmark` 讀 0 照常計費且永不置旗標。
4. **E6（跨層恆等）**：L3 trace 經 ② 投影即 L2 trace，L2 trace 上的 ((2,K,0),1) 由 Inv3（K ⇒ 歷史 (0,0)）回拉為
   (bndK3, 1)——故 L3 旗標 = R-B 的 L2 旗標、L3 模式位 = L2 模式位（全體 x）；終末位互補（③ ＋ 終態定理）。
   A 的「模式跨層恆等」只在 `L3_2Mode_Recon` §43 以 `#eval` 驗 x < 250，此為**全稱定理**——B 抽象首次反哺 A 沒有的定理。
5. 零 `Fintype`、零 `maxHeartbeats` 調整、零 native 求值；`#print axioms` 僅標準公理。
6. 明確不做：Recon 的 A↔B 等價定理（`V3 … x = cost (SelInst3 …) (extInM x)` 需跨界 import；attest §J 是唯一合法橋）；
   gauge 的任何應用；D(θ)／`rdDFA` 鏡射；`Fintype` 化；paper／registry。
-/
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_L3Machine
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_SelInstance

namespace CollatzFST.ProjectB

/-! ## §L.6 載體：L3 模式追蹤乘積 × 旗標 -/

/-- L3 模式追蹤乘積態：(L3 機器 × B0 DFA) × 旗標 `Bool`（R-B D1）。 -/
abbrev QF3 := (L3State_B × LSt) × Bool

/-- 旗標更新：於機器態 ((2,K,0),0) 讀（去標記）位元 1 時置真，餘傳遞。哨兵 `none` 讀 0，永不置真。 -/
def flagUpd3 (q : L3State_B) (a : Option ℕ) (f : Bool) : Bool :=
  f || decide ((q, unmark a) = (bndK3, 1))

/-- 乘積一步：B0 `prodStep step3_B` × 旗標更新。 -/
def flagStep3 (p : QF3) (a : Option ℕ) : QF3 :=
  (prodStep step3_B p.1 a, flagUpd3 p.1.1 a p.2)

/-- 初態：(`init3_B`, `start`) × 旗標 false。 -/
def initF3 : QF3 := ((init3_B, LSt.start), false)

/-- 終權 β（E5）：機器分量 ((0,S,1),0) 取 `βv (sel p) 0`、((0,S,0),1) 取 `βv (sel p) 1`、餘 0。只看機器分量——
接受字的 DFA 分量恆為 `tail2`，故在 4 個接受態上恰為 β_{m,t}；非接受態的值是 don't-care（B1.5 D5 語義）。 -/
def βsel3 (βv : Fin 2 → Fin 2 → ℚ) (p : QF3) : ℚ :=
  if p.1.1 = ((0, Phase.S, 1), 0) then βv (selF p.2) 0
  else if p.1.1 = ((0, Phase.S, 0), 1) then βv (selF p.2) 1
  else 0

/-- 終末乘積態的機器×DFA 分量：兩終態 × {tail2}（終態定理 `run3_extIn_terminal_B` 之下的接受集）。 -/
def termStates3 : Finset (L3State_B × LSt) :=
  ({((0, Phase.S, 1), 0), ((0, Phase.S, 0), 1)} : Finset L3State_B) ×ˢ {LSt.tail2}

/-- **L3 模式追蹤 Sel 實例**：B1.5 `SelCostAutomaton` 於 L3 旗標乘積上——`sel = 旗標`、
`w m = θ m ∘ featIdx3_B ∘ unmark`（哨兵經 `unmark` 照常計費）、α = 0、β = `βsel3 βv`、接受集 = `termStates3 ×ˢ univ`（4 態）。 -/
def SelInst3 (θ : Fin 2 → Fin 48 → ℚ) (βv : Fin 2 → Fin 2 → ℚ) :
    SelCostAutomaton QF3 (Option ℕ) where
  init := initF3
  step := flagStep3
  accept := termStates3 ×ˢ Finset.univ
  sel := fun p => selF p.2
  w := fun m p a => θ m (featIdx3_B p.1.1 (unmark a))
  α := 0
  β := βsel3 βv

@[simp] lemma SelInst3_init (θ βv) : (SelInst3 θ βv).init = initF3 := rfl
@[simp] lemma SelInst3_step (θ βv) (p : QF3) (a : Option ℕ) :
    (SelInst3 θ βv).step p a
      = ((step3_B p.1.1 (unmark a), lstep p.1.2 a), flagUpd3 p.1.1 a p.2) := rfl
@[simp] lemma SelInst3_sel (θ βv) (p : QF3) : (SelInst3 θ βv).sel p = selF p.2 := rfl
@[simp] lemma SelInst3_w (θ βv) (m : Fin 2) (p : QF3) (a : Option ℕ) :
    (SelInst3 θ βv).w m p a = θ m (featIdx3_B p.1.1 (unmark a)) := rfl
@[simp] lemma SelInst3_α (θ βv) : (SelInst3 θ βv).α = 0 := rfl
@[simp] lemma SelInst3_β (θ βv) (p : QF3) : (SelInst3 θ βv).β p = βsel3 βv p := rfl

/-! ## §L.7 走行（E3：本檔的兩條歸納） -/

/-- 旗標的顯式形：起始旗標 ∨ L3 走行（讀去標記字 `w`）經過 (((2,K,0),0), 1)。 -/
def flagVal3 (f : Bool) (q : L3State_B) (w : List ℕ) : Bool :=
  f || decide ((bndK3, 1) ∈ microTrace3_B q w)

lemma flagVal3_nil (f : Bool) (q : L3State_B) : flagVal3 f q [] = f := by
  unfold flagVal3
  rw [show microTrace3_B q [] = [] from rfl]
  simp

/-- 旗標的合成律：讀一位元 = 更新旗標後續讀。 -/
lemma flagVal3_cons (f : Bool) (q : L3State_B) (b : ℕ) (w : List ℕ) :
    flagVal3 f q (b :: w) = flagVal3 (f || decide ((q, b) = (bndK3, 1))) (step3_B q b) w := by
  unfold flagVal3
  rw [show microTrace3_B q (b :: w) = (q, b) :: microTrace3_B (step3_B q b) w from rfl]
  by_cases h : (q, b) = (bndK3, 1)
  · rw [h]; simp
  · have h' : (bndK3, 1) ≠ (q, b) := fun e => h e.symm
    simp [List.mem_cons, h, h']

/-- **走行引理（歸納 ④，記帳級）**：三分量顯式——機器 = `run3_B`（讀去標記位元）、DFA = `extDFA` 走行、
旗標 = `flagVal3`（R-B `evalFrom_flag` 鏡射）。 -/
theorem evalFrom_flag3 (θ βv) (v : List (Option ℕ)) : ∀ (q : L3State_B) (s : LSt) (f : Bool),
    (SelInst3 θ βv).evalFrom ((q, s), f) v
      = ((run3_B q (v.map unmark), extDFA.evalFrom s v), flagVal3 f q (v.map unmark)) := by
  induction v with
  | nil => intro q s f; simp [flagVal3_nil]
  | cons a t ih =>
      intro q s f
      rw [SelCostAutomaton.evalFrom_cons, SelInst3_step, ih, List.map_cons, flagVal3_cons]
      rfl

/-- **路徑權重（歸納 ⑤，記帳級）**：暫存器 m 的路徑權重 = L3 trace 上 `θ m ∘ featIdx3_B` 之和
（R-B `wpath_flag` 鏡射；旗標分量不進權重）。 -/
theorem wpath_flag3 (θ βv) (m : Fin 2) (v : List (Option ℕ)) :
    ∀ (q : L3State_B) (s : LSt) (f : Bool),
      (SelInst3 θ βv).wpath m ((q, s), f) v
        = ((microTrace3_B q (v.map unmark)).map fun t => θ m (featIdx3_B t.1 t.2)).sum := by
  induction v with
  | nil => intro q s f; rfl
  | cons a t ih =>
      intro q s f
      rw [SelCostAutomaton.wpath_cons, SelInst3_step, ih]
      rfl

/-! ## §L.8 旗標接地 -/

/-- `extInM x` 讀完後的旗標值。 -/
def flagB3 (x : ℕ) : Bool := flagVal3 false init3_B (extIn x)

/-- 特徵層模式：A 的 `(F3 x).getD 33 0 = 1` 之 B 座標形（σ₃(33) = 33）。 -/
def modeB3 (x : ℕ) : Fin 2 := if F3_B x 33 = 1 then 1 else 0

/-- 終末位 = 較舊歷史位（#39 L3 的編碼 `(run3 …).2.2.1`；E5）。 -/
def termB3 (x : ℕ) : Fin 2 := if (run3_B init3_B (extIn x)).2 = 1 then 1 else 0

/-- `extInM x` 的走行終態（顯式；`extInM_unmark` 接回 Core 的 `extIn`）。 -/
theorem evalFrom_extInM3 (θ βv) (x : ℕ) :
    (SelInst3 θ βv).evalFrom initF3 (extInM x)
      = ((run3_B init3_B (extIn x), extDFA.evalFrom .start (extInM x)), flagB3 x) := by
  show (SelInst3 θ βv).evalFrom ((init3_B, LSt.start), false) (extInM x) = _
  rw [evalFrom_flag3, extInM_unmark]
  rfl

/-- **旗標接地（L3）**：`flagB3 x = true ⟺ F3_B x 33 = 1`。
`decide_eq_true_iff` → `mem_iff_33` → `List.count_pos_iff` → `count33_le_one`；零歸納。 -/
theorem flag_iff3 (x : ℕ) : flagB3 x = true ↔ F3_B x 33 = 1 := by
  unfold flagB3 flagVal3
  rw [Bool.false_or, decide_eq_true_iff, mem_iff_33, ← List.count_pos_iff]
  have := count33_le_one x
  unfold F3_B at this ⊢
  omega

/-- `sel` 於 `extInM x` 的走行終態 = 特徵層模式（`flag_iff3` 的 `Fin 2` 形）。 -/
theorem selF_flagB3 (x : ℕ) : selF (flagB3 x) = modeB3 x := by
  unfold selF modeB3
  by_cases h : F3_B x 33 = 1
  · rw [if_pos h, if_pos ((flag_iff3 x).mpr h)]
  · rw [if_neg h, if_neg]
    intro hf
    exact h ((flag_iff3 x).mp hf)

/-! ## §L.9 β 與成本橋 -/

/-- β 於走行終態 = `βv (sel) (終末位)`（終態定理的兩支分案）。 -/
lemma βsel3_final (βv : Fin 2 → Fin 2 → ℚ) (x : ℕ) (s : LSt) (f : Bool) :
    βsel3 βv ((run3_B init3_B (extIn x), s), f) = βv (selF f) (termB3 x) := by
  unfold βsel3 termB3
  rcases run3_extIn_terminal_B x with h | h <;> rw [h] <;> simp

/-- 路徑權重（trace 形）：`wpath m initF3 (extInM x) = Σ_{featList3_B x} θ m`。 -/
theorem wpath_featList3 (θ βv) (m : Fin 2) (x : ℕ) :
    (SelInst3 θ βv).wpath m initF3 (extInM x) = ((featList3_B x).map (θ m)).sum := by
  show (SelInst3 θ βv).wpath m ((init3_B, LSt.start), false) (extInM x) = _
  rw [wpath_flag3, extInM_unmark, featList3_B, List.map_map]
  rfl

/-- 路徑權重（座標形）：`wpath m initF3 (extInM x) = ∑ i, θ m i * F3_B x i`（B3a `cost_eq_sum` 同款收尾）。 -/
theorem wpath_sum3 (θ βv) (m : Fin 2) (x : ℕ) :
    (SelInst3 θ βv).wpath m initF3 (extInM x) = ∑ i, θ m i * F3_B x i := by
  rw [wpath_featList3, Finset.sum_list_map_count, Finset.sum_subset (Finset.subset_univ _)]
  · simp only [F3_B, nsmul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · intro i _ hi
    rw [List.mem_toFinset] at hi
    simp [List.count_eq_zero.mpr hi]

/-- **成本橋（L3）**：`cost (SelInst3 θ βv) (extInM x) = βv (m x) (t x) + θ_{m x} · F3_B x`，對全體 x。
`mode` 由 `evalFrom_extInM3`＋`selF_flagB3` 改成 `modeB3 x`；`wpath` 走 `wpath_sum3`；`β(final)` 走 `βsel3_final`。 -/
theorem cost_eq_sel3 (θ βv) (x : ℕ) :
    (SelInst3 θ βv).cost (extInM x)
      = βv (modeB3 x) (termB3 x) + ∑ i, θ (modeB3 x) i * F3_B x i := by
  have hmode : (SelInst3 θ βv).mode (extInM x) = modeB3 x := by
    unfold SelCostAutomaton.mode
    rw [SelInst3_init, evalFrom_extInM3, SelInst3_sel, selF_flagB3]
  unfold SelCostAutomaton.cost
  rw [hmode, SelInst3_init, wpath_sum3, evalFrom_extInM3, SelInst3_β, βsel3_final, selF_flagB3,
    SelInst3_α]
  ring

/-- 接受（奇數 x）：機器分量落兩終態（`run3_extIn_terminal_B`）、DFA 分量停 `tail2`（B0 `sentinel_positions`）、
旗標任意——語言含全體奇數的 `extInM x`，故 `BoundedBelow` 形非真空。 -/
theorem accepts_extInM_sel3 (θ βv) {x : ℕ} (hx : x % 2 = 1) :
    (SelInst3 θ βv).Accepts (extInM x) := by
  unfold SelCostAutomaton.Accepts
  rw [SelInst3_init, evalFrom_extInM3]
  have h2 : extDFA.evalFrom .start (extInM x) = .tail2 := (sentinel_positions x hx).2.2
  rw [h2]
  show _ ∈ termStates3 ×ˢ (Finset.univ : Finset Bool)
  rw [Finset.mem_product]
  refine ⟨?_, Finset.mem_univ _⟩
  unfold termStates3
  rw [Finset.mem_product]
  refine ⟨?_, Finset.mem_singleton_self _⟩
  rcases run3_extIn_terminal_B x with h | h <;> rw [h] <;> simp

/-! ## §L.10 三層定理與隨附（B 詞彙、素材 B 自產） -/

/-- **軌道回歸（B 的 L3 座標）**：`F3_B 2011 = F3_B 1787`（kernel `decide`：兩條 13 步 `extIn` 走行 × 48 座標；
不引 A-5 的 `F3_2011_eq_F3_1787`）。機制（觀察，不入定理）：與 L2 同形——兩個同錨閉走行對調（電池 §L.V1 第 6 項）。 -/
lemma F3_B_2011_eq : F3_B 2011 = F3_B 1787 := by
  funext i; revert i; decide

/-- 終末位相等（兩者終態皆 ((0,S,1),0)，即 A 的 (0,S,0,1)；`decide`）。 -/
lemma termB3_2011_eq : termB3 2011 = termB3 1787 := by decide

/-- 模式相等（由特徵層相等）。 -/
lemma modeB3_2011_eq : modeB3 2011 = modeB3 1787 := by
  unfold modeB3; rw [F3_B_2011_eq]

/-- **(a) 軌道成本恆等（L3）**：對任意 θ、βv，`cost (extInM 2011) = cost (extInM 1787)`——
橋 ×2 ＋ 特徵／模式／終末位三條相等式（皆 B 座標）。 -/
theorem orbit_cost_eq3 (θ βv) :
    (SelInst3 θ βv).cost (extInM 2011) = (SelInst3 θ βv).cost (extInM 1787) := by
  rw [cost_eq_sel3, cost_eq_sel3, F3_B_2011_eq, modeB3_2011_eq, termB3_2011_eq]

/-- **(b) 無符號 2 見證 no-go（L3）**：不存在任何符號的 θ（兩暫存器 × 48 座標）與 βv（四個 β_{m,t}）使 `SelInst3 θ βv`
的成本在 1787、2681 兩步 Todd 迭代皆嚴格下降。證明 = 兩步下降 ∧ (a) ⟹ `linarith`（0 < 0）。 -/
theorem no_go_sel3_signed : ¬ ∃ (θ : Fin 2 → Fin 48 → ℚ) (βv : Fin 2 → Fin 2 → ℚ),
    ∀ x ∈ WB1787,
      (SelInst3 θ βv).cost (extInM (Todd x)) - (SelInst3 θ βv).cost (extInM x) < 0 := by
  rintro ⟨θ, βv, h⟩
  have h1 := h 1787 (by decide)
  have h2 := h 2681 (by decide)
  rw [Todd_1787] at h1
  rw [Todd_2681, orbit_cost_eq3] at h2
  linarith

/-- **(c) `BoundedBelow` 形（L3）**：假設逐字取 B1.5 `SelCostAutomaton.BoundedBelow`
（`∃ B, ∀ u, Accepts u → B ≤ cost u`；由 `accepts_extInM_sel3` 非真空），**在證明中棄置**（a fortiori 自 (b)）。
此形之意義：把「gauge 目標類（Sel 實例的 bounded-below 類）在此模板上為空」寫成 kernel 可見的形式紀錄。
證明路線是軌道，不是 gauge——`structured_gauge` 未被使用，且其 `Fintype` 前提在本實例不成立。 -/
theorem no_go_sel3_bounded_below : ¬ ∃ (θ : Fin 2 → Fin 48 → ℚ) (βv : Fin 2 → Fin 2 → ℚ),
    (SelInst3 θ βv).BoundedBelow ∧
    ∀ x ∈ WB1787,
      (SelInst3 θ βv).cost (extInM (Todd x)) - (SelInst3 θ βv).cost (extInM x) < 0 :=
  fun ⟨θ, βv, _, h⟩ => no_go_sel3_signed ⟨θ, βv, h⟩

/-- 全稱形（算術量詞：∀ 奇 x > 1）。 -/
theorem no_go_sel3_signed_odd : ¬ ∃ (θ : Fin 2 → Fin 48 → ℚ) (βv : Fin 2 → Fin 2 → ℚ),
    ∀ x : ℕ, x % 2 = 1 → 1 < x →
      (SelInst3 θ βv).cost (extInM (Todd x)) - (SelInst3 θ βv).cost (extInM x) < 0 := by
  rintro ⟨θ, βv, h⟩
  exact no_go_sel3_signed
    ⟨θ, βv, fun x hx => h x (by fin_cases hx <;> decide) (by fin_cases hx <;> decide)⟩

/-- 全稱形（語言層）：量詞走 B0 `RankingDomain`、動力學走 `Uacc`（R-B `no_go_sel_signed_lang` 同形）。 -/
theorem no_go_sel3_signed_lang : ¬ ∃ (θ : Fin 2 → Fin 48 → ℚ) (βv : Fin 2 → Fin 2 → ℚ),
    ∀ w, RankingDomain w →
      (SelInst3 θ βv).cost (markedExt (Uacc w)) - (SelInst3 θ βv).cost (markedExt w) < 0 := by
  rintro ⟨θ, βv, h⟩
  refine no_go_sel3_signed ⟨θ, βv, fun x hx => ?_⟩
  have hodd : x % 2 = 1 := by fin_cases hx <;> decide
  have h1 : 1 < x := by fin_cases hx <;> decide
  have hcan := isCanonicalOdd_digits hodd
  have hdom : RankingDomain (Nat.digits 2 x) :=
    ⟨hcan, (rankingDomain_iff hcan).mpr (by rw [Nat.ofDigits_digits]; exact h1)⟩
  have := h _ hdom
  rwa [Uacc_digits, ← extInM_eq_markedExt, ← extInM_eq_markedExt] at this

/-- **任意函數版（B 詞彙，L3）**：任何以 (B 的 L3 佔用向量, 終末位) 為自變量的函數都不能在 1787、2681 兩步
同時嚴格下降——A-5 `L3` 段任意函數版的 B 側鏡射；三層定理皆其實例。 -/
theorem no_feature_ranking_orbit3_B :
    ¬ ∃ Φ : (Fin 48 → ℕ) → Fin 2 → ℚ,
      Φ (F3_B (Todd 1787)) (termB3 (Todd 1787)) < Φ (F3_B 1787) (termB3 1787) ∧
      Φ (F3_B (Todd 2681)) (termB3 (Todd 2681)) < Φ (F3_B 2681) (termB3 2681) := by
  rintro ⟨Φ, h1, h2⟩
  rw [Todd_1787] at h1
  rw [Todd_2681, F3_B_2011_eq, termB3_2011_eq] at h2
  linarith

/-! ## §L.11 跨層恆等（E6；零歸納） -/

/-- **L3 旗標 = L2 旗標**（R-B 的 `flagB`）：兩者記錄同一物理事件——(2,K) 高能出口。L3 trace 經 ② 投影即 L2 trace；
← 方向把 L2 trace 上的 ((2,K,0),1) 回拉到 L3，Inv3（K ⇒ 歷史 (0,0)）迫使其為 (bndK3, 1)。 -/
theorem flagB3_eq_flagB (x : ℕ) : flagB3 x = flagB x := by
  unfold flagB3 flagB flagVal3 flagVal
  rw [Bool.false_or, Bool.false_or]
  apply decide_eq_decide.mpr
  rw [← microTrace3_B_proj (extIn x) (1, Phase.K, 0) 0]
  constructor
  · intro h
    exact List.mem_map.mpr ⟨(bndK3, 1), h, rfl⟩
  · intro h
    obtain ⟨t, ht, hft⟩ := List.mem_map.mp h
    have hi := (trace3_inv x t ht).1
    obtain ⟨⟨⟨c, P, p⟩, hh⟩, b⟩ := t
    simp only [Prod.mk.injEq] at hft
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hft
    obtain ⟨-, -, -, hK⟩ := hi
    obtain ⟨-, -, hh0⟩ := hK rfl
    simp only at hh0
    subst hh0
    exact ht

/-- **模式跨層恆等（全稱定理）**：`modeB3 x = modeB x`——L3 模式位 = L2 模式位，對全體 x。
A 的「模式跨層恆等」（m_L3(x) = F3(x)[33] ≡ m_L2(x) = F(x)[5]）只在 `L3_2Mode_Recon` §43 以 `#eval` 驗 x < 250；
此為其全稱定理——B 抽象首次反哺 A 沒有的定理。證明：`selF_flagB3`／R-B `selF_flagB` ＋ `flagB3_eq_flagB`。 -/
theorem modeB3_eq_modeB (x : ℕ) : modeB3 x = modeB x := by
  rw [← selF_flagB3, ← selF_flagB, flagB3_eq_flagB]

/-- **終末位跨層互補**：L3 的 t（較舊歷史位）= 1 − L2 的 t（最後輸出位）——兩終態 ((0,S,1),0)／((0,S,0),1)
的核心分量即 L2 的 (0,S,1)／(0,S,0)（③ ＋ 終態定理）。 -/
theorem termB3_eq (x : ℕ) : termB3 x = if termB x = 1 then 0 else 1 := by
  have hp : (run3_B init3_B (extIn x)).1 = run2 (1, Phase.K, 0) (extIn x) := run3_B_proj _ _ _
  unfold termB3 termB
  rcases run3_extIn_terminal_B x with h | h <;> rw [h] at hp ⊢ <;> rw [← hp] <;> decide

/-! ## §L.V2 數據驗證（全部應輸出 `true`）

字面即 `tools/b3_attest.py` §J 的錨（`LEAN_RBL3_*`）。 -/

section Verification

/-- 電池用權重：各座標相異、兩暫存器相異（橋的數值形不退化）。 -/
private def θt3 : Fin 2 → Fin 48 → ℚ := fun m i => (i.val : ℚ) + 1 + 50 * (m.val : ℚ)

/-- 電池用 β：四格相異。 -/
private def βt3 : Fin 2 → Fin 2 → ℚ := fun m t => 100 * (m.val : ℚ) + 10 * (t.val : ℚ) + 1

-- 1 旗標錨：模式 0 例 25、2681；模式 1 例 3、1787
#eval [25, 2681, 3, 1787].map flagB3 == [false, false, true, true]
-- 2 特徵層模式位同序
#eval [25, 2681, 3, 1787].map (fun x => F3_B x 33) == [0, 0, 1, 1]
-- 3 count33 ≤ 1、旗標接地（x < 300，含偶數與 0）
#eval (List.range 300).all fun x => F3_B x 33 ≤ 1 && (flagB3 x == (F3_B x 33 == 1))
-- 4 四類 (m, t)：1787 ↦ (1,0)、2681 ↦ (0,1)、961 ↦ (0,0)、599 ↦ (1,1)（t 為較舊歷史位，與 R-B 例的 t 互補）
#eval [1787, 2681, 961, 599].map (fun x => (modeB3 x, termB3 x)) == [(1, 0), (0, 1), (0, 0), (1, 1)]
-- 5 成本橋數值形（θt3、βt3；x < 100 全體）
#eval (List.range 100).all fun x =>
  decide ((SelInst3 θt3 βt3).cost (extInM x)
    = βt3 (modeB3 x) (termB3 x) + ∑ i, θt3 (modeB3 x) i * F3_B x i)
-- 6 軌道成本恆等數值形、兩步差分和零
#eval decide ((SelInst3 θt3 βt3).cost (extInM 2011) = (SelInst3 θt3 βt3).cost (extInM 1787))
#eval decide (((SelInst3 θt3 βt3).cost (extInM 2681) - (SelInst3 θt3 βt3).cost (extInM 1787))
  + ((SelInst3 θt3 βt3).cost (extInM 2011) - (SelInst3 θt3 βt3).cost (extInM 2681)) = 0)
-- 7 接受（奇）／拒絕（偶）
#eval (List.range 100).all fun k =>
  decide ((SelInst3 θt3 βt3).evalFrom initF3 (extInM (2 * k + 1)) ∈ (SelInst3 θt3 βt3).accept)
#eval (List.range 100).all fun k =>
  !decide ((SelInst3 θt3 βt3).evalFrom initF3 (extInM (2 * k)) ∈ (SelInst3 θt3 βt3).accept)
-- 8 哨兵步不動旗標：只讀 digits x 的旗標 = 讀完 extInM x 的旗標（x < 100）
#eval (List.range 100).all fun x => (flagVal3 false init3_B (Nat.digits 2 x) == flagB3 x)
-- 9 走行分解（evalFrom_extInM3 的數值形，x < 100）
#eval (List.range 100).all fun x =>
  decide ((SelInst3 θt3 βt3).evalFrom initF3 (extInM x)
    = ((run3_B init3_B (extIn x), extDFA.evalFrom .start (extInM x)), flagB3 x))
-- 10 兩暫存器的路徑權重數值形（x < 100）
#eval (List.range 100).all fun x => ([0, 1] : List (Fin 2)).all fun m =>
  decide ((SelInst3 θt3 βt3).wpath m initF3 (extInM x) = ∑ i, θt3 m i * F3_B x i)
-- 11 單步不回歸（軌道回歸是兩步現象）
#eval (List.finRange 48).any fun i => F3_B 2681 i != F3_B 1787 i
-- 12 跨層恆等（x < 300）：旗標 = L2 旗標、模式 = L2 模式、終末位 = 1 − L2 終末位
#eval (List.range 300).all fun x =>
  flagB3 x == flagB x && modeB3 x == modeB x && termB3 x == (if termB x = 1 then 0 else 1)

end Verification

end CollatzFST.ProjectB
