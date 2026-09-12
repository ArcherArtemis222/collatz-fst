/-
# Project B 第八批：R-B——B 側雙模式 Sel 實例化（模式追蹤乘積 × 旗標；B3 殘項收口，Level 2）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。設計核准 2026-09-12
（RB-DESIGN-REPORT；Q1–Q6 作答與裁決點 D1–D11 全項通過：D3 歸納帳 2 條、D7 邊界和納入、
D8 L3 續 PR、D9 attest §I、D6 保留）。

把 A 的 terminal-affine 雙模式模板（#39 `V2`：`V(x) = β_{m(x),t(x)} + θ_{m(x)}ᵀ F(x)`）誠實實例化為
B1.5 的 `SelCostAutomaton`：底層機器 = B3a 乘積 `L2State × LSt` 加一個旗標分量（`Bool`），旗標於
機器態 (2,K,0) 讀 1（B 座標 13，K→S 的高能出口）時置真、餘傳遞，`sel = 旗標`；每暫存器邊權
`w m = θ m ∘ featIdx ∘ unmark`；β 於機器終態 (0,S,t) 取 `βv (sel) t`、餘 0。**零 ProjectA import**
（`scripts/check_boundaries.py` 強制）；素材全 B 自產——F_B、Todd 值經 B0 `U`、`F_B 2011 = F_B 1787`
與終末位在 B 座標重新 `decide`、終態定理由 Core 三錨重推。

**證明路線是軌道（A-5 的 1787 → 2681 → 2011），不是 gauge**：`structured_gauge` 未被使用（其
`Fintype QF`／`Fintype (Option ℕ)` 前提在本實例亦不成立，ROADMAP-B B1.5 收口句）；(c) 的
`BoundedBelow` 形只是把「gauge 目標類（Sel 實例的 bounded-below 類）在此模板上為空」寫成
kernel 可見的形式紀錄，假設在證明中棄置（a fortiori）。

## 內容

* **§R.1 載體**：`QF := (L2State × LSt) × Bool`、`flagUpd`／`flagStep`／`initF`、`selF`（Bool → `Fin 2`）、
  `βsel`、`termStates`（4 個 (終態, 旗標) 態的機器×DFA 分量）、**`SelInst θ βv`**（交付 1）。
* **§R.2 走行與旗標**：`flagVal`（旗標的顯式形：起始旗標 ∨ 走行經過 ((2,K,0),1)）；兩條記帳級歸納
  `evalFrom_flag`（走行三分量顯式；B3a `prodRun_fst`＋B0 `prodRun_snd` 的角色一次收掉、旗標折入）與
  `wpath_flag`（B3a `wpath_prod` 鏡射）——**D3：本檔的全部歸納**。
* **§R.3 旗標接地**（交付 2）：`featIdx_eq_13`（Inv 之下座標 13 唯一）、`mem_iff_13`、`gate_pointwise`、
  **`boundary_sum_B : F_B x 6 + F_B x 13 = 1`**（D7，雙門讀法）、`count13_le_one`、**`flag_iff`**、
  `selF_flagB`；模式 0／1 例（25、2681／3、1787）進電池。
* **§R.4 β 與成本橋**（交付 3）：B 自產終態定理 `run2_extIn_terminal_B`（D4）、`βsel_final`、`wpath_sum`、
  **`cost_eq_sel : cost (SelInst θ βv) (extInM x) = βv (modeB x) (termB x) + ∑ i, θ (modeB x) i * F_B x i`**
  （對全體 x）、`accepts_extInM_sel`（BoundedBelow 形非真空）。
* **§R.5 三層定理**（交付 4）：`orbit_cost_eq`（∀ θ βv）、`no_go_sel_signed`（無符號 2 見證）、
  `no_go_sel_bounded_below`（`BoundedBelow` 逐字為假設）。
* **§R.6 隨附**（D5／D6）：全稱形 `no_go_sel_signed_odd`（∀ 奇 x > 1）、`no_go_sel_signed_lang`
  （B0 `RankingDomain`＋`Uacc`）、任意函數版 `no_feature_ranking_orbit_B`。
* **§R.V 電池**：字面即 `tools/b3_attest.py` §I 的錨。

## 技術註記（設計定案）

1. **D1**：旗標取 `Bool`（合成律 = `Bool.or_assoc`＋`decide_or`，走行引理的 cons 步一次收掉），
   `sel p = if p.2 then 1 else 0`；不把旗標塞進 `LSt`（要換 12 態 DFA 並重推 B0-3，違反 re-export 紅線）。
2. **D2**：參數形 `θ : Fin 2 → Fin 18 → ℚ`（B 的暫存器索引形，對應 `w : Fin 2 → Q → A → ℚ`）、
   `βv : Fin 2 → Fin 2 → ℚ`（(模式, 終末)）；A 的 `θ₀ θ₁` 形以 `![θ₀, θ₁]` 一行換回。
3. **D3（歸納帳）**：兩條 list 歸納（`evalFrom_flag`、`wpath_flag`），與 B3a 同數同形；`flag_iff` 是
   走行引理的投影而非歸納；`count13_le_one` 零歸納（`Inv`＋`microTrace2_inv`＋`boundary_step_unique`＋
   core `countP_map`／`countP_mono_left`）；不需要乘積態不變量。
4. **D4**：β 只看機器分量（DFA／旗標不進條件，旗標經 `sel` 進值），橋因此對**全體 x** 成立（含偶數與
   x = 1；A 的 `V2` 亦對全體 x 定義）；接受集取 4 個 (終態, 旗標) 態而非 B3a D1 的 `S8 ×ˢ {tail2}`——
   靠 B 自產終態定理（Core `extRun_carry`＋`run2_fst`＋`run2_mem_S8`＋`decide`；重推 A 的
   `Flow.run2_extIn_terminal`，邊界機制強制）。哨兵步照 B3a Q1 計費（`featIdx q 0`），且永不置旗標（需讀 1）。
5. **D7（雙門讀法）**：K→S 的出口只有兩道門——門 6 = (1,K,0) 讀 0 與門 13 = (2,K,0) 讀 1；每條走行恰穿過
   其中一道（`boundary_sum_B`，Core `boundary_step_unique` 的 B 座標形）。**模式 = 走的是哪道門**：
   `F_B x 13 = 1` ⟺ 高能門、`F_B x 6 = 1` ⟺ 低能門，互斥且窮盡，模式位對全體 x 良定義
   （A 的 `mode_bit_endpoints` 只對 24 個端點 `decide`，此為全稱形）。
6. 零 `Fintype`、零 `maxHeartbeats` 調整、零 native 求值；`#print axioms` 三標準公理。
7. 明確不做：Recon 的 A↔B 等價定理（`V2 … x = cost (SelInst …) (extInM x)` 需跨界 import，順延）；
   gauge 的任何應用；paper／registry；L3（素材全在 ProjectA、Core 零暴露——續 PR R-B-L3）；
   `L2auto (θ m)` 與 `(SelInst θ βv).restrict m` 的逐邊等式；D(θ)／`rdDFA`。
-/
import Lean4RealConstruction.ProjectB.Collatz_FST_B15_SelGauge
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_L2Instance

namespace CollatzFST.ProjectB

/-! ## §R.1 載體：模式追蹤乘積（B3a 乘積 × 旗標） -/

/-- 高能出口門：機器態 (2,K,0) 讀 1 的 K→S 出口（B 座標 13）。 -/
abbrev bndK : L2State := (2, Phase.K, 0)

/-- 模式追蹤乘積態：B3a 乘積 `L2State × LSt` × 旗標 `Bool`（D1）。 -/
abbrev QF := (L2State × LSt) × Bool

/-- 旗標更新：於機器態 (2,K,0) 讀（去標記）位元 1 時置真，餘傳遞。哨兵 `none` 讀 0，永不置真。 -/
def flagUpd (q : L2State) (a : Option ℕ) (f : Bool) : Bool :=
  f || decide ((q, unmark a) = (bndK, 1))

/-- 乘積一步：B3a `prodStep step2` × 旗標更新。 -/
def flagStep (p : QF) (a : Option ℕ) : QF :=
  (prodStep step2 p.1 a, flagUpd p.1.1 a p.2)

/-- 初態：B3a `L2init` × 旗標 false。 -/
def initF : QF := (L2init, false)

/-- 旗標 → 暫存器指標（`sel = 旗標`；Bool 到 `Fin 2` 的一行）。 -/
def selF (f : Bool) : Fin 2 := if f then 1 else 0

/-- 終權 β（D4）：機器分量 (0,S,t) 取 `βv (sel p) t`、餘 0。只看機器分量——接受字的終態 DFA 分量
恆為 `tail2`，故在 4 個接受態上恰為 β_{m,t}；非接受態的值是 don't-care（B1.5 D5 語義）。 -/
def βsel (βv : Fin 2 → Fin 2 → ℚ) (p : QF) : ℚ :=
  if p.1.1 = (0, Phase.S, 0) then βv (selF p.2) 0
  else if p.1.1 = (0, Phase.S, 1) then βv (selF p.2) 1
  else 0

/-- 終末乘積態的機器×DFA 分量：{(0,S,0), (0,S,1)} × {tail2}（B 自產終態定理 `run2_extIn_terminal_B`
之下的接受集；與旗標相乘即 4 個 (終態, 旗標) 態）。 -/
def termStates : Finset (L2State × LSt) :=
  ({(0, Phase.S, 0), (0, Phase.S, 1)} : Finset L2State) ×ˢ {LSt.tail2}

/-- **模式追蹤 Sel 實例（交付 1）**：B1.5 `SelCostAutomaton` 於旗標乘積上——`sel = 旗標`、
`w m = θ m ∘ featIdx ∘ unmark`（哨兵經 `unmark` 照常計費，B3a Q1）、α = 0、β = `βsel βv`、
接受集 = `termStates ×ˢ univ`（4 態）。 -/
def SelInst (θ : Fin 2 → Fin 18 → ℚ) (βv : Fin 2 → Fin 2 → ℚ) :
    SelCostAutomaton QF (Option ℕ) where
  init := initF
  step := flagStep
  accept := termStates ×ˢ Finset.univ
  sel := fun p => selF p.2
  w := fun m p a => θ m (featIdx p.1.1 (unmark a))
  α := 0
  β := βsel βv

@[simp] lemma SelInst_init (θ βv) : (SelInst θ βv).init = initF := rfl
@[simp] lemma SelInst_step (θ βv) (p : QF) (a : Option ℕ) :
    (SelInst θ βv).step p a = ((step2 p.1.1 (unmark a), lstep p.1.2 a), flagUpd p.1.1 a p.2) := rfl
@[simp] lemma SelInst_sel (θ βv) (p : QF) : (SelInst θ βv).sel p = selF p.2 := rfl
@[simp] lemma SelInst_w (θ βv) (m : Fin 2) (p : QF) (a : Option ℕ) :
    (SelInst θ βv).w m p a = θ m (featIdx p.1.1 (unmark a)) := rfl
@[simp] lemma SelInst_α (θ βv) : (SelInst θ βv).α = 0 := rfl
@[simp] lemma SelInst_β (θ βv) (p : QF) : (SelInst θ βv).β p = βsel βv p := rfl

/-! ## §R.2 走行與旗標（D3：本檔的兩條歸納） -/

/-- 旗標的顯式形：起始旗標 ∨ 走行（讀去標記字 `w`）經過 ((2,K,0), 1)。 -/
def flagVal (f : Bool) (q : L2State) (w : List ℕ) : Bool :=
  f || decide ((bndK, 1) ∈ microTrace2 q w)

lemma flagVal_nil (f : Bool) (q : L2State) : flagVal f q [] = f := by
  unfold flagVal
  rw [show microTrace2 q [] = [] from rfl]
  simp

/-- 旗標的合成律（`Bool.or_assoc`＋`decide_or` 的形狀）：讀一位元 = 更新旗標後續讀。 -/
lemma flagVal_cons (f : Bool) (q : L2State) (b : ℕ) (w : List ℕ) :
    flagVal f q (b :: w) = flagVal (f || decide ((q, b) = (bndK, 1))) (step2 q b) w := by
  unfold flagVal
  rw [show microTrace2 q (b :: w) = (q, b) :: microTrace2 (step2 q b) w from rfl]
  by_cases h : (q, b) = (bndK, 1)
  · rw [h]; simp
  · have h' : (bndK, 1) ≠ (q, b) := fun e => h e.symm
    simp [List.mem_cons, h, h']

/-- **走行引理（歸納 1，記帳級）**：三分量顯式——機器 = Core `run2`（讀去標記位元）、DFA = `extDFA`
走行、旗標 = `flagVal`。B3a `prodRun_fst`＋B0 `prodRun_snd` 的角色一次收掉、旗標折入。 -/
theorem evalFrom_flag (θ βv) (v : List (Option ℕ)) : ∀ (q : L2State) (s : LSt) (f : Bool),
    (SelInst θ βv).evalFrom ((q, s), f) v
      = ((run2 q (v.map unmark), extDFA.evalFrom s v), flagVal f q (v.map unmark)) := by
  induction v with
  | nil => intro q s f; simp [flagVal_nil]
  | cons a t ih =>
      intro q s f
      rw [SelCostAutomaton.evalFrom_cons, SelInst_step, ih, List.map_cons, flagVal_cons]
      rfl

/-- **路徑權重（歸納 2，記帳級）**：暫存器 m 的路徑權重 = trace 上 `θ m ∘ featIdx` 之和
（B3a `wpath_prod` 的鏡射；旗標分量不進權重）。 -/
theorem wpath_flag (θ βv) (m : Fin 2) (v : List (Option ℕ)) : ∀ (q : L2State) (s : LSt) (f : Bool),
    (SelInst θ βv).wpath m ((q, s), f) v
      = ((microTrace2 q (v.map unmark)).map fun t => θ m (featIdx t.1 t.2)).sum := by
  induction v with
  | nil => intro q s f; rfl
  | cons a t ih =>
      intro q s f
      rw [SelCostAutomaton.wpath_cons, SelInst_step, ih]
      rfl

/-! ## §R.3 旗標接地（交付 2） -/

/-- `extInM x` 讀完後的旗標值。 -/
def flagB (x : ℕ) : Bool := flagVal false (1, Phase.K, 0) (extIn x)

/-- 特徵層模式：A 的 `(F x).getD 5 0 = 1` 之 B 座標形（σ(13) = 5）。 -/
def modeB (x : ℕ) : Fin 2 := if F_B x 13 = 1 then 1 else 0

/-- 終末位（#39 的編碼 `(run2 …).2.2`）。 -/
def termB (x : ℕ) : Fin 2 := if (run2 (1, Phase.K, 0) (extIn x)).2.2 = 1 then 1 else 0

/-- `extInM x` 的走行終態（顯式；`extInM_unmark` 接回 Core 的 `extIn`）。 -/
theorem evalFrom_extInM (θ βv) (x : ℕ) :
    (SelInst θ βv).evalFrom initF (extInM x)
      = ((run2 (1, Phase.K, 0) (extIn x), extDFA.evalFrom .start (extInM x)), flagB x) := by
  show (SelInst θ βv).evalFrom (((1, Phase.K, 0), LSt.start), false) (extInM x) = _
  rw [evalFrom_flag, extInM_unmark]
  rfl

/-- 座標 13 的唯一性（`Inv` 之下）：K 列 `6c + b = 13` ⟹ c = 2、b = 1（p = 0 由 Inv）；
S 列 `6c + 2 + 2p + b = 13` 於 c < 3、p < 2、b < 2 無解。皆 `omega`。 -/
lemma featIdx_eq_13 {t : L2State × ℕ} (hinv : Inv t.1) (hb : t.2 < 2)
    (h13 : featIdx t.1 t.2 = 13) : t = (bndK, 1) := by
  obtain ⟨⟨c, P, p⟩, b⟩ := t
  simp only [Inv] at hinv hb
  obtain ⟨hc, hp, hK⟩ := hinv
  have h := congrArg Fin.val h13
  cases P
  · simp only [featIdx] at h
    change (6 * c + b) % 18 = 13 at h
    obtain ⟨-, hp0⟩ := hK rfl
    have hc2 : c = 2 := by omega
    have hb1 : b = 1 := by omega
    subst hc2 hb1 hp0
    rfl
  · simp only [featIdx] at h
    change (6 * c + 2 + 2 * p + b) % 18 = 13 at h
    omega

/-- 走行經過 ((2,K,0),1) ⟺ 座標 13 出現在 `featList x`（← 方向用 `microTrace2_inv` 取 Inv）。 -/
lemma mem_iff_13 (x : ℕ) :
    (bndK, 1) ∈ microTrace2 (1, Phase.K, 0) (extIn x) ↔ (13 : Fin 18) ∈ featList x := by
  constructor
  · intro h
    exact List.mem_map.mpr ⟨(bndK, 1), h, rfl⟩
  · intro h
    obtain ⟨t, ht, hft⟩ := List.mem_map.mp h
    have hi := microTrace2_inv init_inv (extIn_bits x) t ht
    rw [featIdx_eq_13 hi.1 hi.2 hft] at ht
    exact ht

/-- 雙門的逐點刻畫（`Inv` 之下）：「K 相位且輸出 1」的步 ∧ 進位 = 2 ⟺ 座標 13（門 13：(2,K,0) 讀 1，
`outBit 2 1 = 1`）；∧ 進位 ≠ 2 ⟺ 座標 6（門 6：(1,K,0) 讀 0，`outBit 1 0 = 1`）。死態 (0,K,·) 由
Inv 排除（K ⇒ c ≠ 0）。 -/
lemma gate_pointwise {t : L2State × ℕ} (hinv : Inv t.1) (hb : t.2 < 2) :
    ((t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1) && (t.1.1 == 2)) = (featIdx t.1 t.2 == 13)
    ∧ ((t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1) && !(t.1.1 == 2)) = (featIdx t.1 t.2 == 6) := by
  obtain ⟨⟨c, P, p⟩, b⟩ := t
  simp only [Inv] at hinv hb
  obtain ⟨hc, hp, hK⟩ := hinv
  cases P
  · obtain ⟨hc0, hp0⟩ := hK rfl
    subst hp0
    interval_cases c
    · exact absurd rfl hc0
    · interval_cases b <;> decide
    · interval_cases b <;> decide
  · interval_cases c <;> interval_cases p <;> interval_cases b <;> decide

/-- **邊界和（D7，雙門讀法）**：K→S 的出口只有兩道門——門 6 = (1,K,0) 讀 0、門 13 = (2,K,0) 讀 1，
每條 `extIn` 走行恰穿過其中一道：`F_B x 6 + F_B x 13 = 1`（Core `boundary_step_unique` 的 B 座標形，
`countP_bool_split` 依「進位 = 2」拆分＋`gate_pointwise` 逐點對齊）。**模式 = 走的是哪道門**：
`F_B x 13 = 1` ⟺ 高能門（模式 1）、`F_B x 6 = 1` ⟺ 低能門（模式 0），互斥且窮盡——模式位對全體 x
是良定義的一個位元（A 的 `mode_bit_endpoints` 只對 24 個端點 `decide`，此為全稱形）。 -/
theorem boundary_sum_B (x : ℕ) : F_B x 6 + F_B x 13 = 1 := by
  unfold F_B featList
  rw [List.count_eq_countP, List.count_eq_countP, List.countP_map, List.countP_map]
  have hsplit := countP_bool_split
    (fun t : L2State × ℕ => t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1)
    (fun t => t.1.1 == 2) (microTrace2 (1, Phase.K, 0) (extIn x))
  rw [boundary_step_unique x] at hsplit
  have h13 : (microTrace2 (1, Phase.K, 0) (extIn x)).countP
      ((fun i => i == (13 : Fin 18)) ∘ fun t => featIdx t.1 t.2)
      = (microTrace2 (1, Phase.K, 0) (extIn x)).countP
        (fun t => (t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1) && (t.1.1 == 2)) := by
    apply countP_congr'
    intro t ht
    have hi := microTrace2_inv init_inv (extIn_bits x) t ht
    exact (gate_pointwise hi.1 hi.2).1.symm
  have h6 : (microTrace2 (1, Phase.K, 0) (extIn x)).countP
      ((fun i => i == (6 : Fin 18)) ∘ fun t => featIdx t.1 t.2)
      = (microTrace2 (1, Phase.K, 0) (extIn x)).countP
        (fun t => (t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1) && !(t.1.1 == 2)) := by
    apply countP_congr'
    intro t ht
    have hi := microTrace2_inv init_inv (extIn_bits x) t ht
    exact (gate_pointwise hi.1 hi.2).2.symm
  rw [h6, h13, Nat.add_comm]
  exact hsplit.symm

/-- **count13 ≤ 1**：邊界和的系理（設計報告 §3 的原直證——`countP_mono_left` 到
`boundary_step_unique`——被 D7 的雙門形取代）。 -/
theorem count13_le_one (x : ℕ) : F_B x 13 ≤ 1 := by
  have := boundary_sum_B x
  omega

/-- **旗標接地（交付 2）**：`flagB x = true ⟺ F_B x 13 = 1`。
`decide_eq_true_iff` → `mem_iff_13` → `List.count_pos_iff` → `count13_le_one`；零歸納。 -/
theorem flag_iff (x : ℕ) : flagB x = true ↔ F_B x 13 = 1 := by
  unfold flagB flagVal
  rw [Bool.false_or, decide_eq_true_iff, mem_iff_13, ← List.count_pos_iff]
  have := count13_le_one x
  unfold F_B at this ⊢
  omega

/-- `sel` 於 `extInM x` 的走行終態 = 特徵層模式（`flag_iff` 的 `Fin 2` 形）。 -/
theorem selF_flagB (x : ℕ) : selF (flagB x) = modeB x := by
  unfold selF modeB
  by_cases h : F_B x 13 = 1
  · rw [if_pos h, if_pos ((flag_iff x).mpr h)]
  · rw [if_neg h, if_neg]
    intro hf
    exact h ((flag_iff x).mp hf)

/-! ## §R.4 β 與成本橋（交付 3） -/

/-- **B 自產終態定理（D4）**：讀完 `extIn x` 的機器態恆為 (0,S,0) 或 (0,S,1)（對全體 x）。
Core `run2_mem_S8`（可達集）＋ `run2_fst`／`extRun_carry`（終進位 0）＋ `decide` 掃 `S8`；
重推 A 的 `Flow.run2_extIn_terminal`（B 不可 import），零歸納。 -/
theorem run2_extIn_terminal_B (x : ℕ) :
    run2 (1, Phase.K, 0) (extIn x) = (0, Phase.S, 0)
      ∨ run2 (1, Phase.K, 0) (extIn x) = (0, Phase.S, 1) := by
  have h1 : run2 (1, Phase.K, 0) (extIn x) ∈ S8 := run2_mem_S8 (extIn_bits x)
  have h2 : (run2 (1, Phase.K, 0) (extIn x)).1 = 0 := by
    rw [run2_fst]; exact extRun_carry x
  have key : ∀ s ∈ S8, s.1 = 0 → s = (0, Phase.S, 0) ∨ s = (0, Phase.S, 1) := by decide
  exact key _ h1 h2

/-- β 於走行終態 = `βv (sel) (終末位)`（終態定理的兩支分案）。 -/
lemma βsel_final (βv : Fin 2 → Fin 2 → ℚ) (x : ℕ) (s : LSt) (f : Bool) :
    βsel βv ((run2 (1, Phase.K, 0) (extIn x), s), f) = βv (selF f) (termB x) := by
  unfold βsel termB
  rcases run2_extIn_terminal_B x with h | h <;> rw [h] <;> simp

/-- 路徑權重（trace 形）：`wpath m initF (extInM x) = Σ_{featList x} θ m`。 -/
theorem wpath_featList (θ βv) (m : Fin 2) (x : ℕ) :
    (SelInst θ βv).wpath m initF (extInM x) = ((featList x).map (θ m)).sum := by
  show (SelInst θ βv).wpath m (((1, Phase.K, 0), LSt.start), false) (extInM x) = _
  rw [wpath_flag, extInM_unmark, featList, List.map_map]
  rfl

/-- 路徑權重（座標形）：`wpath m initF (extInM x) = ∑ i, θ m i * F_B x i`（B3a `cost_eq_sum` 同款收尾）。 -/
theorem wpath_sum (θ βv) (m : Fin 2) (x : ℕ) :
    (SelInst θ βv).wpath m initF (extInM x) = ∑ i, θ m i * F_B x i := by
  rw [wpath_featList, Finset.sum_list_map_count, Finset.sum_subset (Finset.subset_univ _)]
  · simp only [F_B, nsmul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · intro i _ hi
    rw [List.mem_toFinset] at hi
    simp [List.count_eq_zero.mpr hi]

/-- **成本橋（交付 3）**：`cost (SelInst θ βv) (extInM x) = βv (m x) (t x) + θ_{m x} · F_B x`，對全體 x。
分案結構：`mode` 由 `evalFrom_extInM`＋`selF_flagB` 改成 `modeB x`；`wpath` 走 `wpath_sum`；
`β(final)` 走 `βsel_final`（唯一分案 = 終態定理兩支）；`ring` 收尾。 -/
theorem cost_eq_sel (θ βv) (x : ℕ) :
    (SelInst θ βv).cost (extInM x) = βv (modeB x) (termB x) + ∑ i, θ (modeB x) i * F_B x i := by
  have hmode : (SelInst θ βv).mode (extInM x) = modeB x := by
    unfold SelCostAutomaton.mode
    rw [SelInst_init, evalFrom_extInM, SelInst_sel, selF_flagB]
  unfold SelCostAutomaton.cost
  rw [hmode, SelInst_init, wpath_sum, evalFrom_extInM, SelInst_β, βsel_final, selF_flagB, SelInst_α]
  ring

/-- 接受（奇數 x）：機器分量落終態對（`run2_extIn_terminal_B`）、DFA 分量停 `tail2`
（B0 `sentinel_positions`）、旗標任意——語言含全體奇數的 `extInM x`，故 `BoundedBelow` 形非真空。 -/
theorem accepts_extInM_sel (θ βv) {x : ℕ} (hx : x % 2 = 1) :
    (SelInst θ βv).Accepts (extInM x) := by
  unfold SelCostAutomaton.Accepts
  rw [SelInst_init, evalFrom_extInM]
  have h2 : extDFA.evalFrom .start (extInM x) = .tail2 := (sentinel_positions x hx).2.2
  rw [h2]
  show _ ∈ termStates ×ˢ (Finset.univ : Finset Bool)
  rw [Finset.mem_product]
  refine ⟨?_, Finset.mem_univ _⟩
  unfold termStates
  rw [Finset.mem_product]
  refine ⟨?_, Finset.mem_singleton_self _⟩
  rcases run2_extIn_terminal_B x with h | h <;> rw [h] <;> simp

/-! ## §R.5 三層定理（交付 4；B 詞彙、素材 B 自產） -/

/-- `3·1787 + 1 = 5362 = 2 · 2681`（B0 `U` 經 `ofDigits_Uacc`，kernel 求值；B3a D3）。 -/
lemma Todd_1787 : Todd 1787 = 2681 := by rw [← ofDigits_Uacc]; decide

/-- `3·2681 + 1 = 8044 = 4 · 2011`。 -/
lemma Todd_2681 : Todd 2681 = 2011 := by rw [← ofDigits_Uacc]; decide

/-- **軌道回歸（B 座標）**：`F_B 2011 = F_B 1787`（kernel `decide`：兩條 13 步 `extIn` 走行 × 18 座標；
不引 A 的 `F_2011_eq_F_1787`）。機制（觀察，不入定理）：2011 的位元串是 1787 的位元串把 (2,S,1) 錨定的
兩個閉走行 `[17,17,17]` 與 `[16,9,15]` 對調（電池 11、A-5 註記）。 -/
lemma F_B_2011_eq : F_B 2011 = F_B 1787 := by
  funext i; revert i; decide

/-- 終末位相等（皆為 (0,S,1)，`decide`）。 -/
lemma termB_2011_eq : termB 2011 = termB 1787 := by decide

/-- 模式相等（由特徵層相等）。 -/
lemma modeB_2011_eq : modeB 2011 = modeB 1787 := by
  unfold modeB; rw [F_B_2011_eq]

/-- **(a) 軌道成本恆等**：對任意 θ、βv，`cost (extInM 2011) = cost (extInM 1787)`——
橋 ×2 ＋ 特徵／模式／終末位三條相等式（皆 B 座標）。 -/
theorem orbit_cost_eq (θ βv) :
    (SelInst θ βv).cost (extInM 2011) = (SelInst θ βv).cost (extInM 1787) := by
  rw [cost_eq_sel, cost_eq_sel, F_B_2011_eq, modeB_2011_eq, termB_2011_eq]

/-- 兩步見證集（軌道前兩點；`Todd 1787 = 2681`、`Todd 2681 = 2011`）。 -/
def WB1787 : List ℕ := [1787, 2681]

/-- **(b) 無符號 2 見證 no-go**：不存在任何符號的 θ（兩暫存器）與 βv（四個 β_{m,t}）使 `SelInst θ βv`
的成本在 1787、2681 兩步 Todd 迭代皆嚴格下降。證明 = 兩步下降 ∧ (a) ⟹ `linarith`（0 < 0）。 -/
theorem no_go_sel_signed : ¬ ∃ (θ : Fin 2 → Fin 18 → ℚ) (βv : Fin 2 → Fin 2 → ℚ),
    ∀ x ∈ WB1787, (SelInst θ βv).cost (extInM (Todd x)) - (SelInst θ βv).cost (extInM x) < 0 := by
  rintro ⟨θ, βv, h⟩
  have h1 := h 1787 (by decide)
  have h2 := h 2681 (by decide)
  rw [Todd_1787] at h1
  rw [Todd_2681, orbit_cost_eq] at h2
  linarith

/-- **(c) `BoundedBelow` 形**：假設逐字取 B1.5 `SelCostAutomaton.BoundedBelow`
（`∃ B, ∀ u, Accepts u → B ≤ cost u`；由 `accepts_extInM_sel` 非真空），**在證明中棄置**（a fortiori 自 (b)）。
此形之意義：把「gauge 目標類（Sel 實例的 bounded-below 類）在此模板上為空」寫成 kernel 可見的形式紀錄。
證明路線是軌道，不是 gauge——`structured_gauge` 未被使用，且其 `Fintype` 前提在本實例不成立。 -/
theorem no_go_sel_bounded_below : ¬ ∃ (θ : Fin 2 → Fin 18 → ℚ) (βv : Fin 2 → Fin 2 → ℚ),
    (SelInst θ βv).BoundedBelow ∧
    ∀ x ∈ WB1787, (SelInst θ βv).cost (extInM (Todd x)) - (SelInst θ βv).cost (extInM x) < 0 :=
  fun ⟨θ, βv, _, h⟩ => no_go_sel_signed ⟨θ, βv, h⟩

/-! ## §R.6 隨附（D5 全稱形兩式、D6 任意函數版；皆 a fortiori） -/

/-- 全稱形（算術量詞：∀ 奇 x > 1）。 -/
theorem no_go_sel_signed_odd : ¬ ∃ (θ : Fin 2 → Fin 18 → ℚ) (βv : Fin 2 → Fin 2 → ℚ),
    ∀ x : ℕ, x % 2 = 1 → 1 < x →
      (SelInst θ βv).cost (extInM (Todd x)) - (SelInst θ βv).cost (extInM x) < 0 := by
  rintro ⟨θ, βv, h⟩
  exact no_go_sel_signed
    ⟨θ, βv, fun x hx => h x (by fin_cases hx <;> decide) (by fin_cases hx <;> decide)⟩

/-- 全稱形（語言層）：量詞走 B0 `RankingDomain`、動力學走 `Uacc`（B3a D7／B3c D6 同形）。 -/
theorem no_go_sel_signed_lang : ¬ ∃ (θ : Fin 2 → Fin 18 → ℚ) (βv : Fin 2 → Fin 2 → ℚ),
    ∀ w, RankingDomain w →
      (SelInst θ βv).cost (markedExt (Uacc w)) - (SelInst θ βv).cost (markedExt w) < 0 := by
  rintro ⟨θ, βv, h⟩
  refine no_go_sel_signed ⟨θ, βv, fun x hx => ?_⟩
  have hodd : x % 2 = 1 := by fin_cases hx <;> decide
  have h1 : 1 < x := by fin_cases hx <;> decide
  have hcan := isCanonicalOdd_digits hodd
  have hdom : RankingDomain (Nat.digits 2 x) :=
    ⟨hcan, (rankingDomain_iff hcan).mpr (by rw [Nat.ofDigits_digits]; exact h1)⟩
  have := h _ hdom
  rwa [Uacc_digits, ← extInM_eq_markedExt, ← extInM_eq_markedExt] at this

/-- **任意函數版（B 詞彙，D6）**：任何以 (B 佔用向量, 終末位) 為自變量的函數都不能在 1787、2681
兩步同時嚴格下降——A-5 `TwoMode.no_feature_ranking_orbit_1787` 的 B 側鏡射；三層定理皆其實例。 -/
theorem no_feature_ranking_orbit_B :
    ¬ ∃ Φ : (Fin 18 → ℕ) → Fin 2 → ℚ,
      Φ (F_B (Todd 1787)) (termB (Todd 1787)) < Φ (F_B 1787) (termB 1787) ∧
      Φ (F_B (Todd 2681)) (termB (Todd 2681)) < Φ (F_B 2681) (termB 2681) := by
  rintro ⟨Φ, h1, h2⟩
  rw [Todd_1787] at h1
  rw [Todd_2681, F_B_2011_eq, termB_2011_eq] at h2
  linarith

/-! ## §R.V 數據驗證（全部應輸出 `true`；編號照 RB-DESIGN-REPORT §10）

字面即 `tools/b3_attest.py` §I 的錨（`LEAN_RB_*`）。 -/

section Verification

/-- 電池用權重：各座標相異、兩暫存器相異（橋的數值形不退化）。 -/
private def θt : Fin 2 → Fin 18 → ℚ := fun m i => (i.val : ℚ) + 1 + 20 * (m.val : ℚ)

/-- 電池用 β：四格相異。 -/
private def βt : Fin 2 → Fin 2 → ℚ := fun m t => 100 * (m.val : ℚ) + 10 * (t.val : ℚ) + 1

-- 1 旗標錨：模式 0 例 25、2681；模式 1 例 3、1787
#eval [25, 2681, 3, 1787].map flagB == [false, false, true, true]
-- 2 特徵層模式位同序
#eval [25, 2681, 3, 1787].map (fun x => F_B x 13) == [0, 0, 1, 1]
-- 3 count13 ≤ 1（x < 300，含偶數與 0）
#eval (List.range 300).all fun x => F_B x 13 ≤ 1
-- 4 旗標接地：flagB x = [F_B x 13 = 1]（x < 300）
#eval (List.range 300).all fun x => (flagB x == (F_B x 13 == 1))
-- 5 四類 (m, t) 各有實例：1787 ↦ (1,1)、2681 ↦ (0,0)、961 ↦ (0,1)、599 ↦ (1,0)
#eval [1787, 2681, 961, 599].map (fun x => (modeB x, termB x)) == [(1, 1), (0, 0), (0, 1), (1, 0)]
-- 6 成本橋數值形（θt、βt；x < 100 全體）
#eval (List.range 100).all fun x =>
  decide ((SelInst θt βt).cost (extInM x) = βt (modeB x) (termB x) + ∑ i, θt (modeB x) i * F_B x i)
-- 7 軌道成本恆等數值形
#eval decide ((SelInst θt βt).cost (extInM 2011) = (SelInst θt βt).cost (extInM 1787))
-- 8 接受（奇）／拒絕（偶）
#eval (List.range 100).all fun k =>
  decide ((SelInst θt βt).evalFrom initF (extInM (2 * k + 1)) ∈ (SelInst θt βt).accept)
#eval (List.range 100).all fun k =>
  !decide ((SelInst θt βt).evalFrom initF (extInM (2 * k)) ∈ (SelInst θt βt).accept)
-- 9 Todd 鏈
#eval [1787, 2681].map Todd == [2681, 2011]
-- 10 哨兵步不動旗標：只讀 digits x 的旗標 = 讀完 extInM x 的旗標（x < 100）
#eval (List.range 100).all fun x => (flagVal false (1, Phase.K, 0) (Nat.digits 2 x) == flagB x)
-- 11 featList 字面（attest 錨；A-5 機制註記：兩閉走行 [17,17,17]／[16,9,15] 對調）
#eval featList 1787 == [7, 13, 16, 9, 15, 17, 17, 17, 16, 9, 15, 16, 8]
#eval featList 2011 == [7, 13, 16, 9, 15, 16, 9, 15, 17, 17, 17, 16, 8]
-- 12 模式與終末位：1787 ↦ (1,1)、2681 ↦ (0,0)（V2 對照：hm_1787／hm_2681 與終態 (0,S,1)／(0,S,0)）
#eval modeB 1787 == 1 && termB 1787 == 1 && modeB 2681 == 0 && termB 2681 == 0
  && run2 (1, Phase.K, 0) (extIn 1787) == (0, Phase.S, 1) && run2 (1, Phase.K, 0) (extIn 2681) == (0, Phase.S, 0)
-- 13 邊界和雙門（x < 300）＋ 門的實例：25、2681 走門 6；3、1787 走門 13
#eval (List.range 300).all fun x => F_B x 6 + F_B x 13 == 1
#eval [25, 2681].all (fun x => F_B x 6 == 1 && F_B x 13 == 0) && [3, 1787].all (fun x => F_B x 13 == 1 && F_B x 6 == 0)
-- 14 走行分解（evalFrom_extInM 的數值形，x < 100）
#eval (List.range 100).all fun x =>
  decide ((SelInst θt βt).evalFrom initF (extInM x)
    = ((run2 (1, Phase.K, 0) (extIn x), extDFA.evalFrom .start (extInM x)), flagB x))
-- 15 兩暫存器的路徑權重數值形（x < 100）
#eval (List.range 100).all fun x => ([0, 1] : List (Fin 2)).all fun m =>
  decide ((SelInst θt βt).wpath m initF (extInM x) = ∑ i, θt m i * F_B x i)
-- 16 單步不回歸（軌道回歸是兩步現象）
#eval (List.finRange 18).any fun i => F_B 2681 i != F_B 1787 i
-- 17 兩步差分之和為零（no_go_sel_signed 的可見形；θt、βt）
#eval decide (((SelInst θt βt).cost (extInM 2681) - (SelInst θt βt).cost (extInM 1787))
  + ((SelInst θt βt).cost (extInM 2011) - (SelInst θt βt).cost (extInM 2681)) = 0)

end Verification

end CollatzFST.ProjectB
