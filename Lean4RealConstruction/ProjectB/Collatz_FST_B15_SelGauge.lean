/-
# Project B 第四批：Structured Gauge Lemma（B1.5 殘項收口）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。設計核准 2026-08-28
（B15-GAUGE-DESIGN-REPORT；Q1–Q4 與偏差點 D1–D5 全項通過）。

把 B1 的 gauge 定理升到**雙暫存器＋終態選擇**抽象層——ROADMAP-B §0 對
雙模式模板的歸類（2-register copyless CRA + final selection）。證明主體是
**B1 出口的兩次應用＋一個 β 吸收恆等式**，零新圖論歸納（唯一新歸納是
D1 的 list 層望遠鏡 `reweight_wpath`，鏡像 B1 §B1.4 同名引理）。

## 內容

* **§S1 定義層**：`SelCostAutomaton`——單一底層機器（init/step/accept）＋
  終態選擇 `sel : Q → Fin 2`＋每暫存器邊權 `w : Fin 2 → Q → A → ℚ`＋
  共享 α、β。`cost u = α + wpath_{sel(final u)} u + β(final u)`。
  投影 `restrict m`（同機器、接受集過濾 `sel · = m`、權重 `w m`）——
  B1 的 `CostAutomaton` 全 API 免費取得，這是本設計的全部槓桿（Q1）。
* **§S2 Q3 分解**：`cost_restrict`（模式相符的字成本相等）＋
  `boundedBelow_restrict`（一致下界對量詞限縮封閉；接受集空的 m 空虛
  成立，B1 全鏈零接受集非空前提——無需特判，本檔 type-check 即探針）。
* **§S3 β-吸收**（Q4）：`reweight`——`w′ m = w m + h m∘src − h m∘dst`、
  **α 不動**、`β′ q = β q + h (sel q) q − h (sel q) init`。
  `reweight_cost`：任意 h、對**全體字** cost 恆等（與蘊含正交）。
  α 不動的理由：α 是共享常數，per-mode 校正必須住在 per-state 的 β；
  β′ 對接受終態 t 的偏移是常數 `h (sel t) t − h (sel t) init`——恰為
  per-(mode, terminal) 偏移類，與 #39 兩條 terminal-affine no-go 的
  β_{m,t} 對齊（合成 = A 定理升級，見後續 PR；本檔不做）。
* **§S4 主定理**：`HasPotential`（Q2 措辭紀律：逐 m 只對
  `(restrict m).UsefulEdge` 宣稱）；`hasPotential_of_boundedBelow`
  （B1 三條出口 × 每個 m，`choose` 收族）；`structured_gauge` 雙連言收口。
  雙模式 bounded-below ⟹ WLOG θ_m ≥ 0 ＋自由 β_{m,t} 自此成立。

## 技術註記（設計定案）

1. **D1**：恆等式的望遠鏡 `reweight_wpath` 是本檔唯一新歸納（list 層、
   4 行、鏡像 B1）。成因：`(S.reweight h).restrict m` 與
   `(S.restrict m).reweight (h m)` 的 w/step 逐點 defeq 但 α/β 不同，
   兩結構體不相等，B1 引理無法直接改寫。
2. **D2**：主定理雙連言形＋具名端點 `HasPotential`（顯式不等式形，
   B1 命名慣例），兩形以 `reweight_w` rfl 級互通；#39 合成 PR 逐條消費。
3. **D3**：逆向（`HasPotential → BoundedBelow`）非交付項、合成不消費，不做。
4. **D5**：`cost`／`mode` 對全體字有定義（B1 紀律照搬），恆等式因此對
   全體字敘述；β′ 在非接受態亦被改寫（用該態 sel 值）——這正是恆等式
   能對全體字成立的原因，don't-care 語義無洩漏。
5. instance 經濟學：定義層＋ §S2 ＋ §S3 **零 Fintype 需求**；
   §S4 兩定理繼承 B1 (2)⟹(3) 的全四個 instance。
-/
import Lean4RealConstruction.ProjectB.Collatz_FST_B1_Reweighting

namespace CollatzFST.ProjectB

/-- 雙暫存器＋終態選擇成本自動機（ROADMAP-B §0 之
2-register copyless CRA + final selection 的最小載體，B1.5 structured
gauge 的敘述層）：單一底層機器（init/step/accept）＋終態選擇 `sel`＋
每暫存器邊權 `w m`＋共享 α、β。`sel` 取全域函數：非接受態的值為
don't-care（不影響任何接受字的成本；參與 β′ 定義但無語義洩漏，D5）。 -/
structure SelCostAutomaton (Q A : Type*) where
  /-- 初始狀態。 -/
  init : Q
  /-- 確定性狀態轉移（兩暫存器共享同一底層機器）。 -/
  step : Q → A → Q
  /-- 接受集。 -/
  accept : Finset Q
  /-- 終態選擇：接受時由終態決定讀哪個暫存器。 -/
  sel : Q → Fin 2
  /-- 每暫存器邊權。 -/
  w : Fin 2 → Q → A → ℚ
  /-- 共享初始常數權重。 -/
  α : ℚ
  /-- 共享終權。 -/
  β : Q → ℚ

namespace SelCostAutomaton

variable {Q A : Type*} (S : SelCostAutomaton Q A)

/-! ## §S1 定義層 -/

/-- 走行（與 `CostAutomaton.evalFrom` 同一 `foldl`）。 -/
def evalFrom (q : Q) (u : List A) : Q := u.foldl S.step q

@[simp] lemma evalFrom_nil (q : Q) : S.evalFrom q [] = q := rfl

lemma evalFrom_cons (q : Q) (a : A) (u : List A) :
    S.evalFrom q (a :: u) = S.evalFrom (S.step q a) u := rfl

/-- 字的模式：終態的 sel 值。對全體字有定義（D5）。 -/
def mode (u : List A) : Fin 2 := S.sel (S.evalFrom S.init u)

/-- 接受謂詞。 -/
def Accepts (u : List A) : Prop := S.evalFrom S.init u ∈ S.accept

/-- 投影到單暫存器 `CostAutomaton`（Q1 槓桿）：同機器、接受集過濾
`sel · = m`、權重 `w m`、α β 原封不動。filter 的可判定性由
`Fin 2` 的 `DecidableEq` 自動解決，無額外 instance。 -/
def restrict (m : Fin 2) : CostAutomaton Q A where
  init := S.init
  step := S.step
  accept := S.accept.filter fun q => S.sel q = m
  w := S.w m
  α := S.α
  β := S.β

@[simp] lemma restrict_init (m : Fin 2) : (S.restrict m).init = S.init := rfl
@[simp] lemma restrict_step (m : Fin 2) (q : Q) (a : A) :
    (S.restrict m).step q a = S.step q a := rfl
@[simp] lemma restrict_accept (m : Fin 2) :
    (S.restrict m).accept = S.accept.filter fun q => S.sel q = m := rfl
@[simp] lemma restrict_w (m : Fin 2) (q : Q) (a : A) :
    (S.restrict m).w q a = S.w m q a := rfl
@[simp] lemma restrict_α (m : Fin 2) : (S.restrict m).α = S.α := rfl
@[simp] lemma restrict_β (m : Fin 2) (q : Q) : (S.restrict m).β q = S.β q := rfl
@[simp] lemma restrict_evalFrom (m : Fin 2) (q : Q) (u : List A) :
    (S.restrict m).evalFrom q u = S.evalFrom q u := rfl

/-- 每暫存器路徑權重（定義即 restrict 的 `wpath`，rfl 透明）。 -/
def wpath (m : Fin 2) : Q → List A → ℚ := (S.restrict m).wpath

@[simp] lemma wpath_nil (m : Fin 2) (q : Q) : S.wpath m q [] = 0 := rfl

lemma wpath_cons (m : Fin 2) (q : Q) (a : A) (u : List A) :
    S.wpath m q (a :: u) = S.w m q a + S.wpath m (S.step q a) u := rfl

/-- 成本：`α + wpath_{sel(final u)} u + β(final u)`。對全體字有定義；
諸敘述只對 `Accepts` 量化（B1 紀律，D5）。 -/
def cost (u : List A) : ℚ :=
  S.α + S.wpath (S.mode u) S.init u + S.β (S.evalFrom S.init u)

/-- 接受字的成本集合有一致下界（B1 端點 (1) 的 Sel 版）。 -/
def BoundedBelow : Prop := ∃ B : ℚ, ∀ u, S.Accepts u → B ≤ S.cost u

/-! ## §S2 Q3 分解：BoundedBelow 對 restrict 封閉 -/

/-- restrict 的接受 ⟺ 原接受 ∧ 模式相符（`Finset.mem_filter` 的包裝）。 -/
lemma restrict_accepts {m : Fin 2} {u : List A} :
    (S.restrict m).Accepts u ↔ S.Accepts u ∧ S.mode u = m := by
  unfold CostAutomaton.Accepts Accepts mode
  exact Finset.mem_filter

/-- **Q3 對應引理**（ROADMAP-B B1.5）：模式相符的字，restrict 成本 = 原成本
（α、β、走行全共享，僅 wpath 的暫存器指標由 `hm` 對齊）。 -/
lemma cost_restrict {m : Fin 2} {u : List A} (hm : S.mode u = m) :
    (S.restrict m).cost u = S.cost u := by
  simp only [CostAutomaton.cost, cost, wpath, hm, restrict_α, restrict_β,
    restrict_init, restrict_evalFrom]

/-- **Q3 分解**（ROADMAP-B B1.5）：一致下界對量詞限縮封閉——restrict 的
接受字 ⊆ 原接受字且成本相等，同一個 B 直接複用。接受集空的 m 空虛成立，
無需特判。 -/
lemma boundedBelow_restrict (h1 : S.BoundedBelow) (m : Fin 2) :
    (S.restrict m).BoundedBelow := by
  obtain ⟨B, hB⟩ := h1
  refine ⟨B, fun u hu => ?_⟩
  obtain ⟨hacc, hm⟩ := S.restrict_accepts.mp hu
  rw [S.cost_restrict hm]
  exact hB u hacc

/-! ## §S3 β-吸收（Q4；α 不動、與蘊含正交） -/

/-- **Q4 β-吸收 reweight**：`w′ m = w m + h m∘src − h m∘dst`；**α 不動**；
`β′ q = β q + h (sel q) q − h (sel q) init`。init/step/accept/sel 原封不動。
α 不動的理由：α 是共享常數，B1 的 `α′ = α − h(init)` 形在雙暫存器下
無定義（兩個 `h m` 各要吸一份），per-mode 校正必須住在 per-state 的 β。
β′ 對接受終態 t 的偏移 `h (sel t) t − h (sel t) init` 是 per-(mode, terminal)
常數——與 #39 terminal-affine no-go 的 β_{m,t} 對齊處（合成見後續 PR）。 -/
def reweight (h : Fin 2 → Q → ℚ) : SelCostAutomaton Q A :=
  { S with
    w := fun m q a => S.w m q a + h m q - h m (S.step q a)
    β := fun q => S.β q + h (S.sel q) q - h (S.sel q) S.init }

@[simp] lemma reweight_init (h : Fin 2 → Q → ℚ) : (S.reweight h).init = S.init := rfl
@[simp] lemma reweight_step (h : Fin 2 → Q → ℚ) (q : Q) (a : A) :
    (S.reweight h).step q a = S.step q a := rfl
@[simp] lemma reweight_accept (h : Fin 2 → Q → ℚ) : (S.reweight h).accept = S.accept := rfl
@[simp] lemma reweight_sel (h : Fin 2 → Q → ℚ) (q : Q) :
    (S.reweight h).sel q = S.sel q := rfl
@[simp] lemma reweight_w (h : Fin 2 → Q → ℚ) (m : Fin 2) (q : Q) (a : A) :
    (S.reweight h).w m q a = S.w m q a + h m q - h m (S.step q a) := rfl
@[simp] lemma reweight_α (h : Fin 2 → Q → ℚ) : (S.reweight h).α = S.α := rfl
@[simp] lemma reweight_β (h : Fin 2 → Q → ℚ) (q : Q) :
    (S.reweight h).β q = S.β q + h (S.sel q) q - h (S.sel q) S.init := rfl
@[simp] lemma reweight_evalFrom (h : Fin 2 → Q → ℚ) (q : Q) (u : List A) :
    (S.reweight h).evalFrom q u = S.evalFrom q u := rfl

/-- 望遠鏡（**D1：本檔唯一新歸納**，list 層、鏡像 B1 §B1.4 的
`reweight_wpath`）：reweighted 每暫存器路徑權重 = 原權重 + 端點勢能差。 -/
lemma reweight_wpath (h : Fin 2 → Q → ℚ) (m : Fin 2) (q : Q) (u : List A) :
    (S.reweight h).wpath m q u = S.wpath m q u + h m q - h m (S.evalFrom q u) := by
  induction u generalizing q with
  | nil => simp
  | cons a t ih =>
      simp only [wpath_cons, reweight_w, reweight_step, evalFrom_cons, ih]
      ring

/-- **B1.5 β-吸收恆等式**（ROADMAP-B B1.5）：任意 h、對**全體字**（非只
接受字）reweighted cost ≡ 原 cost；α 不動。與 §S4 的蘊含正交
（B1 `reweight_cost` 的結構升級版）。推導：`sel f = m` 之下望遠鏡的
`h m init − h m f` 與 β′ 的 `h m f − h m init` 恰好對消。 -/
theorem reweight_cost (h : Fin 2 → Q → ℚ) (u : List A) :
    (S.reweight h).cost u = S.cost u := by
  simp only [cost, mode, reweight_α, reweight_β, reweight_sel, reweight_init,
    reweight_evalFrom, reweight_wpath]
  ring

/-! ## §S4 主定理（structured gauge） -/

/-- 端點（**Q2 措辭紀律**）：存在每暫存器勢能族 `h : Fin 2 → Q → ℚ`，
使每個 m、每條**對模式 m 有用**的邊（`(restrict m).UsefulEdge`——可達 ∧
可出到 sel = m 的接受態）reduced weight ≥ 0。同一條邊可對兩個 m 各得
一條保證、也可只對一個；聯合 useful 邊的雙保證是假命題（反例見 §S.V
電池項 5：只通往 m=0 接受態的自環，w₁ 在其上對任意 h 恆負）。 -/
def HasPotential : Prop :=
  ∃ h : Fin 2 → Q → ℚ, ∀ m q a,
    (S.restrict m).UsefulEdge q a → 0 ≤ S.w m q a + h m q - h m (S.step q a)

/-- **B1.5 主蘊含**（ROADMAP-B B1.5）：雙模式 bounded-below ⟹ 每暫存器
勢能族。證明 = B1 出口的兩次應用：每個 m 走 `boundedBelow_restrict` →
`cyclesNonneg_of_boundedBelow` → `hasPotential_of_cyclesNonneg`，
`choose` 收族。instance 需求全數繼承自 B1 (2)⟹(3)。 -/
theorem hasPotential_of_boundedBelow
    [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (h1 : S.BoundedBelow) : S.HasPotential := by
  have key : ∀ m : Fin 2, ∃ hm : Q → ℚ, ∀ q a, (S.restrict m).UsefulEdge q a →
      0 ≤ (S.restrict m).w q a + hm q - hm ((S.restrict m).step q a) :=
    fun m => (S.restrict m).hasPotential_of_cyclesNonneg
      ((S.restrict m).cyclesNonneg_of_boundedBelow (S.boundedBelow_restrict h1 m))
  choose h hh using key
  exact ⟨h, fun m q a he => hh m q a he⟩

/-- **B1.5 主定理（structured gauge）**（ROADMAP-B B1.5）：雙連言收口——
存在 gauge `h : Fin 2 → Q → ℚ` 使 (i) 每個 m、每條 `(restrict m).UsefulEdge`
的 reweighted 權重 ≥ 0；(ii) β-吸收後（α 不動）cost 對全體字恆等。
「雙模式 bounded-below ⟹ WLOG θ_m ≥ 0 ＋自由 β_{m,t}」的形式本體；
與 #39 terminal-affine no-go 的合成（A 定理升級）見後續 PR。 -/
theorem structured_gauge
    [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (h1 : S.BoundedBelow) :
    ∃ h : Fin 2 → Q → ℚ,
      (∀ m q a, (S.restrict m).UsefulEdge q a → 0 ≤ (S.reweight h).w m q a) ∧
      (∀ u, (S.reweight h).cost u = S.cost u) := by
  obtain ⟨h, hh⟩ := S.hasPotential_of_boundedBelow h1
  exact ⟨h, fun m q a he => hh m q a he, fun u => S.reweight_cost h u⟩

end SelCostAutomaton

/-! ## §S.V 數據驗證（全部應輸出 `true`）

玩具電池（設計報告 §5）：`Ssel`——Fin 4 states × Fin 2 letters（字母
a = 0、b = 1），一台機器覆蓋四個目的：兩暫存器各含負權邊（勢能非平凡）、
模式 1 循環 tight（三角全等式）、q2 自環 w₁ < 0（Q2 反例）、兩個不同
sel 的接受態（β_{m,t} 偏移可見）。

```
init 0；step: 0 —a→ 1, 0 —b→ 2, 1 —a→ 0, 1 —b→ 3, 2 —·→ 2, 3 —·→ 3
accept {2, 3}；sel = (q3 ↦ 1，其餘 0)
w 0: (0,a)=−2, (1,a)=3, (0,b)=0, (1,b)=−1, (2,·)=0, (3,·)=0
w 1: (0,a)=1, (1,a)=−1, (0,b)=4, (1,b)=−5, (2,·)=−1, (3,·)=0
α = 5；β 2 = 7, β 3 = −2, 其餘 0
```

restrict 0（accept {2}）useful 循環：0↔1 權 1、q2 自環 0，皆 ≥ 0；
restrict 1（accept {3}）useful 循環：0↔1 權 0（tight）、q3 自環 0；
q2 自環 w₁ = −1 但 q2 非模式-1 useful——雙下界成立而聯合保證失敗的機制。 -/

section Verification

open SelCostAutomaton

private def Ssel : SelCostAutomaton (Fin 4) (Fin 2) where
  init := 0
  step := fun q a =>
    if q = 0 then (if a = 0 then 1 else 2)
    else if q = 1 then (if a = 0 then 0 else 3)
    else q
  accept := {2, 3}
  sel := fun q => if q = 3 then 1 else 0
  w := fun m q a =>
    if m = 0 then
      if q = 0 ∧ a = 0 then -2
      else if q = 1 ∧ a = 0 then 3
      else if q = 1 ∧ a = 1 then -1
      else 0
    else
      if q = 0 ∧ a = 0 then 1
      else if q = 1 ∧ a = 0 then -1
      else if q = 0 ∧ a = 1 then 4
      else if q = 1 ∧ a = 1 then -5
      else if q = 2 then -1
      else 0
  α := 5
  β := fun q => if q = 2 then 7 else if q = 3 then -2 else 0

/-- 兩個 h 皆機算（B1 的 `potential`，per-mode 各跑一次）。 -/
private def hsel : Fin 2 → Fin 4 → ℚ := fun m => (Ssel.restrict m).potential

-- 電池項 1：per-mode usefulness 具體見證（Reach 字／CoReach 出字）。
-- 模式 0 的 useful 態 {0, 1, 2}
#eval decide ((Ssel.restrict 0).evalFrom Ssel.init [] = 0)
    && decide ((Ssel.restrict 0).evalFrom 0 [1] ∈ (Ssel.restrict 0).accept)
#eval decide ((Ssel.restrict 0).evalFrom Ssel.init [0] = 1)
    && decide ((Ssel.restrict 0).evalFrom 1 [0, 1] ∈ (Ssel.restrict 0).accept)
#eval decide ((Ssel.restrict 0).evalFrom Ssel.init [1] = 2)
    && decide ((Ssel.restrict 0).evalFrom 2 [] ∈ (Ssel.restrict 0).accept)
-- 模式 1 的 useful 態 {0, 1, 3}
#eval decide ((Ssel.restrict 1).evalFrom Ssel.init [] = 0)
    && decide ((Ssel.restrict 1).evalFrom 0 [0, 1] ∈ (Ssel.restrict 1).accept)
#eval decide ((Ssel.restrict 1).evalFrom Ssel.init [0] = 1)
    && decide ((Ssel.restrict 1).evalFrom 1 [1] ∈ (Ssel.restrict 1).accept)
#eval decide ((Ssel.restrict 1).evalFrom Ssel.init [0, 1] = 3)
    && decide ((Ssel.restrict 1).evalFrom 3 [] ∈ (Ssel.restrict 1).accept)
-- 反向邊界（token 探針；完整論證：q3/q2 是自環 sink，任何出字停在原態，
-- 接受集過濾把它擋下 ⟹ q3 非模式-0 useful、q2 非模式-1 useful）
#eval decide ((Ssel.restrict 0).evalFrom 3 [] ∉ (Ssel.restrict 0).accept)
#eval decide ((Ssel.restrict 1).evalFrom 2 [] ∉ (Ssel.restrict 1).accept)

-- 電池項 2：機算勢能 = 手算預期（八格；設計報告 §5 表）。
#eval ([0, 1, 2, 3] : List (Fin 4)).all fun q =>
  decide (hsel 0 q = if q = 0 then 0 else if q = 1 then -2 else if q = 2 then 0 else -3)
#eval ([0, 1, 2, 3] : List (Fin 4)).all fun q =>
  decide (hsel 1 q = if q = 0 then 0 else if q = 1 then 1 else if q = 2 then 2 else -4)

-- 電池項 3：per-mode 三角——顯式 useful 邊列表（Q2 紀律：不掃全邊）。
-- 模式 0 useful 邊：(0,a) (0,b) (1,a) (2,·)
#eval ([(0, 0), (0, 1), (1, 0), (2, 0), (2, 1)] : List (Fin 4 × Fin 2)).all fun e =>
  decide (0 ≤ (Ssel.reweight hsel).w 0 e.1 e.2)
-- 模式 1 useful 邊：(0,a) (1,a) (1,b) (3,·)
#eval ([(0, 0), (1, 0), (1, 1), (3, 0), (3, 1)] : List (Fin 4 × Fin 2)).all fun e =>
  decide (0 ≤ (Ssel.reweight hsel).w 1 e.1 e.2)

-- 電池項 4：cost_restrict 可見形（終態 2 走模式 0、終態 3 走模式 1）。
#eval decide ((Ssel.restrict 0).cost [1] = Ssel.cost [1])
#eval decide ((Ssel.restrict 1).cost [0, 1] = Ssel.cost [0, 1])

-- 電池項 5：Q2 反例探針——q2 自環是 (restrict 0).UsefulEdge（見證見電池項 1），
-- 其模式 1 reduced weight = −1 + h₁(q2) − h₁(q2) = −1 < 0 對**任意** h 成立
-- （自環望遠鏡歸零）⟹ 聯合 useful 邊的雙保證版是假命題。
#eval decide ((Ssel.reweight hsel).w 1 2 0 < 0)

-- 電池項 6：恆等式全字枚舉（長 ≤ 6）＋正交性（junk h = 模式對調再跑一次）。
private def wordsB15 : ℕ → List (List (Fin 2))
  | 0 => [[]]
  | n + 1 => (wordsB15 n).flatMap fun u => [0 :: u, 1 :: u]

private def hswap : Fin 2 → Fin 4 → ℚ := fun m => hsel (1 - m)

#eval ((List.range 7).flatMap wordsB15).all fun u =>
  decide ((Ssel.reweight hsel).cost u = Ssel.cost u)
#eval ((List.range 7).flatMap wordsB15).all fun u =>
  decide ((Ssel.reweight hswap).cost u = Ssel.cost u)

-- 電池項 7：α 不動＋β_{m,t} 偏移可見形（#39 對齊的機算面）。
#eval decide ((Ssel.reweight hsel).α = Ssel.α)
#eval ([2, 3] : List (Fin 4)).all fun t =>
  decide ((Ssel.reweight hsel).β t - Ssel.β t = hsel (Ssel.sel t) t - hsel (Ssel.sel t) 0)

end Verification

end CollatzFST.ProjectB
