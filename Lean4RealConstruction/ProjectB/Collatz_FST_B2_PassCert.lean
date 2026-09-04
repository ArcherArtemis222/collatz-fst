/-
# Project B 第六批：B2 驗證書——pass 憑證 (R, C, d) 的 P1–P5 與健全性（B3c，泛型層）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。設計核准 2026-09-04
（B3C-DESIGN-REPORT；Q1–Q5 作答與裁決點 D1–D9 全項通過；D1 裁定拆檔：本檔 = 泛型層＋
實例，**純 B1 依賴、零 Core**；對立對定理另立 `Collatz_FST_B3_OpposingPair.lean`）。

`tools/b2_engine.py` 的 pass 憑證 = `(R, C, d)`：R ⊇ Reach、C ⊇ CoReach ∩ R（P1 前向封閉、
P2 對 R 後向封閉 ⟹ R ∩ C ⊇ Useful，把量化域「useful」局部化）、d 為逐態勢能值
（P3 三角、P4 接受、P5 對齊）。本檔把 `verify_pass_cert` 的五條檢查逐字鏡射成 `PassOK`，
並證健全性 `allNeg_of_passOK : M.PassOK c → M.AllNeg`——**B2 引擎的 pass 憑證自此可換成
Lean 定理**（實例：B2 已知答案 T3）。

## 內容

* **§B2.1 定義層**：`PassCert Q`（`R C : Finset Q`、`d : Q → ℚ` 全函數、死區任值）、
  `AllNeg`（所有接受字成本 < 0）、`PassOK`（P1–P5 五段合取；D = R ∩ C 以「∈ R ∧ ∈ C」展開，
  零 `DecidableEq` 需求）、兩個泛型 `Decidable` 實例（`PassOK` 於 `[DecidableEq Q] [Fintype A]`、
  `Accepts` 於 `[DecidableEq Q]`）。
* **§B2.2 健全性**：三條記帳級 list 歸納——`evalFrom_mem_R`（前綴入 R）、`mem_C_of_evalFrom`
  （由終態反拉入 C）、`cert_telescope`（d 沿走行的望遠鏡）——＋ P2a／P4／P5 ＋ `linarith`。
  **零 instance 需求**；真空（語言空）與空接受集由同一證明涵蓋、不分案。
* **§B2.3 實例**：T3 `MposNeg`（B1 `Mpos` 之 w/α/β 取負；pass，憑證 `d = (−5, −3, −2)`、
  R = C = 全態）、T1 `Mneg`（fail；見證 `[0, 1]` 成本 0）、T5 `Mempty`（真空 pass）。

## 技術註記（設計定案）

1. **D2**：P3 保留 `step q a ∈ R` 一段（由 P1 可推出）以與 `verify_pass_cert` 的「t ∈ D」字面同步。
2. **D3**：ℚ 憑證檢查的 `decide` 在 elaborator 端被 Batteries `@[irreducible] Rat.add` 卡住
   （reduction 停在 `Rat.blt` 的 match），改 `decide +kernel`（kernel 不看 reducibility）；
   證明項仍是 `of_decide_eq_true rfl`、公理不變（非 native 求值，不加 `Lean.ofReduceBool`）。repo 前例：
   `ProjectA/Collatz_FST_L3_DimLower.lean` §84。
3. **D5**：B1 的 `Mneg`／`Mpos` 為 `private`，本檔以公開 `def` 重宣告（字面照
   `b2_engine.from_b1_toy` 行 430–444，該處又照 B1 行 513–521／534–550 轉錄）；B1 檔零改動（Q5）。
4. **Q5**：健全性只用 B1 的 `evalFrom_cons`／`wpath_cons`／`cost`／`Accepts`；不為 P1–P5 另立 cost。
5. 本檔對 Collatz 實例零宣稱（`L2auto θ` 的字母表 `Option ℕ` 無 `Fintype`；D(θ) 鏡射為後續事）。
-/
import Lean4RealConstruction.ProjectB.Collatz_FST_B1_Reweighting
import Mathlib.Data.Fin.VecNotation

namespace CollatzFST.ProjectB

namespace CostAutomaton

variable {Q A : Type*} (M : CostAutomaton Q A)

/-! ## §B2.1 定義層 -/

/-- pass 憑證（B2 `PassCert` 鏡射）：`R ⊇ Reach`、`C ⊇ CoReach ∩ R`、`d` 為逐態勢能值
（全函數；`R ∩ C` 外的值不進任何檢查）。 -/
structure PassCert (Q : Type*) where
  /-- 可達集的上近似（P1 前向封閉）。 -/
  R : Finset Q
  /-- 可出集的上近似（P2 對 R 後向封閉）。 -/
  C : Finset Q
  /-- 逐態勢能值。 -/
  d : Q → ℚ

/-- **AllNeg**（B2 的判定目標）：每個接受字成本 < 0。 -/
def AllNeg : Prop := ∀ u, M.Accepts u → M.cost u < 0

/-- P1–P5（照 `tools/b2_engine.py` `verify_pass_cert` 逐字；`D = R ∩ C` 以 `∈ R ∧ ∈ C` 展開）。 -/
def PassOK (c : PassCert Q) : Prop :=
  -- P1：init ∈ R ∧ R 前向封閉
  (M.init ∈ c.R ∧ ∀ q ∈ c.R, ∀ a, M.step q a ∈ c.R) ∧
  -- P2：R ∩ accept ⊆ C ∧ C 對 R 後向封閉
  ((∀ q ∈ c.R, q ∈ M.accept → q ∈ c.C) ∧ ∀ q ∈ c.R, ∀ a, M.step q a ∈ c.C → q ∈ c.C) ∧
  -- P3：D 內邊三角 d q + w q a ≤ d (step q a)
  (∀ q ∈ c.R, q ∈ c.C → ∀ a, M.step q a ∈ c.R → M.step q a ∈ c.C →
      c.d q + M.w q a ≤ c.d (M.step q a)) ∧
  -- P4：D 內接受態 d + β < 0
  (∀ q ∈ c.R, q ∈ c.C → q ∈ M.accept → c.d q + M.β q < 0) ∧
  -- P5：init ∈ D → α ≤ d init
  (M.init ∈ c.R → M.init ∈ c.C → M.α ≤ c.d M.init)

/-- 可判定性（只在實例 `decide` 處需要；健全性定理零 instance）。 -/
instance (c : PassCert Q) [DecidableEq Q] [Fintype A] : Decidable (M.PassOK c) := by
  unfold PassOK; infer_instance

/-- `Accepts` 的可判定性（接受集為 `Finset`）。 -/
instance (u : List A) [DecidableEq Q] : Decidable (M.Accepts u) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-! ## §B2.2 健全性 -/

section Sound

variable {M} {c : PassCert Q}

/-- 前綴閉包（歸納 1，記帳級）：`q ∈ R ⟹ evalFrom q u ∈ R`（P1 逐步）。 -/
lemma evalFrom_mem_R (h1 : ∀ q ∈ c.R, ∀ a, M.step q a ∈ c.R) :
    ∀ (u : List A) (q : Q), q ∈ c.R → M.evalFrom q u ∈ c.R := by
  intro u
  induction u with
  | nil => intro q hq; exact hq
  | cons a t ih => intro q hq; exact ih _ (h1 q hq a)

/-- 反向閉包（歸納 2，記帳級）：`q ∈ R` 且 `evalFrom q u ∈ C ⟹ q ∈ C`（P1 ＋ P2b 逐步）。 -/
lemma mem_C_of_evalFrom (h1 : ∀ q ∈ c.R, ∀ a, M.step q a ∈ c.R)
    (h2 : ∀ q ∈ c.R, ∀ a, M.step q a ∈ c.C → q ∈ c.C) :
    ∀ (u : List A) (q : Q), q ∈ c.R → M.evalFrom q u ∈ c.C → q ∈ c.C := by
  intro u
  induction u with
  | nil => intro q _ hC; exact hC
  | cons a t ih => intro q hq hC; exact h2 q hq a (ih _ (h1 q hq a) hC)

/-- 望遠鏡（歸納 3，記帳級）：`q ∈ D`、`evalFrom q u ∈ C ⟹ d q + wpath q u ≤ d (evalFrom q u)`
（P3 逐步；沿途每個態經歸納 1、2 都在 D 內）。 -/
lemma cert_telescope (h1 : ∀ q ∈ c.R, ∀ a, M.step q a ∈ c.R)
    (h2 : ∀ q ∈ c.R, ∀ a, M.step q a ∈ c.C → q ∈ c.C)
    (h3 : ∀ q ∈ c.R, q ∈ c.C → ∀ a, M.step q a ∈ c.R → M.step q a ∈ c.C →
      c.d q + M.w q a ≤ c.d (M.step q a)) :
    ∀ (u : List A) (q : Q), q ∈ c.R → q ∈ c.C → M.evalFrom q u ∈ c.C →
      c.d q + M.wpath q u ≤ c.d (M.evalFrom q u) := by
  intro u
  induction u with
  | nil => intro q _ _ _; simp
  | cons a t ih =>
      intro q hqR hqC hC
      have hR' : M.step q a ∈ c.R := h1 q hqR a
      have hC' : M.step q a ∈ c.C := mem_C_of_evalFrom h1 h2 t (M.step q a) hR' hC
      have e1 := h3 q hqR hqC a hR' hC'
      have e2 := ih (M.step q a) hR' hC' hC
      rw [M.wpath_cons, M.evalFrom_cons]
      linarith

end Sound

/-- **健全性（B2 P1–P5 ⟹ AllNeg）**：憑證檢查通過 ⟹ 每個接受字成本 < 0。
接受字 u：終態 ∈ R（歸納 1）→ ∈ C（P2a）→ init ∈ C（歸納 2）→ α ≤ d init（P5）→
d init + wpath ≤ d 終態（歸納 3）→ d 終態 + β < 0（P4）→ cost < 0。
零 instance 需求；真空與空接受集皆由同一證明涵蓋（不分案）。 -/
theorem allNeg_of_passOK {c : PassCert Q} (h : M.PassOK c) : M.AllNeg := by
  obtain ⟨⟨hinit, h1⟩, ⟨h2a, h2b⟩, h3, h4, h5⟩ := h
  intro u hu
  have hu' : M.evalFrom M.init u ∈ M.accept := hu
  have hfR : M.evalFrom M.init u ∈ c.R := evalFrom_mem_R h1 u M.init hinit
  have hfC : M.evalFrom M.init u ∈ c.C := h2a _ hfR hu'
  have hiC : M.init ∈ c.C := mem_C_of_evalFrom h1 h2b u M.init hinit hfC
  have htel := cert_telescope h1 h2b h3 u M.init hinit hiC hfC
  have h4' := h4 _ hfR hfC hu'
  have h5' := h5 hinit hiC
  unfold cost
  linarith

end CostAutomaton

/-! ## §B2.3 實例（B2 已知答案 T3／T1／T5；字面照 `tools/b2_engine.py` `from_b1_toy`） -/

open CostAutomaton

/-- T3 `Mpos_neg`（b2_engine 行 440–444：B1 `Mpos`（行 534–550）之 w/α/β 全取負）：
`0 →ₐ 1`（w 2）、`1 →ₐ 0`（w −3）、`1 →_b 2`（w 1）、`0 →_b 2`（w 0）、accept {2}、
α = −5、β(2) = −7。全循環非正（0→1→0 權 −1、2 自環權 0），M* = −9 < 0 ⟹ pass。 -/
def MposNeg : CostAutomaton (Fin 3) (Fin 2) where
  init := 0
  step := fun q a =>
    if q = 0 then (if a = 0 then 1 else 2)
    else if q = 1 then (if a = 0 then 0 else 2)
    else 2
  accept := {2}
  w := fun q a =>
    if q = 0 ∧ a = 0 then 2
    else if q = 1 ∧ a = 0 then -3
    else if q = 1 ∧ a = 1 then 1
    else 0
  α := -5
  β := fun q => if q = 2 then -7 else 0

/-- T3 憑證（b2_engine 行 466–471 逐字：R = C = 全態、d = {0: −5, 1: −3, 2: −2}）。
P3 於 (0,a)、(1,b)、(2,·) tight；P4：−2 − 7 = −9 < 0（= 引擎 M*）；P5：−5 ≤ −5 tight。 -/
def certMposNeg : PassCert (Fin 3) := ⟨Finset.univ, Finset.univ, ![-5, -3, -2]⟩

/-- T3 憑證過 P1–P5（`decide +kernel`，D3）。 -/
theorem MposNeg_passOK : MposNeg.PassOK certMposNeg := by decide +kernel

/-- **引擎 pass 憑證 ⟹ Lean 定理**：`MposNeg` 的每個接受字成本 < 0。 -/
theorem MposNeg_allNeg : MposNeg.AllNeg := allNeg_of_passOK _ MposNeg_passOK

/-- T1 `Mneg`（b2_engine 行 430–434 ＝ B1 行 513–521）：`0 →ₐ 1`、`1 →ₐ 1`（自環 w −1）、
`1 →_b 2`、accept {2}、α = 0、β ≡ 0。無正循環而 M* = 0 ⟹ fail（B2「Karp 單獨不足」的角）。 -/
def Mneg : CostAutomaton (Fin 3) (Fin 2) where
  init := 0
  step := fun q a => if q = 0 then 1 else if q = 1 then (if a = 0 then 1 else 2) else 2
  accept := {2}
  w := fun q a => if q = 1 ∧ a = 0 then -1 else 0
  α := 0
  β := fun _ => 0

/-- T1 fail 見證（b2_engine 行 461：見證字 (0, 1)、成本 0）：接受且成本 ≥ 0。 -/
theorem Mneg_witness : Mneg.Accepts [0, 1] ∧ 0 ≤ Mneg.cost [0, 1] := by decide +kernel

/-- fail 側：一個成本 ≥ 0 的接受字即否定 AllNeg。 -/
theorem Mneg_not_allNeg : ¬ Mneg.AllNeg :=
  fun h => absurd (h _ Mneg_witness.1) (not_lt.mpr Mneg_witness.2)

/-- T5 `Mempty`（b2_engine 行 450–454）：accept 不可達——真空 pass。 -/
def Mempty : CostAutomaton (Fin 2) (Fin 1) where
  init := 0
  step := fun q _ => q
  accept := {1}
  w := fun _ _ => 0
  α := 0
  β := fun _ => 0

/-- T5 憑證（引擎輸出：R = {0}、C = {1}、d = ∅——此處 d 任取 0）；D = ∅，P3–P5 真空真。 -/
def certMempty : PassCert (Fin 2) := ⟨{0}, {1}, fun _ => 0⟩

theorem Mempty_passOK : Mempty.PassOK certMempty := by decide +kernel

/-- 真空情形不分案：同一健全性定理。 -/
theorem Mempty_allNeg : Mempty.AllNeg := allNeg_of_passOK _ Mempty_passOK

/-! ## §B2.V 數據驗證（全部應輸出 `true`；編號 14–22 承接 B3C-DESIGN-REPORT §8）

字面即 `tools/b3_attest.py` §H 的錨（`LEAN_B3C_T3`／`LEAN_B3C_T1`）：Lean 電池與 Python
各自比對同一字面，兩邊漂移 CI 即紅。 -/

section Verification

-- 14 T3 機器 step 表
#eval (List.finRange 3).map (fun q => (List.finRange 2).map fun a => MposNeg.step q a)
    == [[1, 2], [0, 2], [2, 2]]

-- 15 T3 權重表（Mpos 取負）
#eval (List.finRange 3).map (fun q => (List.finRange 2).map fun a => MposNeg.w q a)
    == [[2, 0], [-3, 1], [0, 0]]

-- 16 α、β、accept
#eval MposNeg.α == -5 && (List.finRange 3).map MposNeg.β == [0, 0, -7] && MposNeg.accept == {2}

-- 17 憑證三值與 R = C = 全態
#eval (List.finRange 3).map certMposNeg.d == [-5, -3, -2]
    && certMposNeg.R == Finset.univ && certMposNeg.C == Finset.univ

-- 18 P1–P5 機算
#eval decide (MposNeg.PassOK certMposNeg)

-- 19 d + β（接受態 2 的 −9 = 引擎 M*）
#eval (List.finRange 3).map (fun q => certMposNeg.d q + MposNeg.β q) == [-5, -3, -9]

-- 20 T1 見證：接受且成本 0（引擎 T1 見證字 (0, 1)、M* = 0）
#eval decide (Mneg.Accepts [0, 1]) && Mneg.cost [0, 1] == 0

-- 21 竄改 d₂ += 10 ⟹ P4 破（PassOK 必 false）
#eval !decide (MposNeg.PassOK ⟨Finset.univ, Finset.univ, ![-5, -3, 8]⟩)

-- 22 竄改 d₁ −= 10 ⟹ P3 破（PassOK 必 false）
#eval !decide (MposNeg.PassOK ⟨Finset.univ, Finset.univ, ![-5, -13, -2]⟩)

end Verification

end CollatzFST.ProjectB
