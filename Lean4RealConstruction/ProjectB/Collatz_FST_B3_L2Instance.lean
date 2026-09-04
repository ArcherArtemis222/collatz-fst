/-
# Project B 第五批：B3a——Level 2 單模式實例化橋（用 B 框架重推 A）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。設計核准 2026-09-04
（B3A-DESIGN-REPORT；Q1–Q5 作答與裁決點 D1–D7 全項通過）。

B3 是 abstraction 的驗收測試：A 的 no-go 應能在 B 的語言裡誠實重推——
**零 ProjectA import**（`scripts/check_boundaries.py` 強制）。本檔為第一階段 B3a：
Level 2 **單模式**模板的實例化橋＋見證集 no-go 重推。素材全 B 自產
（Core＋B0＋B1＋mathlib）：座標、佔用向量、Todd 值、憑證皆另起；只有見證集
`W_B = W₁₀` 照抄（問題輸入，非解答）。λ_B 由 `tools/b3_attest.py` 以單座標憑證
掃描獨立重解（最輕者：Σλ = 34、聚合 = e₁₇），Python 通道另認證 `F_B ≡ F2 ∘ σ`
與「A 的 λ 恰為掃描三成員之一」。雙模式／仿射（SelGauge 實例化）、差分自動機與
B2 引擎全語言重推、Lean 驗證書皆為 **B3b** 之事。

## 內容

* **§B3.1 座標與佔用向量**：`featIdx`（狀態 tuple `(c, P, p)` 與位元 `b` 的字典序，
  K 列 `p` 摺疊——與 A 的 phase-major 順序不同，σ 非平凡）、`featList`
  （Core `microTrace2` 逐步投影）、`F_B`（交付 2）。
* **§B3.2 實例化橋** `L2auto θ`：Core Level-2 機器 × B0 `extDFA` 的 language-product
  （`prodStep step2`，B0 現成）；`w (q, s) a = θ (featIdx q (unmark a))`——哨兵字母
  經 `unmark` 照常計費（Q1）；α = β = 0；接受集 `S8.toFinset ×ˢ {tail2}`（D1）。
* **§B3.3 橋定理**：`prodRun_fst`（B0 `prodRun_snd` 的姊妹）、`wpath_prod`
  （本檔唯一實質歸納）、`cost_eq_featList`（trace 形）、**`cost_eq_sum`**
  （`cost (L2auto θ) (extInM x) = ∑ i, θ i * F_B x i`）、`accepts_extInM`。
* **§B3.4 抽象 Farkas 矛盾** `farkas_contra`：λ > 0 且聚合 Σλ·D 逐座標 ≥ 0 ⟹
  不存在 θ ≥ 0 使每列 θ·D_j < 0（ROADMAP-B B5「錐矛盾」的形式本體；一般引理，非 ad-hoc）。
* **§B3.5 no-go 重推** `no_go_L2`（交付 3）：Todd 值經 B0 的 `U`（D3）、差分表 `DB`
  由 Core 機器計算、聚合非負 `agg_nonneg` 由 kernel `decide`（D4：Lean 端零 ΔF 字面）。
* **§B3.6 語言層全稱形** `no_go_L2_lang`（D7）：量詞走 B0 `RankingDomain`、動力學走 `Uacc`。

## 技術註記（設計定案）

1. **D1**：接受集取 Core 的可達集 `S8`（× `{tail2}`），不取終末態對——後者是 A 的
   `Flow.run2_extIn_terminal`，B 不可 import。語義等價：被 extDFA 接受的字其機器分量
   必落在 `S8`（`run2_mem_S8`）。
2. **D2**：`featIdx` 以 `% 18` 全函數化；`extIn` 走行零垃圾（Core `microTrace2_inv`：
   c < 3、b < 2、K ⇒ p = 0），該分支在橋與 no-go 的量化域上從未觸發。
3. **D3**：`Todd x = ofDigits (Uacc (digits x))`（B0 `ofDigits_Uacc`）＋ kernel `decide`
   （`Nat.digits` 於此 rev 為 semireducible）；不用 `padicValNat` 算術。
4. **D4**：no-go = `farkas_contra` ＋ `agg_nonneg`（`decide` 對 20 條 `extIn` 走行 × 18
   座標直接求值）；可見形 `agg_eq_e17`；20 條 `featList` 由 §B3.V 電池印出供 attest 當錨。
5. **D5**：W₁₀ 上的單座標 Farkas 憑證**不唯一**——`b3_attest.py` 掃描恰得三個
   （B 座標 k = 2：A 的 Σλ = 1024、係數 31；k = 4：Σλ = 312、係數 31；
   k = 17：Σλ = 34、係數 1）。本檔取最輕的 k = 17：`lamB = (3, 2, 4, 2, 2, 6, 5, 1, 6, 3)`。
6. **Q5**：全檔對 `L2State × LSt` 零 `Fintype` 需求；`Accepts`／`decide` 只用 `DecidableEq`。
7. B1 紀律：`cost` 對全體字有定義；no-go 只對 `extInM x`（x ∈ W_B）量化。
-/
import Lean4RealConstruction.Core
import Lean4RealConstruction.ProjectB.Collatz_FST_OddLanguage
import Lean4RealConstruction.ProjectB.Collatz_FST_Transducer
import Lean4RealConstruction.ProjectB.Collatz_FST_B1_Reweighting
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace CollatzFST.ProjectB

/-! ## §B3.1 座標與佔用向量 -/

/-- Level-2 機器狀態（Core 的 `ℕ × Phase × ℕ`：進位、相位、上一輸出）。 -/
abbrev L2State := ℕ × Phase × ℕ

/-- B 自訂特徵座標：狀態 tuple `(c, P, p)` 與位元 `b` 的字典序（`Phase` 依建構子序
K < S；K 列 `p` 由 Core `Inv`（K ⇒ p = 0）摺疊）：`(c, K, _) b ↦ 6c + b`、
`(c, S, p) b ↦ 6c + 2 + 2p + b`。垃圾輸入（c ≥ 3／p ≥ 2／b ≥ 2）以 `% 18` 收回
`Fin 18`——`extIn` 走行上不出現（D2）。 -/
def featIdx : L2State → ℕ → Fin 18
  | (c, .K, _), b => ⟨(6 * c + b) % 18, Nat.mod_lt _ (by decide)⟩
  | (c, .S, p), b => ⟨(6 * c + 2 + 2 * p + b) % 18, Nat.mod_lt _ (by decide)⟩

/-- 走行的特徵座標序列：Core `microTrace2`（初態 `(1, K, 0)`、輸入 `extIn x`）逐步投影。 -/
def featList (x : ℕ) : List (Fin 18) :=
  (microTrace2 (1, Phase.K, 0) (extIn x)).map fun t => featIdx t.1 t.2

/-- **B 的佔用向量（交付 2）**：座標 i 在走行上出現的次數。由 Core 機器重新定義，
不經 A 的 `KEYS`／`occ2`；與 A 的 `F2` 的座標雙射關係由 `tools/b3_attest.py`
以 Python 通道認證。 -/
def F_B (x : ℕ) (i : Fin 18) : ℕ := (featList x).count i

/-! ## §B3.2 實例化橋 -/

/-- 乘積初態：機器 `(1, K, 0)` × DFA `start`。 -/
def L2init : L2State × LSt := ((1, Phase.K, 0), LSt.start)

/-- **實例化橋（交付 1）**：Core Level-2 機器 × B0 `extDFA` 的 language-product
（`prodStep step2`），權重 `θ (featIdx q (unmark a))`（哨兵字母經 `unmark` 照常計費，
Q1；LSt 分量不進權重），α = β = 0，接受集 `S8.toFinset ×ˢ {tail2}`（D1）。 -/
def L2auto (θ : Fin 18 → ℚ) : CostAutomaton (L2State × LSt) (Option ℕ) where
  init := L2init
  step := prodStep step2
  accept := S8.toFinset ×ˢ {LSt.tail2}
  w := fun s a => θ (featIdx s.1 (unmark a))
  α := 0
  β := fun _ => 0

@[simp] lemma L2auto_init (θ : Fin 18 → ℚ) : (L2auto θ).init = L2init := rfl
@[simp] lemma L2auto_step (θ : Fin 18 → ℚ) (s : L2State × LSt) (a : Option ℕ) :
    (L2auto θ).step s a = (step2 s.1 (unmark a), lstep s.2 a) := rfl
@[simp] lemma L2auto_w (θ : Fin 18 → ℚ) (s : L2State × LSt) (a : Option ℕ) :
    (L2auto θ).w s a = θ (featIdx s.1 (unmark a)) := rfl
@[simp] lemma L2auto_α (θ : Fin 18 → ℚ) : (L2auto θ).α = 0 := rfl
@[simp] lemma L2auto_β (θ : Fin 18 → ℚ) (s : L2State × LSt) : (L2auto θ).β s = 0 := rfl

/-! ## §B3.3 橋定理 -/

/-- 乘積走行的機器分量 = Core `run2`（讀去標記位元；B0 `prodRun_snd` 的姊妹）。 -/
theorem prodRun_fst (θ : Fin 18 → ℚ) (q : L2State) (s : LSt) (v : List (Option ℕ)) :
    ((L2auto θ).evalFrom (q, s) v).1 = run2 q (v.map unmark) := by
  induction v generalizing q s with
  | nil => rfl
  | cons a t ih => exact ih _ _

/-- 乘積走行的 DFA 分量 = `extDFA` 走行（B0 `prodRun_snd` 的 re-export）。 -/
theorem prodRun_snd' (θ : Fin 18 → ℚ) (q : L2State) (s : LSt) (v : List (Option ℕ)) :
    ((L2auto θ).evalFrom (q, s) v).2 = extDFA.evalFrom s v :=
  prodRun_snd step2 (q, s) v

/-- 路徑權重 = trace 上 `θ ∘ featIdx` 之和（本檔唯一實質歸納：對 v、generalizing 兩分量）。 -/
theorem wpath_prod (θ : Fin 18 → ℚ) (q : L2State) (s : LSt) (v : List (Option ℕ)) :
    (L2auto θ).wpath (q, s) v
      = ((microTrace2 q (v.map unmark)).map fun t => θ (featIdx t.1 t.2)).sum := by
  induction v generalizing q s with
  | nil => rfl
  | cons a t ih => rw [CostAutomaton.wpath_cons, L2auto_step, ih]; rfl

/-- 橋定理（trace 形）：`cost (L2auto θ) (extInM x) = Σ_{featList x} θ`。
α = β = 0，`extInM_unmark` 接回 Core 的 `extIn`。 -/
theorem cost_eq_featList (θ : Fin 18 → ℚ) (x : ℕ) :
    (L2auto θ).cost (extInM x) = ((featList x).map θ).sum := by
  unfold CostAutomaton.cost
  show 0 + (L2auto θ).wpath ((1, Phase.K, 0), LSt.start) (extInM x) + 0 = _
  rw [wpath_prod, extInM_unmark, featList, List.map_map, zero_add, add_zero]
  rfl

/-- **橋定理（座標形，交付 2）**：`cost (L2auto θ) (extInM x) = ∑ i, θ i * F_B x i`。
trace 形 → `Finset.sum_list_map_count`（在 `toFinset` 上）→ `sum_subset` 擴到 `univ`
（`toFinset` 外的座標 count = 0）。 -/
theorem cost_eq_sum (θ : Fin 18 → ℚ) (x : ℕ) :
    (L2auto θ).cost (extInM x) = ∑ i, θ i * F_B x i := by
  rw [cost_eq_featList, Finset.sum_list_map_count, Finset.sum_subset (Finset.subset_univ _)]
  · simp only [F_B, nsmul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · intro i _ hi
    rw [List.mem_toFinset] at hi
    simp [List.count_eq_zero.mpr hi]

/-- 接受：奇數 x 的 `extInM x` 被 `L2auto θ` 接受——機器分量落在 `S8`
（Core `run2_mem_S8`）、DFA 分量停在 `tail2`（B0 `sentinel_positions`）。 -/
theorem accepts_extInM (θ : Fin 18 → ℚ) {x : ℕ} (hx : x % 2 = 1) :
    (L2auto θ).Accepts (extInM x) := by
  unfold CostAutomaton.Accepts
  have h1 : ((L2auto θ).evalFrom (L2auto θ).init (extInM x)).1
      = run2 (1, Phase.K, 0) (extIn x) := by
    rw [← extInM_unmark]; exact prodRun_fst θ _ _ _
  have h2 : ((L2auto θ).evalFrom (L2auto θ).init (extInM x)).2 = LSt.tail2 := by
    rw [prodRun_snd']; exact (sentinel_positions x hx).2.2
  show _ ∈ S8.toFinset ×ˢ ({LSt.tail2} : Finset LSt)
  rw [Finset.mem_product, h1, h2]
  exact ⟨List.mem_toFinset.mpr (run2_mem_S8 (extIn_bits x)), Finset.mem_singleton_self _⟩

/-! ## §B3.4 抽象 Farkas 矛盾 -/

/-- **錐矛盾**（ROADMAP-B B5 三成分之一的形式本體）：λ > 0（非空族）且聚合
`Σ_j λ_j D_j` 逐座標 ≥ 0 ⟹ 不存在 θ ≥ 0 使每列 `θ · D_j < 0`。
證明：`Σ_j λ_j (θ · D_j) < 0`（`Finset.sum_neg`），而交換求和後
`= Σ_i θ_i (Σ_j λ_j D_j i) ≥ 0`（`sum_comm`、`sum_nonneg`）。 -/
theorem farkas_contra {n m : ℕ} (D : Fin n → Fin m → ℤ) (lam : Fin n → ℕ)
    (hpos : ∀ j, 0 < lam j) (hn : 0 < n)
    (hagg : ∀ i, 0 ≤ ∑ j, (lam j : ℤ) * D j i)
    (θ : Fin m → ℚ) (hθ : ∀ i, 0 ≤ θ i)
    (hneg : ∀ j, ∑ i, θ i * D j i < 0) : False := by
  have h1 : ∑ j, (lam j : ℚ) * ∑ i, θ i * D j i < 0 :=
    Finset.sum_neg (fun j _ => mul_neg_of_pos_of_neg (by exact_mod_cast hpos j) (hneg j))
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have h2 : ∑ j, (lam j : ℚ) * ∑ i, θ i * D j i = ∑ i, θ i * ∑ j, (lam j : ℚ) * D j i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h3 : 0 ≤ ∑ i, θ i * ∑ j, (lam j : ℚ) * D j i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hθ i) (by exact_mod_cast hagg i)
  linarith

/-! ## §B3.5 no-go 重推 -/

/-- 見證集（= A 的 W₁₀，照抄：問題輸入非解答，Q3）。 -/
def W_B : List ℕ := [231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511]

/-- 見證集的 `Fin 10` 索引形（Farkas 引理的族索引）。 -/
def wB : Fin 10 → ℕ := ![231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511]

/-- 各見證的 Todd 值（`Todd_wB` 逐條由 B0 的 `U` 算出）。 -/
def tB : Fin 10 → ℕ := ![347, 485, 605, 827, 511, 329, 1475, 1619, 979, 2267]

/-- **λ_B**：`tools/b3_attest.py` 單座標憑證掃描所得三者中最輕的一個（D5）：
Σλ = 34、聚合 = e₁₇（B 座標 17 = `(2, S, 1, 1)`）。 -/
def lamB : Fin 10 → ℕ := ![3, 2, 4, 2, 2, 6, 5, 1, 6, 3]

/-! Todd 值經 B0 的 `U`（D3）：`Nat.ofDigits 2 (Uacc (Nat.digits 2 x)) = Todd x`
（`ofDigits_Uacc`），左端由 kernel 直接求值。 -/

lemma Todd_231 : Todd 231 = 347 := by rw [← ofDigits_Uacc]; decide
lemma Todd_323 : Todd 323 = 485 := by rw [← ofDigits_Uacc]; decide
lemma Todd_403 : Todd 403 = 605 := by rw [← ofDigits_Uacc]; decide
lemma Todd_551 : Todd 551 = 827 := by rw [← ofDigits_Uacc]; decide
lemma Todd_681 : Todd 681 = 511 := by rw [← ofDigits_Uacc]; decide
lemma Todd_877 : Todd 877 = 329 := by rw [← ofDigits_Uacc]; decide
lemma Todd_983 : Todd 983 = 1475 := by rw [← ofDigits_Uacc]; decide
lemma Todd_1079 : Todd 1079 = 1619 := by rw [← ofDigits_Uacc]; decide
lemma Todd_1305 : Todd 1305 = 979 := by rw [← ofDigits_Uacc]; decide
lemma Todd_1511 : Todd 1511 = 2267 := by rw [← ofDigits_Uacc]; decide

/-- 見證的 Todd 值表。 -/
lemma Todd_wB : ∀ j, Todd (wB j) = tB j := by
  intro j
  fin_cases j
  · exact Todd_231
  · exact Todd_323
  · exact Todd_403
  · exact Todd_551
  · exact Todd_681
  · exact Todd_877
  · exact Todd_983
  · exact Todd_1079
  · exact Todd_1305
  · exact Todd_1511

/-- 差分表 `DB j i = F_B (Todd x_j) i − F_B x_j i`——由 Core 機器計算，不是外掛數據。 -/
def DB (j : Fin 10) (i : Fin 18) : ℤ := (F_B (tB j) i : ℤ) - F_B (wB j) i

/-- 聚合非負：kernel `decide` 直接對 20 條 `extIn` 走行 × 18 座標求值（D4）。 -/
lemma agg_nonneg : ∀ i, 0 ≤ ∑ j, (lamB j : ℤ) * DB j i := by decide

/-- 可見形：聚合恰為 `e₁₇`（λ_B 湮滅其餘 17 座標，係數 1——么模子式）。 -/
theorem agg_eq_e17 :
    (fun i => ∑ j, (lamB j : ℤ) * DB j i)
      = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  funext i; revert i; decide

/-- **no-go 重推（交付 3；敘述照任務逐字）**：不存在非負權重 θ 使 `L2auto θ` 的成本
在 `W_B` 每一步 Todd 迭代皆嚴格下降。證明 = 橋定理 ×2 ＋ `farkas_contra`
（λ_B、`agg_nonneg`）。 -/
theorem no_go_L2 : ¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧
    ∀ x ∈ W_B, (L2auto θ).cost (extInM (Todd x)) - (L2auto θ).cost (extInM x) < 0 := by
  rintro ⟨θ, hθ, h⟩
  refine farkas_contra DB lamB (by decide) (by norm_num) agg_nonneg θ hθ fun j => ?_
  have hj := h (wB j) (by fin_cases j <;> decide)
  rw [cost_eq_sum, cost_eq_sum, Todd_wB, ← Finset.sum_sub_distrib] at hj
  refine lt_of_eq_of_lt (Finset.sum_congr rfl fun i _ => ?_) hj
  simp only [DB]
  push_cast
  ring

/-! ## §B3.6 語言層全稱形（D7） -/

/-- 標記哨兵包裝：`w.map some ++ [none, none]`（`extInM x = markedExt (digits x)`，rfl）。 -/
def markedExt (w : List ℕ) : List (Option ℕ) := w.map some ++ [none, none]

lemma extInM_eq_markedExt (x : ℕ) : extInM x = markedExt (Nat.digits 2 x) := rfl

lemma W_B_odd : ∀ x ∈ W_B, x % 2 = 1 := by decide

lemma W_B_gt_one : ∀ x ∈ W_B, 1 < x := by decide

/-- **語言層全稱形**：量詞走 B0 的 domain 條款 `RankingDomain`（`L ∖ {[1]}`）、動力學走
transducer 的加速輸出 `Uacc`——B2 段 `D_A(x) = V(U(x)) − V(x)` 的形狀。由 `no_go_L2`
a fortiori 得出：`W_B ⊆ 奇數 ∩ (1, ∞)`，`Uacc_digits` 把 `markedExt (Uacc (digits x))`
改寫成 `extInM (Todd x)`。 -/
theorem no_go_L2_lang : ¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧
    ∀ w, RankingDomain w →
      (L2auto θ).cost (markedExt (Uacc w)) - (L2auto θ).cost (markedExt w) < 0 := by
  rintro ⟨θ, hθ, h⟩
  refine no_go_L2 ⟨θ, hθ, fun x hx => ?_⟩
  have hcan := isCanonicalOdd_digits (W_B_odd x hx)
  have hdom : RankingDomain (Nat.digits 2 x) :=
    ⟨hcan, (rankingDomain_iff hcan).mpr (by rw [Nat.ofDigits_digits]; exact W_B_gt_one x hx)⟩
  have := h _ hdom
  rwa [Uacc_digits, ← extInM_eq_markedExt, ← extInM_eq_markedExt] at this

/-! ## §B3.V 數據驗證（全部應輸出 `true`）

電池：手算對照（x = 3）、乘積走行分量、佔用向量的守恆量（總和、死座標、K 座標和）、
橋的數值形、接受性、attest 錨（見證與 Todd 像的 `featList`、Todd 值）、憑證可見形、
D7 素材。 -/

section Verification

/-- 電池用的具體權重：`θ₀ i = i + 1`（各座標相異，橋的數值形不退化）。 -/
private def θ₀ : Fin 18 → ℚ := fun i => (i.val : ℚ) + 1

/-- `θ₁ ≡ 1`：成本 = 走行長度。 -/
private def θ₁ : Fin 18 → ℚ := fun _ => 1

-- 手算對照（設計報告 §4）：x = 3 與其 Todd 像 5
#eval featList 3 == [7, 13, 16, 8]
#eval featList 5 == [7, 12, 7, 12, 6]

-- x = 3 乘積走行前綴：DFA 分量 start/acc/acc/tail1/tail2、機器分量 = run2
#eval (List.range 5).map (fun n => ((L2auto θ₀).evalFrom L2init ((extInM 3).take n)).2)
    == [LSt.start, LSt.acc, LSt.acc, LSt.tail1, LSt.tail2]
#eval (List.range 5).all fun n =>
  ((L2auto θ₀).evalFrom L2init ((extInM 3).take n)).1
    == run2 (1, Phase.K, 0) ((extIn 3).take n)

-- 佔用向量總和 = 走行長度；死座標 0、1 恆零（Core occ2_deadState 的 B 座標形）
#eval (List.range 200).all fun x => ((List.finRange 18).map (F_B x)).sum == (extIn x).length
#eval (List.range 200).all fun x => F_B x 0 == 0 && F_B x 1 == 0

-- K 座標和 = v₂(3x+1) + 1（Core sum_EK_components 的 B 座標形）
#eval (List.range 200).all fun x =>
  F_B x 0 + F_B x 1 + F_B x 6 + F_B x 7 + F_B x 12 + F_B x 13
    == padicValNat 2 (3 * x + 1) + 1

-- 橋的數值形（θ₀，x < 100）
#eval (List.range 100).all fun x =>
  decide ((L2auto θ₀).cost (extInM x) = ∑ i, θ₀ i * F_B x i)

-- 接受（`Accepts` 展開為 Finset 成員）：奇數接受、偶數不接受
#eval (List.range 150).all fun k =>
  decide ((L2auto θ₀).evalFrom L2init (extInM (2 * k + 1)) ∈ (L2auto θ₀).accept)
#eval (List.range 150).all fun k =>
  !decide ((L2auto θ₀).evalFrom L2init (extInM (2 * k)) ∈ (L2auto θ₀).accept)

-- 錨（tools/b3_attest.py 抄錄處）：見證的 Todd 值、見證與 Todd 像的 featList
#eval W_B.map Todd == [347, 485, 605, 827, 511, 329, 1475, 1619, 979, 2267]
#eval W_B.map featList == [
  [7, 13, 17, 16, 8, 5, 11, 15, 16, 8],
  [7, 13, 16, 8, 4, 2, 3, 10, 5, 10, 4],
  [7, 13, 16, 8, 5, 10, 4, 3, 11, 14, 8],
  [7, 13, 17, 16, 8, 5, 10, 4, 2, 3, 10, 4],
  [7, 12, 6, 5, 10, 5, 10, 5, 10, 5, 10, 4],
  [7, 12, 7, 13, 16, 9, 15, 16, 9, 15, 16, 8],
  [7, 13, 17, 16, 9, 14, 9, 15, 17, 17, 16, 8],
  [7, 13, 17, 16, 9, 15, 16, 8, 4, 2, 3, 10, 4],
  [7, 12, 6, 5, 11, 14, 8, 4, 3, 10, 5, 10, 4],
  [7, 13, 17, 16, 8, 5, 11, 15, 17, 16, 9, 14, 8]]
#eval (W_B.map Todd).map featList == [
  [7, 13, 16, 9, 15, 16, 9, 14, 9, 14, 8],
  [7, 12, 7, 12, 6, 5, 11, 15, 17, 16, 8],
  [7, 12, 7, 13, 17, 16, 9, 14, 8, 5, 10, 4],
  [7, 13, 16, 9, 15, 17, 16, 8, 5, 11, 14, 8],
  [7, 13, 17, 17, 17, 17, 17, 17, 17, 16, 8],
  [7, 12, 6, 5, 10, 4, 3, 10, 5, 10, 4],
  [7, 13, 16, 8, 4, 2, 3, 11, 15, 16, 9, 14, 8],
  [7, 13, 16, 8, 5, 10, 5, 10, 4, 3, 11, 14, 8],
  [7, 13, 16, 8, 5, 10, 5, 11, 15, 17, 16, 8],
  [7, 13, 16, 9, 15, 16, 9, 15, 16, 8, 4, 3, 10, 4]]

-- 憑證：Σλ_B = 34、逐項 > 0、聚合 = e₁₇
#eval (∑ j, lamB j) == 34
#eval (List.finRange 10).all fun j => 0 < lamB j
#eval (List.finRange 18).map (fun i => ∑ j, (lamB j : ℤ) * DB j i)
    == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

-- Farkas 可見形（θ₁ ≡ 1）：Σⱼ λⱼ (cost yⱼ − cost xⱼ) = 1 = θ₁ 17
#eval decide ((∑ j, (lamB j : ℚ) *
    ((L2auto θ₁).cost (extInM (tB j)) - (L2auto θ₁).cost (extInM (wB j)))) = 1)

-- D7 素材：markedExt (Uacc (digits x)) = extInM (Todd x)；W_B 的位元串落在 RankingDomain
#eval (List.range 100).all fun k =>
  markedExt (Uacc (Nat.digits 2 (2 * k + 1))) == extInM (Todd (2 * k + 1))
#eval W_B.all fun x => decide (IsCanonicalOdd (Nat.digits 2 x)) && (Nat.digits 2 x != [1])

end Verification

end CollatzFST.ProjectB
