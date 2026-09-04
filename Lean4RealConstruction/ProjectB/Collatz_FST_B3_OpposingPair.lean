/-
# Project B 第七批：B3c——無符號對立對定理（Level 2 單模式任意符號線性 ranking 的 2 見證 no-go）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。設計核准 2026-09-04
（B3C-DESIGN-REPORT；Q1–Q5 作答與裁決點 D1–D9 全項通過；D1 裁定拆檔：泛型驗證書見
`Collatz_FST_B2_PassCert.lean`，本檔 = 對立對定理）。

B3b（tools 層）以 θ-LP 的圖論 Farkas 憑證證明 L2 單模式的全語言 no-go，其**極小純路徑形**
是對立對 (25, 315)：ν = (1, 1)、零循環、聚合 = 0——聚合為零的憑證不用 θ ≥ 0，故對**任意符號**
θ ∈ ℚ¹⁸ 成立（A 的 `no_nonneg_linear_ranking` 需 θ ≥ 0、10 見證）。本檔把它鏡射進 kernel：
`ΔF_B 25 + ΔF_B 315 = 0` 由 `decide` 對 Core 機器直接求值，有限形定理 = 和零 ＋ `linarith`
（零符號假設、零圖論、零歸納）；全稱形 a fortiori。**零 ProjectA import**
（`scripts/check_boundaries.py` 強制）；素材全 B3a／B0／B1。

## 內容

* **§B3c.1 差分向量與對立對**：`ΔF_B x i = F_B (Todd x) i − F_B x i`（B3a `DB` 的全稱形，
  `DB_eq_ΔF_B` 接回）；Todd 值經 B0 `U`（B3a D3）；`pair_sum_zero`（kernel `decide`：
  4 條 `extIn` 走行 × 18 座標）；可見形 `ΔF_B_25_eq`。
* **§B3c.2 定理**：有限形 `no_signed_ranking_pair`（頭條）；成本形 `no_signed_ranking_pair_cost`
  （B3a `no_go_L2` 的形狀去掉 `θ ≥ 0`、見證集縮為 {25, 315}）。
* **§B3c.3 全稱形**：算術量詞 `no_signed_ranking_odd`（∀ 奇 x > 1）；語言層 `no_signed_ranking_lang`
  （B3a D7 `no_go_L2_lang` 逐字去掉 `θ ≥ 0`）；`no_go_L2_lang_of_signed`（B3a 定理為本定理特例）。
* **§B3c.4 負向對照**：`single_witness_insufficient`——θ = −e₄ 使 θ·ΔF_B 25 < 0：單一見證擋不住，
  兩見證的對立才是障礙。

## 技術註記（設計定案）

1. **D4**：Lean 端零 ΔF 字面——和零由 `decide` 對機器求值；字面只出現在可見形與電池（attest 錨）。
2. **D6**：全稱形雙敘述——算術量詞為主（任務逐字）、語言層形隨附（與 B3a D7 同形），
   `rankingDomain_iff` 對接。
3. **D9**：B3b 三件套的 Lean 對應——和零 → `pair_sum_zero`；皆在域內 → `rankingDomain_digits`
   實例（＋電池）；**elementary 不宣稱**（D(θ) 圖含輸出側的性質；`L2auto` 乘積態序列上 315 有
   重複），仍是 tools 錨（`b3b_diff.EXPECT_PAIR`）。
4. **機制（觀察，不入定理）**：`featList 315 = featList 19` 於第 3 步後插入 `[9, 15, 17, 16]`、
   `featList 473 = featList 25` 於末步前插入同一區塊——它是 Core 機器在 (1,S,0) 的 4 步閉走行
   （(1,S,0) →1→ (2,S,0) →1→ (2,S,1) →1→ (2,S,1) →0→ (1,S,0)：長 3 循環＋(2,S,1) 自環）。
   同一閉走行同時插進 x 走行與 Todd x 走行、在差分中對消、輸入／輸出角色互換：
   `ΔF_B 315 = (F 25 + c) − (F 19 + c) = −ΔF_B 25`。ROADMAP-B B5「語境封閉」的最小實例。
5. 明確不做（B3c 之後）：Lean 端 D(θ) 與橋定理；路徑枚舉完備性；6 循環 LP 憑證的 pump 族；
   `rdDFA`（D7 緩辦，待 D(θ) 鏡射一併）；雙模式／仿射無符號定理（B3b D5 (4) 觀察層）。
-/
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_L2Instance
import Mathlib.Data.Fin.VecNotation

namespace CollatzFST.ProjectB

/-! ## §B3c.1 差分向量與對立對 -/

/-- 差分向量 `ΔF_B x i = F_B (Todd x) i − F_B x i`（B3a `DB` 的全稱形；由 Core 機器計算，
不是外掛數據）。 -/
def ΔF_B (x : ℕ) (i : Fin 18) : ℤ := (F_B (Todd x) i : ℤ) - F_B x i

/-- 與 B3a 差分表的一致性：`DB j = ΔF_B (wB j)`。 -/
lemma DB_eq_ΔF_B (j : Fin 10) (i : Fin 18) : DB j i = ΔF_B (wB j) i := by
  unfold DB ΔF_B; rw [Todd_wB]

/-! Todd 值經 B0 的 `U`（B3a D3）：`Nat.ofDigits 2 (Uacc (Nat.digits 2 x)) = Todd x`，
左端由 kernel 直接求值。 -/

lemma Todd_25 : Todd 25 = 19 := by rw [← ofDigits_Uacc]; decide
lemma Todd_315 : Todd 315 = 473 := by rw [← ofDigits_Uacc]; decide

/-- **對立對**：`ΔF_B 25 + ΔF_B 315 = 0` 逐座標（kernel `decide`：4 條 `extIn` 走行 × 18 座標；
Lean 端零 ΔF 字面，D4）。 -/
lemma pair_sum_zero : ∀ i, ΔF_B 25 i + ΔF_B 315 i = 0 := by
  intro i
  unfold ΔF_B
  rw [Todd_25, Todd_315]
  revert i
  decide

/-- 可見形（attest 錨的來源）：`ΔF_B 25 = +e₄ −e₆ +e₁₀ −e₁₁ −e₁₂ +e₁₃ −e₁₄ +e₁₆`；
`ΔF_B 315` 為其負（`pair_sum_zero`）。 -/
theorem ΔF_B_25_eq :
    (fun i => ΔF_B 25 i) = ![0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 1, -1, -1, 1, -1, 0, 1, 0] := by
  funext i; unfold ΔF_B; rw [Todd_25]; revert i; decide

/-! ## §B3c.2 定理 -/

/-- **無符號對立對定理（有限形；本 PR 頭條）**：不存在**任何符號**的 θ ∈ ℚ¹⁸ 使 x = 25 與
x = 315 的 Todd 步同時嚴格下降。證明 = 和零 ＋ `linarith`；零符號假設、零圖論、零歸納。
（B3b 圖論 Farkas 憑證的極小純路徑形：ν = (1, 1)、零循環、聚合 = 0。） -/
theorem no_signed_ranking_pair : ¬ ∃ θ : Fin 18 → ℚ,
    ∑ i, θ i * ΔF_B 25 i < 0 ∧ ∑ i, θ i * ΔF_B 315 i < 0 := by
  rintro ⟨θ, h1, h2⟩
  have hsum : ∑ i, θ i * ΔF_B 25 i + ∑ i, θ i * ΔF_B 315 i = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← mul_add]
    have h : ((ΔF_B 25 i : ℤ) : ℚ) + ((ΔF_B 315 i : ℤ) : ℚ) = 0 := by
      exact_mod_cast pair_sum_zero i
    rw [h, mul_zero]
  linarith

/-- 成本形：B3a `no_go_L2` 的形狀、去掉 `θ ≥ 0`、見證集縮為 {25, 315}（橋定理 `cost_eq_sum` ×2）。 -/
theorem no_signed_ranking_pair_cost : ¬ ∃ θ : Fin 18 → ℚ,
    (L2auto θ).cost (extInM (Todd 25)) - (L2auto θ).cost (extInM 25) < 0 ∧
    (L2auto θ).cost (extInM (Todd 315)) - (L2auto θ).cost (extInM 315) < 0 := by
  rintro ⟨θ, h1, h2⟩
  refine no_signed_ranking_pair ⟨θ, ?_, ?_⟩
  · rw [cost_eq_sum, cost_eq_sum, ← Finset.sum_sub_distrib] at h1
    refine lt_of_eq_of_lt (Finset.sum_congr rfl fun i _ => ?_) h1
    simp only [ΔF_B]; push_cast; ring
  · rw [cost_eq_sum, cost_eq_sum, ← Finset.sum_sub_distrib] at h2
    refine lt_of_eq_of_lt (Finset.sum_congr rfl fun i _ => ?_) h2
    simp only [ΔF_B]; push_cast; ring

/-! ## §B3c.3 全稱形（D6：算術量詞為主、語言層形隨附） -/

/-- **全稱形（算術量詞）**：∀ 奇 x > 1 的無符號線性 descent 不存在——a fortiori，
25 與 315 皆在域內。 -/
theorem no_signed_ranking_odd : ¬ ∃ θ : Fin 18 → ℚ,
    ∀ x, x % 2 = 1 → 1 < x → ∑ i, θ i * ΔF_B x i < 0 := by
  rintro ⟨θ, h⟩
  exact no_signed_ranking_pair
    ⟨θ, h 25 (by norm_num) (by norm_num), h 315 (by norm_num) (by norm_num)⟩

/-- 奇數 x > 1 的位元串落在 B0 `RankingDomain`（B3a D7 素材的一般形；`rankingDomain_iff` 對接）。 -/
lemma rankingDomain_digits {x : ℕ} (hx : x % 2 = 1) (h1 : 1 < x) :
    RankingDomain (Nat.digits 2 x) :=
  ⟨isCanonicalOdd_digits hx,
    (rankingDomain_iff (isCanonicalOdd_digits hx)).mpr (by rw [Nat.ofDigits_digits]; exact h1)⟩

/-- **全稱形（語言層）**：B3a D7 `no_go_L2_lang` 逐字去掉 `θ ≥ 0`——量詞走 B0 `RankingDomain`、
動力學走 `Uacc`（B2 段 `D_A(x) = V(U(x)) − V(x)` 的形狀）。 -/
theorem no_signed_ranking_lang : ¬ ∃ θ : Fin 18 → ℚ,
    ∀ w, RankingDomain w →
      (L2auto θ).cost (markedExt (Uacc w)) - (L2auto θ).cost (markedExt w) < 0 := by
  rintro ⟨θ, h⟩
  refine no_signed_ranking_pair_cost ⟨θ, ?_, ?_⟩
  · have := h _ (rankingDomain_digits (x := 25) (by norm_num) (by norm_num))
    rwa [Uacc_digits, ← extInM_eq_markedExt, ← extInM_eq_markedExt] at this
  · have := h _ (rankingDomain_digits (x := 315) (by norm_num) (by norm_num))
    rwa [Uacc_digits, ← extInM_eq_markedExt, ← extInM_eq_markedExt] at this

/-- 與 B3a 的關係：`no_go_L2_lang` 的敘述是本定理的特例（多一個 `θ ≥ 0` 前提）。 -/
theorem no_go_L2_lang_of_signed : (¬ ∃ θ : Fin 18 → ℚ,
    ∀ w, RankingDomain w →
      (L2auto θ).cost (markedExt (Uacc w)) - (L2auto θ).cost (markedExt w) < 0) →
    ¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧
    ∀ w, RankingDomain w →
      (L2auto θ).cost (markedExt (Uacc w)) - (L2auto θ).cost (markedExt w) < 0 :=
  fun hn ⟨θ, _, h⟩ => hn ⟨θ, h⟩

/-! ## §B3c.4 負向對照（NOTES Q1） -/

lemma ΔF_B_25_4 : ΔF_B 25 4 = 1 := by unfold ΔF_B; rw [Todd_25]; decide

/-- **單一見證擋不住**：存在 θ（= −e₄，因 `ΔF_B 25 4 = 1`）使 θ·ΔF_B 25 < 0——
兩見證的對立才是障礙（此 θ 之下 θ·ΔF_B 315 = +1，電池第 11 項）。 -/
theorem single_witness_insufficient : ∃ θ : Fin 18 → ℚ, ∑ i, θ i * ΔF_B 25 i < 0 := by
  refine ⟨fun i => if i = 4 then -1 else 0, ?_⟩
  rw [Finset.sum_eq_single (4 : Fin 18) (fun b _ hb => by simp [hb]) (by simp)]
  simp [ΔF_B_25_4]

/-! ## §B3c.V 數據驗證（全部應輸出 `true`；編號 1–13 照 B3C-DESIGN-REPORT §8）

字面即 `tools/b3_attest.py` §H 的錨（`LEAN_B3C_PAIR*`／`LEAN_B3C_DF25`／`LEAN_B3C_FEATLIST`）。 -/

section Verification

/-- 負向對照的 θ = −e₄。 -/
private def θneg : Fin 18 → ℚ := fun i => if i = 4 then -1 else 0

/-- 成本形數值對照用權重：`θ₀ i = i + 1`（各座標相異）。 -/
private def θ₀ : Fin 18 → ℚ := fun i => (i.val : ℚ) + 1

-- 1 Todd 值
#eval [25, 315].map Todd == [19, 473]

-- 2–5 四條 featList（機制觀察：315 = 19 插入 [9, 15, 17, 16]、473 = 25 插入同區塊）
#eval featList 25 == [7, 12, 6, 5, 11, 14, 8]
#eval featList 19 == [7, 13, 16, 8, 5, 10, 4]
#eval featList 315 == [7, 13, 16, 9, 15, 17, 16, 8, 5, 10, 4]
#eval featList 473 == [7, 12, 6, 5, 11, 14, 9, 15, 17, 16, 8]

-- 6–7 ΔF_B 向量字面（315 = −25）
#eval (List.finRange 18).map (ΔF_B 25) == [0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 1, -1, -1, 1, -1, 0, 1, 0]
#eval (List.finRange 18).map (ΔF_B 315) == [0, 0, 0, 0, -1, 0, 1, 0, 0, 0, -1, 1, 1, -1, 1, 0, -1, 0]

-- 8 逐座標和零
#eval (List.finRange 18).all fun i => ΔF_B 25 i + ΔF_B 315 i == 0

-- 9–10 兩見證落域：奇且 > 1；位元串為 canonical odd 且 ≠ [1]（RankingDomain）
#eval [25, 315].all fun x => x % 2 == 1 && 1 < x
#eval [25, 315].all fun x => decide (IsCanonicalOdd (Nat.digits 2 x)) && (Nat.digits 2 x != [1])

-- 11 負向對照：θ = −e₄ 之下 θ·ΔF_B 25 < 0 而 θ·ΔF_B 315 > 0（對立的可見形）
#eval decide (∑ i, θneg i * ΔF_B 25 i < 0) && decide (0 < ∑ i, θneg i * ΔF_B 315 i)

-- 12 成本形數值（θ₀）：兩差分之和 = 0
#eval decide ((L2auto θ₀).cost (extInM 19) - (L2auto θ₀).cost (extInM 25)
  + ((L2auto θ₀).cost (extInM 473) - (L2auto θ₀).cost (extInM 315)) = 0)

-- 13 B3a 對照：DB j = ΔF_B (wB j) 全表
#eval (List.finRange 10).all fun j => (List.finRange 18).all fun i => DB j i == ΔF_B (wB j) i

end Verification

end CollatzFST.ProjectB
