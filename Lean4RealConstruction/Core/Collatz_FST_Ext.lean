/-
# 3x+1 FST 第二批：Lemma 3 / Theorem 3 / Lemma 4 / Theorem 4（**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_Statements.lean`。

16 條定理無 `sorry`、無禁用戰術（未用 aesop / simp_all / decide 以外的自動化）。
12 項數據驗證見檔末。

## 各節重點

* **§8 `run_append`（組合律）** —— 這批的地基。Lemma 4 與 Theorem 4 都由它導出，
  它同時也是 Theorem 4「進位歷史不被回頭改動」的形式根據（見 `run_take`）。
* **§9 Lemma 3** —— `carry_reset_zero_zero` / `carry_saturate_one_one` 是
  `interval_cases c <;> rfl` 級別。易方向 `synchronizing_of_infix` 走 `run_append` 三段分解。
* **§9 難方向** —— 推論的實質內容。關鍵是 `Good p q b`（狀態對 × 下一位元的相容關係）
  這個不變量：安全轉移只有 `(0,1)--1-->(1,2)`、`(1,2)--0-->(0,1)`、`(0,2)` 起始自由。
  交錯條件（`List.IsChain (· ≠ ·)`）恰好保證只走安全轉移，故像集大小恆為 2、永不塌縮。
  **注意方向**：`(0,1)` 配的是下一位元 `1`（不是 `0`）——`(0,1)` 讀 `0` 會塌縮成 `(0,0)`。
* **§10 Theorem 3** —— 唯一需要真正歸納的。核心發現是**兩側遞迴完全同構**：
  x 偶 → 兩側皆 0；x ≡ 3 (mod 4) → 兩側皆 1；x = 4k+1 → 兩側皆「遞迴值 + 2」
  （`3(4k+1)+1 = 2²(3k+1)`，對應剝掉交錯前綴 `01` 兩位，見 `breaksAlt_shift`）。
  以 `Nat.strong_induction_on` 三分支合併。
* **§11 Lemma 4** —— `run_append` + `sentinel_flush` 的直接應用。
* **§12 Theorem 4** —— 由第一批的 `transduce_split` 導出；性質 2 的精確版
  `digits_Todd_eq_drop` 需要「末位非零」，其根據是 `terminal_carry_ne_zero`
  （若終端進位為 0，則 `3x+1 < 2^len ≤ 2x`，矛盾——用 `Nat.base_pow_length_digits_le`）。

## 技術註記

1. **Theorem 3 不需要「x 為奇數」假設**——此式對所有 x 成立（x 偶時兩側皆 0）。
2. `synchronizing_of_infix` 需額外前提 `∀ b ∈ w, b < 2`（維持進位不變量），
   這在實際應用（w 為二進位串）恆成立。
3. Theorem 4 性質 2 採最強讀法：平移後的序列**恰為**下一次迭代的輸入位元串。
-/
import Lean4RealConstruction.Core.Collatz_FST_Statements
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Find
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Chain

namespace CollatzFST

/-! ## §8 組合律 -/

/-- 規格中的 `t_w(c)`：從進位 `c` 讀完字串 `w` 後的最終進位。 -/
abbrev runCarry (w : List ℕ) (c : ℕ) : ℕ := (run c w).1

theorem run_append (c : ℕ) (w₁ w₂ : List ℕ) :
    run c (w₁ ++ w₂)
      = ((run (run c w₁).1 w₂).1, (run c w₁).2 ++ (run (run c w₁).1 w₂).2) := by
  induction w₁ generalizing c with
  | nil => simp
  | cons b bs ih => rw [List.cons_append, run_cons, ih, run_cons]; simp

theorem run_take (c : ℕ) (bs : List ℕ) (n : ℕ) :
    (run c bs).2.take n = (run c (bs.take n)).2 := by
  induction bs generalizing c n with
  | nil => simp
  | cons b bs ih =>
      cases n with
      | zero => simp
      | succ m => simp [ih]

/-! ## §9 Lemma 3：同步字詞與狀態重置 -/

theorem carry_reset_zero_zero {c : ℕ} (hc : c < 3) : runCarry [0, 0] c = 0 := by
  interval_cases c <;> rfl
theorem carry_saturate_one_one {c : ℕ} (hc : c < 3) : runCarry [1, 1] c = 2 := by
  interval_cases c <;> rfl

-- 進位不變量：任意輸入（不需 b<2）下界仍成立？測試 b 任意時 run 的行為
-- 實際上 synchronizing 只需 w 的位元 < 2；但 c<3 保持需要 b<2。
-- 更簡單：只要 s 讀完後狀態 <3，讀 00 即歸零。
theorem sync_zero {s t : List ℕ} {c c' : ℕ}
    (hc : (run c s).1 < 3) (hc' : (run c' s).1 < 3) :
    runCarry (s ++ [0,0] ++ t) c = runCarry (s ++ [0,0] ++ t) c' := by
  show (run c _).1 = (run c' _).1
  simp only [List.append_assoc, run_append, carry_reset_zero_zero hc,
    carry_reset_zero_zero hc']

theorem sync_one {s t : List ℕ} {c c' : ℕ}
    (hc : (run c s).1 < 3) (hc' : (run c' s).1 < 3) :
    runCarry (s ++ [1,1] ++ t) c = runCarry (s ++ [1,1] ++ t) c' := by
  show (run c _).1 = (run c' _).1
  simp only [List.append_assoc, run_append, carry_saturate_one_one hc,
    carry_saturate_one_one hc']

theorem synchronizing_of_infix {w : List ℕ} {c c' : ℕ} (hc : c < 3) (hc' : c' < 3)
    (hb : ∀ b ∈ w, b < 2)
    (h : [0, 0] <:+: w ∨ [1, 1] <:+: w) : runCarry w c = runCarry w c' := by
  have hsub : ∀ (s : List ℕ), (∀ b ∈ s, b < 2) → ∀ d : ℕ, d < 3 → (run d s).1 < 3 :=
    fun s hs d hd => run_carry_lt_three hd hs
  rcases h with ⟨s, t, hst⟩ | ⟨s, t, hst⟩
  · subst hst
    have hs : ∀ b ∈ s, b < 2 := fun b hb' => hb b (by simp [List.mem_append, hb'])
    exact sync_zero (hsub s hs c hc) (hsub s hs c' hc')
  · subst hst
    have hs : ∀ b ∈ s, b < 2 := fun b hb' => hb b (by simp [List.mem_append, hb'])
    exact sync_one (hsub s hs c hc) (hsub s hs c' hc')

/-! ### §9b 難方向：交錯 ⇒ 不同步 -/

/-- `(p,q)` 與「即將讀入的位元 `b`」相容。
安全轉移：(0,1)--1-->(1,2)，(1,2)--0-->(0,1)，(0,2) 讀任意皆安全。 -/
def Good (p q b : ℕ) : Bool :=
  (p == 0 && q == 1 && b == 1) || (p == 1 && q == 2 && b == 0) || (p == 0 && q == 2)

theorem good_step {p q b b' : ℕ} (h : Good p q b = true) (hb : b < 2) (hb' : b' < 2)
    (hne : b' ≠ b) (hp : p < 3) (hq : q < 3) :
    Good (nextCarry p b) (nextCarry q b) b' = true := by
  interval_cases p <;> interval_cases q <;> interval_cases b <;> interval_cases b' <;>
    revert h hne <;> decide

theorem good_ne {p q b : ℕ} (h : Good p q b = true) (hp : p < 3) (hq : q < 3) (hb : b < 2) :
    p ≠ q := by
  interval_cases p <;> interval_cases q <;> interval_cases b <;> revert h <;> decide

/-- 主歸納：相容狀態對沿交錯串演化後仍不塌縮。 -/
theorem alt_invariant : ∀ (w : List ℕ) (p q : ℕ), p < 3 → q < 3 →
    (∀ b ∈ w, b < 2) → List.IsChain (· ≠ ·) w →
    (∀ b, w.head? = some b → Good p q b = true) →
    (p ≠ q → (run p w).1 ≠ (run q w).1) := by
  intro w
  induction w with
  | nil => intro p q _ _ _ _ _ hpq; simpa using hpq
  | cons b bs ih =>
      intro p q hp hq hb halt hgood hpq
      have hb2 : b < 2 := hb b (List.mem_cons_self ..)
      have hgb : Good p q b = true := hgood b rfl
      simp only [run_cons_fst]
      have hbs : ∀ y ∈ bs, y < 2 := fun y hy => hb y (List.mem_cons_of_mem _ hy)
      have hp' : nextCarry p b < 3 := nextCarry_lt_three hp hb2
      have hq' : nextCarry q b < 3 := nextCarry_lt_three hq hb2
      apply ih (nextCarry p b) (nextCarry q b) hp' hq' hbs halt.tail
      · intro y hy
        have hy2 : y < 2 := hbs y (List.mem_of_mem_head? hy)
        have hyb : y ≠ b := by
          cases bs with
          | nil => simp at hy
          | cons z t =>
              simp only [List.head?_cons, Option.some.injEq] at hy
              subst hy
              rw [List.isChain_cons_cons] at halt
              exact fun hc => halt.1 hc.symm
        exact good_step hgb hb2 hy2 hyb hp hq
      · -- 新狀態對不塌縮：由轉移表逐一檢查
        revert hgb
        interval_cases p <;> interval_cases q <;> interval_cases b <;> decide

/-- 難方向：嚴格交錯 ⇒ 不同步（t_w(0) ≠ t_w(2)）。 -/
theorem not_synchronizing_of_alternating {w : List ℕ} (hb : ∀ b ∈ w, b < 2)
    (halt : List.IsChain (· ≠ ·) w) : (run 0 w).1 ≠ (run 2 w).1 := by
  apply alt_invariant w 0 2 (by norm_num) (by norm_num) hb halt
  · intro b _
    unfold Good
    simp
  · norm_num

/-! ## §10 Theorem 3：2-adic valuation = 最低位交錯前綴長度 -/

def BreaksAlt (x i : ℕ) : Prop := x.testBit i ≠ decide (i % 2 = 0)
instance (x i : ℕ) : Decidable (BreaksAlt x i) := by unfold BreaksAlt; infer_instance
theorem exists_breaksAlt (x : ℕ) : ∃ i, BreaksAlt x i := by
  refine ⟨2 * x, ?_⟩
  unfold BreaksAlt
  have h : x < 2 ^ (2 * x) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.testBit_eq_false_of_lt h]; simp [Nat.mul_mod_right]
def altPrefixLen (x : ℕ) : ℕ := Nat.find (exists_breaksAlt x)

theorem breaksAlt_shift (k i : ℕ) : BreaksAlt (4 * k + 1) (i + 2) ↔ BreaksAlt k i := by
  unfold BreaksAlt
  rw [show i + 2 = i + 1 + 1 from rfl]
  rw [show (4 * k + 1) = 2 * (2 * k) + 1 by ring, Nat.testBit_succ,
      show (2 * (2*k) + 1) / 2 = 2 * k by omega, Nat.testBit_succ,
      show (2 * k) / 2 = k by omega]
  rw [show (i + 1 + 1) % 2 = i % 2 by omega]

-- 情形 A：x 偶
theorem alt_of_even {x : ℕ} (h : x % 2 = 0) : altPrefixLen x = 0 := by
  unfold altPrefixLen
  rw [Nat.find_eq_iff]
  refine ⟨?_, fun n hn => absurd hn (by omega)⟩
  unfold BreaksAlt
  rw [Nat.testBit_zero, h]
  simp

-- 情形 B：x ≡ 3 (mod 4)
theorem alt_of_three_mod_four {x : ℕ} (h : x % 4 = 3) : altPrefixLen x = 1 := by
  unfold altPrefixLen
  rw [Nat.find_eq_iff]
  constructor
  · unfold BreaksAlt
    rw [Nat.testBit_succ, Nat.testBit_zero]
    have : x / 2 % 2 = 1 := by omega
    rw [this]; simp
  · intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    unfold BreaksAlt
    rw [Nat.testBit_zero]
    have : x % 2 = 1 := by omega
    rw [this]; simp

-- 情形 C：x = 4k+1（遞迴）
theorem alt_of_one_mod_four (k : ℕ) : altPrefixLen (4 * k + 1) = altPrefixLen k + 2 := by
  unfold altPrefixLen
  rw [Nat.find_eq_iff]
  constructor
  · rw [breaksAlt_shift]
    exact Nat.find_spec (exists_breaksAlt k)
  · intro n hn
    match n, hn with
    | 0, _ => unfold BreaksAlt; rw [Nat.testBit_zero]; simp; omega
    | 1, _ =>
        unfold BreaksAlt
        rw [Nat.testBit_succ, Nat.testBit_zero, show (4*k+1)/2 = 2*k by omega]
        simp
    | (m+2), hm =>
        rw [breaksAlt_shift]
        exact Nat.find_min (exists_breaksAlt k) (by omega)


theorem v_of_even {x : ℕ} (h : x % 2 = 0) : padicValNat 2 (3 * x + 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd; omega
theorem v_of_three_mod_four {x : ℕ} (h : x % 4 = 3) : padicValNat 2 (3 * x + 1) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ : ∃ k, x = 4 * k + 3 := ⟨x / 4, by omega⟩
  subst hk
  rw [show 3 * (4 * k + 3) + 1 = 2 * (6 * k + 5) by ring,
    padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by omega)]
theorem v_of_one_mod_four (k : ℕ) :
    padicValNat 2 (3 * (4 * k + 1) + 1) = padicValNat 2 (3 * k + 1) + 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show 3 * (4 * k + 1) + 1 = 2 ^ 2 * (3 * k + 1) by ring,
    padicValNat.mul (by norm_num) (by omega), padicValNat.prime_pow]
  omega

/-- **Theorem 3**：v₂(3x+1) = a(x)。對 x 強歸納，三分支對應兩側相同的遞迴。 -/
theorem padicValNat_eq_altPrefixLen (x : ℕ) :
    padicValNat 2 (3 * x + 1) = altPrefixLen x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
      rcases Nat.lt_or_ge x 1 with hx | hx
      · interval_cases x
        · rw [v_of_even (by norm_num), alt_of_even (by norm_num)]
      · rcases Nat.even_or_odd x with he | ho
        · rw [v_of_even (Nat.even_iff.mp he), alt_of_even (Nat.even_iff.mp he)]
        · rcases Nat.lt_or_ge (x % 4) 3 with h4 | h4
          · -- x 奇 且 x%4 < 3 ⇒ x%4 = 1
            have h1 : x % 4 = 1 := by
              have := Nat.odd_iff.mp ho; omega
            obtain ⟨k, hk⟩ : ∃ k, x = 4 * k + 1 := ⟨x / 4, by omega⟩
            subst hk
            rw [v_of_one_mod_four, alt_of_one_mod_four, ih k (by omega)]
          · have h3 : x % 4 = 3 := by
              have := Nat.odd_iff.mp ho; omega
            rw [v_of_three_mod_four h3, alt_of_three_mod_four h3]

/-! ## §11 Lemma 4：終端進位排空（哨兵零） -/

/-- 兩個哨兵零把殘留進位 `c` 完整輸出為兩個位元，且狀態歸零。 -/
theorem sentinel_flush {c : ℕ} (hc : c < 3) : run c [0, 0] = (0, [c % 2, c / 2]) := by
  interval_cases c <;> rfl

/-- 該兩位元的數值恰為殘留進位。 -/
theorem sentinel_flush_value {c : ℕ} (hc : c < 3) :
    Nat.ofDigits 2 (run c [0, 0]).2 = c := by
  rw [sentinel_flush hc]
  simp [Nat.ofDigits]
  omega

/-- 補上哨兵零後的完整封閉：輸出串接兩位元、末狀態歸零。 -/
theorem run_append_sentinel (c : ℕ) (bs : List ℕ) (hc : (run c bs).1 < 3) :
    run c (bs ++ [0, 0])
      = (0, (run c bs).2 ++ [(run c bs).1 % 2, (run c bs).1 / 2]) := by
  rw [run_append, sentinel_flush hc]

/-! ## §12 Theorem 4：尾零刪除的平移等距性 -/

theorem dropWhile_eq_drop (x : ℕ) :
    (transduce x).dropWhile (· = 0) = (transduce x).drop (padicValNat 2 (3 * x + 1)) := by
  conv_rhs => rw [transduce_split x]
  rw [List.drop_append_of_le_length (by rw [List.length_replicate])]
  simp

/-- 終端進位非零：否則 `3x+1 < 2^len ≤ 2x`，矛盾。 -/
theorem terminal_carry_ne_zero (x : ℕ) : (run 1 (Nat.digits 2 x)).1 ≠ 0 := by
  intro h0
  have hsound := ofDigits_run 1 (Nat.digits 2 x)
  rw [h0, Nat.mul_zero, Nat.add_zero, Nat.ofDigits_digits] at hsound
  have hlen := length_run 1 (Nat.digits 2 x)
  have hlt : Nat.ofDigits 2 (run 1 (Nat.digits 2 x)).2 < 2 ^ (Nat.digits 2 x).length := by
    rw [← hlen]
    exact Nat.ofDigits_lt_base_pow_length (by norm_num) (fun d hd => run_out_lt_two d hd)
  rw [hsound] at hlt
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp at hlt
  · have hle := Nat.base_pow_length_digits_le 2 x (by norm_num) (by omega)
    omega

theorem transduce_ne_nil (x : ℕ) : transduce x ≠ [] := by
  rw [transduce_def]
  intro h
  have := List.append_eq_nil_iff.mp h
  exact (Nat.digits_ne_nil_iff_ne_zero.mpr (terminal_carry_ne_zero x)) this.2

theorem transduce_getLast?_ne_zero (x : ℕ) : (transduce x).getLast? ≠ some 0 := by
  have hc := terminal_carry_ne_zero x
  have hne : Nat.digits 2 (run 1 (Nat.digits 2 x)).1 ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr hc
  have hval : (transduce x).getLast?
      = (Nat.digits 2 (run 1 (Nat.digits 2 x)).1).getLast? := by
    rw [transduce_def, List.getLast?_append]
    cases hd : (Nat.digits 2 (run 1 (Nat.digits 2 x)).1).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hd) hne
    | some v => rfl
  rw [hval, List.getLast?_eq_some_getLast hne]
  intro hcon
  exact Nat.getLast_digit_ne_zero 2 hc (Option.some.inj hcon)

theorem transduce_getLast_ne_zero (x : ℕ) (h : transduce x ≠ []) :
    (transduce x).getLast h ≠ 0 := by
  intro hcon
  apply transduce_getLast?_ne_zero x
  rw [List.getLast?_eq_some_getLast h, hcon]

theorem digits_Todd_eq_drop (x : ℕ) :
    Nat.digits 2 (Todd x) = (transduce x).drop (padicValNat 2 (3 * x + 1)) := by
  rw [← dropWhile_eq_drop, ← Todd_eq_dropWhile x]
  apply Nat.digits_ofDigits 2 (by norm_num)
  · intro l hl
    exact transduce_digits_lt_two x l ((List.dropWhile_suffix _).mem hl)
  · intro hne
    have hsuf : (transduce x).dropWhile (· = 0) <:+ transduce x := List.dropWhile_suffix _
    rw [List.IsSuffix.getLast hsuf hne]
    exact transduce_getLast_ne_zero x (transduce_ne_nil x)

/-! ## §13 數據驗證（全部應輸出 `true`） -/

section Verification

private def words : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [0 :: w, 1 :: w])

private def hasRun2 : List ℕ → Bool
  | a :: b :: t => (a == b) || hasRun2 (b :: t)
  | _ => false

private def isBad (x i : ℕ) : Bool := x.testBit i != decide (i % 2 = 0)
private def aIdx (x : ℕ) : ℕ := ((List.range 64).find? (fun i => isBad x i)).getD 64

-- Lemma 3.1 / 3.2
#eval (List.range 3).all fun c => (run c [0, 0]).1 == 0
#eval (List.range 3).all fun c => (run c [1, 1]).1 == 2

-- 推論（→）：含 00/11 ⇒ 同步
#eval ((List.range 9).flatMap words).all fun w =>
  !hasRun2 w || ((run 0 w).1 == (run 1 w).1 && (run 1 w).1 == (run 2 w).1)

-- 推論（←）：交錯 ⇒ 不同步
#eval ((List.range 9).flatMap words).all fun w =>
  hasRun2 w || ((run 0 w).1 != (run 2 w).1)

-- alternating_pair 不變量
#eval ((List.range 9).flatMap words).all fun w =>
  hasRun2 w || (((run 0 w).1, (run 2 w).1) == (0, 2) ||
                ((run 0 w).1, (run 2 w).1) == (0, 1) ||
                ((run 0 w).1, (run 2 w).1) == (1, 2))

-- Theorem 3：全部 x < 400
#eval (List.range 400).all fun x => padicValNat 2 (3 * x + 1) == aIdx x
-- Theorem 3：奇數專測
#eval (List.range 400).all fun x =>
  padicValNat 2 (3 * (2 * x + 1) + 1) == aIdx (2 * x + 1)

-- Lemma 4
#eval (List.range 3).all fun c => run c [0, 0] == (0, [c % 2, c / 2])
#eval (List.range 400).all fun x =>
  let cN := (run 1 (Nat.digits 2 (x + 1))).1; cN == 1 || cN == 2

-- run 組合律
#eval ((List.range 7).flatMap words).all fun w₁ =>
  ((List.range 5).flatMap words).all fun w₂ =>
    (List.range 3).all fun c =>
      run c (w₁ ++ w₂) ==
        ((run (run c w₁).1 w₂).1, (run c w₁).2 ++ (run (run c w₁).1 w₂).2)

-- Theorem 4
#eval (List.range 300).all fun x =>
  (transduce x).dropWhile (· = 0) == (transduce x).drop (padicValNat 2 (3 * x + 1))
#eval (List.range 300).all fun x =>
  Nat.digits 2 (Todd x) == (transduce x).drop (padicValNat 2 (3 * x + 1))

end Verification

end CollatzFST
