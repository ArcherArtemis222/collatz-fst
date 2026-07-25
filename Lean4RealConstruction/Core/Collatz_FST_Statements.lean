/-
# 3x+1 有限狀態進位轉換器：形式化（**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。背景工具支援見 `Collatz_FST_Survey.lean`。

原規格的五組敘述全部成立，21 條定理無 `sorry`、無禁用戰術，
僅依賴 `propext` / `Classical.choice` / `Quot.sound`。

## 關鍵 helper（讓歸納可行的原因）

* `run_nil` / `run_cons_fst` / `run_cons_snd`：`run` 的方程式引理，三條都是 `rfl`。
  這是整份證明的樞紐——沒有它們，`run` 的 `let` 綁定會擋住 `simp`/歸納。
* `transduce_def`：把 `transduce` 的 `let` 展開成 `++` 形式（`rfl`），
  解決你提到的「transduce 構造長度動態變化」——長度守恆由 `length_run` 單獨處理，
  `transduce` 本身只在 `ofDigits_append` 層面拆解，不必對其長度歸納。
* `ofDigits_replicate_zero` / `takeWhile_zero_eq_replicate` / `zeros_split` /
  `ofDigits_eq_pow_mul`：把「LSB 端連續零」的組合操作翻譯成 `2^k * m` 的算術分解。
* `not_two_dvd_ofDigits_dropWhile`：消零後首位必為 1，故為奇數（走歸納，
  避開 `List.head` 的依賴型別麻煩）。
* `padicValNat_two_pow_mul`：`v₂(2^k · m) = k`（m 奇）。

## 證明結構

§1 不變量 → §2 soundness（`ofDigits out + 2^n·c_out = 3·ofDigits bs + c_in`，
對 bs 歸納，核心恆等式為 `outBit + 2·nextCarry = 3b + c`，即 `Nat.mod_add_div`）
→ §3/§4 區塊重寫（對 g/L 歸納）→ §5 由 §4 直接讀出 → §6 走
「輸出 = 2^v · 奇數」的唯一分解。

## 技術註記（同前，不影響正確性）

* Lemma 1/2 不需要「內部」限定詞：區塊重寫規則對任意位置成立，只由 `c_in` 決定。
* Theorem 1 的 case 說明對 L = 1 略有出入（c_in = 0 且 L = 1 時輸出 `1`，產生 **0** 個零）；
  定理本身寫「至多 1 個」故成立，見 `fission_bound` 中 L = 1 的分支。
* Theorem 2 後半句採「最強精確版」`transduce_split`：輸出串恰為
  「`v₂(3x+1)` 個前綴 0」++「消去後的串」。若你要別的讀法，告訴我。
-/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace CollatzFST

/-! ## §0 定義 -/

/-- 局部轉移：輸出位元 `d = (3b + c) % 2`。 -/
def outBit (c b : ℕ) : ℕ := (3 * b + c) % 2

/-- 局部轉移：下一進位 `c' = ⌊(3b + c) / 2⌋`。 -/
def nextCarry (c b : ℕ) : ℕ := (3 * b + c) / 2

/-- 沿 **LSB → MSB** 掃描輸入位元串，回傳 `(最終進位, 輸出位元串)`。 -/
def run : ℕ → List ℕ → ℕ × List ℕ
  | c, [] => (c, [])
  | c, b :: bs =>
      let r := run (nextCarry c b) bs
      (r.1, outBit c b :: r.2)

/-- 完整的 `3x+1` 轉換：以 `c₀ = 1` 起始，尾端補上最終進位的二進位展開。 -/
def transduce (x : ℕ) : List ℕ :=
  let r := run 1 (Nat.digits 2 x)
  r.2 ++ Nat.digits 2 r.1

/-- Collatz 加速映射 `T_o(x) = (3x+1) / 2^{v₂(3x+1)}`。 -/
def Todd (x : ℕ) : ℕ := (3 * x + 1) / 2 ^ padicValNat 2 (3 * x + 1)

/-! ### 方程式引理（歸納的樞紐，皆為 `rfl`） -/

@[simp] lemma run_nil (c : ℕ) : run c [] = (c, []) := rfl

@[simp] lemma run_cons_fst (c b : ℕ) (bs : List ℕ) :
    (run c (b :: bs)).1 = (run (nextCarry c b) bs).1 := rfl

@[simp] lemma run_cons_snd (c b : ℕ) (bs : List ℕ) :
    (run c (b :: bs)).2 = outBit c b :: (run (nextCarry c b) bs).2 := rfl

lemma run_cons (c b : ℕ) (bs : List ℕ) :
    run c (b :: bs)
      = ((run (nextCarry c b) bs).1, outBit c b :: (run (nextCarry c b) bs).2) := rfl

lemma transduce_def (x : ℕ) :
    transduce x = (run 1 (Nat.digits 2 x)).2 ++ Nat.digits 2 (run 1 (Nat.digits 2 x)).1 := rfl

theorem three_x_plus_one_pos (x : ℕ) : 0 < 3 * x + 1 := by omega

/-! ## §1 基本不變量 -/

theorem nextCarry_lt_three {c b : ℕ} (hc : c < 3) (hb : b < 2) : nextCarry c b < 3 := by
  unfold nextCarry; omega

theorem run_carry_lt_three {c : ℕ} {bs : List ℕ} (hc : c < 3) (hb : ∀ b ∈ bs, b < 2) :
    (run c bs).1 < 3 := by
  induction bs generalizing c with
  | nil => simpa using hc
  | cons b bs ih =>
      simp only [run_cons_fst]
      exact ih (nextCarry_lt_three hc (hb b (List.mem_cons_self ..)))
        (fun x hx => hb x (List.mem_cons_of_mem _ hx))

theorem run_out_lt_two {c : ℕ} {bs : List ℕ} : ∀ d ∈ (run c bs).2, d < 2 := by
  induction bs generalizing c with
  | nil => simp
  | cons b bs ih =>
      simp only [run_cons_snd, List.mem_cons]
      rintro d (rfl | hd)
      · unfold outBit; omega
      · exact ih d hd

theorem length_run (c : ℕ) (bs : List ℕ) : (run c bs).2.length = bs.length := by
  induction bs generalizing c with
  | nil => simp
  | cons b bs ih => simp [ih]

/-! ## §2 Soundness 骨幹 -/

theorem ofDigits_run (c : ℕ) (bs : List ℕ) :
    Nat.ofDigits 2 (run c bs).2 + 2 ^ bs.length * (run c bs).1
      = 3 * Nat.ofDigits 2 bs + c := by
  induction bs generalizing c with
  | nil => simp
  | cons b bs ih =>
      have h := ih (nextCarry c b)
      -- 核心恆等式：`outBit + 2·nextCarry = 3b + c`（即 `Nat.mod_add_div`）
      have key : outBit c b + 2 * nextCarry c b = 3 * b + c := by
        unfold outBit nextCarry; omega
      simp only [run_cons_snd, run_cons_fst, Nat.ofDigits_cons, List.length_cons, pow_succ]
      calc outBit c b + 2 * Nat.ofDigits 2 (run (nextCarry c b) bs).2
              + 2 ^ bs.length * 2 * (run (nextCarry c b) bs).1
          = outBit c b + 2 * (Nat.ofDigits 2 (run (nextCarry c b) bs).2
              + 2 ^ bs.length * (run (nextCarry c b) bs).1) := by ring
        _ = outBit c b + 2 * (3 * Nat.ofDigits 2 bs + nextCarry c b) := by rw [h]
        _ = 3 * (b + 2 * Nat.ofDigits 2 bs) + c := by omega

theorem ofDigits_transduce (x : ℕ) : Nat.ofDigits 2 (transduce x) = 3 * x + 1 := by
  have h := ofDigits_run 1 (Nat.digits 2 x)
  rw [Nat.ofDigits_digits] at h
  rw [transduce_def, Nat.ofDigits_append, length_run, Nat.ofDigits_digits]
  exact h

lemma transduce_digits_lt_two (x : ℕ) : ∀ d ∈ transduce x, d < 2 := by
  intro d hd
  rw [transduce_def, List.mem_append] at hd
  rcases hd with h | h
  · exact run_out_lt_two d h
  · exact Nat.digits_lt_base (by norm_num) h

/-! ## §3 Lemma 1：零區塊重寫 `0^g` -/

theorem zeroRun_carry_zero (g : ℕ) :
    run 0 (List.replicate g 0) = (0, List.replicate g 0) := by
  induction g with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, run_cons]; norm_num [outBit, nextCarry, ih]

theorem zeroRun_carry_one {g : ℕ} (hg : 1 ≤ g) :
    run 1 (List.replicate g 0) = (0, 1 :: List.replicate (g - 1) 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  rw [List.replicate_succ, run_cons]
  norm_num [outBit, nextCarry, zeroRun_carry_zero]

theorem zeroRun_carry_two_one : run 2 (List.replicate 1 0) = (1, [0]) := rfl

theorem zeroRun_carry_two {g : ℕ} (hg : 2 ≤ g) :
    run 2 (List.replicate g 0) = (0, 0 :: 1 :: List.replicate (g - 2) 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
  rw [show k + 2 = (k + 1) + 1 from rfl, List.replicate_succ, List.replicate_succ, run_cons]
  norm_num [outBit, nextCarry, run_cons, zeroRun_carry_zero]
  omega

/-! ## §4 Lemma 2：一區塊重寫 `1^L` -/

theorem oneRun_carry_two (L : ℕ) :
    run 2 (List.replicate L 1) = (2, List.replicate L 1) := by
  induction L with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, run_cons]; norm_num [outBit, nextCarry, ih]

theorem oneRun_carry_one {L : ℕ} (hL : 1 ≤ L) :
    run 1 (List.replicate L 1) = (2, 0 :: List.replicate (L - 1) 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  rw [List.replicate_succ, run_cons]
  norm_num [outBit, nextCarry, oneRun_carry_two]

theorem oneRun_carry_zero_one : run 0 (List.replicate 1 1) = (1, [1]) := rfl

theorem oneRun_carry_zero {L : ℕ} (hL : 2 ≤ L) :
    run 0 (List.replicate L 1) = (2, 1 :: 0 :: List.replicate (L - 2) 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 2 := ⟨L - 2, by omega⟩
  rw [show k + 2 = (k + 1) + 1 from rfl, List.replicate_succ, List.replicate_succ, run_cons]
  norm_num [outBit, nextCarry, run_cons, oneRun_carry_two]
  omega

/-! ## §5 Theorem 1：單一 1-block 的 O(1) 裂變上限 -/

theorem fission_count_carry_two (L : ℕ) :
    (run 2 (List.replicate L 1)).2.count 0 = 0 := by
  rw [oneRun_carry_two]; simp [List.count_replicate]

theorem fission_count_carry_one {L : ℕ} (hL : 1 ≤ L) :
    (run 1 (List.replicate L 1)).2.count 0 = 1 := by
  rw [oneRun_carry_one hL]; simp [List.count_replicate]

theorem fission_count_carry_zero {L : ℕ} (hL : 2 ≤ L) :
    (run 0 (List.replicate L 1)).2.count 0 = 1 := by
  rw [oneRun_carry_zero hL]; simp [List.count_replicate]

/-- 任意 `L ≥ 1`、任意 `c_in ∈ {0,1,2}`，`1^L` 經單次轉移至多新增 1 個零位元。
注意 `c = 0` 需分 `L = 1`（輸出 `1`，**0** 個零）與 `L ≥ 2`（1 個零）。 -/
theorem fission_bound {c L : ℕ} (hc : c < 3) (hL : 1 ≤ L) :
    (run c (List.replicate L 1)).2.count 0 ≤ 1 := by
  interval_cases c
  · rcases Nat.lt_or_ge L 2 with h | h
    · have hL1 : L = 1 := by omega
      subst hL1; rw [oneRun_carry_zero_one]; simp
    · rw [fission_count_carry_zero h]
  · rw [fission_count_carry_one hL]
  · rw [fission_count_carry_two]; omega

/-! ## §6 Theorem 2：邊界尾零消去 -/

lemma ofDigits_replicate_zero (k : ℕ) : Nat.ofDigits 2 (List.replicate k 0) = 0 := by
  induction k with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, Nat.ofDigits_cons, ih]

lemma takeWhile_zero_eq_replicate (l : List ℕ) :
    l.takeWhile (· = 0) = List.replicate (l.takeWhile (· = 0)).length 0 := by
  induction l with
  | nil => simp
  | cons d t ih =>
      by_cases hd : d = 0
      · simp only [hd, List.takeWhile_cons, decide_true, if_true, List.length_cons,
          List.replicate_succ, List.cons.injEq, true_and]
        exact ih
      · simp [hd]

lemma zeros_split (l : List ℕ) :
    l = List.replicate (l.takeWhile (· = 0)).length 0 ++ l.dropWhile (· = 0) := by
  nth_rewrite 1 [← List.takeWhile_append_dropWhile (p := (· = 0)) (l := l)]
  congr 1
  exact takeWhile_zero_eq_replicate l

lemma ofDigits_eq_pow_mul (l : List ℕ) :
    Nat.ofDigits 2 l
      = 2 ^ (l.takeWhile (· = 0)).length * Nat.ofDigits 2 (l.dropWhile (· = 0)) := by
  nth_rewrite 1 [zeros_split l]
  rw [Nat.ofDigits_append, ofDigits_replicate_zero, List.length_replicate]
  simp

/-- 消零後首位必為 1，故所得數為奇數。 -/
lemma not_two_dvd_ofDigits_dropWhile : ∀ (l : List ℕ), (∀ d ∈ l, d < 2) →
    Nat.ofDigits 2 (l.dropWhile (· = 0)) ≠ 0 →
    ¬ 2 ∣ Nat.ofDigits 2 (l.dropWhile (· = 0)) := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons d t ih =>
      intro hlt hne
      by_cases hd : d = 0
      · have hdrop : (d :: t).dropWhile (· = 0) = t.dropWhile (· = 0) := by simp [hd]
        rw [hdrop] at hne ⊢
        exact ih (fun y hy => hlt y (List.mem_cons_of_mem _ hy)) hne
      · have hdrop : (d :: t).dropWhile (· = 0) = d :: t := by simp [hd]
        rw [hdrop] at hne ⊢
        have hd1 : d = 1 := by have := hlt d (List.mem_cons_self ..); omega
        rw [Nat.ofDigits_cons, hd1]; omega

lemma padicValNat_two_pow_mul {k m : ℕ} (hm : m ≠ 0) (hodd : ¬ 2 ∣ m) :
    padicValNat 2 (2 ^ k * m) = k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hm, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hodd, Nat.add_zero]

/-- 「僅影響位移對齊、不干擾高位」的精確版：輸出串恰為
「`v₂(3x+1)` 個 0」++「消去後的串」。 -/
theorem transduce_split (x : ℕ) :
    transduce x
      = List.replicate (padicValNat 2 (3 * x + 1)) 0 ++ (transduce x).dropWhile (· = 0) := by
  have hpow := ofDigits_eq_pow_mul (transduce x)
  have htot := ofDigits_transduce x
  have hm : Nat.ofDigits 2 ((transduce x).dropWhile (· = 0)) ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero, htot] at hpow
    omega
  have hodd := not_two_dvd_ofDigits_dropWhile (transduce x) (transduce_digits_lt_two x) hm
  have hval : padicValNat 2 (3 * x + 1) = ((transduce x).takeWhile (· = 0)).length := by
    rw [← htot, hpow]
    exact padicValNat_two_pow_mul hm hodd
  rw [hval]
  exact zeros_split (transduce x)

/-- 尾零消去後的數值，恰為加速映射 `T_o(x)`。 -/
theorem Todd_eq_dropWhile (x : ℕ) :
    Nat.ofDigits 2 ((transduce x).dropWhile (· = 0)) = Todd x := by
  have hpos : 0 < 2 ^ padicValNat 2 (3 * x + 1) := pow_pos (by norm_num) _
  have key : 3 * x + 1
      = 2 ^ padicValNat 2 (3 * x + 1) * Nat.ofDigits 2 ((transduce x).dropWhile (· = 0)) := by
    conv_lhs => rw [← ofDigits_transduce x, transduce_split x, Nat.ofDigits_append,
                    ofDigits_replicate_zero, List.length_replicate]
    simp
  unfold Todd
  calc Nat.ofDigits 2 ((transduce x).dropWhile (· = 0))
      = 2 ^ padicValNat 2 (3 * x + 1) * Nat.ofDigits 2 ((transduce x).dropWhile (· = 0))
          / 2 ^ padicValNat 2 (3 * x + 1) := (Nat.mul_div_cancel_left _ hpos).symm
    _ = (3 * x + 1) / 2 ^ padicValNat 2 (3 * x + 1) := by rw [← key]

/-! ## §7 數據驗證（regression tests；全部應輸出 `true`） -/

section Verification

-- 進位不變量
#eval (List.range 3).all fun c => (List.range 2).all fun b => nextCarry c b < 3

-- Lemma 1：g = 1..8 × c = 0,1,2
#eval (List.range 3).all fun c => (List.range 8).all fun g' =>
  let g := g' + 1
  let expect : ℕ × List ℕ :=
    if c = 0 then (0, List.replicate g 0)
    else if c = 1 then (0, 1 :: List.replicate (g - 1) 0)
    else if g = 1 then (1, [0])
    else (0, 0 :: 1 :: List.replicate (g - 2) 0)
  run c (List.replicate g 0) == expect

-- Lemma 2：L = 1..8 × c = 0,1,2
#eval (List.range 3).all fun c => (List.range 8).all fun L' =>
  let L := L' + 1
  let expect : ℕ × List ℕ :=
    if c = 2 then (2, List.replicate L 1)
    else if c = 1 then (2, 0 :: List.replicate (L - 1) 1)
    else if L = 1 then (1, [1])
    else (2, 1 :: 0 :: List.replicate (L - 2) 1)
  run c (List.replicate L 1) == expect

-- Theorem 1：L = 1..12 × c = 0,1,2
#eval (List.range 3).all fun c => (List.range 12).all fun L' =>
  (run c (List.replicate (L' + 1) 1)).2.count 0 ≤ 1

-- Soundness 不變量：x < 64 × c = 0,1,2
#eval (List.range 3).all fun c => (List.range 64).all fun n =>
  let bs := Nat.digits 2 n
  let r := run c bs
  Nat.ofDigits 2 r.2 + 2 ^ bs.length * r.1 == 3 * Nat.ofDigits 2 bs + c

-- 端到端 3x+1：x < 200
#eval (List.range 200).all fun x => Nat.ofDigits 2 (transduce x) == 3 * x + 1

-- Theorem 2 尾零消去：x < 300
#eval (List.range 300).all fun x =>
  Nat.ofDigits 2 ((transduce x).dropWhile (· = 0)) == Todd x

-- Theorem 2 於奇數：y = 2x+1, x < 300
#eval (List.range 300).all fun x =>
  let y := 2 * x + 1
  Nat.ofDigits 2 ((transduce y).dropWhile (· = 0)) == Todd y

-- transduce_split：前綴零個數恰為 v₂(3x+1)，x < 200
#eval (List.range 200).all fun x =>
  transduce x == List.replicate (padicValNat 2 (3 * x + 1)) 0 ++ (transduce x).dropWhile (· = 0)

end Verification

end CollatzFST
