/-
# Project B 第二批：subsequential transducer 介面與 `U` 實例（B0-2 / closure）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_OddLanguage.lean`。

## 內容

* **§B0.4 介面**：`SubTransducer`——小而專用（states = 型參 Q、`init`、`step`、
  per-transition 有界輸出 `out`（`bound`/`out_le` 為結構欄位）、`finalOut`）。
  不設 initial output（`U` 不需要；B2 合成若需要再加，不預鋪）。
* **§B0.5 `U` 實例**：Core 3x+1 機器的包裝。狀態 = 進位（init 1、`U_state_lt_three`
  給出有效狀態 {0,1,2}）、每步輸出恰一位（`U_out_len`）、final output =
  終端進位的二進位（**無填零**，對齊 `transduce`；哨兵沖洗的兩位填零形對齊的是
  `extOut`，在 `c = 1` 時給輸出尾零、破壞正規性——Q2 技術註記）。
* **§B0.6 acceptance（soundness 不重證）**：唯一的結構歸納是橋接 `U_runOut`
  （與 Core `run` 同形遞迴，逐 case rfl）；語義內容全部 re-export：
  `ofDigits_U_output` ← `ofDigits_transduce`、`U_output_split` ← `transduce_split`、
  `ofDigits_Uacc` ← `Todd_eq_dropWhile`、`Uacc_digits` ← `digits_Todd_eq_drop`。
* **§B0.7 closure**：`w ∈ L ⟹ Uacc w ∈ L`，對**全體** L 成立、不排除 `[1]`
  （`[1] ↦ [1]` 是 Todd 不動點的落點，`Uacc_one`）。排名 domain 條款
  `RankingDomain`（`L ∖ {[1]}`）另立，`rankingDomain_iff` 接 no-go 的 `1 < x` 量詞（Q1）。

## 技術註記

1. **Q2 選項 (a)**：K 步照發 0，加速輸出 `Uacc = dropWhile (· = 0) ∘ U.output`
   另包一層。K/S 相位是（初始進位, 已讀前綴）的確定函數（Core `runP_K_iff` 是錨），
   截斷語義住在 `U_output_split`；B1/B3 的 cost automaton 要對 K 步另計權重時，
   在它自己的狀態裡追蹤相位，`U` 不需要為此擴狀態。選項 (b)（K 步緩衝）要求
   重推「緩衝發射串 = 原始輸出的 dropWhile」的歸納，違反 re-export 紅線。
2. 哨兵的 edge 讀法（`extIn`）與 finalOut 讀法（本檔）的對帳由 Core 現成的
   `run_append_sentinel` 承擔，B0 不需新 API。
-/
import Lean4RealConstruction.ProjectB.Collatz_FST_OddLanguage

namespace CollatzFST.ProjectB

/-! ## §B0.4 subsequential transducer 介面 -/

/-- 小而專用的 subsequential transducer：輸入/輸出皆為位元串（`List ℕ`，與 Core 載體
一致）。`bound`/`out_le` 把「per-transition 有界輸出」編進結構本身。 -/
structure SubTransducer (Q : Type*) where
  /-- 初始狀態。 -/
  init : Q
  /-- 狀態轉移。 -/
  step : Q → ℕ → Q
  /-- 每步輸出的位元區塊。 -/
  out : Q → ℕ → List ℕ
  /-- 讀完輸入後的 final output。 -/
  finalOut : Q → List ℕ
  /-- 每步輸出長度的一致上界。 -/
  bound : ℕ
  /-- 有界性見證。 -/
  out_le : ∀ q b, (out q b).length ≤ bound

namespace SubTransducer

variable {Q : Type*}

/-- 逐步累積（鏡射 Core `run` 的遞迴形狀）：回傳（終態, 轉移輸出串）。 -/
def runOut (T : SubTransducer Q) : Q → List ℕ → Q × List ℕ
  | q, [] => (q, [])
  | q, b :: bs =>
      let r := T.runOut (T.step q b) bs
      (r.1, T.out q b ++ r.2)

@[simp] lemma runOut_nil (T : SubTransducer Q) (q : Q) : T.runOut q [] = (q, []) := rfl

lemma runOut_cons (T : SubTransducer Q) (q : Q) (b : ℕ) (bs : List ℕ) :
    T.runOut q (b :: bs)
      = ((T.runOut (T.step q b) bs).1, T.out q b ++ (T.runOut (T.step q b) bs).2) := rfl

/-- 完整輸出 = 轉移輸出 ++ final output。 -/
def output (T : SubTransducer Q) (w : List ℕ) : List ℕ :=
  (T.runOut T.init w).2 ++ T.finalOut (T.runOut T.init w).1

end SubTransducer

/-! ## §B0.5 `U`：Core 3x+1 機器的 subsequential 包裝 -/

/-- **U**：狀態 = 進位（init 1）、每步輸出恰一位、final output = 終端進位的二進位
（無填零，對齊 `transduce`）。 -/
def U : SubTransducer ℕ where
  init := 1
  step := nextCarry
  out := fun c b => [outBit c b]
  finalOut := fun c => Nat.digits 2 c
  bound := 1
  out_le := fun _ _ => by simp

@[simp] lemma U_init : U.init = 1 := rfl
@[simp] lemma U_step (c b : ℕ) : U.step c b = nextCarry c b := rfl
@[simp] lemma U_out (c b : ℕ) : U.out c b = [outBit c b] := rfl
@[simp] lemma U_finalOut (c : ℕ) : U.finalOut c = Nat.digits 2 c := rfl

/-- 每步輸出長度恰為 1（`bound = 1` 是緊的）。 -/
theorem U_out_len (c b : ℕ) : (U.out c b).length = 1 := rfl

/-- 橋接（本檔唯一的結構歸納；逐 case rfl 級）：`U` 的累積走行 = Core 的 `run`。 -/
theorem U_runOut (c : ℕ) (w : List ℕ) : U.runOut c w = run c w := by
  induction w generalizing c with
  | nil => rfl
  | cons b bs ih => rw [SubTransducer.runOut_cons, run_cons, ih]; rfl

/-- 有效狀態空間 {0,1,2}：進位不變量的 re-export（`run_carry_lt_three`）。 -/
theorem U_state_lt_three {c : ℕ} {w : List ℕ} (hc : c < 3) (hw : ∀ b ∈ w, b < 2) :
    (U.runOut c w).1 < 3 := by
  rw [U_runOut]
  exact run_carry_lt_three hc hw

/-- final output 長度 ≤ 2（進位 < 3 之下）。 -/
theorem U_finalOut_len {c : ℕ} (hc : c < 3) : (U.finalOut c).length ≤ 2 := by
  interval_cases c <;> simp

/-! ## §B0.6 Acceptance：soundness 全部 re-export -/

/-- `U` 的完整輸出恰為 Core 的 `transduce`（`transduce_def` 級改寫）。 -/
theorem U_output_eq_transduce (x : ℕ) : U.output (Nat.digits 2 x) = transduce x := by
  unfold SubTransducer.output
  rw [U_runOut, transduce_def]
  rfl

/-- **soundness（re-export `ofDigits_transduce`）**：輸出值恰為 `3x + 1`。 -/
theorem ofDigits_U_output (x : ℕ) :
    Nat.ofDigits 2 (U.output (Nat.digits 2 x)) = 3 * x + 1 := by
  rw [U_output_eq_transduce]
  exact ofDigits_transduce x

/-- **分裂形（re-export `transduce_split`）**：輸出恰為「`v₂(3x+1)` 個前綴 0」++
消去後的串。 -/
theorem U_output_split (x : ℕ) :
    U.output (Nat.digits 2 x)
      = List.replicate (padicValNat 2 (3 * x + 1)) 0
          ++ (U.output (Nat.digits 2 x)).dropWhile (· = 0) := by
  rw [U_output_eq_transduce]
  exact transduce_split x

/-- 加速（canonical）輸出：K 前導零由 wrapper 收掉（Q2 選項 (a)）。 -/
def Uacc (w : List ℕ) : List ℕ := (U.output w).dropWhile (· = 0)

/-- **加速語義（re-export `Todd_eq_dropWhile`）**：加速輸出的值恰為 `T_o(x)`。 -/
theorem ofDigits_Uacc (x : ℕ) : Nat.ofDigits 2 (Uacc (Nat.digits 2 x)) = Todd x := by
  unfold Uacc
  rw [U_output_eq_transduce]
  exact Todd_eq_dropWhile x

/-- **加速輸出的結構形（re-export `digits_Todd_eq_drop`）**：恰為 `Todd x` 的
二進位展開。 -/
theorem Uacc_digits (x : ℕ) : Uacc (Nat.digits 2 x) = Nat.digits 2 (Todd x) := by
  unfold Uacc
  rw [U_output_eq_transduce, dropWhile_eq_drop]
  exact (digits_Todd_eq_drop x).symm

/-! ## §B0.7 Closure 與排名 domain -/

/-- `T_o` 的值恆為奇數（Core `not_two_dvd_ofDigits_dropWhile` + `Todd_eq_dropWhile`
的包裝；`≠ 0` 由 `2^{v₂} ∣ 3x+1` 的整除性給出）。 -/
theorem Todd_odd (x : ℕ) : Todd x % 2 = 1 := by
  have hdvd : 2 ^ padicValNat 2 (3 * x + 1) ∣ 3 * x + 1 := pow_padicValNat_dvd
  have hpos : 0 < Todd x := by
    unfold Todd
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (pow_pos (by norm_num) _)
  have h1 : Nat.ofDigits 2 ((transduce x).dropWhile (· = 0)) = Todd x := Todd_eq_dropWhile x
  have hne : Nat.ofDigits 2 ((transduce x).dropWhile (· = 0)) ≠ 0 := by
    rw [h1]; omega
  have hodd := not_two_dvd_ofDigits_dropWhile (transduce x) (transduce_digits_lt_two x) hne
  rw [h1] at hodd
  omega

/-- 語言層語義（最強形）：對 `w ∈ L`，加速輸出恰為 `Todd` 值的 canonical 展開。 -/
theorem Uacc_eq_digits_Todd {w : List ℕ} (h : IsCanonicalOdd w) :
    Uacc w = Nat.digits 2 (Todd (Nat.ofDigits 2 w)) := by
  conv_lhs => rw [← digits_ofDigits_of_canonical h]
  exact Uacc_digits _

/-- 語言層語義（數值形）：`U` 的加速輸出在 `L` 上實現 `T_o`。 -/
theorem ofDigits_Uacc_mem {w : List ℕ} (h : IsCanonicalOdd w) :
    Nat.ofDigits 2 (Uacc w) = Todd (Nat.ofDigits 2 w) := by
  rw [Uacc_eq_digits_Todd h, Nat.ofDigits_digits]

/-- **Closure（B0 主定理）**：`w ∈ L ⟹ Uacc w ∈ L`。對全體 `L` 成立，
不需排除 `[1]`（Q1：`[1] ↦ [1]` 是 Todd 不動點的落點）。 -/
theorem isCanonicalOdd_Uacc {w : List ℕ} (h : IsCanonicalOdd w) :
    IsCanonicalOdd (Uacc w) := by
  rw [Uacc_eq_digits_Todd h]
  exact isCanonicalOdd_digits (Todd_odd _)

private lemma digits_two_one : Nat.digits 2 1 = [1] := by
  rw [Nat.digits_def' (by norm_num : 1 < 2) one_pos]
  simp

/-- 落點示例：`Uacc [1] = [1]`（`x = 1` 是 `T_o` 的不動點）。 -/
theorem Uacc_one : Uacc [1] = [1] := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : Todd 1 = 1 := by
    unfold Todd
    rw [show 3 * 1 + 1 = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    norm_num
  calc Uacc [1] = Uacc (Nat.digits 2 1) := by rw [digits_two_one]
    _ = Nat.digits 2 (Todd 1) := Uacc_digits 1
    _ = [1] := by rw [hT, digits_two_one]

/-- 排名 domain（Q1）：語言不排除 `[1]`；排除 1 是 no-go 量詞的條款。
B0 自身的定理都不需要此條款；此定義是 B1 對接用的 hook。 -/
def RankingDomain (w : List ℕ) : Prop := IsCanonicalOdd w ∧ w ≠ [1]

/-- domain 條款與 no-go 量詞 `1 < x` 的等價（在 `L` 上）。 -/
theorem rankingDomain_iff {w : List ℕ} (h : IsCanonicalOdd w) :
    w ≠ [1] ↔ 1 < Nat.ofDigits 2 w := by
  have hodd := ofDigits_odd h
  constructor
  · intro hw
    rcases Nat.lt_or_ge 1 (Nat.ofDigits 2 w) with h1 | h1
    · exact h1
    · exfalso
      apply hw
      have hv : Nat.ofDigits 2 w = 1 := by omega
      have := digits_ofDigits_of_canonical h
      rw [hv, digits_two_one] at this
      exact this.symm
  · intro h1 hw
    subst hw
    simp [Nat.ofDigits] at h1

/-! ## §B0.V 數據驗證（全部應輸出 `true`） -/

section Verification

private def words : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [0 :: w, 1 :: w])

-- 橋接：U.output = transduce（x < 300）
#eval (List.range 300).all fun x => U.output (Nat.digits 2 x) == transduce x

-- 加速語義：Uacc (digits (2k+1)) = digits (Todd (2k+1))（k < 200）
#eval (List.range 200).all fun k =>
  Uacc (Nat.digits 2 (2 * k + 1)) == Nat.digits 2 (Todd (2 * k + 1))

-- closure：長度 ≤ 8 的全體 canonical odd words 經 Uacc 後仍 canonical odd
#eval ((List.range 9).flatMap words).all fun w =>
  !decide (IsCanonicalOdd w) || decide (IsCanonicalOdd (Uacc w))

-- closure 與 DFA 層一致（抽測：奇數的位元串）
#eval (List.range 200).all fun k =>
  decide (oddDFA.eval (Uacc (Nat.digits 2 (2 * k + 1))) = .acc)

-- 落點：Uacc [1] = [1]；Todd 奇性（x < 300）
#eval Uacc [1] == [1]
#eval (List.range 300).all fun x => Todd x % 2 == 1

-- 有界性：每步輸出恰一位（c < 3, b < 2）；finalOut 長度 ≤ 2（c < 3）
#eval (List.range 3).all fun c => (List.range 2).all fun b => (U.out c b).length == 1
#eval (List.range 3).all fun c => (U.finalOut c).length ≤ 2

-- 排名 domain 等價：w ≠ [1] ↔ 1 < 值（長度 ≤ 8 的 canonical odd words）
#eval ((List.range 9).flatMap words).all fun w =>
  !decide (IsCanonicalOdd w) ||
    (decide (w ≠ [1]) == decide (1 < Nat.ofDigits 2 w))

end Verification

end CollatzFST.ProjectB
