/-
# 3x+1 FST 第四批：Level 1 相位擴充（Truncation）（**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_Monoid.lean`。

## 重要技術註記（請對方確認）

1. **Lemma 6 的計數慣例有 off-by-one 要釐清。**「進入 S 之前停留在 K 所經歷的
   轉移步數」若解讀為 **K→K 轉移步數**（不含觸發 K→S 的那一步），則精確等於
   v₂（本檔 `kStay_eq_padicValNat`）。但若解讀為「起始相位為 K 的步數」——
   **這正是 12 維向量 Σ_{q,b} E^K_{q,b} 的總和**——則等於 **v₂ + 1**
   （`sum_EK_eq`；多出的 1 是觸發邊界那一步：它的起始相位仍是 K）。
   兩個量都已形式化；規格行文採前者，佔用特徵天然給後者，組裝時需自覺換算。

2. **「對於任意奇數 x」的限定不必要**——Lemma 6 對所有 x 成立
   （x 偶時首步即輸出 1、立刻進入 S，兩側皆 0）。敘述不帶奇偶假設。

3. **兩個哨兵零在此不可省**：v₂ 可以超過 |digits x|（例 x = 5：v₂(16) = 4 >
   3 = 位元數），K 相位的停留會延伸進哨兵區。哨兵保證（i）末進位歸零
   （`extRun_carry`，計算封閉）且（ii）機器必然進入 S（`final_phase_S`）。
   v₂ ≤ |digits x| + 1 < |extIn x| 由 `leadingZeros_lt_length` 保證。

## 結構

* §19 相位機定義：`Phase`（K/S）、`phaseStep`、`stepP`、`runP`、`microTraceP`、
  `occP`／`occVecP`（12 維）。初始狀態 (1, K) 為定義（`extRunP`）。
* §20 相位基礎：投影回 Level 0（`runP_fst`）、S 吸收（`runP_S`、`microTraceP_S`）、
  **K 刻畫**（`runP_K_iff`：仍在 K ⟺ 目前輸出全為 0）——相位語義的錨點。
* §21 Lemma 6：`leadingZeros_eq_padicValNat`（一般化：位元串前導零 = 其值之 v₂，
  §6 機制的抽出）→ `leadingZeros_extOut` → `kStay_eq_padicValNat`。
* §22 佔用特徵：`occ_phase_split`（12 = 6 + 6：Level 0 每格計數被兩相位精確劃分）、
  `sum_EK_eq`（Σ E^K = v₂ + 1）、`occVecP` 十二元組。
-/
import Lean4RealConstruction.Core.Collatz_FST_Monoid
import Mathlib.Data.List.TakeWhile

namespace CollatzFST

/-! ## §19 Level 1 相位擴充狀態空間 -/

/-- 截斷相位：K = 將被尾零刪除；S = 已存活（單向吸收）。 -/
inductive Phase | K | S
  deriving DecidableEq, Repr

/-- 相位轉移：完全由當前相位與本步輸出 d 決定。 -/
def phaseStep (P : Phase) (d : ℕ) : Phase :=
  match P with
  | .S => .S
  | .K => if d = 0 then .K else .S

/-- Level 1 聯合轉移 `T₁((c, P), b) = (c', P')`。 -/
def stepP (s : ℕ × Phase) (b : ℕ) : ℕ × Phase :=
  (nextCarry s.1 b, phaseStep s.2 (outBit s.1 b))

/-- 讀完字串後的 Level 1 終態。 -/
def runP : (ℕ × Phase) → List ℕ → ℕ × Phase
  | s, [] => s
  | s, b :: bs => runP (stepP s b) bs

@[simp] lemma runP_nil (s : ℕ × Phase) : runP s [] = s := rfl
lemma runP_cons (s : ℕ × Phase) (b : ℕ) (bs : List ℕ) :
    runP s (b :: bs) = runP (stepP s b) bs := rfl

/-- Level 1 微觀轉移軌跡：每步記下 `(c, P, b)` 三元組。 -/
def microTraceP : (ℕ × Phase) → List ℕ → List (ℕ × Phase × ℕ)
  | _, [] => []
  | s, b :: bs => (s.1, s.2, b) :: microTraceP (stepP s b) bs

/-- Level 1 佔用計數 `E^P_{q,b}`。 -/
def occP (s : ℕ × Phase) (w : List ℕ) (p : ℕ × Phase × ℕ) : ℕ := (microTraceP s w).count p

/-- 哨兵擴充輸入與其輸出（延續第二批 Lemma 4 的設定）。 -/
def extIn (x : ℕ) : List ℕ := Nat.digits 2 x ++ [0, 0]
def extOut (x : ℕ) : List ℕ := (run 1 (extIn x)).2

/-- 規格的初始狀態 (c₀, P₀) = (1, K)：整條 Level 1 軌跡的入口。 -/
def extRunP (x : ℕ) : ℕ × Phase := runP (1, Phase.K) (extIn x)

def leadingZeros (l : List ℕ) : ℕ := (l.takeWhile (· = 0)).length

/-- 規格要求的 12 維向量
`(E^K_{0,0}, E^K_{0,1}, …, E^K_{2,1}, E^S_{0,0}, …, E^S_{2,1})`。 -/
def occVecP (x : ℕ) : (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  let f := occP (1, Phase.K) (extIn x)
  ((f (0, .K, 0), f (0, .K, 1), f (1, .K, 0), f (1, .K, 1), f (2, .K, 0), f (2, .K, 1)),
   (f (0, .S, 0), f (0, .S, 1), f (1, .S, 0), f (1, .S, 1), f (2, .S, 0), f (2, .S, 1)))

/-! ## §20 相位基礎引理 -/

/-- 進位分量與相位無關（Level 1 投影回 Level 0）。 -/
theorem runP_fst (c : ℕ) (P : Phase) (w : List ℕ) :
    (runP (c, P) w).1 = runCarry w c := by
  induction w generalizing c P with
  | nil => rfl
  | cons b bs ih => rw [runP_cons]; exact ih (nextCarry c b) _

/-- S 為單向吸收態（終態版）。 -/
theorem runP_S (c : ℕ) (w : List ℕ) : (runP (c, Phase.S) w).2 = Phase.S := by
  induction w generalizing c with
  | nil => rfl
  | cons b bs ih => rw [runP_cons]; exact ih (nextCarry c b)

/-- S 為單向吸收態（軌跡版）：從 S 出發的所有微觀轉移相位皆 S。 -/
theorem microTraceP_S (c : ℕ) (w : List ℕ) :
    ∀ t ∈ microTraceP (c, Phase.S) w, t.2.1 = Phase.S := by
  induction w generalizing c with
  | nil => intro t ht; cases ht
  | cons b bs ih =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · rfl
      · exact ih (nextCarry c b) t ht'

/-- **相位語義的錨點**：讀完 w 仍在 K ⟺ 目前為止的輸出全為 0。 -/
theorem runP_K_iff (c : ℕ) (w : List ℕ) :
    (runP (c, Phase.K) w).2 = Phase.K ↔ ∀ d ∈ (run c w).2, d = 0 := by
  induction w generalizing c with
  | nil => simp
  | cons b bs ih =>
      rw [runP_cons, run_cons_snd]
      by_cases hd : outBit c b = 0
      · have hstep : stepP (c, Phase.K) b = (nextCarry c b, Phase.K) := by
          unfold stepP phaseStep; rw [hd]; rfl
        rw [hstep, ih]
        constructor
        · intro h d hdm
          rcases List.mem_cons.mp hdm with rfl | hdm'
          · exact hd
          · exact h d hdm'
        · intro h d hdm; exact h d (List.mem_cons_of_mem _ hdm)
      · have hstep : stepP (c, Phase.K) b = (nextCarry c b, Phase.S) := by
          unfold stepP phaseStep
          rw [if_neg hd]
        rw [hstep, runP_S]
        constructor
        · intro h; exact absurd h (by intro hc; cases hc)
        · intro h; exact absurd (h _ (List.mem_cons_self ..)) hd

/-! ## §21 Lemma 6：v₂ 與 Killed 相位的等價性 -/

theorem extIn_bits (x : ℕ) : ∀ b ∈ extIn x, b < 2 := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact Nat.digits_lt_base (by norm_num) h
  · have : b = 0 := by
      rcases List.mem_cons.mp h with rfl | h2
      · rfl
      · rcases List.mem_cons.mp h2 with rfl | h3
        · rfl
        · cases h3
    omega

theorem ofDigits_extIn (x : ℕ) : Nat.ofDigits 2 (extIn x) = x := by
  unfold extIn
  rw [show ([0, 0] : List ℕ) = List.replicate 2 0 from rfl,
    Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

/-- 哨兵保證計算封閉：末進位歸零（第二批 Lemma 4 的應用）。 -/
theorem extRun_carry (x : ℕ) : (run 1 (extIn x)).1 = 0 := by
  unfold extIn
  rw [run_append_sentinel 1 (Nat.digits 2 x)
    (run_carry_lt_three (by norm_num) (fun b hb => Nat.digits_lt_base (by norm_num) hb))]

/-- soundness：extOut 的值恰為 3x+1（無需再拆最終進位）。 -/
theorem ofDigits_extOut (x : ℕ) : Nat.ofDigits 2 (extOut x) = 3 * x + 1 := by
  have h := ofDigits_run 1 (extIn x)
  rw [extRun_carry, Nat.mul_zero, Nat.add_zero, ofDigits_extIn] at h
  exact h

theorem extOut_length (x : ℕ) : (extOut x).length = (Nat.digits 2 x).length + 2 := by
  unfold extOut extIn
  rw [length_run, List.length_append]
  rfl

/-- 一般化引理（§6 機制抽出）：位元串的前導零數 = 其值之 v₂。 -/
theorem leadingZeros_eq_padicValNat {l : List ℕ} (hb : ∀ d ∈ l, d < 2)
    (h0 : Nat.ofDigits 2 l ≠ 0) :
    leadingZeros l = padicValNat 2 (Nat.ofDigits 2 l) := by
  have hpow := ofDigits_eq_pow_mul l
  have hm : Nat.ofDigits 2 (l.dropWhile (· = 0)) ≠ 0 := by
    intro hc; rw [hc, Nat.mul_zero] at hpow; exact h0 hpow
  have hodd := not_two_dvd_ofDigits_dropWhile l hb hm
  rw [hpow, padicValNat_two_pow_mul hm hodd]
  rfl

/-- **Lemma 6（前導零形式）**：v₂(3x+1) = extOut 的前導零數。
（規格限定奇數 x，實則對所有 x 成立。） -/
theorem leadingZeros_extOut (x : ℕ) :
    leadingZeros (extOut x) = padicValNat 2 (3 * x + 1) := by
  have h := leadingZeros_eq_padicValNat (l := extOut x)
    (fun d hd => run_out_lt_two d hd) (by rw [ofDigits_extOut]; omega)
  rw [ofDigits_extOut] at h
  exact h

/-- v₂ 嚴格小於擴充字串長度（K 停留必在字串內結束；哨兵在此發揮作用）。 -/
theorem leadingZeros_lt_length (x : ℕ) : leadingZeros (extOut x) < (extOut x).length := by
  have hle : (extOut x).takeWhile (· = 0) ≠ extOut x := by
    intro heq
    have hall : ∀ d ∈ extOut x, d = 0 := by
      intro d hd
      have := List.mem_takeWhile_imp (l := extOut x) (p := (· = 0)) (heq ▸ hd)
      simpa using this
    have h0 : Nat.ofDigits 2 (extOut x) = 0 := by
      have : extOut x = List.replicate (extOut x).length 0 := by
        rw [List.eq_replicate_iff]
        exact ⟨rfl, hall⟩
      rw [this, ofDigits_replicate_zero]
    rw [ofDigits_extOut] at h0
    omega
  have hlen := (List.takeWhile_prefix (l := extOut x) (fun d => decide (d = 0))).length_le
  rcases lt_or_eq_of_le hlen with h | h
  · exact h
  · exact absurd ((List.takeWhile_prefix _).eq_of_length h) hle

/-- **Lemma 6（步數形式）**：K→K 轉移步數 = v₂(3x+1)。
（不含觸發 K→S 的那一步；起始相位為 K 的總步數見 `sum_EK_eq`。） -/
def kStay (x : ℕ) : ℕ :=
  (microTraceP (1, Phase.K) (extIn x)).countP
    (fun t => t.2.1 == Phase.K && phaseStep t.2.1 (outBit t.1 t.2.2) == Phase.K)

/-- 起始於 K 的步數 = min（前導零數 + 1, 字串長度）。
（K 相位序列因吸收性必為 K…KS…S 形，故計數即 takeWhile 長度。） -/
theorem countP_startK (c : ℕ) (w : List ℕ) :
    (microTraceP (c, Phase.K) w).countP (fun t => t.2.1 == Phase.K)
      = min (leadingZeros (run c w).2 + 1) w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons b bs ih =>
      show List.countP _ ((c, Phase.K, b) :: microTraceP (stepP (c, Phase.K) b) bs) = _
      rw [List.countP_cons]
      by_cases hd : outBit c b = 0
      · have hstep : stepP (c, Phase.K) b = (nextCarry c b, Phase.K) := by
          unfold stepP phaseStep; rw [hd]; rfl
        rw [hstep, ih]
        have hlz : leadingZeros (run c (b :: bs)).2
            = leadingZeros (run (nextCarry c b) bs).2 + 1 := by
          unfold leadingZeros
          rw [run_cons_snd, List.takeWhile_cons, if_pos (by simpa using hd), List.length_cons]
        rw [hlz, List.length_cons]
        simp
      · have hstep : stepP (c, Phase.K) b = (nextCarry c b, Phase.S) := by
          unfold stepP phaseStep; rw [if_neg hd]
        have hzero : (microTraceP (stepP (c, Phase.K) b) bs).countP
            (fun t => t.2.1 == Phase.K) = 0 := by
          rw [hstep, List.countP_eq_zero]
          intro t ht
          rw [microTraceP_S (nextCarry c b) bs t ht]
          decide
        rw [hzero]
        have hlz : leadingZeros (run c (b :: bs)).2 = 0 := by
          unfold leadingZeros
          rw [run_cons_snd, List.takeWhile_cons, if_neg (by simpa using hd)]
          rfl
        rw [hlz, List.length_cons]
        simp

/-- K→K 步數 = 前導零數（起始 K 步數扣掉觸發那一步）。 -/
theorem countP_stayK (c : ℕ) (w : List ℕ) :
    (microTraceP (c, Phase.K) w).countP
      (fun t => t.2.1 == Phase.K && phaseStep t.2.1 (outBit t.1 t.2.2) == Phase.K)
      = leadingZeros (run c w).2 := by
  induction w generalizing c with
  | nil => rfl
  | cons b bs ih =>
      show List.countP _ ((c, Phase.K, b) :: microTraceP (stepP (c, Phase.K) b) bs) = _
      rw [List.countP_cons]
      by_cases hd : outBit c b = 0
      · have hstep : stepP (c, Phase.K) b = (nextCarry c b, Phase.K) := by
          unfold stepP phaseStep; rw [hd]; rfl
        have hcond : ((Phase.K == Phase.K) && (phaseStep Phase.K (outBit c b) == Phase.K)) = true := by
          unfold phaseStep; rw [hd]; rfl
        rw [hstep, ih, if_pos hcond]
        have hlz : leadingZeros (run c (b :: bs)).2
            = leadingZeros (run (nextCarry c b) bs).2 + 1 := by
          unfold leadingZeros
          rw [run_cons_snd, List.takeWhile_cons, if_pos (by simpa using hd), List.length_cons]
        rw [hlz]
      · have hstep : stepP (c, Phase.K) b = (nextCarry c b, Phase.S) := by
          unfold stepP phaseStep; rw [if_neg hd]
        have hcond : ¬ (((Phase.K == Phase.K) && (phaseStep Phase.K (outBit c b) == Phase.K)) = true) := by
          unfold phaseStep; rw [if_neg hd]; decide
        have hzero : (microTraceP (stepP (c, Phase.K) b) bs).countP
            (fun t => t.2.1 == Phase.K && phaseStep t.2.1 (outBit t.1 t.2.2) == Phase.K) = 0 := by
          rw [hstep, List.countP_eq_zero]
          intro t ht
          rw [Bool.and_eq_true]
          rintro ⟨h1, -⟩
          rw [microTraceP_S (nextCarry c b) bs t ht] at h1
          exact absurd h1 (by decide)
        rw [hzero, if_neg hcond]
        have hlz : leadingZeros (run c (b :: bs)).2 = 0 := by
          unfold leadingZeros
          rw [run_cons_snd, List.takeWhile_cons, if_neg (by simpa using hd)]
          rfl
        rw [hlz]

/-- **Lemma 6（主定理）**：kStay x = v₂(3x+1)。 -/
theorem kStay_eq_padicValNat (x : ℕ) : kStay x = padicValNat 2 (3 * x + 1) := by
  unfold kStay
  rw [countP_stayK]
  exact leadingZeros_extOut x

/-- 哨兵保證機器必然進入 S（截斷邊界必在字串內觸發）。 -/
theorem final_phase_S (x : ℕ) : (extRunP x).2 = Phase.S := by
  unfold extRunP
  rcases h : (runP (1, Phase.K) (extIn x)).2 with _ | _
  · exfalso
    have hall := (runP_K_iff 1 (extIn x)).mp h
    have h0 : Nat.ofDigits 2 (extOut x) = 0 := by
      have : extOut x = List.replicate (extOut x).length 0 := by
        rw [List.eq_replicate_iff]
        exact ⟨rfl, fun d hd => hall d hd⟩
      rw [this, ofDigits_replicate_zero]
    rw [ofDigits_extOut] at h0
    omega
  · rfl

/-! ## §22 佔用特徵：12 = 6 + 6 與 Σ E^K -/

/-- **切分定理**：Level 0 的每個計數被 K/S 兩相位精確劃分（無遺漏、無重複）。
這是「12 維向量細分 6 維向量」的形式內容。 -/
theorem occ_phase_split (w : List ℕ) (c : ℕ) (P : Phase) (q b : ℕ) :
    occ c w (q, b) = occP (c, P) w (q, Phase.K, b) + occP (c, P) w (q, Phase.S, b) := by
  induction w generalizing c P with
  | nil => rfl
  | cons b' bs ih =>
      have hrec := ih (nextCarry c b') (phaseStep P (outBit c b'))
      unfold occ occP at hrec ⊢
      show List.count _ ((c, b') :: microTrace (nextCarry c b') bs) = _
      have hT : microTraceP (c, P) (b' :: bs)
          = (c, P, b') :: microTraceP (nextCarry c b', phaseStep P (outBit c b')) bs := rfl
      rw [hT, List.count_cons, List.count_cons, List.count_cons, hrec]
      by_cases hqb : ((c, b') : ℕ × ℕ) = (q, b)
      · rw [Prod.mk.injEq] at hqb
        obtain ⟨rfl, rfl⟩ := hqb
        rcases P with _ | _
        · rw [if_pos (beq_self_eq_true _), if_pos (beq_self_eq_true _),
            if_neg (by intro h; rw [beq_iff_eq, Prod.mk.injEq, Prod.mk.injEq] at h
                       exact absurd h.2.1 (by decide))]
          omega
        · rw [if_pos (beq_self_eq_true _),
            if_neg (by intro h; rw [beq_iff_eq, Prod.mk.injEq, Prod.mk.injEq] at h
                       exact absurd h.2.1 (by decide)),
            if_pos (beq_self_eq_true _)]
          omega
      · have hne : ((c, b') : ℕ × ℕ) ≠ (q, b) := hqb
        rw [if_neg (by intro h; exact hne (beq_iff_eq.mp h))]
        have hK : ¬ (((c, P, b') : ℕ × Phase × ℕ) == (q, Phase.K, b)) = true := by
          intro h
          rw [beq_iff_eq, Prod.mk.injEq, Prod.mk.injEq] at h
          exact hne (by rw [Prod.mk.injEq]; exact ⟨h.1, h.2.2⟩)
        have hS : ¬ (((c, P, b') : ℕ × Phase × ℕ) == (q, Phase.S, b)) = true := by
          intro h
          rw [beq_iff_eq, Prod.mk.injEq, Prod.mk.injEq] at h
          exact hne (by rw [Prod.mk.injEq]; exact ⟨h.1, h.2.2⟩)
        rw [if_neg hK, if_neg hS]
        omega

/-- **Σ E^K = v₂ + 1**（off-by-one 的形式化：多出的 1 是觸發邊界那一步）。 -/
theorem sum_EK_eq (x : ℕ) :
    (microTraceP (1, Phase.K) (extIn x)).countP (fun t => t.2.1 == Phase.K)
      = padicValNat 2 (3 * x + 1) + 1 := by
  rw [countP_startK]
  have h1 : leadingZeros (run 1 (extIn x)).2 = padicValNat 2 (3 * x + 1) :=
    leadingZeros_extOut x
  have hlt := leadingZeros_lt_length x
  rw [leadingZeros_extOut] at hlt
  have hlen : (extOut x).length = (extIn x).length := length_run 1 (extIn x)
  rw [h1]
  unfold extOut at hlt hlen
  omega



/-! ## §22b 代數約束恆等式（分量形式；LP 的第一組線性約束）

對方 Lemma 6 Update 的恆等式寫在**六個分量之和**上，而 `sum_EK_eq` 證的是
trace 上的 countP。兩者相等需要**狀態空間有界性**這座橋（trace 的每個 (c,b)
都落在 {0,1,2}×{0,1}，否則分量和會漏數）——`microTraceP_bounds` +
`countP_phase_eq_sum`。以下三條即為未來 LP／勢能函數可直接引用的線性約束：

* `sum_EK_components`：Σ E^K = v₂ + 1（含 −1 補償的根源）
* `sum_ES_components`：Σ E^S + (v₂ + 1) = |digits x| + 2（加法形式，避 ℕ 截斷減法）
* 兩者相加即 12 分量總和 = |extIn x|（由 `countP_K_add_S` 承載） -/

/-- trace 有界性：初始進位 <3、輸入位元 <2 ⇒ 每筆微觀轉移的 (c,b) 落在狀態空間內。 -/
theorem microTraceP_bounds (c : ℕ) (P : Phase) (w : List ℕ) (hc : c < 3)
    (hw : ∀ b ∈ w, b < 2) :
    ∀ t ∈ microTraceP (c, P) w, t.1 < 3 ∧ t.2.2 < 2 := by
  induction w generalizing c P with
  | nil => intro t ht; cases ht
  | cons b bs ih =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨hc, hw b (List.mem_cons_self ..)⟩
      · exact ih (nextCarry c b) _ (nextCarry_lt_three hc (hw b (List.mem_cons_self ..)))
          (fun y hy => hw y (List.mem_cons_of_mem _ hy)) t ht'

/-- 增量劃分：一筆狀態空間內的轉移，在六個 key 上恰好命中一次（若相位相符）。 -/
theorem indicator_partition {q b : ℕ} (hq : q < 3) (hb : b < 2) (P P₀ : Phase) :
    (if ((q, P, b) : ℕ × Phase × ℕ) == (0, P₀, 0) then 1 else 0)
      + (if ((q, P, b) : ℕ × Phase × ℕ) == (0, P₀, 1) then 1 else 0)
      + (if ((q, P, b) : ℕ × Phase × ℕ) == (1, P₀, 0) then 1 else 0)
      + (if ((q, P, b) : ℕ × Phase × ℕ) == (1, P₀, 1) then 1 else 0)
      + (if ((q, P, b) : ℕ × Phase × ℕ) == (2, P₀, 0) then 1 else 0)
      + (if ((q, P, b) : ℕ × Phase × ℕ) == (2, P₀, 1) then 1 else 0)
      = (if P == P₀ then 1 else 0) := by
  rcases P <;> rcases P₀ <;> interval_cases q <;> interval_cases b <;> decide

/-- countP（按相位）＝ 六分量之和（需狀態空間有界性）。 -/
theorem countP_phase_eq_sum (P₀ : Phase) :
    ∀ (L : List (ℕ × Phase × ℕ)), (∀ t ∈ L, t.1 < 3 ∧ t.2.2 < 2) →
    L.countP (fun t => t.2.1 == P₀)
      = L.count (0, P₀, 0) + L.count (0, P₀, 1) + L.count (1, P₀, 0)
        + L.count (1, P₀, 1) + L.count (2, P₀, 0) + L.count (2, P₀, 1) := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons t ts ih =>
      intro hL
      have ih' := ih (fun u hu => hL u (List.mem_cons_of_mem _ hu))
      obtain ⟨q, P, b⟩ := t
      obtain ⟨hq, hb⟩ := hL (q, P, b) (List.mem_cons_self ..)
      have hq' : q < 3 := hq
      have hb' : b < 2 := hb
      have hstep : List.countP (fun t => t.2.1 == P₀) ((q, P, b) :: ts)
          = List.countP (fun t => t.2.1 == P₀) ts + (if P == P₀ then 1 else 0) := by
        rw [List.countP_cons]
      rw [hstep, ih', List.count_cons, List.count_cons, List.count_cons,
        List.count_cons, List.count_cons, List.count_cons]
      have hind := indicator_partition hq' hb' P P₀
      omega
/-- K/S 兩相位計數合為總步數（Phase 只有兩個構造子）。 -/
theorem countP_K_add_S (L : List (ℕ × Phase × ℕ)) :
    L.countP (fun t => t.2.1 == Phase.K) + L.countP (fun t => t.2.1 == Phase.S)
      = L.length := by
  induction L with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨q, P, b⟩ := t
      rcases P with _ | _
      · have h1 : List.countP (fun t => t.2.1 == Phase.K) ((q, Phase.K, b) :: ts)
            = List.countP (fun t => t.2.1 == Phase.K) ts + 1 := by rw [List.countP_cons]; rfl
        have h2 : List.countP (fun t => t.2.1 == Phase.S) ((q, Phase.K, b) :: ts)
            = List.countP (fun t => t.2.1 == Phase.S) ts + 0 := by rw [List.countP_cons]; rfl
        rw [h1, h2, List.length_cons]
        omega
      · have h1 : List.countP (fun t => t.2.1 == Phase.K) ((q, Phase.S, b) :: ts)
            = List.countP (fun t => t.2.1 == Phase.K) ts + 0 := by rw [List.countP_cons]; rfl
        have h2 : List.countP (fun t => t.2.1 == Phase.S) ((q, Phase.S, b) :: ts)
            = List.countP (fun t => t.2.1 == Phase.S) ts + 1 := by rw [List.countP_cons]; rfl
        rw [h1, h2, List.length_cons]
        omega

theorem extIn_length (x : ℕ) : (extIn x).length = (Nat.digits 2 x).length + 2 := by
  unfold extIn; rw [List.length_append]; rfl

theorem microTraceP_length (s : ℕ × Phase) (w : List ℕ) :
    (microTraceP s w).length = w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons b bs ih =>
      show (microTraceP (stepP s b) bs).length + 1 = bs.length + 1
      rw [ih]

private theorem trace_bounds (x : ℕ) :
    ∀ t ∈ microTraceP (1, Phase.K) (extIn x), t.1 < 3 ∧ t.2.2 < 2 :=
  microTraceP_bounds 1 Phase.K (extIn x) (by norm_num) (extIn_bits x)

/-- **代數約束恆等式（分量形式）**：Σ_{q,b} E^K_{q,b} = v₂(3x+1) + 1。 -/
theorem sum_EK_components (x : ℕ) :
    occP (1, Phase.K) (extIn x) (0, Phase.K, 0) + occP (1, Phase.K) (extIn x) (0, Phase.K, 1)
      + occP (1, Phase.K) (extIn x) (1, Phase.K, 0) + occP (1, Phase.K) (extIn x) (1, Phase.K, 1)
      + occP (1, Phase.K) (extIn x) (2, Phase.K, 0) + occP (1, Phase.K) (extIn x) (2, Phase.K, 1)
      = padicValNat 2 (3 * x + 1) + 1 := by
  have h := countP_phase_eq_sum Phase.K (microTraceP (1, Phase.K) (extIn x)) (trace_bounds x)
  unfold occP
  rw [← h]
  exact sum_EK_eq x

/-- **代數約束恆等式（S 側，加法形式避免 ℕ 截斷減法）**：
Σ_{q,b} E^S_{q,b} + (v₂ + 1) = |digits x| + 2。 -/
theorem sum_ES_components (x : ℕ) :
    occP (1, Phase.K) (extIn x) (0, Phase.S, 0) + occP (1, Phase.K) (extIn x) (0, Phase.S, 1)
      + occP (1, Phase.K) (extIn x) (1, Phase.S, 0) + occP (1, Phase.K) (extIn x) (1, Phase.S, 1)
      + occP (1, Phase.K) (extIn x) (2, Phase.S, 0) + occP (1, Phase.K) (extIn x) (2, Phase.S, 1)
      + (padicValNat 2 (3 * x + 1) + 1) = (Nat.digits 2 x).length + 2 := by
  have hS := countP_phase_eq_sum Phase.S (microTraceP (1, Phase.K) (extIn x)) (trace_bounds x)
  have hKS := countP_K_add_S (microTraceP (1, Phase.K) (extIn x))
  have hEK := sum_EK_eq x
  have hlen : (microTraceP (1, Phase.K) (extIn x)).length = (extIn x).length :=
    microTraceP_length _ _
  unfold occP
  rw [← hS]
  rw [extIn_length] at hlen
  omega

/-! ## §23 數據驗證（全部應輸出 `true`） -/

section Verification

-- Lemma 6（步數形式）：kStay = v₂，x < 200
#eval (List.range 200).all fun x => kStay x == padicValNat 2 (3 * x + 1)

-- Lemma 6（前導零形式）
#eval (List.range 200).all fun x => leadingZeros (extOut x) == padicValNat 2 (3 * x + 1)

-- Σ E^K = v₂ + 1（off-by-one）
#eval (List.range 200).all fun x =>
  (microTraceP (1, Phase.K) (extIn x)).countP (fun t => t.2.1 == Phase.K)
    == padicValNat 2 (3 * x + 1) + 1

-- 哨兵保證：終末相位必為 S、末進位歸零
#eval (List.range 200).all fun x => (extRunP x).2 == Phase.S
#eval (List.range 200).all fun x => (run 1 (extIn x)).1 == 0

-- 相位刻畫：仍在 K ⟺ 輸出全為 0
#eval (List.range 100).all fun x => (List.range 8).all fun n =>
  ((runP (1, Phase.K) ((extIn x).take n)).2 == Phase.K)
    == ((run 1 ((extIn x).take n)).2.all (· == 0))

-- 12 = 6 + 6 切分
#eval (List.range 100).all fun x => (List.range 3).all fun q => (List.range 2).all fun b =>
  occ 1 (extIn x) (q, b)
    == occP (1, Phase.K) (extIn x) (q, Phase.K, b)
        + occP (1, Phase.K) (extIn x) (q, Phase.S, b)

-- 12 維向量總和 = 擴充字串長度
#eval (List.range 100).all fun x =>
  let v := occVecP x
  let sK := v.1.1 + v.1.2.1 + v.1.2.2.1 + v.1.2.2.2.1 + v.1.2.2.2.2.1 + v.1.2.2.2.2.2
  let sS := v.2.1 + v.2.2.1 + v.2.2.2.1 + v.2.2.2.2.1 + v.2.2.2.2.2.1 + v.2.2.2.2.2.2
  sK + sS == (extIn x).length

-- 代數約束（分量形式）：Σ E^K = v₂+1；Σ E^S + (v₂+1) = |digits|+2
#eval (List.range 150).all fun x =>
  let f := occP (1, Phase.K) (extIn x)
  f (0,.K,0) + f (0,.K,1) + f (1,.K,0) + f (1,.K,1) + f (2,.K,0) + f (2,.K,1)
    == padicValNat 2 (3*x+1) + 1
#eval (List.range 150).all fun x =>
  let f := occP (1, Phase.K) (extIn x)
  f (0,.S,0) + f (0,.S,1) + f (1,.S,0) + f (1,.S,1) + f (2,.S,0) + f (2,.S,1)
    + (padicValNat 2 (3*x+1) + 1) == (Nat.digits 2 x).length + 2

-- 進位分量投影回 Level 0
#eval (List.range 100).all fun x =>
  (runP (1, Phase.K) (extIn x)).1 == runCarry (extIn x) 1

end Verification

end CollatzFST
