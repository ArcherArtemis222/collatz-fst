/-
# Project B 第一批：canonical odd language 與哨兵語言 DFA（B0-1 / B0-3）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。B0 語義層的語言半邊；
transducer 半邊見 `Collatz_FST_Transducer.lean`。

## 內容

* **§B0.1 謂詞層**：`IsCanonicalOdd`——LSB-first、位元 <2、首位（LSB）= 1（奇性）、
  末位（MSB）= 1（正規性）。與 ℕ 的往返（`isCanonicalOdd_digits` /
  `digits_ofDigits_of_canonical` / `ofDigits_odd`）皆為 mathlib digits 引理的包裝。
* **§B0.2 DFA 層**：單一 6 狀態機 `lstep`（字母表 `Option ℕ`：`some b` = 一般位元、
  `none` = 哨兵標記），兩個接受集：`oddDFA`（沿 `some` 拉回，接受 `{acc}`，
  即 canonical odd language）與 `extDFA`（接受 `{tail2}`，即 `L·⊥⊥`）。
  主定理 `mem_oddDFA_accepts_iff`。
* **§B0.3 哨兵引理**：`extInM x = (digits x).map some ++ [none, none]`
  （`extInM_unmark` 一行接回 Core 的 `extIn`）。位置事實 + 尾段唯哨兵字母可進入
  （`lstep_some_ne_tail1/2`）+ 尾段封閉無出返（`sentinel_edge₁/₂_no_cycle`，
  即「哨兵邊不在任何循環上」的 evalFrom 表述）+ 泛用 product 投影 `prodRun_snd`。

## 技術註記（設計核准紀錄 2026-08-28）

1. **標記字母表是 ROADMAP-B B0-3 原註記的修正**。未標記字母表上「哨兵零落於
   無環尾段」不可能成立：`extIn 1 = [1,0,0]` 是 `extIn 9 = [1,0,0,1,0,0]` 的前綴，
   任何識別 `L·00` 的 DFA 在讀完前者時已在接受態、讀完後者時再度接受——
   接受態位於循環上，哨兵邊與詞中段普通邊重合。修復：哨兵改讀標記字母
   `none`，尾段 `tail1/tail2` 唯 `none` 可進入，無環性變成可枚舉的封閉不變量。
   詳見 docs/ROADMAP-B.md 的 B0 完成紀錄。
2. 「邊 e 在某循環上 ⟺ 存在 head(e) ⇝ tail(e) 的路徑」——本檔以
   `evalFrom` 否定該路徑（`sentinel_edge₁_no_cycle`：`tail1 ⇝̸ acc`；
   `sentinel_edge₂_no_cycle`：`tail2 ⇝̸ tail1`），不引入圖論框架
   （trimmed graph 是 B1 的事）。product 循環的 DFA 分量仍是閉走行
   （`prodRun_snd` 投影），故此兩條對**任意**機器的 language-product 生效。
3. `acc` 與 `mid` 在一般位元上的轉移完全相同（只差當下是否接受）——
   `evalFrom_accMid` 的歸納因此可以共用，這是語言刻畫證明短的原因。
-/
import Lean4RealConstruction.Core
import Mathlib.Computability.DFA

namespace CollatzFST.ProjectB

/-! ## §B0.1 謂詞層：canonical odd words -/

/-- LSB-first canonical odd word：位元皆 <2、首位（LSB）= 1（奇性）、
末位（MSB）= 1（正規性；空串被 `head?` 條款排除）。
語言 **含 `[1]`**：排除 1 是排名問題的量詞條款，不是語言的條款（Q1，設計核准）。 -/
def IsCanonicalOdd (w : List ℕ) : Prop :=
  (∀ b ∈ w, b < 2) ∧ w.head? = some 1 ∧ w.getLast? = some 1

instance : DecidablePred IsCanonicalOdd := fun w => by
  unfold IsCanonicalOdd; infer_instance

/-- 奇數的二進位展開是 canonical odd word（mathlib digits 引理的包裝）。 -/
theorem isCanonicalOdd_digits {x : ℕ} (hx : x % 2 = 1) : IsCanonicalOdd (Nat.digits 2 x) := by
  have hx0 : x ≠ 0 := by omega
  refine ⟨fun b hb => Nat.digits_lt_base (by norm_num) hb, ?_, ?_⟩
  · rw [Nat.digits_def' (by norm_num : 1 < 2) (Nat.pos_of_ne_zero hx0)]
    simp [hx]
  · have hne : Nat.digits 2 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hx0
    rw [List.getLast?_eq_some_getLast hne]
    have h0 : (Nat.digits 2 x).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 2 hx0
    have h2 : (Nat.digits 2 x).getLast hne < 2 :=
      Nat.digits_lt_base (by norm_num) (List.getLast_mem hne)
    congr 1
    omega

/-- canonical odd word 的值為奇數。 -/
theorem ofDigits_odd {w : List ℕ} (h : IsCanonicalOdd w) : Nat.ofDigits 2 w % 2 = 1 := by
  obtain ⟨-, hh, -⟩ := h
  cases w with
  | nil => simp at hh
  | cons b t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      rw [Nat.ofDigits_cons]
      omega

/-- 往返：canonical odd word 經 `ofDigits` 後由 `digits` 精確重現
（`Nat.digits_ofDigits` 的包裝）。 -/
theorem digits_ofDigits_of_canonical {w : List ℕ} (h : IsCanonicalOdd w) :
    Nat.digits 2 (Nat.ofDigits 2 w) = w := by
  obtain ⟨hb, -, hl⟩ := h
  apply Nat.digits_ofDigits 2 (by norm_num) w hb
  intro hne
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hl
  omega

/-! ## §B0.2 DFA 層：單一 6 狀態機、兩個接受集 -/

/-- 語言 DFA 狀態：`start`（未讀）、`acc`（合法且目前以 1 結尾；oddDFA 接受態）、
`mid`（合法、目前以 0 結尾）、`tail1`/`tail2`（哨兵尾段；`tail2` 為 extDFA 接受態）、
`dead`。 -/
inductive LSt
  | start | acc | mid | tail1 | tail2 | dead
  deriving DecidableEq, Repr

/-- 統一步進。字母表 `Option ℕ`：`some b` = 一般位元（`b ≥ 2` 的垃圾字母一律 → dead），
`none` = 哨兵標記。哨兵邊只有 `acc → tail1 → tail2` 兩條（其餘 `none` 皆 → dead）。 -/
def lstep : LSt → Option ℕ → LSt
  | .start, some 1 => .acc
  | .acc,   some 1 => .acc
  | .acc,   some 0 => .mid
  | .acc,   none   => .tail1
  | .mid,   some 1 => .acc
  | .mid,   some 0 => .mid
  | .tail1, none   => .tail2
  | _,      _      => .dead

/-- 哨兵語言 DFA：接受集 `{tail2}`，目標語言 `{w.map some ++ [none, none] | w ∈ L}`
（B0 只形式化 B0-3 需要的方向；完整 iff 刻畫留待 B1 實需時補）。 -/
def extDFA : DFA (Option ℕ) LSt := ⟨lstep, .start, {.tail2}⟩

/-- canonical odd language 的 DFA：`extDFA` 沿 `some` 拉回（同一狀態型、同一步進），
接受集 `{acc}`。 -/
def oddDFA : DFA ℕ LSt := ⟨fun s b => lstep s (some b), .start, {.acc}⟩

@[simp] lemma extDFA_step_eq (s : LSt) (a : Option ℕ) : extDFA.step s a = lstep s a := rfl
@[simp] lemma oddDFA_step_eq (s : LSt) (b : ℕ) : oddDFA.step s b = lstep s (some b) := rfl

private lemma evalFrom_nil {α σ : Type*} (M : DFA α σ) (s : σ) : M.evalFrom s [] = s := rfl

private lemma evalFrom_cons {α σ : Type*} (M : DFA α σ) (s : σ) (a : α) (u : List α) :
    M.evalFrom s (a :: u) = M.evalFrom (M.step s a) u := rfl

private lemma evalFrom_append {α σ : Type*} (M : DFA α σ) (s : σ) (u v : List α) :
    M.evalFrom s (u ++ v) = M.evalFrom (M.evalFrom s u) v := by
  simp [DFA.evalFrom, List.foldl_append]

/-- 兩台 DFA 的橋：`oddDFA` 走 `w` = `extDFA` 走 `w.map some`。 -/
theorem oddDFA_evalFrom_map (s : LSt) (w : List ℕ) :
    oddDFA.evalFrom s w = extDFA.evalFrom s (w.map some) := by
  induction w generalizing s with
  | nil => rfl
  | cons b t ih => rw [List.map_cons, evalFrom_cons, evalFrom_cons, ih]; rfl

/-- 垃圾位元（`b ≥ 2`）從任何狀態一步入 dead。 -/
lemma lstep_junk (s : LSt) {b : ℕ} (hb : 2 ≤ b) : lstep s (some b) = .dead := by
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 2 := ⟨b - 2, by omega⟩
  cases s <;> rfl

@[simp] lemma lstep_dead (a : Option ℕ) : lstep .dead a = .dead := by
  rcases a with _ | (_ | _ | n) <;> rfl

@[simp] lemma lstep_tail2 (a : Option ℕ) : lstep .tail2 a = .dead := by
  rcases a with _ | (_ | _ | n) <;> rfl

lemma lstep_tail1_mem (a : Option ℕ) :
    lstep .tail1 a = .tail2 ∨ lstep .tail1 a = .dead := by
  rcases a with _ | (_ | _ | n)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

private lemma extDFA_evalFrom_dead (u : List (Option ℕ)) :
    extDFA.evalFrom .dead u = .dead := by
  induction u with
  | nil => rfl
  | cons a t ih => rw [evalFrom_cons, extDFA_step_eq, lstep_dead]; exact ih

private lemma oddDFA_evalFrom_dead (v : List ℕ) : oddDFA.evalFrom .dead v = .dead := by
  rw [oddDFA_evalFrom_map]; exact extDFA_evalFrom_dead _

/-- 歸納主引理：`acc` 與 `mid` 在一般位元上轉移相同，讀 `v` 後落在 `acc`
⟺ 位元合法且（`v` 以 1 結尾，或 `v` 為空且出發點就是 `acc`）。 -/
private lemma evalFrom_accMid :
    ∀ (v : List ℕ) (s : LSt), s = .acc ∨ s = .mid →
      (oddDFA.evalFrom s v = .acc ↔
        ((∀ b ∈ v, b < 2) ∧ (v.getLast? = some 1 ∨ (v = [] ∧ s = .acc)))) := by
  intro v
  induction v with
  | nil => rintro s (rfl | rfl) <;> simp
  | cons b t ih =>
      rintro s hs
      rw [evalFrom_cons, oddDFA_step_eq]
      rcases hs with rfl | rfl <;> rcases b with _ | _ | n
      · -- acc, 讀 0 → mid
        rw [show lstep .acc (some 0) = .mid from rfl, ih .mid (Or.inr rfl)]
        cases t with
        | nil => simp
        | cons c t' => simp [List.getLast?_cons_cons]
      · -- acc, 讀 1 → acc
        rw [show lstep .acc (some 1) = .acc from rfl, ih .acc (Or.inl rfl)]
        cases t with
        | nil => simp
        | cons c t' => simp [List.getLast?_cons_cons]
      · -- acc, 垃圾 → dead
        rw [lstep_junk _ (by omega), oddDFA_evalFrom_dead]
        refine iff_of_false (by decide) ?_
        rintro ⟨hb, -⟩
        have := hb _ (List.mem_cons_self ..)
        omega
      · -- mid, 讀 0 → mid
        rw [show lstep .mid (some 0) = .mid from rfl, ih .mid (Or.inr rfl)]
        cases t with
        | nil => simp
        | cons c t' => simp [List.getLast?_cons_cons]
      · -- mid, 讀 1 → acc
        rw [show lstep .mid (some 1) = .acc from rfl, ih .acc (Or.inl rfl)]
        cases t with
        | nil => simp
        | cons c t' => simp [List.getLast?_cons_cons]
      · -- mid, 垃圾 → dead
        rw [lstep_junk _ (by omega), oddDFA_evalFrom_dead]
        refine iff_of_false (by decide) ?_
        rintro ⟨hb, -⟩
        have := hb _ (List.mem_cons_self ..)
        omega

/-- **B0-1 主定理**：DFA 層與謂詞層一致——`oddDFA` 恰接受 canonical odd language。 -/
theorem mem_oddDFA_accepts_iff (w : List ℕ) : w ∈ oddDFA.accepts ↔ IsCanonicalOdd w := by
  rw [DFA.mem_accepts]
  show oddDFA.evalFrom .start w ∈ ({LSt.acc} : Set LSt) ↔ _
  rw [Set.mem_singleton_iff]
  cases w with
  | nil =>
      rw [evalFrom_nil]
      refine iff_of_false (by decide) ?_
      rintro ⟨-, hh, -⟩
      simp at hh
  | cons b t =>
      rw [evalFrom_cons, oddDFA_step_eq]
      rcases b with _ | _ | n
      · -- 首位 0：非奇
        rw [show lstep .start (some 0) = .dead from rfl, oddDFA_evalFrom_dead]
        refine iff_of_false (by decide) ?_
        rintro ⟨-, hh, -⟩
        simp at hh
      · -- 首位 1：交給 accMid 歸納
        rw [show lstep .start (some 1) = .acc from rfl, evalFrom_accMid t .acc (Or.inl rfl)]
        unfold IsCanonicalOdd
        cases t with
        | nil => simp
        | cons c t' => simp [List.getLast?_cons_cons]
      · -- 首位垃圾
        rw [lstep_junk _ (by omega), oddDFA_evalFrom_dead]
        refine iff_of_false (by decide) ?_
        rintro ⟨hb, -⟩
        have := hb _ (List.mem_cons_self ..)
        omega

/-! ## §B0.3 哨兵引理（B0-3）

`extInM` 是 Core `extIn` 的標記版：一般位元包 `some`、兩個哨兵零改讀 `none`。
`extInM_unmark` 把它一行接回 Core。以下四組事實合為 B0-3 的收口
（見檔頭技術註記 1、2 與 docs/ROADMAP-B.md 的 B0 完成紀錄）。 -/

/-- 標記哨兵輸入：`(digits x).map some ++ [none, none]`。 -/
def extInM (x : ℕ) : List (Option ℕ) := (Nat.digits 2 x).map some ++ [none, none]

/-- 去標記投影（`none ↦ 0`）。 -/
def unmark (a : Option ℕ) : ℕ := a.getD 0

/-- 與 Core 的橋：去標記後恰為 `extIn x`。 -/
theorem extInM_unmark (x : ℕ) : (extInM x).map unmark = extIn x := by
  unfold extInM extIn
  rw [List.map_append, List.map_map]
  congr 1
  exact List.map_id' _

/-- 尾段狀態唯哨兵字母可進入：一般位元（含垃圾）從任何狀態都到不了 `tail1`。 -/
theorem lstep_some_ne_tail1 (s : LSt) (b : ℕ) : lstep s (some b) ≠ .tail1 := by
  rcases b with _ | _ | n
  · cases s <;> exact fun h => LSt.noConfusion h
  · cases s <;> exact fun h => LSt.noConfusion h
  · rw [lstep_junk _ (by omega)]; exact fun h => LSt.noConfusion h

/-- 尾段狀態唯哨兵字母可進入：一般位元（含垃圾）從任何狀態都到不了 `tail2`。 -/
theorem lstep_some_ne_tail2 (s : LSt) (b : ℕ) : lstep s (some b) ≠ .tail2 := by
  rcases b with _ | _ | n
  · cases s <;> exact fun h => LSt.noConfusion h
  · cases s <;> exact fun h => LSt.noConfusion h
  · rw [lstep_junk _ (by omega)]; exact fun h => LSt.noConfusion h

/-- 只讀一般位元的走行永不觸尾段（`lstep_some_ne_tail1/2` 的 evalFrom 版）。 -/
theorem evalFrom_map_some_no_tail (v : List ℕ) :
    ∀ s : LSt, s ≠ .tail1 → s ≠ .tail2 →
      extDFA.evalFrom s (v.map some) ≠ .tail1 ∧ extDFA.evalFrom s (v.map some) ≠ .tail2 := by
  induction v with
  | nil => intro s h1 h2; exact ⟨h1, h2⟩
  | cons b t ih =>
      intro s _ _
      rw [List.map_cons, evalFrom_cons, extDFA_step_eq]
      exact ih _ (lstep_some_ne_tail1 s b) (lstep_some_ne_tail2 s b)

/-- 讀完 canonical odd word（奇數 x 的位元串）後，extDFA 停在 `acc`。 -/
theorem extDFA_run_word (x : ℕ) (hx : x % 2 = 1) :
    extDFA.evalFrom .start ((Nat.digits 2 x).map some) = .acc := by
  rw [← oddDFA_evalFrom_map]
  have h := (mem_oddDFA_accepts_iff (Nat.digits 2 x)).mpr (isCanonicalOdd_digits hx)
  rw [DFA.mem_accepts] at h
  simpa using h

/-- **B0-3 位置事實**：對奇數 x，`extInM x` 的走行在前 `|digits x|` 步不觸尾段，
第一、二哨兵步分別進入 `tail1`、`tail2`（`tail2` = 接受態，即 `extInM x ∈ extDFA.accepts`）。 -/
theorem sentinel_positions (x : ℕ) (hx : x % 2 = 1) :
    (∀ n ≤ (Nat.digits 2 x).length,
        extDFA.evalFrom .start ((extInM x).take n) ≠ .tail1 ∧
        extDFA.evalFrom .start ((extInM x).take n) ≠ .tail2)
  ∧ extDFA.evalFrom .start ((extInM x).take ((Nat.digits 2 x).length + 1)) = .tail1
  ∧ extDFA.eval (extInM x) = .tail2 := by
  refine ⟨fun n hn => ?_, ?_, ?_⟩
  · have h1 : (extInM x).take n = ((Nat.digits 2 x).take n).map some := by
      unfold extInM
      rw [List.take_append]
      have h0 : n - ((Nat.digits 2 x).map some).length = 0 := by
        simp only [List.length_map]; omega
      rw [h0]
      simp [List.map_take]
    rw [h1]
    exact evalFrom_map_some_no_tail _ .start (by decide) (by decide)
  · have htake : (extInM x).take ((Nat.digits 2 x).length + 1)
        = (Nat.digits 2 x).map some ++ [none] := by
      have hsplit : extInM x = ((Nat.digits 2 x).map some ++ [none]) ++ [none] := by
        simp [extInM]
      rw [hsplit]
      exact List.take_left' (by simp)
    rw [htake, evalFrom_append, extDFA_run_word x hx]
    rfl
  · show extDFA.evalFrom .start (extInM x) = .tail2
    unfold extInM
    rw [evalFrom_append, extDFA_run_word x hx]
    rfl

/-- 尾段封閉：`{tail2, dead}` 對全字母表封閉。 -/
theorem evalFrom_tail2_or_dead (u : List (Option ℕ)) :
    ∀ s : LSt, s = .tail2 ∨ s = .dead →
      extDFA.evalFrom s u = .tail2 ∨ extDFA.evalFrom s u = .dead := by
  induction u with
  | nil => intro s hs; exact hs
  | cons a t ih =>
      rintro s (rfl | rfl)
      · rw [evalFrom_cons, extDFA_step_eq, lstep_tail2]; exact ih _ (Or.inr rfl)
      · rw [evalFrom_cons, extDFA_step_eq, lstep_dead]; exact ih _ (Or.inr rfl)

/-- **B0-3 無環性（哨兵邊 `acc → tail1`）**：從 `tail1` 沒有任何字可回到 `acc`，
故該邊不在任何循環上（邊在循環上 ⟺ 存在從邊頭回邊尾的路徑）。 -/
theorem sentinel_edge₁_no_cycle (u : List (Option ℕ)) :
    extDFA.evalFrom .tail1 u ≠ .acc := by
  cases u with
  | nil => exact fun hc => LSt.noConfusion hc
  | cons a t =>
      rw [evalFrom_cons, extDFA_step_eq]
      have key : ∀ s : LSt, s = .tail2 ∨ s = .dead → extDFA.evalFrom s t ≠ .acc := by
        intro s hs hc
        rcases evalFrom_tail2_or_dead t s hs with h2 | h2 <;>
          rw [h2] at hc <;> exact LSt.noConfusion hc
      rcases lstep_tail1_mem a with h | h <;> rw [h]
      · exact key _ (Or.inl rfl)
      · exact key _ (Or.inr rfl)

/-- **B0-3 無環性（哨兵邊 `tail1 → tail2`）**：從 `tail2` 沒有任何字可回到 `tail1`。 -/
theorem sentinel_edge₂_no_cycle (u : List (Option ℕ)) :
    extDFA.evalFrom .tail2 u ≠ .tail1 := by
  intro hc
  rcases evalFrom_tail2_or_dead u .tail2 (Or.inl rfl) with h | h <;>
    rw [h] at hc <;> exact LSt.noConfusion hc

/-- 任意機器 × 語言 DFA 的 language-product 一步（機器讀去標記位元、DFA 讀原字母）。 -/
def prodStep {σ : Type*} (m : σ → ℕ → σ) (s : σ × LSt) (a : Option ℕ) : σ × LSt :=
  (m s.1 (unmark a), lstep s.2 a)

/-- **product 投影**：product 走行的 DFA 分量恰為 `extDFA` 的走行——
上述位置事實與無環性因此對任意機器的 language-product 生效
（product 中的循環投影後仍是 DFA 閉走行）。 -/
theorem prodRun_snd {σ : Type*} (m : σ → ℕ → σ) (s : σ × LSt) (v : List (Option ℕ)) :
    (v.foldl (prodStep m) s).2 = extDFA.evalFrom s.2 v := by
  induction v generalizing s with
  | nil => rfl
  | cons a t ih => rw [List.foldl_cons, ih]; rfl

/-! ## §B0.V 數據驗證（全部應輸出 `true`） -/

section Verification

private def words : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [0 :: w, 1 :: w])

-- B0-1：DFA 與謂詞層在長度 ≤ 8 的全體 0/1 字上一致
#eval ((List.range 9).flatMap words).all fun w =>
  decide (oddDFA.eval w = .acc) == decide (IsCanonicalOdd w)

-- 奇數位元串皆被接受；偶數（含 0）皆被拒絕
#eval (List.range 200).all fun k => decide (oddDFA.eval (Nat.digits 2 (2 * k + 1)) = .acc)
#eval (List.range 200).all fun k => decide (oddDFA.eval (Nat.digits 2 (2 * k)) ≠ .acc)

-- B0-3：extInM 的接受（奇數）與拒絕（偶數）
#eval (List.range 200).all fun k => decide (extDFA.eval (extInM (2 * k + 1)) = .tail2)
#eval (List.range 200).all fun k => decide (extDFA.eval (extInM (2 * k)) ≠ .tail2)

-- B0-3：位置事實——前 |digits| 步不觸尾段、第一/二哨兵步分別到 tail1/tail2
#eval (List.range 100).all fun k =>
  let x := 2 * k + 1
  let L := (Nat.digits 2 x).length
  ((List.range (L + 1)).all fun n =>
    decide (extDFA.evalFrom .start ((extInM x).take n) ≠ .tail1) &&
    decide (extDFA.evalFrom .start ((extInM x).take n) ≠ .tail2)) &&
  decide (extDFA.evalFrom .start ((extInM x).take (L + 1)) = .tail1) &&
  decide (extDFA.evalFrom .start ((extInM x).take (L + 2)) = .tail2)

-- 去標記橋：extInM 投影回 extIn
#eval (List.range 200).all fun x => (extInM x).map unmark == extIn x

-- 無環性抽測：從 tail1/tail2 出發讀任何 ≤6 長的字都回不到 acc/tail1
private def mwords : ℕ → List (List (Option ℕ))
  | 0 => [[]]
  | n + 1 => (mwords n).flatMap (fun w => [none :: w, some 0 :: w, some 1 :: w])

#eval ((List.range 7).flatMap mwords).all fun u =>
  decide (extDFA.evalFrom .tail1 u ≠ .acc) && decide (extDFA.evalFrom .tail2 u ≠ .tail1)

-- product 投影抽測（機器取 Core 進位機 nextCarry）
#eval (List.range 100).all fun k =>
  let x := 2 * k + 1
  ((extInM x).foldl (prodStep nextCarry) (1, .start)).2 == extDFA.eval (extInM x)

end Verification

end CollatzFST.ProjectB
