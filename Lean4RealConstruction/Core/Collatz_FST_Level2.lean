/-
# 3x+1 FST 第五批：Level 2 邊界感知狀態空間（**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_Phase.lean`。

## 三點技術註記（請對方確認）

1. **9 個有效狀態中只有 8 個可達：(0, K, 0) 是死狀態。**
   K 相位期間 soundness 給 `2ⁿ·c = 3·prefix + 1 ≥ 1`，進位不可能歸零——
   「+1」讓進位在被刪除區死不了。形式化：不變量 `Inv`（K ⇒ c ≠ 0）、
   可達集 `S8`（閉包 `S8_closed` + 八個見證字 `S8_reachable`）、
   以及 **兩個恆為零的特徵** `occ2_deadState`（E^{K}_{(0,K,·),b} ≡ 0，
   LP 的免費約束）。18 維特徵有效維度實為 16。

2. **d_prev 的更新其實恆為 `d_prev' = d`**（`step2_eq` / `step2_dPrev`）。
   規格的三分支完全一致但可摺疊——K 期間輸出全為 0，故「上一個存活輸出」
   與「上一個輸出」在 K 內自動重合（緊湊化約定 K ⇒ d_prev = 0 是**定理**
   而非約定，見 `Inv`）。組裝時可任選一種形式，兩者已證等價。

3. **K 相位的內部轉移只有 (1,K)-b1→(2,K) 與 (2,K)-b0→(1,K) 兩條**——
   停留在 K 強制輸入交錯，這是第二批 Theorem 3（v₂ = 交錯前綴長）在
   Level 2 的狀態機重現；E^K 的有效支撐因此塌縮到
   {(1,K,1), (2,K,0)}（K→K）∪ {(1,K,0), (2,K,1)}（K→S 出口）。
   出口步恰一次（`boundary_step_unique`）：聚合形式的
   E^K_{(1,K),0} + E^K_{(2,K),1} = 1，配合第四批 Σ E^K = v₂ + 1 即得
   E^K_{(1,K),1} + E^K_{(2,K),0} = v₂。

## Theorem 7 的形式內容

* **`count2_pair`（邊界捕捉核心）**：trace 上以 (d_prev, 輸出) 分類的特徵計數
  = 輸出串的相鄰對計數 `adjPairs`（前綴虛位 p）。四種邊界為其特例：
  誕生 (0→1)、高能延續 (1→1)、死亡 (1→0)、舒張延續 (0→0)。
  「徹底消滅全域計數依賴」的精確意義：N_{d_prev d} 型的全域相鄰統計
  已嚴格等於本地狀態轉移的計數。
* **`birth_death_conservation`**：#(0→1) + [p=1] = #(1→0) + [末位=1]——
  誕生與死亡差恰為「串是否以 1 結尾」，LP 級的守恆約束。
* **`run2_dPrev`（d_prev 語義錨點）**：讀完 w 後 d_prev = 最後一個輸出
  （`lastD`），Level 2 對 Level 1 是纖維化（`run2_fst`/`run2_phase`/
  `microTrace2_proj`）。
-/
import Lean4RealConstruction.Core.Collatz_FST_Phase

namespace CollatzFST

/-! ## §24 Level 2 定義 -/

def step2 (s : ℕ × Phase × ℕ) (b : ℕ) : ℕ × Phase × ℕ :=
  let d := outBit s.1 b
  let c' := nextCarry s.1 b
  match s.2.1 with
  | .K => if d = 0 then (c', .K, 0) else (c', .S, 1)
  | .S => (c', .S, d)

def run2 : (ℕ × Phase × ℕ) → List ℕ → (ℕ × Phase × ℕ)
  | s, [] => s
  | s, b :: bs => run2 (step2 s b) bs

def microTrace2 : (ℕ × Phase × ℕ) → List ℕ → List ((ℕ × Phase × ℕ) × ℕ)
  | _, [] => []
  | s, b :: bs => (s, b) :: microTrace2 (step2 s b) bs

def occ2 (s : ℕ × Phase × ℕ) (w : List ℕ) (f : (ℕ × Phase × ℕ) × ℕ) : ℕ :=
  (microTrace2 s w).count f

def lastD (p : ℕ) (l : List ℕ) : ℕ := l.foldl (fun _ d => d) p

@[simp] lemma run2_nil (s) : run2 s [] = s := rfl
lemma run2_cons (s b bs) : run2 s (b :: bs) = run2 (step2 s b) bs := rfl

lemma outBit_lt_two (c b : ℕ) : outBit c b < 2 := Nat.mod_lt _ (by norm_num)

/-- 規格三分支的統一形式：三個分量都有閉式。特別地 **d_prev' = d 恆成立**。 -/
theorem step2_eq (c : ℕ) (P : Phase) (p b : ℕ) :
    step2 (c, P, p) b = (nextCarry c b, phaseStep P (outBit c b), outBit c b) := by
  rcases P with _ | _
  · show (if outBit c b = 0 then _ else _) = _
    by_cases hd : outBit c b = 0
    · rw [if_pos hd]
      unfold phaseStep
      rw [if_pos hd, hd]
    · rw [if_neg hd]
      unfold phaseStep
      rw [if_neg hd]
      have := outBit_lt_two c b
      have hd1 : outBit c b = 1 := by omega
      rw [hd1]
  · rfl

theorem step2_dPrev (s : ℕ × Phase × ℕ) (b : ℕ) : (step2 s b).2.2 = outBit s.1 b := by
  obtain ⟨c, P, p⟩ := s
  rw [step2_eq]

theorem run2_fst (c : ℕ) (P : Phase) (p : ℕ) (w : List ℕ) :
    (run2 (c, P, p) w).1 = runCarry w c := by
  induction w generalizing c P p with
  | nil => rfl
  | cons b bs ih => rw [run2_cons, step2_eq]; exact ih _ _ _

theorem run2_phase (c : ℕ) (P : Phase) (p : ℕ) (w : List ℕ) :
    (run2 (c, P, p) w).2.1 = (runP (c, P) w).2 := by
  induction w generalizing c P p with
  | nil => rfl
  | cons b bs ih => rw [run2_cons, step2_eq, runP_cons]; exact ih _ _ _

/-- **d_prev 語義錨點**：讀完 w 後的 d_prev = 最後一個輸出（無輸出則為初始值）。 -/
theorem run2_dPrev (c : ℕ) (P : Phase) (p : ℕ) (w : List ℕ) :
    (run2 (c, P, p) w).2.2 = lastD p (run c w).2 := by
  induction w generalizing c P p with
  | nil => rfl
  | cons b bs ih =>
      rw [run2_cons, step2_eq, run_cons_snd]
      show _ = lastD (outBit c b) (run (nextCarry c b) bs).2
      exact ih _ _ _
/-- 核心不變量：K 相位期間進位恆為 1 或 2（「+1」讓進位在被刪除區死不了）。
同時 d_prev 的緊湊化約定（K ⇒ d_prev = 0）自動成立。 -/
def Inv (s : ℕ × Phase × ℕ) : Prop :=
  s.1 < 3 ∧ s.2.2 < 2 ∧ (s.2.1 = Phase.K → s.1 ≠ 0 ∧ s.2.2 = 0)

theorem inv_step {s : ℕ × Phase × ℕ} {b : ℕ} (hs : Inv s) (hb : b < 2) :
    Inv (step2 s b) := by
  obtain ⟨c, P, p⟩ := s
  obtain ⟨hc, hp, hK⟩ := hs
  rw [step2_eq]
  refine ⟨nextCarry_lt_three hc hb, outBit_lt_two c b, ?_⟩
  intro hPh
  rcases P with _ | _
  · obtain ⟨hc0, -⟩ := hK rfl
    unfold phaseStep at hPh
    by_cases hd : outBit c b = 0
    · constructor
      · -- K→K：轉移封閉於 {1,2}
        unfold outBit at hd
        unfold nextCarry
        intro hnc
        interval_cases c <;> interval_cases b <;> omega
      · exact hd
    · rw [if_neg hd] at hPh
      cases hPh
  · unfold phaseStep at hPh
    cases hPh

/-- trace 上的不變量：初始滿足 ⇒ 每筆微觀轉移的狀態都滿足。 -/
theorem microTrace2_inv {s : ℕ × Phase × ℕ} {w : List ℕ} (hs : Inv s)
    (hw : ∀ b ∈ w, b < 2) :
    ∀ t ∈ microTrace2 s w, Inv t.1 ∧ t.2 < 2 := by
  induction w generalizing s with
  | nil => intro t ht; cases ht
  | cons b bs ih =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨hs, hw b (List.mem_cons_self ..)⟩
      · exact ih (inv_step hs (hw b (List.mem_cons_self ..)))
          (fun y hy => hw y (List.mem_cons_of_mem _ hy)) t ht'

theorem init_inv : Inv (1, Phase.K, 0) := ⟨by norm_num, by norm_num, fun _ => ⟨by omega, rfl⟩⟩

/-- **死狀態**：(0, K, ·) 的兩個特徵計數恆為零（LP 的免費約束）。 -/
theorem occ2_deadState (x : ℕ) (p b : ℕ) :
    occ2 (1, Phase.K, 0) (extIn x) ((0, Phase.K, p), b) = 0 := by
  unfold occ2
  rw [List.count_eq_zero]
  intro hmem
  have hinv := (microTrace2_inv init_inv (extIn_bits x) _ hmem).1
  obtain ⟨-, -, hK⟩ := hinv
  exact (hK rfl).1 rfl
/-- 可達的 8 個狀態（9 個有效狀態去掉死狀態 (0,K,0)）。 -/
def S8 : List (ℕ × Phase × ℕ) :=
  [(1, .K, 0), (2, .K, 0),
   (0, .S, 0), (0, .S, 1), (1, .S, 0), (1, .S, 1), (2, .S, 0), (2, .S, 1)]

theorem S8_closed : ∀ s ∈ S8, ∀ b < 2, step2 s b ∈ S8 := by decide

theorem run2_mem_S8 {w : List ℕ} (hw : ∀ b ∈ w, b < 2) :
    run2 (1, Phase.K, 0) w ∈ S8 := by
  suffices h : ∀ (w : List ℕ), (∀ b ∈ w, b < 2) → ∀ s ∈ S8, run2 s w ∈ S8 by
    exact h w hw _ (by decide)
  intro w
  induction w with
  | nil => intro _ s hs; exact hs
  | cons b bs ih =>
      intro hw s hs
      rw [run2_cons]
      exact ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _
        (S8_closed s hs b (hw b (List.mem_cons_self ..)))

/-- 8 個狀態全部可達（逐一給出見證字）。 -/
theorem S8_reachable : ∀ s ∈ S8, ∃ w : List ℕ, (∀ b ∈ w, b < 2) ∧ run2 (1, Phase.K, 0) w = s := by
  intro s hs
  simp only [S8, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨[], ⟨fun b hb => absurd hb (List.not_mem_nil), rfl⟩⟩
  · exact ⟨[1], by decide, by decide⟩
  · exact ⟨[0, 0], by decide, by decide⟩
  · exact ⟨[0], by decide, by decide⟩
  · exact ⟨[0, 1, 1, 0], by decide, by decide⟩
  · exact ⟨[0, 1], by decide, by decide⟩
  · exact ⟨[0, 1, 1], by decide, by decide⟩
  · exact ⟨[0, 1, 1, 1], by decide, by decide⟩

/-- 相鄰對計數：`adjPairs a d₀ p l` = 在 `p :: l` 中相鄰對 `(a, d₀)` 的個數。 -/
def adjPairs (a d₀ : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | p, d :: ds => (if p == a && d == d₀ then 1 else 0) + adjPairs a d₀ d ds

lemma adjPairs_nil (a d₀ p : ℕ) : adjPairs a d₀ p [] = 0 := rfl
lemma adjPairs_cons (a d₀ p d : ℕ) (ds : List ℕ) :
    adjPairs a d₀ p (d :: ds) = (if p == a && d == d₀ then 1 else 0) + adjPairs a d₀ d ds := rfl

/-- **Theorem 7 核心（邊界捕捉）**：trace 上以 (d_prev, 輸出) 分類的特徵計數，
恰為輸出串（前綴虛位 p）的相鄰對計數。四種邊界（誕生/延續/死亡/舒張）
分別取 (a, d₀) = (0,1)/(1,1)/(1,0)/(0,0)。 -/
theorem count2_pair (a d₀ : ℕ) : ∀ (w : List ℕ) (c : ℕ) (P : Phase) (p : ℕ),
    (microTrace2 (c, P, p) w).countP
        (fun t => t.1.2.2 == a && outBit t.1.1 t.2 == d₀)
      = adjPairs a d₀ p (run c w).2 := by
  intro w
  induction w with
  | nil => intro c P p; rfl
  | cons b bs ih =>
      intro c P p
      have hstep : (microTrace2 (c, P, p) (b :: bs)).countP
            (fun t => t.1.2.2 == a && outBit t.1.1 t.2 == d₀)
          = (microTrace2 (step2 (c, P, p) b) bs).countP
              (fun t => t.1.2.2 == a && outBit t.1.1 t.2 == d₀)
            + (if p == a && outBit c b == d₀ then 1 else 0) := by
        rw [show microTrace2 (c, P, p) (b :: bs)
            = ((c, P, p), b) :: microTrace2 (step2 (c, P, p) b) bs from rfl,
          List.countP_cons]
      rw [hstep, step2_eq, ih, run_cons_snd, adjPairs_cons]
      omega
/-- 誕生−死亡守恆律：#(0→1) + [p=1] = #(1→0) + [末位=1]。
（每個 1-block 有一次誕生；除非串以 1 結尾，否則也有一次死亡。） -/
theorem birth_death_conservation : ∀ (l : List ℕ) (p : ℕ), p < 2 → (∀ d ∈ l, d < 2) →
    adjPairs 0 1 p l + (if p = 1 then 1 else 0)
      = adjPairs 1 0 p l + (if lastD p l = 1 then 1 else 0) := by
  intro l
  induction l with
  | nil =>
      intro p hp _
      show 0 + _ = 0 + _
      rfl
  | cons d ds ih =>
      intro p hp hl
      have hd : d < 2 := hl d (List.mem_cons_self ..)
      have hih := ih d hd (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      rw [adjPairs_cons, adjPairs_cons,
        show lastD p (d :: ds) = lastD d ds from rfl]
      interval_cases p <;> interval_cases d <;> simp at hih ⊢ <;> omega

/-- countP 依第二個 Bool 述詞拆分。 -/
theorem countP_bool_split {α : Type} (p q : α → Bool) : ∀ (l : List α),
    l.countP p = l.countP (fun a => p a && q a) + l.countP (fun a => p a && !q a) := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
      cases hp : p a <;> cases hq : q a <;> simp <;> omega

/-- countP 對逐點相等的述詞不變。 -/
theorem countP_congr' {α : Type} {p q : α → Bool} : ∀ {l : List α},
    (∀ a ∈ l, p a = q a) → l.countP p = l.countP q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      rw [List.countP_cons, List.countP_cons, h a (List.mem_cons_self ..),
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Level 2 trace 投影回 Level 1 trace（Level 2 是 Level 1 的纖維化）。 -/
theorem microTrace2_proj : ∀ (w : List ℕ) (c : ℕ) (P : Phase) (p : ℕ),
    (microTrace2 (c, P, p) w).map (fun t => (t.1.1, t.1.2.1, t.2))
      = microTraceP (c, P) w := by
  intro w
  induction w with
  | nil => intro c P p; rfl
  | cons b bs ih =>
      intro c P p
      show ((c, P, b) : ℕ × Phase × ℕ) :: (microTrace2 (step2 (c, P, p) b) bs).map _
          = (c, P, b) :: microTraceP (nextCarry c b, phaseStep P (outBit c b)) bs
      rw [step2_eq, ih]

/-- **邊界觸發步唯一**：起始相位 K 且輸出 1 的步恰好一次
（＝聚合形式的 E^K_{(1),b=0} + E^K_{(2),b=1} = 1）。 -/
theorem boundary_step_unique (x : ℕ) :
    (microTrace2 (1, Phase.K, 0) (extIn x)).countP
        (fun t => t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1) = 1 := by
  -- 先投影到 Level 1
  have hproj : (microTrace2 (1, Phase.K, 0) (extIn x)).countP
        (fun t => t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1)
      = (microTraceP (1, Phase.K) (extIn x)).countP
          (fun t => t.2.1 == Phase.K && outBit t.1 t.2.2 == 1) := by
    rw [← microTrace2_proj (extIn x) 1 Phase.K 0, List.countP_map]
    rfl
  rw [hproj]
  -- K 步依輸出 0/1 拆分
  have hsplit := countP_bool_split (fun t : ℕ × Phase × ℕ => t.2.1 == Phase.K)
    (fun t => outBit t.1 t.2.2 == 0) (microTraceP (1, Phase.K) (extIn x))
  have hK := sum_EK_eq x
  -- (K ∧ out=0) 逐點等於 stayK 述詞
  have h0 : (microTraceP (1, Phase.K) (extIn x)).countP
        (fun t => t.2.1 == Phase.K && (outBit t.1 t.2.2 == 0))
      = (microTraceP (1, Phase.K) (extIn x)).countP
          (fun t => t.2.1 == Phase.K && phaseStep t.2.1 (outBit t.1 t.2.2) == Phase.K) := by
    apply countP_congr'
    intro t _
    rcases ht : t.2.1 with _ | _
    · have := outBit_lt_two t.1 t.2.2
      by_cases hd : outBit t.1 t.2.2 = 0
      · rw [hd]
        show (true && (0 == 0)) = (true && _)
        unfold phaseStep
        rfl
      · have hd1 : outBit t.1 t.2.2 = 1 := by omega
        rw [hd1]
        show (true && (1 == 0)) = (true && _)
        unfold phaseStep
        rfl
    · rfl
  -- (K ∧ ¬(out=0)) 逐點等於 (K ∧ out=1)
  have h1 : (microTraceP (1, Phase.K) (extIn x)).countP
        (fun t => t.2.1 == Phase.K && !(outBit t.1 t.2.2 == 0))
      = (microTraceP (1, Phase.K) (extIn x)).countP
          (fun t => t.2.1 == Phase.K && outBit t.1 t.2.2 == 1) := by
    apply countP_congr'
    intro t _
    have := outBit_lt_two t.1 t.2.2
    by_cases hd : outBit t.1 t.2.2 = 0
    · rw [hd]; rfl
    · have hd1 : outBit t.1 t.2.2 = 1 := by omega
      rw [hd1]; rfl
  have hstay := countP_stayK 1 (extIn x)
  have hlz : leadingZeros (run 1 (extIn x)).2 = padicValNat 2 (3 * x + 1) :=
    leadingZeros_extOut x
  rw [h0, hstay, hlz] at hsplit
  rw [hK] at hsplit
  rw [h1] at hsplit
  omega

/-! ## §28 數據驗證（全部應輸出 `true`） -/

section Verification

private def bfs2 : ℕ → List (ℕ × Phase × ℕ) → List (ℕ × Phase × ℕ)
  | 0, acc => acc
  | n + 1, acc =>
      let nxt := (acc.flatMap fun s => [step2 s 0, step2 s 1]).filter (fun g => !acc.contains g)
      if nxt.isEmpty then acc else bfs2 n (acc ++ nxt.eraseDups)

-- 可達集恰為 S8（BFS 8 個、皆屬 S8、不含死狀態）
#eval let R := bfs2 30 [(1, Phase.K, 0)]
      R.length == 8 && R.all (· ∈ S8) && !R.contains (0, Phase.K, 0)

-- d_prev 語義：= 最後一個輸出
#eval (List.range 150).all fun x =>
  (run2 (1, Phase.K, 0) (extIn x)).2.2 == lastD 0 (extOut x)

-- 投影一致（進位、相位）
#eval (List.range 150).all fun x =>
  (run2 (1, Phase.K, 0) (extIn x)).1 == runCarry (extIn x) 1 &&
  ((run2 (1, Phase.K, 0) (extIn x)).2.1 == (runP (1, Phase.K) (extIn x)).2)

-- d_prev 更新恆為 d
#eval (List.range 3).all fun c => (List.range 2).all fun b => (List.range 2).all fun p =>
  [Phase.K, Phase.S].all fun P => (step2 (c, P, p) b).2.2 == outBit c b

-- 死狀態特徵恆零
#eval (List.range 150).all fun x => (List.range 2).all fun p => (List.range 2).all fun b =>
  occ2 (1, Phase.K, 0) (extIn x) ((0, Phase.K, p), b) == 0

-- 邊界捕捉：四種 (d_prev, d) 配對計數 = 相鄰對計數
#eval (List.range 120).all fun x =>
  [(0, 1), (1, 1), (1, 0), (0, 0)].all fun (a, d₀) =>
    (microTrace2 (1, Phase.K, 0) (extIn x)).countP
        (fun t => t.1.2.2 == a && outBit t.1.1 t.2 == d₀)
      == adjPairs a d₀ 0 (extOut x)

-- 誕生−死亡守恆
#eval (List.range 150).all fun x =>
  adjPairs 0 1 0 (extOut x)
    == adjPairs 1 0 0 (extOut x) + (if lastD 0 (extOut x) == 1 then 1 else 0)

-- 邊界觸發步唯一
#eval (List.range 150).all fun x =>
  (microTrace2 (1, Phase.K, 0) (extIn x)).countP
      (fun t => t.1.2.1 == Phase.K && outBit t.1.1 t.2 == 1) == 1

end Verification

end CollatzFST
