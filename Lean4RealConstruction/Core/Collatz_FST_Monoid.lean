/-
# 3x+1 FST 第三批：t_w / n_w / Σ_w 與狀態轉換么半群（**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_Ext.lean`。

## 三點技術註記（請對方確認）

1. **Theorem 5 的基數 8 正確，但括號裡的說明是錯的。**
   規格寫「其元素（即從 {0,1,2} 映射到 {0,1,2} 的所有可能函數）數量極小，基數精確等於 8」。
   從 {0,1,2} 到 {0,1,2} 的**所有**函數共 `3^3 = 27` 個（已形式化：`card_all`），
   而 M 是其中的**真子集**，恰 8 個元素。兩者不同，括號應刪去或改寫成
   「M 是 {0,1,2} 上全體變換（27 個）中的一個 8 元子么半群」。

2. **「8」與「么半群」是綁定的，不能說成半群。**
   由非空字生成的**半群** ⟨t_0, t_1⟩⁺ 只有 **7** 個元素，且**不含恆等變換**
   （已形式化：`M7_card`、`tW_ne_one`——任何非空字的 t_w 都不是恆等）。
   第 8 個元素恰是空字給出的 `id`。所以敘述必須是么半群（含空字），基數才是 8。

3. **規格作者對 `decide` 的預期完全正確。** 本檔所有有限性檢查
   （閉包、基數、8 個元素的具體字）皆由 `decide` 一行完成。

## M 的 8 個元素（以 `(t(0), t(1), t(2))` 表示）

| 代表字 w | t_w |
|---|---|
| ε | (0,1,2) = id |
| 0 | (0,0,1) |
| 1 | (1,2,2) |
| 00 | (0,0,0) |
| 01 | (1,1,2) |
| 10 | (0,1,1) |
| 11 | (2,2,2) |
| 001 | (1,1,1) |

其中 `00 ↦ (0,0,0)`（常數 0）與 `11 ↦ (2,2,2)`（常數 2）正是第二批 Lemma 3 的
萬用重置與萬用飽和——同步字詞就是「t_w 為常數函數」的字詞。

## 設計決策

* **t_w 不另外定義**：規格的 t_w 就是既有的 `runCarry w q = (run q w).1`，
  三條定義方程（空字/單位元/串接）分別是 `t_nil`、`t_single`（皆 `rfl`）與
  `t_append`（第二批的 `run_append` 第一分量）。
* **n_w 走「微觀轉移軌跡 + 計數」**：`microTrace` 記下每步的 `(c_i, b_i)`，
  `occ q w p = (microTrace q w).count p`。這讓串接規則直接由
  `List.count_append` 得出，比直接遞迴定義六維向量好證得多。
  `occVec` 給出規格要求的 `(E_{0,0}, …, E_{2,1})` 六元組。
* **Σ 是真的么半群**：`Sig` 帶 `Monoid` instance（乘法即規格的組合律），
  `sig : List ℕ → Sig` 滿足 `sig (u ++ v) = sig u * sig v`，
  精確表達「無需重新掃描位元」。
* **Theorem 5 用 `Fin 3` / `Fin 2`**：么半群結構取 `Function.End (Fin 3)`
  （Mathlib 的乘法慣例為 `f * g = f ∘ g`）。`tW_val` 提供與 ℕ 版 `runCarry` 的橋。
-/
import Lean4RealConstruction.Core.Collatz_FST_Ext
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Data.Set.Card

namespace CollatzFST

/-! ## §14 狀態轉換函數 t_w

規格的 t_w 即既有的 `runCarry`。三條定義方程如下。 -/

/-- 定義方程 1（空字串）：t_ε(q) = q。 -/
theorem t_nil (q : ℕ) : runCarry [] q = q := rfl

/-- 定義方程 2（單一位元）：t_b(q) = ⌊(3b+q)/2⌋。 -/
theorem t_single (b q : ℕ) : runCarry [b] q = nextCarry q b := rfl

/-- 定義方程 3（串接）：t_{uv}(q) = t_v(t_u(q))。 -/
theorem t_append (u v : List ℕ) (q : ℕ) :
    runCarry (u ++ v) q = runCarry v (runCarry u q) := by
  show (run q (u ++ v)).1 = _
  rw [run_append]

/-! ## §15 轉移佔用向量 n_w -/

/-- 讀取過程中的微觀轉移序列 `(c_i, b_i)`。 -/
def microTrace : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | c, b :: bs => (c, b) :: microTrace (nextCarry c b) bs

/-- `occ q w p`：從進位 `q` 讀 `w` 時，微觀轉移 `p = (c, b)` 的發生次數。 -/
def occ (q : ℕ) (w : List ℕ) (p : ℕ × ℕ) : ℕ := (microTrace q w).count p

theorem microTrace_append (q : ℕ) (u v : List ℕ) :
    microTrace q (u ++ v) = microTrace q u ++ microTrace (runCarry u q) v := by
  induction u generalizing q with
  | nil => rfl
  | cons b bs ih => show (q, b) :: microTrace (nextCarry q b) (bs ++ v) = _; rw [ih]; rfl

/-- 定義方程 1（空字串）：n_ε(q) = 0。 -/
theorem occ_nil (q : ℕ) (p : ℕ × ℕ) : occ q [] p = 0 := rfl

/-- 定義方程 2（單一位元）：n_b(q) = e_{q,b}。 -/
theorem occ_single (q b : ℕ) (p : ℕ × ℕ) : occ q [b] p = if p = (q, b) then 1 else 0 := by
  unfold occ microTrace
  rw [List.count_cons]
  by_cases h : p = (q, b)
  · subst h; simp [microTrace]
  · simp [microTrace, h, Ne.symm h]

/-- 定義方程 3（串接）：n_{uv}(q) = n_u(q) + n_v(t_u(q))。
注意 v 的計算基於 u 留下的最終狀態 `runCarry u q`。 -/
theorem occ_append (q : ℕ) (u v : List ℕ) (p : ℕ × ℕ) :
    occ q (u ++ v) p = occ q u p + occ (runCarry u q) v p := by
  unfold occ
  rw [microTrace_append, List.count_append]

/-- 規格要求的六維向量 `(E_{0,0}, E_{0,1}, E_{1,0}, E_{1,1}, E_{2,0}, E_{2,1})`。 -/
def occVec (q : ℕ) (w : List ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (occ q w (0,0), occ q w (0,1), occ q w (1,0), occ q w (1,1), occ q w (2,0), occ q w (2,1))

theorem microTrace_length (q : ℕ) (w : List ℕ) : (microTrace q w).length = w.length := by
  induction w generalizing q with
  | nil => rfl
  | cons b bs ih =>
      show (microTrace (nextCarry q b) bs).length + 1 = _
      rw [ih, List.length_cons]

/-- 六分量總和 = 字串長度（每步恰觸發一種轉移，故六維向量無遺漏、無重複）。 -/
theorem occVec_sum {q : ℕ} {w : List ℕ} (hq : q < 3) (hb : ∀ b ∈ w, b < 2) :
    occ q w (0,0) + occ q w (0,1) + occ q w (1,0) + occ q w (1,1)
      + occ q w (2,0) + occ q w (2,1) = w.length := by
  induction w generalizing q with
  | nil => rfl
  | cons b bs ih =>
      have hb2 : b < 2 := hb b (List.mem_cons_self ..)
      have hrest : ∀ y ∈ bs, y < 2 := fun y hy => hb y (List.mem_cons_of_mem _ hy)
      have key := ih (nextCarry_lt_three hq hb2) hrest
      show _ = bs.length + 1
      rw [show ((b :: bs) : List ℕ) = [b] ++ bs from rfl]
      simp only [occ_append, t_single]
      rw [occ_single, occ_single, occ_single, occ_single, occ_single, occ_single]
      interval_cases q <;> interval_cases b <;> simp <;> omega

/-! ## §16 可組合區塊簽章 Σ_w -/

/-- 區塊簽章 `Σ(w) = (t_w, n_w)`。 -/
structure Sig where
  t : ℕ → ℕ
  n : ℕ → (ℕ × ℕ → ℕ)

namespace Sig

theorem ext' : ∀ {a b : Sig}, a.t = b.t → a.n = b.n → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

/-- 規格的組合律：`Σ(uv) = (t_v ∘ t_u, n_u + n_v ∘ t_u)`。 -/
instance : Mul Sig := ⟨fun a b => ⟨b.t ∘ a.t, fun q => a.n q + b.n (a.t q)⟩⟩

instance : One Sig := ⟨⟨id, fun _ => 0⟩⟩

/-- 簽章在該組合律下構成么半群。 -/
instance : Monoid Sig where
  mul_assoc _ _ _ := ext' rfl (funext fun _ => add_assoc _ _ _)
  one_mul _ := ext' rfl (funext fun _ => zero_add _)
  mul_one _ := ext' rfl (funext fun _ => add_zero _)

end Sig

/-- 字串 `w` 的簽章。 -/
def sig (w : List ℕ) : Sig := ⟨fun q => runCarry w q, fun q => occ q w⟩

theorem sig_t (w : List ℕ) (q : ℕ) : (sig w).t q = runCarry w q := rfl
theorem sig_n (w : List ℕ) (q : ℕ) (p : ℕ × ℕ) : (sig w).n q p = occ q w p := rfl
theorem sig_nil : sig [] = 1 := rfl

/-- **可組合性**：`Σ(uv) = Σ(u) * Σ(v)`，展開即 `(t_v ∘ t_u, n_u + n_v ∘ t_u)`。
`sig` 因此是自由么半群 `(List ℕ, ++)` 到 `Sig` 的么半群同態——
這正是「無需重新掃描位元」的精確意義。 -/
theorem sig_append (u v : List ℕ) : sig (u ++ v) = sig u * sig v :=
  Sig.ext' (funext fun q => t_append u v q) (funext fun q => funext fun p => occ_append q u v p)

/-! ## §17 Theorem 5：狀態轉換么半群的有限性 -/

instance : DecidableEq (Function.End (Fin 3)) := inferInstanceAs (DecidableEq (Fin 3 → Fin 3))
instance : Fintype (Function.End (Fin 3)) := inferInstanceAs (Fintype (Fin 3 → Fin 3))

/-- 單一位元的狀態轉換（`Fin 3` 版；良定義性來自 `nextCarry_lt_three`）。 -/
def tF (b : Fin 2) : Function.End (Fin 3) := fun q => ⟨nextCarry q b, nextCarry_lt_three q.2 b.2⟩

/-- 字串的狀態轉換。注意 `Function.End` 的乘法慣例是 `f * g = f ∘ g`，
故 `tW (b :: bs) = tW bs * tF b` 表示「先讀 b，再讀 bs」。 -/
def tW : List (Fin 2) → Function.End (Fin 3)
  | [] => 1
  | b :: bs => tW bs * tF b

/-- 與 ℕ 版 `runCarry` 的橋。 -/
theorem tW_val (w : List (Fin 2)) (q : Fin 3) :
    ((tW w q : Fin 3) : ℕ) = runCarry (w.map (·.val)) q := by
  induction w generalizing q with
  | nil => rfl
  | cons b bs ih => show ((tW bs (tF b q) : Fin 3) : ℕ) = _; rw [ih]; rfl

theorem tW_append (u v : List (Fin 2)) : tW (u ++ v) = tW v * tW u := by
  induction u with
  | nil => show tW v = tW v * 1; rw [mul_one]
  | cons b bs ih => show tW (bs ++ v) * tF b = _; rw [ih, mul_assoc]; rfl

/-- M 的 8 個元素（以 `![t 0, t 1, t 2]` 表示）。 -/
def MFinset : Finset (Function.End (Fin 3)) :=
  {![0,1,2], ![0,0,1], ![1,2,2], ![0,0,0], ![1,1,2], ![0,1,1], ![2,2,2], ![1,1,1]}

theorem MFinset_card : MFinset.card = 8 := by decide

/-- 對照：`{0,1,2}` 上的**全體**變換共 27 個。M 是其 8 元真子集。 -/
theorem card_all : Fintype.card (Function.End (Fin 3)) = 27 := by decide

theorem MFinset_closed : ∀ f ∈ MFinset, ∀ b : Fin 2, f * tF b ∈ MFinset := by decide

theorem tW_mem (w : List (Fin 2)) : tW w ∈ MFinset := by
  induction w with
  | nil => decide
  | cons b bs ih => exact MFinset_closed _ ih b

theorem MFinset_sub_range : ↑MFinset ⊆ Set.range tW := by
  intro f hf
  simp only [MFinset, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
    Set.mem_singleton_iff] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  exacts [⟨[], by decide⟩, ⟨[0], by decide⟩, ⟨[1], by decide⟩, ⟨[0,0], by decide⟩,
          ⟨[0,1], by decide⟩, ⟨[1,0], by decide⟩, ⟨[1,1], by decide⟩, ⟨[0,0,1], by decide⟩]

/-- 狀態轉換么半群 `M = ⟨t_0, t_1⟩`（作為所有字串的 t_w 之集）。 -/
def Mmon : Submonoid (Function.End (Fin 3)) where
  carrier := Set.range tW
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨v ++ u, tW_append v u⟩

/-- `M` 確實是由 `t_0` 與 `t_1` 生成的么半群。 -/
theorem Mmon_eq_closure : Mmon = Submonoid.closure {tF 0, tF 1} := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    induction w with
    | nil => exact Submonoid.one_mem _
    | cons b bs ih =>
        refine Submonoid.mul_mem _ ih (Submonoid.subset_closure ?_)
        revert b
        decide
  · rw [Submonoid.closure_le]
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact ⟨[0], one_mul _⟩
    · exact ⟨[1], one_mul _⟩

theorem Mmon_coe : (Mmon : Set (Function.End (Fin 3))) = ↑MFinset :=
  Set.Subset.antisymm (by rintro _ ⟨w, rfl⟩; exact tW_mem w) MFinset_sub_range

/-- **Theorem 5**：M 有限，且基數精確等於 8。 -/
theorem card_Mmon : Nat.card Mmon = 8 := by
  rw [show Nat.card Mmon = Nat.card ((Mmon : Set (Function.End (Fin 3)))) from rfl,
    Nat.card_coe_set_eq, Mmon_coe, Set.ncard, Set.encard_coe_eq_coe_finsetCard, MFinset_card]
  rfl

theorem Mmon_finite : (Mmon : Set (Function.End (Fin 3))).Finite := by
  rw [Mmon_coe]; exact (MFinset : Finset (Function.End (Fin 3))).finite_toSet

/-! ### §17b 「8」與「么半群」綁定：半群只有 7 個元素且不含恆等 -/

/-- 非空字生成的 7 個元素（M 去掉 `id`）。 -/
def M7 : Finset (Function.End (Fin 3)) :=
  {![0,0,1], ![1,2,2], ![0,0,0], ![1,1,2], ![0,1,1], ![2,2,2], ![1,1,1]}

theorem M7_card : M7.card = 7 := by decide

theorem M7_closed : ∀ f ∈ MFinset, ∀ b : Fin 2, f * tF b ∈ M7 := by decide

/-- 任何**非空**字的 t_w 都不是恆等變換。
故第 8 個元素只能來自空字，敘述必須用么半群而非半群。 -/
theorem tW_ne_one : ∀ (w : List (Fin 2)), w ≠ [] → tW w ≠ 1 := by
  rintro (_ | ⟨b, bs⟩) hw
  · exact absurd rfl hw
  · have hmem : tW (b :: bs) ∈ M7 := M7_closed _ (tW_mem bs) b
    intro h1
    rw [h1] at hmem
    revert hmem
    decide

/-! ## §18 數據驗證（全部應輸出 `true`） -/

section Verification

private def nc (c b : ℕ) : ℕ := (3 * b + c) / 2
private abbrev Tri := ℕ × ℕ × ℕ
private def stepR (f : Tri) (b : ℕ) : Tri := (nc f.1 b, nc f.2.1 b, nc f.2.2 b)
private def bfs : ℕ → List Tri → List Tri
  | 0, acc => acc
  | n + 1, acc =>
      let nxt := (acc.flatMap fun f => [stepR f 0, stepR f 1]).filter (fun g => !acc.contains g)
      if nxt.isEmpty then acc else bfs n (acc ++ nxt.eraseDups)

private def words : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [0 :: w, 1 :: w])

-- Theorem 5：么半群基數 = 8（BFS 閉包）
#eval (bfs 30 [(0, 1, 2)]).length == 8

-- 對照：全體變換 27 個；半群（非空字）只有 7 個且不含 id
#eval 3 ^ 3 == 27
#eval let S := bfs 30 [stepR (0,1,2) 0, stepR (0,1,2) 1]; S.length == 7 && !S.contains (0,1,2)

-- t_w 串接律
#eval ((List.range 6).flatMap words).all fun u => ((List.range 5).flatMap words).all fun v =>
  (List.range 3).all fun q => runCarry (u ++ v) q == runCarry v (runCarry u q)

-- n_w 串接律（六分量逐一比對）
#eval ((List.range 6).flatMap words).all fun u => ((List.range 5).flatMap words).all fun v =>
  (List.range 3).all fun q =>
    [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)].all fun p =>
      occ q (u ++ v) p == occ q u p + occ (runCarry u q) v p

-- n_w 單一位元 = e_{q,b}
#eval (List.range 3).all fun q => (List.range 2).all fun b =>
  [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)].all fun p =>
    occ q [b] p == (if p == (q, b) then 1 else 0)

-- 六分量總和 = 長度
#eval ((List.range 9).flatMap words).all fun w => (List.range 3).all fun q =>
  let v := occVec q w
  v.1 + v.2.1 + v.2.2.1 + v.2.2.2.1 + v.2.2.2.2.1 + v.2.2.2.2.2 == w.length

-- Σ 組合律（t 分量與 n 分量）
#eval ((List.range 6).flatMap words).all fun u => ((List.range 5).flatMap words).all fun v =>
  (List.range 3).all fun q =>
    (sig (u ++ v)).t q == (sig u * sig v).t q &&
    [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)].all fun p =>
      (sig (u ++ v)).n q p == (sig u * sig v).n q p

-- 同步字詞 = t_w 為常數函數（呼應第二批 Lemma 3）
#eval (List.range 3).all fun q => runCarry [0,0] q == 0
#eval (List.range 3).all fun q => runCarry [1,1] q == 2

end Verification

end CollatzFST
