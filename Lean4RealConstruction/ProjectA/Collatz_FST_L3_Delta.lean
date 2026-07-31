/-
# Level 3 差分層：65 條泛函（ROADMAP A-3 Level 3 第二步）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_L3_Flow.lean`（§65–72）。

## 設計決策（動手前先做的兩個判斷）

**① 不經過 `F3` 的 List 層。** 維度定理與既有的 `no_go_level3_2mode_potential`
互相獨立（Level 2 先例相同：`no_nonneg_linear_ranking` 與 `finrank_span_dFQ_eq_ten`
互不引用），所以本檔的 `dF96` 直接用 `occ3` 定義——Level 2 那 18 條座標橋在這裡
**不需要類比物**（96 條橋消失）。

**② 第 65 條用 `f_start` 重組，不用 `θ₀[16] + θ₁[33]`。** 湮滅子是 65 維、
家族已有 64 維，任何能補滿的方向模掉家族都相同。`f_start|b0 + f_start|b1`
（初始狀態 `(1,K,0,0)` 的流守恆對兩區塊求和）的證明成本幾乎為零：
兩端的 kirchhoff 常數 −1 在相減時對消，完全不需要模式分析。
`tools/l3_recon.py` 對兩個方向都有對帳。

`occ3_mode_bit_sum`（§72）沒有白做：兩條**區塊相依死座標**
（`θ₀[33]`、`θ₁[16]`）靠它——模式座標在區塊 0 恆為 0、出口座標在區塊 1 恆為 0。

## 65 條的帳（`tools/l3_recon.py` 精確有理驗算，CI 每次 push 跑）

| 家族 | 條數 | 形式 |
|---|---|---|
| 提升死座標 | 20 × 2 = 40 | `dF96_dead`（參數化一條） |
| 提升乾淨流守恆（c = 0 的 11 個狀態） | 11 × 2 = 22 | `dF96_flow_clean`（參數化一條） |
| 區塊相依死座標 | 2 | `dF96_block0_mode`、`dF96_block1_exit` |
| `f_start` 跨區塊重組 | 1 | `dF96_fstart` |
| **合計** | **65** | = 96 − 31 ⇒ 上界的材料齊了 |

單模式 13 條可用關係裡，`g = (1,K,0,0)`（常數 −1，初始狀態）與合併終末
（常數 +1）**提升不上**——提升後殘留 `c·([m(y)=0] − [m(x)=0])`，模式一翻轉
就 ±1；`f_start` 重組正是前者的兩區塊和，常數對消後活下來。

## 不在本檔範圍

`Fin 96 → ℚ` 的打包、解空間、上界 `≤ 31`、下界見證——下一步。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_Flow

namespace CollatzFST.L3

open CollatzFST

/-! ## §73 差分層的定義（不經過 List 層） -/

/-- 端點特徵（ℚ 值）：`E3 x k = occ3 (1,K,0,0) (extIn x) k`。 -/
def E3 (x : ℕ) (k : (ℕ × Phase × ℕ × ℕ) × ℕ) : ℚ :=
  (occ3 (1, Phase.K, 0, 0) (extIn x) k : ℚ)

/-- 模式位元 m(x)：`occ3` 在 key33（`((2,K,0,0),1)`）的計數是否為 1。
與 `no_go_level3_2mode_potential` 的 `(F3 x).getD 33 0 = 1` 同一判準。 -/
def mode3 (x : ℕ) : ℕ :=
  if occ3 (1, Phase.K, 0, 0) (extIn x) (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 1
  then 1 else 0

/-- 96 維雙模式差分：區塊 `b`、座標 `k` 的分量。
區塊 `m(Todd x)` 加上 `E3 (Todd x)`，區塊 `m(x)` 減去 `E3 x`。 -/
def dF96 (x : ℕ) (b : ℕ) (k : (ℕ × Phase × ℕ × ℕ) × ℕ) : ℚ :=
  (if b = mode3 (Todd x) then E3 (Todd x) k else 0)
    - (if b = mode3 x then E3 x k else 0)

lemma mode3_cases (z : ℕ) : mode3 z = 0 ∨ mode3 z = 1 := by
  unfold mode3; split_ifs <;> simp

/-! ## §74 死座標：40 條（參數化） -/

/-- 不可達狀態的佔用恆為零（`occ2_deadState` 的 Level 3 對應，覆蓋全部 20 個死態）。 -/
theorem occ3_not_reachable (x : ℕ) {g : ℕ × Phase × ℕ × ℕ} (hg : g ∉ S14) (b : ℕ) :
    occ3 (1, Phase.K, 0, 0) (extIn x) (g, b) = 0 := by
  unfold occ3
  rw [List.count_eq_zero]
  intro hmem
  exact hg (microTrace3_mem_S14 (extIn x) _ (by decide) (extIn_bits x) _ hmem).1

/-- **提升死座標**（40 條合一）：狀態不可達 ⇒ 兩個區塊的該座標皆恆零。 -/
theorem dF96_dead (x : ℕ) (b : ℕ) {g : ℕ × Phase × ℕ × ℕ} (hg : g ∉ S14) (c : ℕ) :
    dF96 x b (g, c) = 0 := by
  unfold dF96 E3
  rw [occ3_not_reachable _ hg, occ3_not_reachable _ hg]
  simp

/-! ## §75 區塊相依死座標：2 條（`occ3_mode_bit_sum` 在此上場） -/

/-- key33 的佔用就是模式位元（由 §72 的和恆為 1）。 -/
lemma occ3_mode_key_eq (z : ℕ) :
    occ3 (1, Phase.K, 0, 0) (extIn z) (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1)
      = mode3 z := by
  have hsum := occ3_mode_bit_sum z
  unfold mode3
  split_ifs with hc
  · exact hc
  · omega

/-- key16 的佔用是模式位元的補（同樣由 §72）。 -/
lemma occ3_exit_key_eq (z : ℕ) :
    occ3 (1, Phase.K, 0, 0) (extIn z) (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
      = 1 - mode3 z := by
  have hsum := occ3_mode_bit_sum z
  have h33 := occ3_mode_key_eq z
  omega

/-- **θ₀[33] 恆零**：區塊 0 表示「模式 = 0」，而模式座標在模式 0 時計數為 0。 -/
theorem dF96_block0_mode (x : ℕ) :
    dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 0 := by
  unfold dF96 E3
  rw [occ3_mode_key_eq, occ3_mode_key_eq]
  rcases mode3_cases (Todd x) with hy | hy <;> rcases mode3_cases x with hx | hx <;>
    rw [hy, hx] <;> norm_num

/-- **θ₁[16] 恆零**：區塊 1 表示「模式 = 1」，而出口座標在模式 1 時計數為 0。 -/
theorem dF96_block1_exit (x : ℕ) :
    dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) = 0 := by
  unfold dF96 E3
  rw [occ3_exit_key_eq, occ3_exit_key_eq]
  rcases mode3_cases (Todd x) with hy | hy <;> rcases mode3_cases x with hx | hx <;>
    rw [hy, hx] <;> norm_num

/-! ## §76 提升乾淨流守恆：22 條（參數化） -/

private lemma sum_map_sub {α : Type} (l : List α) (f g : α → ℚ) :
    (l.map (fun e => f e - g e)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

private lemma sum_map_ite {α : Type} (l : List α) (P : Prop) [Decidable P] (f : α → ℚ) :
    (l.map (fun e => if P then f e else 0)).sum = if P then (l.map f).sum else 0 := by
  split_ifs <;> simp_all

private lemma cast_sum_map {α : Type} (l : List α) (f : α → ℕ) :
    (((l.map f).sum : ℕ) : ℚ) = (l.map (fun e => (f e : ℚ))).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons]
      push_cast [ih]
      ring

/-- 乾淨 kirchhoff 的 ℚ 版（`g` 非初始、非終末 ⇒ 無指示項）。 -/
lemma kirchhoff_E3_clean (z : ℕ) (g : ℕ × Phase × ℕ × ℕ)
    (hI : g ≠ ((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)))
    (h0 : g ≠ ((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)))
    (h1 : g ≠ ((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ))) :
    ((inEdges3 g).map (fun e => E3 z e)).sum = E3 z (g, 0) + E3 z (g, 1) := by
  have h := kirchhoff_occ3_extIn_clean z g h0 h1
  rw [if_neg (fun hh => hI hh.symm), Nat.add_zero] at h
  unfold E3
  rw [← cast_sum_map]
  exact_mod_cast h

/-- **提升乾淨流守恆**（22 條合一）：`c = 0` 的狀態 g、任一區塊 b，
入邊和 = 出邊和（區塊內、差分層）。 -/
theorem dF96_flow_clean (x : ℕ) (b : ℕ) (g : ℕ × Phase × ℕ × ℕ)
    (hI : g ≠ ((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)))
    (h0 : g ≠ ((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)))
    (h1 : g ≠ ((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ))) :
    ((inEdges3 g).map (fun e => dF96 x b e)).sum = dF96 x b (g, 0) + dF96 x b (g, 1) := by
  unfold dF96
  rw [sum_map_sub, sum_map_ite, sum_map_ite,
    kirchhoff_E3_clean (Todd x) g hI h0 h1, kirchhoff_E3_clean x g hI h0 h1]
  split_ifs <;> ring

/-! ## §77 第 65 條：`f_start` 跨區塊重組 -/

/-- 兩區塊求和把模式指示消掉（`mode3 ∈ {0,1}` 由定義保證）。 -/
theorem sum_blocks (x : ℕ) (k : (ℕ × Phase × ℕ × ℕ) × ℕ) :
    dF96 x 0 k + dF96 x 1 k = E3 (Todd x) k - E3 x k := by
  unfold dF96
  rcases mode3_cases (Todd x) with hy | hy <;> rcases mode3_cases x with hx | hx <;>
    rw [hy, hx] <;> norm_num <;> ring

/-- **第 65 條**：初始狀態 `(1,K,0,0)` 的流守恆對兩區塊求和。
兩端的 kirchhoff 常數 −1（初始指示）在相減時對消——不需要任何模式分析。
（單獨一個區塊時這條**不**成立：常數 −1 會乘上模式翻轉指示。） -/
theorem dF96_fstart (x : ℕ) :
    (dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
        - dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
        - dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1))
      + (dF96 x 1 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
        - dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
        - dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1)) = 0 := by
  have hx := kirchhoff_occ3_extIn x ((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ))
  have hy := kirchhoff_occ3_extIn (Todd x) ((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ))
  simp only [show inEdges3 ((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ))
      = [(((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hx hy
  have htx : run3 (1, Phase.K, 0, 0) (extIn x) ≠ ((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)) := by
    rcases run3_extIn_terminal x with h | h <;> rw [h] <;> decide
  have hty : run3 (1, Phase.K, 0, 0) (extIn (Todd x))
      ≠ ((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)) := by
    rcases run3_extIn_terminal (Todd x) with h | h <;> rw [h] <;> decide
  rw [if_neg htx] at hx
  rw [if_neg hty] at hy
  have s1 := sum_blocks x (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
  have s2 := sum_blocks x (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
  have s3 := sum_blocks x (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1)
  unfold E3 at s1 s2 s3
  have hx' : (occ3 (1, Phase.K, 0, 0) (extIn x)
        (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) : ℚ) + 1
      = (occ3 (1, Phase.K, 0, 0) (extIn x) (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) : ℚ)
        + (occ3 (1, Phase.K, 0, 0) (extIn x)
            (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) : ℚ) := by
    exact_mod_cast hx
  have hy' : (occ3 (1, Phase.K, 0, 0) (extIn (Todd x))
        (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) : ℚ) + 1
      = (occ3 (1, Phase.K, 0, 0) (extIn (Todd x))
            (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) : ℚ)
        + (occ3 (1, Phase.K, 0, 0) (extIn (Todd x))
            (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) : ℚ) := by
    exact_mod_cast hy
  linarith [s1, s2, s3]

/-! ## §78 數值回歸（`#guard` 失敗即 build 紅）

掃 x < 40，涵蓋 x = 0、1 與偶數（差分層對所有 x 成立）。 -/

section Verification

-- 提升死座標（抽兩個死態代表 × 兩區塊）
#guard (List.range 40).all fun x =>
  [0, 1].all fun b =>
    decide (dF96 x b (((0 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 0) = 0)
      && decide (dF96 x b (((0 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 1) = 0)

-- 區塊相依死座標
#guard (List.range 40).all fun x =>
  decide (dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 0)
    && decide (dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) = 0)

-- 提升乾淨流守恆（抽 (2,K,0,0) 與 (1,S,1,1) 兩個代表 × 兩區塊）
#guard (List.range 40).all fun x =>
  [0, 1].all fun b =>
    decide (((inEdges3 ((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ))).map
          (fun e => dF96 x b e)).sum
        = dF96 x b (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
          + dF96 x b (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1))
      && decide (((inEdges3 ((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ))).map
          (fun e => dF96 x b e)).sum
        = dF96 x b (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0)
          + dF96 x b (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1))

-- 第 65 條（f_start 跨區塊）
#guard (List.range 40).all fun x =>
  decide ((dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
      - dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
      - dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1))
    + (dF96 x 1 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
      - dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0)
      - dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1)) = 0)

end Verification

end CollatzFST.L3
