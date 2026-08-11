/-
# B1.5 per-(mode, terminal) 仿射勢能不可行性（Level 3，**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_L3_2Mode_NoGo.lean`
（模板與 A-2 證法血統）與 `Collatz_FST_L3_Flow.lean`（終末狀態定理）。

## 主定理

`no_go_level3_2mode_terminal_affine_potential`（ROADMAP-B B1.5）：Level 3
雙模式勢能的截距升級為 per-(mode, terminal) 的 β_(m,t)（4 個，無符號約束），
仍不能在 W26 的每一步嚴格下降。

終末觀測量 t(x) = `(run3 (1,K,0,0) (extIn x)).2.2.1`——狀態第三分量
（`run3_fst` 簽名中的 `h₂`，倒數第二個輸出位；注意 tools/certificates.py 的
`KEYS_L3` 把同一槽位叫 `h1`，兩套命名相反，本檔以 Lean 端 `L3_Flow` 為準）。
`run3_extIn_terminal` 證終末恆為 (0,S,0,1)/(0,S,1,0)，兩態於此位取 0/1，
且第四分量 = 1 − 第三分量，故單一位忠實編碼終末（`terminal_bit_faithful3`）。

## 憑證

λ = (324933258, 68950678, 580696143, 506947154, 489030970, 831689147, 474825962, 613976452, 585136222, 51271520, 452045333, 467676557, 220147089, 161505288, 6408940, 381461112, 238934519, 895971728, 5016178, 379378979, 392227128, 106062111, 451013313, 76907280, 804321970, 25635760)，Σλ = 9592170791。
錨：`tools/certificates.py --b15`；推導：`tools/search/b15_exact_balance.py`。
既有 W₂₀ 憑證終末不平衡 ±753（`tools/b15_terminal_balance.py`），
故此升級需要**新見證集**——W26 與 W₂₀ 不相交。

## 證明骨架（同 A-2 血統）

* 26 條 `Todd_x`；50 條 `F3_n` 求值（`decide`；W26 有兩個見證的 Todd 像
  也是見證——1819→2729、2427→3641——端點去重後 50 個）。
* 雙層 if 消去 → 26 條嚴格負假設 → `key` 恆等式（`ring`，β 項因四條
  per-(m,t) 平衡對消）→ 十九項非負聚合 vs 0 ≤ −9592170791 矛盾。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_2Mode_NoGo
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_Flow

namespace CollatzFST.L3

open CollatzFST

/-- 終末位忠實編碼終末狀態：`run3` 讀完 `extIn x` 的狀態由其第三分量完全決定，
且第四分量 = 1 − 第三分量（`run3_extIn_terminal` 的重述）。 -/
lemma terminal_bit_faithful3 (x : ℕ) :
    run3 (1, Phase.K, 0, 0) (extIn x)
      = ((0 : ℕ), Phase.S, (run3 (1, Phase.K, 0, 0) (extIn x)).2.2.1,
         1 - (run3 (1, Phase.K, 0, 0) (extIn x)).2.2.1) := by
  rcases run3_extIn_terminal x with h | h <;> rw [h] <;> rfl

/-- B1.5 Level 3 雙平衡見證集（26 個奇數；ROADMAP-B B1.5）。 -/
def W26 : List ℕ := [37, 487, 527, 779, 1423, 1819, 1911, 2091, 2209, 2337, 2407, 2427, 2457, 2505, 2721, 2729, 2735, 2863, 3255, 3343, 3377, 3639, 3641, 3825, 3913, 3937]

/-- (x, Todd x, λ, m(x), m(y), t(x), t(y))；回歸驗證用。 Σλ = 9592170791。 -/
def cert26 : List (ℕ × ℕ × ℤ × ℤ × ℤ × ℕ × ℕ) :=
  [(37, 7, 324933258, 0, 1, 1, 0), (487, 731, 68950678, 1, 1, 0, 0), (527, 791, 580696143, 1, 1, 1, 0), (779, 1169, 506947154, 1, 0, 0, 1), (1423, 2135, 489030970, 1, 1, 0, 1), (1819, 2729, 831689147, 1, 0, 0, 1), (1911, 2867, 474825962, 1, 1, 0, 0), (2091, 3137, 613976452, 1, 0, 1, 0), (2209, 1657, 585136222, 0, 0, 1, 0), (2337, 1753, 51271520, 0, 0, 1, 0), (2407, 3611, 452045333, 1, 1, 1, 0), (2427, 3641, 467676557, 1, 0, 1, 0), (2457, 1843, 220147089, 0, 1, 1, 0), (2505, 1879, 161505288, 0, 1, 1, 0), (2721, 2041, 6408940, 0, 0, 1, 0), (2729, 2047, 381461112, 0, 1, 1, 0), (2735, 4103, 238934519, 1, 1, 0, 1), (2863, 4295, 895971728, 1, 1, 0, 1), (3255, 4883, 5016178, 1, 1, 0, 1), (3343, 5015, 379378979, 1, 1, 0, 1), (3377, 2533, 392227128, 0, 0, 0, 1), (3639, 5459, 106062111, 1, 1, 0, 1), (3641, 2731, 451013313, 0, 1, 0, 0), (3825, 2869, 76907280, 0, 1, 0, 0), (3913, 2935, 804321970, 0, 1, 0, 0), (3937, 2953, 25635760, 0, 0, 0, 0)]

/-! ## Todd 值（26 條） -/

lemma Todd_37 : Todd 37 = 7 := by
  have hv : padicValNat 2 (3 * 37 + 1) = 4 := by
    rw [show (3 * 37 + 1 : ℕ) = 2 ^ 4 * 7 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_487 : Todd 487 = 731 := by
  have hv : padicValNat 2 (3 * 487 + 1) = 1 := by
    rw [show (3 * 487 + 1 : ℕ) = 2 ^ 1 * 731 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_527 : Todd 527 = 791 := by
  have hv : padicValNat 2 (3 * 527 + 1) = 1 := by
    rw [show (3 * 527 + 1 : ℕ) = 2 ^ 1 * 791 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_779 : Todd 779 = 1169 := by
  have hv : padicValNat 2 (3 * 779 + 1) = 1 := by
    rw [show (3 * 779 + 1 : ℕ) = 2 ^ 1 * 1169 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_1423 : Todd 1423 = 2135 := by
  have hv : padicValNat 2 (3 * 1423 + 1) = 1 := by
    rw [show (3 * 1423 + 1 : ℕ) = 2 ^ 1 * 2135 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_1819 : Todd 1819 = 2729 := by
  have hv : padicValNat 2 (3 * 1819 + 1) = 1 := by
    rw [show (3 * 1819 + 1 : ℕ) = 2 ^ 1 * 2729 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_1911 : Todd 1911 = 2867 := by
  have hv : padicValNat 2 (3 * 1911 + 1) = 1 := by
    rw [show (3 * 1911 + 1 : ℕ) = 2 ^ 1 * 2867 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2091 : Todd 2091 = 3137 := by
  have hv : padicValNat 2 (3 * 2091 + 1) = 1 := by
    rw [show (3 * 2091 + 1 : ℕ) = 2 ^ 1 * 3137 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2209 : Todd 2209 = 1657 := by
  have hv : padicValNat 2 (3 * 2209 + 1) = 2 := by
    rw [show (3 * 2209 + 1 : ℕ) = 2 ^ 2 * 1657 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2337 : Todd 2337 = 1753 := by
  have hv : padicValNat 2 (3 * 2337 + 1) = 2 := by
    rw [show (3 * 2337 + 1 : ℕ) = 2 ^ 2 * 1753 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2407 : Todd 2407 = 3611 := by
  have hv : padicValNat 2 (3 * 2407 + 1) = 1 := by
    rw [show (3 * 2407 + 1 : ℕ) = 2 ^ 1 * 3611 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2427 : Todd 2427 = 3641 := by
  have hv : padicValNat 2 (3 * 2427 + 1) = 1 := by
    rw [show (3 * 2427 + 1 : ℕ) = 2 ^ 1 * 3641 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2457 : Todd 2457 = 1843 := by
  have hv : padicValNat 2 (3 * 2457 + 1) = 2 := by
    rw [show (3 * 2457 + 1 : ℕ) = 2 ^ 2 * 1843 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2505 : Todd 2505 = 1879 := by
  have hv : padicValNat 2 (3 * 2505 + 1) = 2 := by
    rw [show (3 * 2505 + 1 : ℕ) = 2 ^ 2 * 1879 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2721 : Todd 2721 = 2041 := by
  have hv : padicValNat 2 (3 * 2721 + 1) = 2 := by
    rw [show (3 * 2721 + 1 : ℕ) = 2 ^ 2 * 2041 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2729 : Todd 2729 = 2047 := by
  have hv : padicValNat 2 (3 * 2729 + 1) = 2 := by
    rw [show (3 * 2729 + 1 : ℕ) = 2 ^ 2 * 2047 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2735 : Todd 2735 = 4103 := by
  have hv : padicValNat 2 (3 * 2735 + 1) = 1 := by
    rw [show (3 * 2735 + 1 : ℕ) = 2 ^ 1 * 4103 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2863 : Todd 2863 = 4295 := by
  have hv : padicValNat 2 (3 * 2863 + 1) = 1 := by
    rw [show (3 * 2863 + 1 : ℕ) = 2 ^ 1 * 4295 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3255 : Todd 3255 = 4883 := by
  have hv : padicValNat 2 (3 * 3255 + 1) = 1 := by
    rw [show (3 * 3255 + 1 : ℕ) = 2 ^ 1 * 4883 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3343 : Todd 3343 = 5015 := by
  have hv : padicValNat 2 (3 * 3343 + 1) = 1 := by
    rw [show (3 * 3343 + 1 : ℕ) = 2 ^ 1 * 5015 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3377 : Todd 3377 = 2533 := by
  have hv : padicValNat 2 (3 * 3377 + 1) = 2 := by
    rw [show (3 * 3377 + 1 : ℕ) = 2 ^ 2 * 2533 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3639 : Todd 3639 = 5459 := by
  have hv : padicValNat 2 (3 * 3639 + 1) = 1 := by
    rw [show (3 * 3639 + 1 : ℕ) = 2 ^ 1 * 5459 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3641 : Todd 3641 = 2731 := by
  have hv : padicValNat 2 (3 * 3641 + 1) = 2 := by
    rw [show (3 * 3641 + 1 : ℕ) = 2 ^ 2 * 2731 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3825 : Todd 3825 = 2869 := by
  have hv : padicValNat 2 (3 * 3825 + 1) = 2 := by
    rw [show (3 * 3825 + 1 : ℕ) = 2 ^ 2 * 2869 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3913 : Todd 3913 = 2935 := by
  have hv : padicValNat 2 (3 * 3913 + 1) = 2 := by
    rw [show (3 * 3913 + 1 : ℕ) = 2 ^ 2 * 2935 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3937 : Todd 3937 = 2953 := by
  have hv : padicValNat 2 (3 * 3937 + 1) = 2 := by
    rw [show (3 * 3937 + 1 : ℕ) = 2 ^ 2 * 2953 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num

/-! ## F3 求值與模式／終末位引理（50 個相異端點） -/

lemma F3_37 : F3 37 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
lemma F3_7 : F3 7 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0] := by decide
lemma F3_487 : F3 487 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0] := by decide
lemma F3_731 : F3 731 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0] := by decide
lemma F3_527 : F3 527 = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1] := by decide
lemma F3_791 : F3 791 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0] := by decide
lemma F3_779 : F3 779 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0] := by decide
lemma F3_1169 : F3 1169 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 3, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
lemma F3_1423 : F3 1423 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1] := by decide
lemma F3_2135 : F3 2135 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0] := by decide
lemma F3_1819 : F3 1819 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1, 0, 0] := by decide
lemma F3_2729 : F3 2729 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 4, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
lemma F3_1911 : F3 1911 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 3, 0] := by decide
lemma F3_2867 : F3 2867 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0] := by decide
lemma F3_2091 : F3 2091 = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0] := by decide
lemma F3_3137 : F3 3137 = [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by decide
lemma F3_2209 : F3 2209 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
lemma F3_1657 : F3 1657 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0] := by decide
lemma F3_2337 : F3 2337 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 3, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
lemma F3_1753 : F3 1753 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0] := by decide
lemma F3_2407 : F3 2407 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0] := by decide
lemma F3_3611 : F3 3611 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1, 0, 0] := by decide
lemma F3_2427 : F3 2427 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1] := by decide
lemma F3_3641 : F3 3641 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0] := by decide
lemma F3_2457 : F3 2457 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0] := by decide
lemma F3_1843 : F3 1843 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0] := by decide
lemma F3_2505 : F3 2505 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0] := by decide
lemma F3_1879 : F3 1879 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 2, 0] := by decide
lemma F3_2721 : F3 2721 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
lemma F3_2041 : F3 2041 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 4] := by decide
lemma F3_2047 : F3 2047 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 8] := by decide
lemma F3_2735 : F3 2735 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 1, 1] := by decide
lemma F3_4103 : F3 4103 = [0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0] := by decide
lemma F3_2863 : F3 2863 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 1, 1] := by decide
lemma F3_4295 : F3 4295 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0] := by decide
lemma F3_3255 : F3 3255 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0] := by decide
lemma F3_4883 : F3 4883 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] := by decide
lemma F3_3343 : F3 3343 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1] := by decide
lemma F3_5015 : F3 5015 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0] := by decide
lemma F3_3377 : F3 3377 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0] := by decide
lemma F3_2533 : F3 2533 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0] := by decide
lemma F3_3639 : F3 3639 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 1, 1, 0] := by decide
lemma F3_5459 : F3 5459 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by decide
lemma F3_2731 : F3 2731 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 5, 0, 1, 0, 0, 0, 0, 0] := by decide
lemma F3_3825 : F3 3825 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 2, 0] := by decide
lemma F3_2869 : F3 2869 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0] := by decide
lemma F3_3913 : F3 3913 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0] := by decide
lemma F3_2935 : F3 2935 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 2, 0] := by decide
lemma F3_3937 : F3 3937 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1] := by decide
lemma F3_2953 : F3 2953 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0] := by decide

lemma hm_37 : ¬ (F3 37).getD 33 0 = 1 := by rw [F3_37]; decide
lemma hm_7 : (F3 7).getD 33 0 = 1 := by rw [F3_7]; decide
lemma hm_487 : (F3 487).getD 33 0 = 1 := by rw [F3_487]; decide
lemma hm_731 : (F3 731).getD 33 0 = 1 := by rw [F3_731]; decide
lemma hm_527 : (F3 527).getD 33 0 = 1 := by rw [F3_527]; decide
lemma hm_791 : (F3 791).getD 33 0 = 1 := by rw [F3_791]; decide
lemma hm_779 : (F3 779).getD 33 0 = 1 := by rw [F3_779]; decide
lemma hm_1169 : ¬ (F3 1169).getD 33 0 = 1 := by rw [F3_1169]; decide
lemma hm_1423 : (F3 1423).getD 33 0 = 1 := by rw [F3_1423]; decide
lemma hm_2135 : (F3 2135).getD 33 0 = 1 := by rw [F3_2135]; decide
lemma hm_1819 : (F3 1819).getD 33 0 = 1 := by rw [F3_1819]; decide
lemma hm_2729 : ¬ (F3 2729).getD 33 0 = 1 := by rw [F3_2729]; decide
lemma hm_1911 : (F3 1911).getD 33 0 = 1 := by rw [F3_1911]; decide
lemma hm_2867 : (F3 2867).getD 33 0 = 1 := by rw [F3_2867]; decide
lemma hm_2091 : (F3 2091).getD 33 0 = 1 := by rw [F3_2091]; decide
lemma hm_3137 : ¬ (F3 3137).getD 33 0 = 1 := by rw [F3_3137]; decide
lemma hm_2209 : ¬ (F3 2209).getD 33 0 = 1 := by rw [F3_2209]; decide
lemma hm_1657 : ¬ (F3 1657).getD 33 0 = 1 := by rw [F3_1657]; decide
lemma hm_2337 : ¬ (F3 2337).getD 33 0 = 1 := by rw [F3_2337]; decide
lemma hm_1753 : ¬ (F3 1753).getD 33 0 = 1 := by rw [F3_1753]; decide
lemma hm_2407 : (F3 2407).getD 33 0 = 1 := by rw [F3_2407]; decide
lemma hm_3611 : (F3 3611).getD 33 0 = 1 := by rw [F3_3611]; decide
lemma hm_2427 : (F3 2427).getD 33 0 = 1 := by rw [F3_2427]; decide
lemma hm_3641 : ¬ (F3 3641).getD 33 0 = 1 := by rw [F3_3641]; decide
lemma hm_2457 : ¬ (F3 2457).getD 33 0 = 1 := by rw [F3_2457]; decide
lemma hm_1843 : (F3 1843).getD 33 0 = 1 := by rw [F3_1843]; decide
lemma hm_2505 : ¬ (F3 2505).getD 33 0 = 1 := by rw [F3_2505]; decide
lemma hm_1879 : (F3 1879).getD 33 0 = 1 := by rw [F3_1879]; decide
lemma hm_2721 : ¬ (F3 2721).getD 33 0 = 1 := by rw [F3_2721]; decide
lemma hm_2041 : ¬ (F3 2041).getD 33 0 = 1 := by rw [F3_2041]; decide
lemma hm_2047 : (F3 2047).getD 33 0 = 1 := by rw [F3_2047]; decide
lemma hm_2735 : (F3 2735).getD 33 0 = 1 := by rw [F3_2735]; decide
lemma hm_4103 : (F3 4103).getD 33 0 = 1 := by rw [F3_4103]; decide
lemma hm_2863 : (F3 2863).getD 33 0 = 1 := by rw [F3_2863]; decide
lemma hm_4295 : (F3 4295).getD 33 0 = 1 := by rw [F3_4295]; decide
lemma hm_3255 : (F3 3255).getD 33 0 = 1 := by rw [F3_3255]; decide
lemma hm_4883 : (F3 4883).getD 33 0 = 1 := by rw [F3_4883]; decide
lemma hm_3343 : (F3 3343).getD 33 0 = 1 := by rw [F3_3343]; decide
lemma hm_5015 : (F3 5015).getD 33 0 = 1 := by rw [F3_5015]; decide
lemma hm_3377 : ¬ (F3 3377).getD 33 0 = 1 := by rw [F3_3377]; decide
lemma hm_2533 : ¬ (F3 2533).getD 33 0 = 1 := by rw [F3_2533]; decide
lemma hm_3639 : (F3 3639).getD 33 0 = 1 := by rw [F3_3639]; decide
lemma hm_5459 : (F3 5459).getD 33 0 = 1 := by rw [F3_5459]; decide
lemma hm_2731 : (F3 2731).getD 33 0 = 1 := by rw [F3_2731]; decide
lemma hm_3825 : ¬ (F3 3825).getD 33 0 = 1 := by rw [F3_3825]; decide
lemma hm_2869 : (F3 2869).getD 33 0 = 1 := by rw [F3_2869]; decide
lemma hm_3913 : ¬ (F3 3913).getD 33 0 = 1 := by rw [F3_3913]; decide
lemma hm_2935 : (F3 2935).getD 33 0 = 1 := by rw [F3_2935]; decide
lemma hm_3937 : ¬ (F3 3937).getD 33 0 = 1 := by rw [F3_3937]; decide
lemma hm_2953 : ¬ (F3 2953).getD 33 0 = 1 := by rw [F3_2953]; decide

lemma ht_37 : (run3 (1, Phase.K, 0, 0) (extIn 37)).2.2.1 = 1 := by decide
lemma ht_7 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 7)).2.2.1 = 1 := by decide
lemma ht_487 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 487)).2.2.1 = 1 := by decide
lemma ht_731 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 731)).2.2.1 = 1 := by decide
lemma ht_527 : (run3 (1, Phase.K, 0, 0) (extIn 527)).2.2.1 = 1 := by decide
lemma ht_791 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 791)).2.2.1 = 1 := by decide
lemma ht_779 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 779)).2.2.1 = 1 := by decide
lemma ht_1169 : (run3 (1, Phase.K, 0, 0) (extIn 1169)).2.2.1 = 1 := by decide
lemma ht_1423 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 1423)).2.2.1 = 1 := by decide
lemma ht_2135 : (run3 (1, Phase.K, 0, 0) (extIn 2135)).2.2.1 = 1 := by decide
lemma ht_1819 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 1819)).2.2.1 = 1 := by decide
lemma ht_2729 : (run3 (1, Phase.K, 0, 0) (extIn 2729)).2.2.1 = 1 := by decide
lemma ht_1911 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 1911)).2.2.1 = 1 := by decide
lemma ht_2867 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 2867)).2.2.1 = 1 := by decide
lemma ht_2091 : (run3 (1, Phase.K, 0, 0) (extIn 2091)).2.2.1 = 1 := by decide
lemma ht_3137 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 3137)).2.2.1 = 1 := by decide
lemma ht_2209 : (run3 (1, Phase.K, 0, 0) (extIn 2209)).2.2.1 = 1 := by decide
lemma ht_1657 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 1657)).2.2.1 = 1 := by decide
lemma ht_2337 : (run3 (1, Phase.K, 0, 0) (extIn 2337)).2.2.1 = 1 := by decide
lemma ht_1753 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 1753)).2.2.1 = 1 := by decide
lemma ht_2407 : (run3 (1, Phase.K, 0, 0) (extIn 2407)).2.2.1 = 1 := by decide
lemma ht_3611 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 3611)).2.2.1 = 1 := by decide
lemma ht_2427 : (run3 (1, Phase.K, 0, 0) (extIn 2427)).2.2.1 = 1 := by decide
lemma ht_3641 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 3641)).2.2.1 = 1 := by decide
lemma ht_2457 : (run3 (1, Phase.K, 0, 0) (extIn 2457)).2.2.1 = 1 := by decide
lemma ht_1843 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 1843)).2.2.1 = 1 := by decide
lemma ht_2505 : (run3 (1, Phase.K, 0, 0) (extIn 2505)).2.2.1 = 1 := by decide
lemma ht_1879 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 1879)).2.2.1 = 1 := by decide
lemma ht_2721 : (run3 (1, Phase.K, 0, 0) (extIn 2721)).2.2.1 = 1 := by decide
lemma ht_2041 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 2041)).2.2.1 = 1 := by decide
lemma ht_2047 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 2047)).2.2.1 = 1 := by decide
lemma ht_2735 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 2735)).2.2.1 = 1 := by decide
lemma ht_4103 : (run3 (1, Phase.K, 0, 0) (extIn 4103)).2.2.1 = 1 := by decide
lemma ht_2863 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 2863)).2.2.1 = 1 := by decide
lemma ht_4295 : (run3 (1, Phase.K, 0, 0) (extIn 4295)).2.2.1 = 1 := by decide
lemma ht_3255 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 3255)).2.2.1 = 1 := by decide
lemma ht_4883 : (run3 (1, Phase.K, 0, 0) (extIn 4883)).2.2.1 = 1 := by decide
lemma ht_3343 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 3343)).2.2.1 = 1 := by decide
lemma ht_5015 : (run3 (1, Phase.K, 0, 0) (extIn 5015)).2.2.1 = 1 := by decide
lemma ht_3377 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 3377)).2.2.1 = 1 := by decide
lemma ht_2533 : (run3 (1, Phase.K, 0, 0) (extIn 2533)).2.2.1 = 1 := by decide
lemma ht_3639 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 3639)).2.2.1 = 1 := by decide
lemma ht_5459 : (run3 (1, Phase.K, 0, 0) (extIn 5459)).2.2.1 = 1 := by decide
lemma ht_2731 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 2731)).2.2.1 = 1 := by decide
lemma ht_3825 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 3825)).2.2.1 = 1 := by decide
lemma ht_2869 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 2869)).2.2.1 = 1 := by decide
lemma ht_3913 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 3913)).2.2.1 = 1 := by decide
lemma ht_2935 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 2935)).2.2.1 = 1 := by decide
lemma ht_3937 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 3937)).2.2.1 = 1 := by decide
lemma ht_2953 : ¬ (run3 (1, Phase.K, 0, 0) (extIn 2953)).2.2.1 = 1 := by decide

/-- 模式為位元（同 `mode_bit_endpoints3`，52 端點）。 -/
lemma mode_bit_endpoints_W26 :
    ∀ n ∈ (cert26.flatMap fun t => [t.1, t.2.1]),
      (F3 n).getD 16 0 + (F3 n).getD 33 0 = 1 := by decide

private lemma addneg {a b : ℚ} (ha : a < 0) (hb : b < 0) : a + b < 0 := by
  have h := add_lt_add ha hb
  simpa using h

/-- **主定理**（ROADMAP-B B1.5）：截距升級為 per-(mode, terminal) 的
β_(m,t)（2 × 2 = 4 個，**無符號約束**），非負權重的雙模式仿射勢能仍不能在
W26 的每一步嚴格下降。β 項對消依賴四條 per-(m,t) 平衡精確成立
（`tools/certificates.py --b15`）；終末位忠實編碼終末狀態，見
`terminal_bit_faithful3`。 -/
theorem no_go_level3_2mode_terminal_affine_potential :
    ¬ ∃ (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 48 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W26,
        (if (F3 (Todd x)).getD 33 0 = 1
           then (if (run3 (1, Phase.K, 0, 0) (extIn (Todd x))).2.2.1 = 1 then β₁₁ else β₁₀)
                  + dot48 θ₁ (F3 (Todd x))
           else (if (run3 (1, Phase.K, 0, 0) (extIn (Todd x))).2.2.1 = 1 then β₀₁ else β₀₀)
                  + dot48 θ₀ (F3 (Todd x)))
          - (if (F3 x).getD 33 0 = 1
           then (if (run3 (1, Phase.K, 0, 0) (extIn x)).2.2.1 = 1 then β₁₁ else β₁₀)
                  + dot48 θ₁ (F3 x)
           else (if (run3 (1, Phase.K, 0, 0) (extIn x)).2.2.1 = 1 then β₀₁ else β₀₀)
                  + dot48 θ₀ (F3 x)) < 0 := by
  rintro ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, hθ₀, hθ₁, hdesc⟩
  have h1 := hdesc 37 (by decide)
  have h2 := hdesc 487 (by decide)
  have h3 := hdesc 527 (by decide)
  have h4 := hdesc 779 (by decide)
  have h5 := hdesc 1423 (by decide)
  have h6 := hdesc 1819 (by decide)
  have h7 := hdesc 1911 (by decide)
  have h8 := hdesc 2091 (by decide)
  have h9 := hdesc 2209 (by decide)
  have h10 := hdesc 2337 (by decide)
  have h11 := hdesc 2407 (by decide)
  have h12 := hdesc 2427 (by decide)
  have h13 := hdesc 2457 (by decide)
  have h14 := hdesc 2505 (by decide)
  have h15 := hdesc 2721 (by decide)
  have h16 := hdesc 2729 (by decide)
  have h17 := hdesc 2735 (by decide)
  have h18 := hdesc 2863 (by decide)
  have h19 := hdesc 3255 (by decide)
  have h20 := hdesc 3343 (by decide)
  have h21 := hdesc 3377 (by decide)
  have h22 := hdesc 3639 (by decide)
  have h23 := hdesc 3641 (by decide)
  have h24 := hdesc 3825 (by decide)
  have h25 := hdesc 3913 (by decide)
  have h26 := hdesc 3937 (by decide)
  rw [Todd_37, if_pos hm_7, if_neg hm_37, if_neg ht_7, if_pos ht_37] at h1
  rw [Todd_487, if_pos hm_731, if_pos hm_487, if_neg ht_731, if_neg ht_487] at h2
  rw [Todd_527, if_pos hm_791, if_pos hm_527, if_neg ht_791, if_pos ht_527] at h3
  rw [Todd_779, if_neg hm_1169, if_pos hm_779, if_pos ht_1169, if_neg ht_779] at h4
  rw [Todd_1423, if_pos hm_2135, if_pos hm_1423, if_pos ht_2135, if_neg ht_1423] at h5
  rw [Todd_1819, if_neg hm_2729, if_pos hm_1819, if_pos ht_2729, if_neg ht_1819] at h6
  rw [Todd_1911, if_pos hm_2867, if_pos hm_1911, if_neg ht_2867, if_neg ht_1911] at h7
  rw [Todd_2091, if_neg hm_3137, if_pos hm_2091, if_neg ht_3137, if_pos ht_2091] at h8
  rw [Todd_2209, if_neg hm_1657, if_neg hm_2209, if_neg ht_1657, if_pos ht_2209] at h9
  rw [Todd_2337, if_neg hm_1753, if_neg hm_2337, if_neg ht_1753, if_pos ht_2337] at h10
  rw [Todd_2407, if_pos hm_3611, if_pos hm_2407, if_neg ht_3611, if_pos ht_2407] at h11
  rw [Todd_2427, if_neg hm_3641, if_pos hm_2427, if_neg ht_3641, if_pos ht_2427] at h12
  rw [Todd_2457, if_pos hm_1843, if_neg hm_2457, if_neg ht_1843, if_pos ht_2457] at h13
  rw [Todd_2505, if_pos hm_1879, if_neg hm_2505, if_neg ht_1879, if_pos ht_2505] at h14
  rw [Todd_2721, if_neg hm_2041, if_neg hm_2721, if_neg ht_2041, if_pos ht_2721] at h15
  rw [Todd_2729, if_pos hm_2047, if_neg hm_2729, if_neg ht_2047, if_pos ht_2729] at h16
  rw [Todd_2735, if_pos hm_4103, if_pos hm_2735, if_pos ht_4103, if_neg ht_2735] at h17
  rw [Todd_2863, if_pos hm_4295, if_pos hm_2863, if_pos ht_4295, if_neg ht_2863] at h18
  rw [Todd_3255, if_pos hm_4883, if_pos hm_3255, if_pos ht_4883, if_neg ht_3255] at h19
  rw [Todd_3343, if_pos hm_5015, if_pos hm_3343, if_pos ht_5015, if_neg ht_3343] at h20
  rw [Todd_3377, if_neg hm_2533, if_neg hm_3377, if_pos ht_2533, if_neg ht_3377] at h21
  rw [Todd_3639, if_pos hm_5459, if_pos hm_3639, if_pos ht_5459, if_neg ht_3639] at h22
  rw [Todd_3641, if_pos hm_2731, if_neg hm_3641, if_neg ht_2731, if_neg ht_3641] at h23
  rw [Todd_3825, if_pos hm_2869, if_neg hm_3825, if_neg ht_2869, if_neg ht_3825] at h24
  rw [Todd_3913, if_pos hm_2935, if_neg hm_3913, if_neg ht_2935, if_neg ht_3913] at h25
  rw [Todd_3937, if_neg hm_2953, if_neg hm_3937, if_neg ht_2953, if_neg ht_3937] at h26
  have t1 : (324933258 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 7)) - (β₀₁ + dot48 θ₀ (F3 37))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h1
  have t2 : (68950678 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 731)) - (β₁₀ + dot48 θ₁ (F3 487))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h2
  have t3 : (580696143 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 791)) - (β₁₁ + dot48 θ₁ (F3 527))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h3
  have t4 : (506947154 : ℚ) * ((β₀₁ + dot48 θ₀ (F3 1169)) - (β₁₀ + dot48 θ₁ (F3 779))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h4
  have t5 : (489030970 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 2135)) - (β₁₀ + dot48 θ₁ (F3 1423))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h5
  have t6 : (831689147 : ℚ) * ((β₀₁ + dot48 θ₀ (F3 2729)) - (β₁₀ + dot48 θ₁ (F3 1819))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h6
  have t7 : (474825962 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2867)) - (β₁₀ + dot48 θ₁ (F3 1911))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h7
  have t8 : (613976452 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 3137)) - (β₁₁ + dot48 θ₁ (F3 2091))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h8
  have t9 : (585136222 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 1657)) - (β₀₁ + dot48 θ₀ (F3 2209))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h9
  have t10 : (51271520 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 1753)) - (β₀₁ + dot48 θ₀ (F3 2337))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h10
  have t11 : (452045333 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 3611)) - (β₁₁ + dot48 θ₁ (F3 2407))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h11
  have t12 : (467676557 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 3641)) - (β₁₁ + dot48 θ₁ (F3 2427))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h12
  have t13 : (220147089 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 1843)) - (β₀₁ + dot48 θ₀ (F3 2457))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h13
  have t14 : (161505288 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 1879)) - (β₀₁ + dot48 θ₀ (F3 2505))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h14
  have t15 : (6408940 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 2041)) - (β₀₁ + dot48 θ₀ (F3 2721))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h15
  have t16 : (381461112 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2047)) - (β₀₁ + dot48 θ₀ (F3 2729))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h16
  have t17 : (238934519 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 4103)) - (β₁₀ + dot48 θ₁ (F3 2735))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h17
  have t18 : (895971728 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 4295)) - (β₁₀ + dot48 θ₁ (F3 2863))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h18
  have t19 : (5016178 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 4883)) - (β₁₀ + dot48 θ₁ (F3 3255))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h19
  have t20 : (379378979 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 5015)) - (β₁₀ + dot48 θ₁ (F3 3343))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h20
  have t21 : (392227128 : ℚ) * ((β₀₁ + dot48 θ₀ (F3 2533)) - (β₀₀ + dot48 θ₀ (F3 3377))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h21
  have t22 : (106062111 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 5459)) - (β₁₀ + dot48 θ₁ (F3 3639))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h22
  have t23 : (451013313 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2731)) - (β₀₀ + dot48 θ₀ (F3 3641))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h23
  have t24 : (76907280 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2869)) - (β₀₀ + dot48 θ₀ (F3 3825))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h24
  have t25 : (804321970 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2935)) - (β₀₀ + dot48 θ₀ (F3 3913))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h25
  have t26 : (25635760 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 2953)) - (β₀₀ + dot48 θ₀ (F3 3937))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h26
  have hlt :
      (324933258 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 7)) - (β₀₁ + dot48 θ₀ (F3 37)))
      + (68950678 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 731)) - (β₁₀ + dot48 θ₁ (F3 487)))
      + (580696143 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 791)) - (β₁₁ + dot48 θ₁ (F3 527)))
      + (506947154 : ℚ) * ((β₀₁ + dot48 θ₀ (F3 1169)) - (β₁₀ + dot48 θ₁ (F3 779)))
      + (489030970 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 2135)) - (β₁₀ + dot48 θ₁ (F3 1423)))
      + (831689147 : ℚ) * ((β₀₁ + dot48 θ₀ (F3 2729)) - (β₁₀ + dot48 θ₁ (F3 1819)))
      + (474825962 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2867)) - (β₁₀ + dot48 θ₁ (F3 1911)))
      + (613976452 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 3137)) - (β₁₁ + dot48 θ₁ (F3 2091)))
      + (585136222 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 1657)) - (β₀₁ + dot48 θ₀ (F3 2209)))
      + (51271520 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 1753)) - (β₀₁ + dot48 θ₀ (F3 2337)))
      + (452045333 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 3611)) - (β₁₁ + dot48 θ₁ (F3 2407)))
      + (467676557 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 3641)) - (β₁₁ + dot48 θ₁ (F3 2427)))
      + (220147089 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 1843)) - (β₀₁ + dot48 θ₀ (F3 2457)))
      + (161505288 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 1879)) - (β₀₁ + dot48 θ₀ (F3 2505)))
      + (6408940 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 2041)) - (β₀₁ + dot48 θ₀ (F3 2721)))
      + (381461112 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2047)) - (β₀₁ + dot48 θ₀ (F3 2729)))
      + (238934519 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 4103)) - (β₁₀ + dot48 θ₁ (F3 2735)))
      + (895971728 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 4295)) - (β₁₀ + dot48 θ₁ (F3 2863)))
      + (5016178 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 4883)) - (β₁₀ + dot48 θ₁ (F3 3255)))
      + (379378979 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 5015)) - (β₁₀ + dot48 θ₁ (F3 3343)))
      + (392227128 : ℚ) * ((β₀₁ + dot48 θ₀ (F3 2533)) - (β₀₀ + dot48 θ₀ (F3 3377)))
      + (106062111 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 5459)) - (β₁₀ + dot48 θ₁ (F3 3639)))
      + (451013313 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2731)) - (β₀₀ + dot48 θ₀ (F3 3641)))
      + (76907280 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2869)) - (β₀₀ + dot48 θ₀ (F3 3825)))
      + (804321970 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2935)) - (β₀₀ + dot48 θ₀ (F3 3913)))
      + (25635760 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 2953)) - (β₀₀ + dot48 θ₀ (F3 3937)))
        < 0 :=
    addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11) t12) t13) t14) t15) t16) t17) t18) t19) t20) t21) t22) t23) t24) t25) t26
  have key :
      (324933258 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 7)) - (β₀₁ + dot48 θ₀ (F3 37)))
      + (68950678 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 731)) - (β₁₀ + dot48 θ₁ (F3 487)))
      + (580696143 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 791)) - (β₁₁ + dot48 θ₁ (F3 527)))
      + (506947154 : ℚ) * ((β₀₁ + dot48 θ₀ (F3 1169)) - (β₁₀ + dot48 θ₁ (F3 779)))
      + (489030970 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 2135)) - (β₁₀ + dot48 θ₁ (F3 1423)))
      + (831689147 : ℚ) * ((β₀₁ + dot48 θ₀ (F3 2729)) - (β₁₀ + dot48 θ₁ (F3 1819)))
      + (474825962 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2867)) - (β₁₀ + dot48 θ₁ (F3 1911)))
      + (613976452 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 3137)) - (β₁₁ + dot48 θ₁ (F3 2091)))
      + (585136222 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 1657)) - (β₀₁ + dot48 θ₀ (F3 2209)))
      + (51271520 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 1753)) - (β₀₁ + dot48 θ₀ (F3 2337)))
      + (452045333 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 3611)) - (β₁₁ + dot48 θ₁ (F3 2407)))
      + (467676557 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 3641)) - (β₁₁ + dot48 θ₁ (F3 2427)))
      + (220147089 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 1843)) - (β₀₁ + dot48 θ₀ (F3 2457)))
      + (161505288 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 1879)) - (β₀₁ + dot48 θ₀ (F3 2505)))
      + (6408940 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 2041)) - (β₀₁ + dot48 θ₀ (F3 2721)))
      + (381461112 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2047)) - (β₀₁ + dot48 θ₀ (F3 2729)))
      + (238934519 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 4103)) - (β₁₀ + dot48 θ₁ (F3 2735)))
      + (895971728 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 4295)) - (β₁₀ + dot48 θ₁ (F3 2863)))
      + (5016178 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 4883)) - (β₁₀ + dot48 θ₁ (F3 3255)))
      + (379378979 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 5015)) - (β₁₀ + dot48 θ₁ (F3 3343)))
      + (392227128 : ℚ) * ((β₀₁ + dot48 θ₀ (F3 2533)) - (β₀₀ + dot48 θ₀ (F3 3377)))
      + (106062111 : ℚ) * ((β₁₁ + dot48 θ₁ (F3 5459)) - (β₁₀ + dot48 θ₁ (F3 3639)))
      + (451013313 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2731)) - (β₀₀ + dot48 θ₀ (F3 3641)))
      + (76907280 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2869)) - (β₀₀ + dot48 θ₀ (F3 3825)))
      + (804321970 : ℚ) * ((β₁₀ + dot48 θ₁ (F3 2935)) - (β₀₀ + dot48 θ₀ (F3 3913)))
      + (25635760 : ℚ) * ((β₀₀ + dot48 θ₀ (F3 2953)) - (β₀₀ + dot48 θ₀ (F3 3937)))
      = 613976452 * θ₀ 8 + 67293870 * θ₀ 17 + 25635760 * θ₀ 25 + 67293870 * θ₀ 32 + 25635760 * θ₀ 40 + 44869465 * θ₁ 10 + 49885643 * θ₁ 13 + 5016178 * θ₁ 14 + 44869465 * θ₁ 15 + 153814560 * θ₁ 17 + 44869465 * θ₁ 24 + 49885643 * θ₁ 26 + 44869465 * θ₁ 29 + 44869465 * θ₁ 31 + 153814560 * θ₁ 32 + 44869465 * θ₁ 40 + 44869465 * θ₁ 43 + 44869465 * θ₁ 45 + 44869465 * θ₁ 46 := by
    rw [F3_37, F3_7, F3_487, F3_731, F3_527, F3_791, F3_779, F3_1169, F3_1423, F3_2135, F3_1819, F3_2729, F3_1911, F3_2867, F3_2091, F3_3137, F3_2209, F3_1657, F3_2337, F3_1753, F3_2407, F3_3611, F3_2427, F3_3641, F3_2457, F3_1843, F3_2505, F3_1879, F3_2721, F3_2041, F3_2047, F3_2735, F3_4103, F3_2863, F3_4295, F3_3255, F3_4883, F3_3343, F3_5015, F3_3377, F3_2533, F3_3639, F3_5459, F3_2731, F3_3825, F3_2869, F3_3913, F3_2935, F3_3937, F3_2953]
    simp only [dot48]
    push_cast
    ring
  rw [key] at hlt
  have hge : (0 : ℚ) ≤ 613976452 * θ₀ 8 + 67293870 * θ₀ 17 + 25635760 * θ₀ 25 + 67293870 * θ₀ 32 + 25635760 * θ₀ 40 + 44869465 * θ₁ 10 + 49885643 * θ₁ 13 + 5016178 * θ₁ 14 + 44869465 * θ₁ 15 + 153814560 * θ₁ 17 + 44869465 * θ₁ 24 + 49885643 * θ₁ 26 + 44869465 * θ₁ 29 + 44869465 * θ₁ 31 + 153814560 * θ₁ 32 + 44869465 * θ₁ 40 + 44869465 * θ₁ 43 + 44869465 * θ₁ 45 + 44869465 * θ₁ 46 :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hθ₀ 8)) (mul_nonneg (by norm_num) (hθ₀ 17))) (mul_nonneg (by norm_num) (hθ₀ 25))) (mul_nonneg (by norm_num) (hθ₀ 32))) (mul_nonneg (by norm_num) (hθ₀ 40))) (mul_nonneg (by norm_num) (hθ₁ 10))) (mul_nonneg (by norm_num) (hθ₁ 13))) (mul_nonneg (by norm_num) (hθ₁ 14))) (mul_nonneg (by norm_num) (hθ₁ 15))) (mul_nonneg (by norm_num) (hθ₁ 17))) (mul_nonneg (by norm_num) (hθ₁ 24))) (mul_nonneg (by norm_num) (hθ₁ 26))) (mul_nonneg (by norm_num) (hθ₁ 29))) (mul_nonneg (by norm_num) (hθ₁ 31))) (mul_nonneg (by norm_num) (hθ₁ 32))) (mul_nonneg (by norm_num) (hθ₁ 40))) (mul_nonneg (by norm_num) (hθ₁ 43))) (mul_nonneg (by norm_num) (hθ₁ 45))) (mul_nonneg (by norm_num) (hθ₁ 46))
  exact absurd hlt (not_lt.mpr hge)

/-! ## 回歸驗證 -/

section Verification

#eval cert26.all fun t => Todd t.1 == t.2.1
#eval cert26.all fun t => ((F3 t.1).getD 33 0 == t.2.2.2.1) && ((F3 t.2.1).getD 33 0 == t.2.2.2.2.1)
#eval cert26.all fun t => (((run3 (1, Phase.K, 0, 0) (extIn t.1)).2.2.1) == t.2.2.2.2.2.1) && (((run3 (1, Phase.K, 0, 0) (extIn t.2.1)).2.2.1) == t.2.2.2.2.2.2)
#eval W26.all fun x => x % 2 == 1

end Verification
end CollatzFST.L3
