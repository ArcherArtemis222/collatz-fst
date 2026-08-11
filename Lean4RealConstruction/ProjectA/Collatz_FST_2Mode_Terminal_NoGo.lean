/-
# B1.5 per-(mode, terminal) 仿射勢能不可行性（Level 2，**全部證畢**）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_2Mode_NoGo.lean`
（模板與 A-2 證法血統）與 `Collatz_FST_Flow.lean`（終末狀態定理 §51）。

## 主定理

`no_go_2mode_terminal_affine_potential`（ROADMAP-B B1.5）：雙模式勢能的截距
升級為 per-(mode, terminal) 的 β_(m,t)（2 × 2 = 4 個，無符號約束），
V(x) = β_(m(x), t(x)) + θ_(m(x))ᵀ F(x)，仍不能在 W17 的每一步嚴格下降。

終末觀測量 t(x) = `(run2 (1,K,0) (extIn x)).2.2`：`Flow.run2_extIn_terminal`
證終末狀態恆為 (0,S,0)/(0,S,1)，故此位忠實編碼終末（`terminal_bit_faithful`）。

## 憑證

λ = (62550, 304251, 247708, 576866, 760514, 240149, 447790, 800581, 159842, 400102, 385240, 122130, 279475, 223895, 544400, 384246, 191626)，Σλ = 6131365。
錨：`tools/certificates.py --b15`（聚合向量、四條 per-(m,t) 平衡 = 0）；
推導：`tools/search/b15_exact_balance.py`（sympy 精確有理，浮點僅取組合資訊）。
既有 W₁₂ 憑證終末不平衡 ±428（`tools/b15_terminal_balance.py`），
故此升級需要**新見證集**——W17 與 W₁₂ 不相交。

## 證明骨架（同 A-2 血統）

* 17 條 `Todd_x`（`padicValNat_two_pow_mul`）；34 條 `F_n` 求值（`decide`）；
  模式引理 `hm_n` 與終末位引理 `ht_n`（`decide`）。
* 模式（外層）與終末（內層）雙層 if 以 `if_pos`/`if_neg` 消去後，17 條假設化為
  `(β_(m_y,t_y) + dot θ_(m_y) (F y)) − (β_(m_x,t_x) + dot θ_(m_x) (F x)) < 0`。
* 組合恆等式 `key` 由 `ring` 收掉：β 項因四條 per-(m,t) 平衡自動對消
  （四條嚴格強於「模式平衡＋終末平衡」——後兩者僅 3 條獨立，收不掉 4 個自由 β）。
* 十七項嚴格負 vs 七項非負：0 ≤ −6131365 矛盾。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_2Mode_NoGo
import Lean4RealConstruction.ProjectA.Collatz_FST_Flow

namespace CollatzFST.TwoMode

open CollatzFST
open CollatzFST.LP (dot)

/-- 終末位忠實編碼終末狀態：`run2` 讀完 `extIn x` 的狀態由其第三分量完全決定
（`Flow.run2_extIn_terminal` 的重述）。 -/
lemma terminal_bit_faithful (x : ℕ) :
    run2 (1, Phase.K, 0) (extIn x)
      = ((0 : ℕ), Phase.S, (run2 (1, Phase.K, 0) (extIn x)).2.2) := by
  rcases Flow.run2_extIn_terminal x with h | h <;> rw [h]

/-- B1.5 Level 2 雙平衡見證集（17 個奇數；ROADMAP-B B1.5）。 -/
def W17 : List ℕ := [3, 243, 599, 961, 1079, 1363, 1369, 1671, 1819, 2345, 2401, 2731, 3083, 3259, 3677, 3745, 3905]

/-- (x, Todd x, λ, m(x), m(y), t(x), t(y))；回歸驗證用。 Σλ = 6131365。 -/
def cert17 : List (ℕ × ℕ × ℤ × ℤ × ℤ × ℕ × ℕ) :=
  [(3, 5, 62550, 1, 0, 1, 1), (243, 365, 304251, 1, 1, 1, 1), (599, 899, 247708, 1, 1, 0, 1), (961, 721, 576866, 0, 0, 1, 1), (1079, 1619, 760514, 1, 1, 0, 1), (1363, 2045, 240149, 1, 1, 0, 1), (1369, 1027, 447790, 0, 1, 1, 0), (1671, 2507, 800581, 1, 1, 1, 0), (1819, 2729, 159842, 1, 0, 1, 0), (2345, 1759, 400102, 0, 1, 0, 1), (2401, 1801, 385240, 0, 0, 0, 1), (2731, 4097, 122130, 1, 0, 1, 0), (3083, 4625, 279475, 1, 0, 1, 0), (3259, 4889, 223895, 1, 0, 1, 0), (3677, 1379, 544400, 1, 1, 1, 1), (3745, 2809, 384246, 0, 0, 1, 1), (3905, 2929, 191626, 0, 0, 1, 1)]

/-! ## Todd 值（17 條） -/

lemma Todd_3 : Todd 3 = 5 := by
  have hv : padicValNat 2 (3 * 3 + 1) = 1 := by
    rw [show (3 * 3 + 1 : ℕ) = 2 ^ 1 * 5 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_243 : Todd 243 = 365 := by
  have hv : padicValNat 2 (3 * 243 + 1) = 1 := by
    rw [show (3 * 243 + 1 : ℕ) = 2 ^ 1 * 365 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_599 : Todd 599 = 899 := by
  have hv : padicValNat 2 (3 * 599 + 1) = 1 := by
    rw [show (3 * 599 + 1 : ℕ) = 2 ^ 1 * 899 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_961 : Todd 961 = 721 := by
  have hv : padicValNat 2 (3 * 961 + 1) = 2 := by
    rw [show (3 * 961 + 1 : ℕ) = 2 ^ 2 * 721 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_1079 : Todd 1079 = 1619 := by
  have hv : padicValNat 2 (3 * 1079 + 1) = 1 := by
    rw [show (3 * 1079 + 1 : ℕ) = 2 ^ 1 * 1619 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_1363 : Todd 1363 = 2045 := by
  have hv : padicValNat 2 (3 * 1363 + 1) = 1 := by
    rw [show (3 * 1363 + 1 : ℕ) = 2 ^ 1 * 2045 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_1369 : Todd 1369 = 1027 := by
  have hv : padicValNat 2 (3 * 1369 + 1) = 2 := by
    rw [show (3 * 1369 + 1 : ℕ) = 2 ^ 2 * 1027 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_1671 : Todd 1671 = 2507 := by
  have hv : padicValNat 2 (3 * 1671 + 1) = 1 := by
    rw [show (3 * 1671 + 1 : ℕ) = 2 ^ 1 * 2507 by norm_num]
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
lemma Todd_2345 : Todd 2345 = 1759 := by
  have hv : padicValNat 2 (3 * 2345 + 1) = 2 := by
    rw [show (3 * 2345 + 1 : ℕ) = 2 ^ 2 * 1759 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2401 : Todd 2401 = 1801 := by
  have hv : padicValNat 2 (3 * 2401 + 1) = 2 := by
    rw [show (3 * 2401 + 1 : ℕ) = 2 ^ 2 * 1801 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_2731 : Todd 2731 = 4097 := by
  have hv : padicValNat 2 (3 * 2731 + 1) = 1 := by
    rw [show (3 * 2731 + 1 : ℕ) = 2 ^ 1 * 4097 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3083 : Todd 3083 = 4625 := by
  have hv : padicValNat 2 (3 * 3083 + 1) = 1 := by
    rw [show (3 * 3083 + 1 : ℕ) = 2 ^ 1 * 4625 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3259 : Todd 3259 = 4889 := by
  have hv : padicValNat 2 (3 * 3259 + 1) = 1 := by
    rw [show (3 * 3259 + 1 : ℕ) = 2 ^ 1 * 4889 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3677 : Todd 3677 = 1379 := by
  have hv : padicValNat 2 (3 * 3677 + 1) = 3 := by
    rw [show (3 * 3677 + 1 : ℕ) = 2 ^ 3 * 1379 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3745 : Todd 3745 = 2809 := by
  have hv : padicValNat 2 (3 * 3745 + 1) = 2 := by
    rw [show (3 * 3745 + 1 : ℕ) = 2 ^ 2 * 2809 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num
lemma Todd_3905 : Todd 3905 = 2929 := by
  have hv : padicValNat 2 (3 * 3905 + 1) = 2 := by
    rw [show (3 * 3905 + 1 : ℕ) = 2 ^ 2 * 2929 by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num

/-! ## F 求值與模式／終末位引理（34 個相異端點） -/

lemma F_3 : F 3 = [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0] := by decide
lemma F_5 : F 5 = [0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
lemma F_243 : F 243 = [0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1, 2, 1] := by decide
lemma F_365 : F 365 = [0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 2, 0, 0, 1, 1, 2, 0] := by decide
lemma F_599 : F 599 = [0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 2, 1, 0, 2, 0, 1, 1] := by decide
lemma F_899 : F 899 = [0, 0, 0, 1, 0, 1, 2, 1, 1, 0, 2, 0, 0, 1, 0, 1, 2, 0] := by decide
lemma F_961 : F 961 = [0, 0, 1, 1, 1, 0, 2, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1] := by decide
lemma F_721 : F 721 = [0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 0] := by decide
lemma F_1079 : F 1079 = [0, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 1, 1, 0, 0, 1, 2, 1] := by decide
lemma F_1619 : F 1619 = [0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 2, 0, 2, 1, 1, 0, 1, 0] := by decide
lemma F_1363 : F 1363 = [0, 0, 0, 1, 0, 1, 0, 0, 1, 4, 1, 0, 4, 0, 0, 0, 1, 0] := by decide
lemma F_2045 : F 2045 = [0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 7] := by decide
lemma F_1369 : F 1369 = [0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 3, 0, 1, 4, 0, 0, 0] := by decide
lemma F_1027 : F 1027 = [0, 0, 0, 1, 0, 1, 5, 1, 2, 0, 1, 0, 1, 0, 0, 0, 1, 0] := by decide
lemma F_1671 : F 1671 = [0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 0, 1, 1] := by decide
lemma F_2507 : F 2507 = [0, 0, 0, 1, 0, 1, 0, 0, 1, 2, 2, 1, 1, 1, 1, 1, 2, 0] := by decide
lemma F_1819 : F 1819 = [0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 2, 1, 0, 1, 0, 2, 3, 0] := by decide
lemma F_2729 : F 2729 = [0, 0, 1, 1, 1, 0, 0, 0, 1, 5, 0, 0, 5, 0, 0, 0, 0, 0] := by decide
lemma F_2345 : F 2345 = [0, 0, 1, 1, 1, 0, 0, 2, 3, 2, 0, 0, 4, 0, 0, 0, 0, 0] := by decide
lemma F_1759 : F 1759 = [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 3, 3] := by decide
lemma F_2401 : F 2401 = [0, 0, 1, 1, 1, 0, 1, 1, 2, 1, 1, 1, 1, 1, 2, 0, 0, 0] := by decide
lemma F_1801 : F 1801 = [0, 0, 1, 1, 1, 0, 2, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0] := by decide
lemma F_2731 : F 2731 = [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 5, 0, 0, 5, 0, 1, 0] := by decide
lemma F_4097 : F 4097 = [0, 0, 1, 1, 1, 0, 8, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by decide
lemma F_3083 : F 3083 = [0, 0, 0, 1, 0, 1, 3, 1, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0] := by decide
lemma F_4625 : F 4625 = [0, 0, 1, 1, 1, 0, 2, 3, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0] := by decide
lemma F_3259 : F 3259 = [0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 2, 2, 0, 1, 2, 1, 2, 1] := by decide
lemma F_4889 : F 4889 = [0, 0, 1, 1, 1, 0, 0, 1, 2, 2, 2, 0, 1, 2, 2, 0, 0, 0] := by decide
lemma F_3677 : F 3677 = [0, 0, 0, 2, 1, 1, 0, 0, 0, 1, 2, 1, 0, 1, 1, 1, 2, 1] := by decide
lemma F_1379 : F 1379 = [0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 3, 0, 1, 0] := by decide
lemma F_3745 : F 3745 = [0, 0, 1, 1, 1, 0, 1, 1, 1, 2, 1, 0, 2, 1, 0, 1, 1, 0] := by decide
lemma F_2809 : F 2809 = [0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 2, 0, 1, 2, 1, 1, 2] := by decide
lemma F_3905 : F 3905 = [0, 0, 1, 1, 1, 0, 2, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1] := by decide
lemma F_2929 : F 2929 = [0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 2, 0, 1, 1, 2, 2, 0] := by decide

lemma hm_3 : (F 3).getD 5 0 = 1 := by rw [F_3]; decide
lemma hm_5 : ¬ (F 5).getD 5 0 = 1 := by rw [F_5]; decide
lemma hm_243 : (F 243).getD 5 0 = 1 := by rw [F_243]; decide
lemma hm_365 : (F 365).getD 5 0 = 1 := by rw [F_365]; decide
lemma hm_599 : (F 599).getD 5 0 = 1 := by rw [F_599]; decide
lemma hm_899 : (F 899).getD 5 0 = 1 := by rw [F_899]; decide
lemma hm_961 : ¬ (F 961).getD 5 0 = 1 := by rw [F_961]; decide
lemma hm_721 : ¬ (F 721).getD 5 0 = 1 := by rw [F_721]; decide
lemma hm_1079 : (F 1079).getD 5 0 = 1 := by rw [F_1079]; decide
lemma hm_1619 : (F 1619).getD 5 0 = 1 := by rw [F_1619]; decide
lemma hm_1363 : (F 1363).getD 5 0 = 1 := by rw [F_1363]; decide
lemma hm_2045 : (F 2045).getD 5 0 = 1 := by rw [F_2045]; decide
lemma hm_1369 : ¬ (F 1369).getD 5 0 = 1 := by rw [F_1369]; decide
lemma hm_1027 : (F 1027).getD 5 0 = 1 := by rw [F_1027]; decide
lemma hm_1671 : (F 1671).getD 5 0 = 1 := by rw [F_1671]; decide
lemma hm_2507 : (F 2507).getD 5 0 = 1 := by rw [F_2507]; decide
lemma hm_1819 : (F 1819).getD 5 0 = 1 := by rw [F_1819]; decide
lemma hm_2729 : ¬ (F 2729).getD 5 0 = 1 := by rw [F_2729]; decide
lemma hm_2345 : ¬ (F 2345).getD 5 0 = 1 := by rw [F_2345]; decide
lemma hm_1759 : (F 1759).getD 5 0 = 1 := by rw [F_1759]; decide
lemma hm_2401 : ¬ (F 2401).getD 5 0 = 1 := by rw [F_2401]; decide
lemma hm_1801 : ¬ (F 1801).getD 5 0 = 1 := by rw [F_1801]; decide
lemma hm_2731 : (F 2731).getD 5 0 = 1 := by rw [F_2731]; decide
lemma hm_4097 : ¬ (F 4097).getD 5 0 = 1 := by rw [F_4097]; decide
lemma hm_3083 : (F 3083).getD 5 0 = 1 := by rw [F_3083]; decide
lemma hm_4625 : ¬ (F 4625).getD 5 0 = 1 := by rw [F_4625]; decide
lemma hm_3259 : (F 3259).getD 5 0 = 1 := by rw [F_3259]; decide
lemma hm_4889 : ¬ (F 4889).getD 5 0 = 1 := by rw [F_4889]; decide
lemma hm_3677 : (F 3677).getD 5 0 = 1 := by rw [F_3677]; decide
lemma hm_1379 : (F 1379).getD 5 0 = 1 := by rw [F_1379]; decide
lemma hm_3745 : ¬ (F 3745).getD 5 0 = 1 := by rw [F_3745]; decide
lemma hm_2809 : ¬ (F 2809).getD 5 0 = 1 := by rw [F_2809]; decide
lemma hm_3905 : ¬ (F 3905).getD 5 0 = 1 := by rw [F_3905]; decide
lemma hm_2929 : ¬ (F 2929).getD 5 0 = 1 := by rw [F_2929]; decide

lemma ht_3 : (run2 (1, Phase.K, 0) (extIn 3)).2.2 = 1 := by decide
lemma ht_5 : (run2 (1, Phase.K, 0) (extIn 5)).2.2 = 1 := by decide
lemma ht_243 : (run2 (1, Phase.K, 0) (extIn 243)).2.2 = 1 := by decide
lemma ht_365 : (run2 (1, Phase.K, 0) (extIn 365)).2.2 = 1 := by decide
lemma ht_599 : ¬ (run2 (1, Phase.K, 0) (extIn 599)).2.2 = 1 := by decide
lemma ht_899 : (run2 (1, Phase.K, 0) (extIn 899)).2.2 = 1 := by decide
lemma ht_961 : (run2 (1, Phase.K, 0) (extIn 961)).2.2 = 1 := by decide
lemma ht_721 : (run2 (1, Phase.K, 0) (extIn 721)).2.2 = 1 := by decide
lemma ht_1079 : ¬ (run2 (1, Phase.K, 0) (extIn 1079)).2.2 = 1 := by decide
lemma ht_1619 : (run2 (1, Phase.K, 0) (extIn 1619)).2.2 = 1 := by decide
lemma ht_1363 : ¬ (run2 (1, Phase.K, 0) (extIn 1363)).2.2 = 1 := by decide
lemma ht_2045 : (run2 (1, Phase.K, 0) (extIn 2045)).2.2 = 1 := by decide
lemma ht_1369 : (run2 (1, Phase.K, 0) (extIn 1369)).2.2 = 1 := by decide
lemma ht_1027 : ¬ (run2 (1, Phase.K, 0) (extIn 1027)).2.2 = 1 := by decide
lemma ht_1671 : (run2 (1, Phase.K, 0) (extIn 1671)).2.2 = 1 := by decide
lemma ht_2507 : ¬ (run2 (1, Phase.K, 0) (extIn 2507)).2.2 = 1 := by decide
lemma ht_1819 : (run2 (1, Phase.K, 0) (extIn 1819)).2.2 = 1 := by decide
lemma ht_2729 : ¬ (run2 (1, Phase.K, 0) (extIn 2729)).2.2 = 1 := by decide
lemma ht_2345 : ¬ (run2 (1, Phase.K, 0) (extIn 2345)).2.2 = 1 := by decide
lemma ht_1759 : (run2 (1, Phase.K, 0) (extIn 1759)).2.2 = 1 := by decide
lemma ht_2401 : ¬ (run2 (1, Phase.K, 0) (extIn 2401)).2.2 = 1 := by decide
lemma ht_1801 : (run2 (1, Phase.K, 0) (extIn 1801)).2.2 = 1 := by decide
lemma ht_2731 : (run2 (1, Phase.K, 0) (extIn 2731)).2.2 = 1 := by decide
lemma ht_4097 : ¬ (run2 (1, Phase.K, 0) (extIn 4097)).2.2 = 1 := by decide
lemma ht_3083 : (run2 (1, Phase.K, 0) (extIn 3083)).2.2 = 1 := by decide
lemma ht_4625 : ¬ (run2 (1, Phase.K, 0) (extIn 4625)).2.2 = 1 := by decide
lemma ht_3259 : (run2 (1, Phase.K, 0) (extIn 3259)).2.2 = 1 := by decide
lemma ht_4889 : ¬ (run2 (1, Phase.K, 0) (extIn 4889)).2.2 = 1 := by decide
lemma ht_3677 : (run2 (1, Phase.K, 0) (extIn 3677)).2.2 = 1 := by decide
lemma ht_1379 : (run2 (1, Phase.K, 0) (extIn 1379)).2.2 = 1 := by decide
lemma ht_3745 : (run2 (1, Phase.K, 0) (extIn 3745)).2.2 = 1 := by decide
lemma ht_2809 : (run2 (1, Phase.K, 0) (extIn 2809)).2.2 = 1 := by decide
lemma ht_3905 : (run2 (1, Phase.K, 0) (extIn 3905)).2.2 = 1 := by decide
lemma ht_2929 : (run2 (1, Phase.K, 0) (extIn 2929)).2.2 = 1 := by decide

/-- 模式為位元（同 `mode_bit_endpoints`，34 端點）。 -/
lemma mode_bit_endpoints_W17 :
    ∀ n ∈ (cert17.flatMap fun t => [t.1, t.2.1]),
      (F n).getD 2 0 + (F n).getD 5 0 = 1 := by decide

private lemma addneg {a b : ℚ} (ha : a < 0) (hb : b < 0) : a + b < 0 := by
  have h := add_lt_add ha hb
  simpa using h

/-- **主定理**（ROADMAP-B B1.5）：截距升級為 per-(mode, terminal) 的
β_(m,t)（2 × 2 = 4 個，**無符號約束**），非負權重的雙模式仿射勢能仍不能在
W17 的每一步嚴格下降。β 項對消依賴四條 per-(m,t) 平衡精確成立
（`tools/certificates.py --b15`）；終末位忠實編碼終末狀態，見
`terminal_bit_faithful`。 -/
theorem no_go_2mode_terminal_affine_potential :
    ¬ ∃ (β₀₀ β₀₁ β₁₀ β₁₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W17,
        (if (F (Todd x)).getD 5 0 = 1
           then (if (run2 (1, Phase.K, 0) (extIn (Todd x))).2.2 = 1 then β₁₁ else β₁₀)
                  + dot θ₁ (F (Todd x))
           else (if (run2 (1, Phase.K, 0) (extIn (Todd x))).2.2 = 1 then β₀₁ else β₀₀)
                  + dot θ₀ (F (Todd x)))
          - (if (F x).getD 5 0 = 1
           then (if (run2 (1, Phase.K, 0) (extIn x)).2.2 = 1 then β₁₁ else β₁₀)
                  + dot θ₁ (F x)
           else (if (run2 (1, Phase.K, 0) (extIn x)).2.2 = 1 then β₀₁ else β₀₀)
                  + dot θ₀ (F x)) < 0 := by
  rintro ⟨β₀₀, β₀₁, β₁₀, β₁₁, θ₀, θ₁, hθ₀, hθ₁, hdesc⟩
  have h1 := hdesc 3 (by decide)
  have h2 := hdesc 243 (by decide)
  have h3 := hdesc 599 (by decide)
  have h4 := hdesc 961 (by decide)
  have h5 := hdesc 1079 (by decide)
  have h6 := hdesc 1363 (by decide)
  have h7 := hdesc 1369 (by decide)
  have h8 := hdesc 1671 (by decide)
  have h9 := hdesc 1819 (by decide)
  have h10 := hdesc 2345 (by decide)
  have h11 := hdesc 2401 (by decide)
  have h12 := hdesc 2731 (by decide)
  have h13 := hdesc 3083 (by decide)
  have h14 := hdesc 3259 (by decide)
  have h15 := hdesc 3677 (by decide)
  have h16 := hdesc 3745 (by decide)
  have h17 := hdesc 3905 (by decide)
  rw [Todd_3, if_neg hm_5, if_pos hm_3, if_pos ht_5, if_pos ht_3] at h1
  rw [Todd_243, if_pos hm_365, if_pos hm_243, if_pos ht_365, if_pos ht_243] at h2
  rw [Todd_599, if_pos hm_899, if_pos hm_599, if_pos ht_899, if_neg ht_599] at h3
  rw [Todd_961, if_neg hm_721, if_neg hm_961, if_pos ht_721, if_pos ht_961] at h4
  rw [Todd_1079, if_pos hm_1619, if_pos hm_1079, if_pos ht_1619, if_neg ht_1079] at h5
  rw [Todd_1363, if_pos hm_2045, if_pos hm_1363, if_pos ht_2045, if_neg ht_1363] at h6
  rw [Todd_1369, if_pos hm_1027, if_neg hm_1369, if_neg ht_1027, if_pos ht_1369] at h7
  rw [Todd_1671, if_pos hm_2507, if_pos hm_1671, if_neg ht_2507, if_pos ht_1671] at h8
  rw [Todd_1819, if_neg hm_2729, if_pos hm_1819, if_neg ht_2729, if_pos ht_1819] at h9
  rw [Todd_2345, if_pos hm_1759, if_neg hm_2345, if_pos ht_1759, if_neg ht_2345] at h10
  rw [Todd_2401, if_neg hm_1801, if_neg hm_2401, if_pos ht_1801, if_neg ht_2401] at h11
  rw [Todd_2731, if_neg hm_4097, if_pos hm_2731, if_neg ht_4097, if_pos ht_2731] at h12
  rw [Todd_3083, if_neg hm_4625, if_pos hm_3083, if_neg ht_4625, if_pos ht_3083] at h13
  rw [Todd_3259, if_neg hm_4889, if_pos hm_3259, if_neg ht_4889, if_pos ht_3259] at h14
  rw [Todd_3677, if_pos hm_1379, if_pos hm_3677, if_pos ht_1379, if_pos ht_3677] at h15
  rw [Todd_3745, if_neg hm_2809, if_neg hm_3745, if_pos ht_2809, if_pos ht_3745] at h16
  rw [Todd_3905, if_neg hm_2929, if_neg hm_3905, if_pos ht_2929, if_pos ht_3905] at h17
  have t1 : (62550 : ℚ) * ((β₀₁ + dot θ₀ (F 5)) - (β₁₁ + dot θ₁ (F 3))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h1
  have t2 : (304251 : ℚ) * ((β₁₁ + dot θ₁ (F 365)) - (β₁₁ + dot θ₁ (F 243))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h2
  have t3 : (247708 : ℚ) * ((β₁₁ + dot θ₁ (F 899)) - (β₁₀ + dot θ₁ (F 599))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h3
  have t4 : (576866 : ℚ) * ((β₀₁ + dot θ₀ (F 721)) - (β₀₁ + dot θ₀ (F 961))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h4
  have t5 : (760514 : ℚ) * ((β₁₁ + dot θ₁ (F 1619)) - (β₁₀ + dot θ₁ (F 1079))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h5
  have t6 : (240149 : ℚ) * ((β₁₁ + dot θ₁ (F 2045)) - (β₁₀ + dot θ₁ (F 1363))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h6
  have t7 : (447790 : ℚ) * ((β₁₀ + dot θ₁ (F 1027)) - (β₀₁ + dot θ₀ (F 1369))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h7
  have t8 : (800581 : ℚ) * ((β₁₀ + dot θ₁ (F 2507)) - (β₁₁ + dot θ₁ (F 1671))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h8
  have t9 : (159842 : ℚ) * ((β₀₀ + dot θ₀ (F 2729)) - (β₁₁ + dot θ₁ (F 1819))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h9
  have t10 : (400102 : ℚ) * ((β₁₁ + dot θ₁ (F 1759)) - (β₀₀ + dot θ₀ (F 2345))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h10
  have t11 : (385240 : ℚ) * ((β₀₁ + dot θ₀ (F 1801)) - (β₀₀ + dot θ₀ (F 2401))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h11
  have t12 : (122130 : ℚ) * ((β₀₀ + dot θ₀ (F 4097)) - (β₁₁ + dot θ₁ (F 2731))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h12
  have t13 : (279475 : ℚ) * ((β₀₀ + dot θ₀ (F 4625)) - (β₁₁ + dot θ₁ (F 3083))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h13
  have t14 : (223895 : ℚ) * ((β₀₀ + dot θ₀ (F 4889)) - (β₁₁ + dot θ₁ (F 3259))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h14
  have t15 : (544400 : ℚ) * ((β₁₁ + dot θ₁ (F 1379)) - (β₁₁ + dot θ₁ (F 3677))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h15
  have t16 : (384246 : ℚ) * ((β₀₁ + dot θ₀ (F 2809)) - (β₀₁ + dot θ₀ (F 3745))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h16
  have t17 : (191626 : ℚ) * ((β₀₁ + dot θ₀ (F 2929)) - (β₀₁ + dot θ₀ (F 3905))) < 0 := mul_neg_of_pos_of_neg (by norm_num) h17
  have hlt :
      (62550 : ℚ) * ((β₀₁ + dot θ₀ (F 5)) - (β₁₁ + dot θ₁ (F 3)))
      + (304251 : ℚ) * ((β₁₁ + dot θ₁ (F 365)) - (β₁₁ + dot θ₁ (F 243)))
      + (247708 : ℚ) * ((β₁₁ + dot θ₁ (F 899)) - (β₁₀ + dot θ₁ (F 599)))
      + (576866 : ℚ) * ((β₀₁ + dot θ₀ (F 721)) - (β₀₁ + dot θ₀ (F 961)))
      + (760514 : ℚ) * ((β₁₁ + dot θ₁ (F 1619)) - (β₁₀ + dot θ₁ (F 1079)))
      + (240149 : ℚ) * ((β₁₁ + dot θ₁ (F 2045)) - (β₁₀ + dot θ₁ (F 1363)))
      + (447790 : ℚ) * ((β₁₀ + dot θ₁ (F 1027)) - (β₀₁ + dot θ₀ (F 1369)))
      + (800581 : ℚ) * ((β₁₀ + dot θ₁ (F 2507)) - (β₁₁ + dot θ₁ (F 1671)))
      + (159842 : ℚ) * ((β₀₀ + dot θ₀ (F 2729)) - (β₁₁ + dot θ₁ (F 1819)))
      + (400102 : ℚ) * ((β₁₁ + dot θ₁ (F 1759)) - (β₀₀ + dot θ₀ (F 2345)))
      + (385240 : ℚ) * ((β₀₁ + dot θ₀ (F 1801)) - (β₀₀ + dot θ₀ (F 2401)))
      + (122130 : ℚ) * ((β₀₀ + dot θ₀ (F 4097)) - (β₁₁ + dot θ₁ (F 2731)))
      + (279475 : ℚ) * ((β₀₀ + dot θ₀ (F 4625)) - (β₁₁ + dot θ₁ (F 3083)))
      + (223895 : ℚ) * ((β₀₀ + dot θ₀ (F 4889)) - (β₁₁ + dot θ₁ (F 3259)))
      + (544400 : ℚ) * ((β₁₁ + dot θ₁ (F 1379)) - (β₁₁ + dot θ₁ (F 3677)))
      + (384246 : ℚ) * ((β₀₁ + dot θ₀ (F 2809)) - (β₀₁ + dot θ₀ (F 3745)))
      + (191626 : ℚ) * ((β₀₁ + dot θ₀ (F 2929)) - (β₀₁ + dot θ₀ (F 3905)))
        < 0 :=
    addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (addneg (t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11) t12) t13) t14) t15) t16) t17
  have key :
      (62550 : ℚ) * ((β₀₁ + dot θ₀ (F 5)) - (β₁₁ + dot θ₁ (F 3)))
      + (304251 : ℚ) * ((β₁₁ + dot θ₁ (F 365)) - (β₁₁ + dot θ₁ (F 243)))
      + (247708 : ℚ) * ((β₁₁ + dot θ₁ (F 899)) - (β₁₀ + dot θ₁ (F 599)))
      + (576866 : ℚ) * ((β₀₁ + dot θ₀ (F 721)) - (β₀₁ + dot θ₀ (F 961)))
      + (760514 : ℚ) * ((β₁₁ + dot θ₁ (F 1619)) - (β₁₀ + dot θ₁ (F 1079)))
      + (240149 : ℚ) * ((β₁₁ + dot θ₁ (F 2045)) - (β₁₀ + dot θ₁ (F 1363)))
      + (447790 : ℚ) * ((β₁₀ + dot θ₁ (F 1027)) - (β₀₁ + dot θ₀ (F 1369)))
      + (800581 : ℚ) * ((β₁₀ + dot θ₁ (F 2507)) - (β₁₁ + dot θ₁ (F 1671)))
      + (159842 : ℚ) * ((β₀₀ + dot θ₀ (F 2729)) - (β₁₁ + dot θ₁ (F 1819)))
      + (400102 : ℚ) * ((β₁₁ + dot θ₁ (F 1759)) - (β₀₀ + dot θ₀ (F 2345)))
      + (385240 : ℚ) * ((β₀₁ + dot θ₀ (F 1801)) - (β₀₀ + dot θ₀ (F 2401)))
      + (122130 : ℚ) * ((β₀₀ + dot θ₀ (F 4097)) - (β₁₁ + dot θ₁ (F 2731)))
      + (279475 : ℚ) * ((β₀₀ + dot θ₀ (F 4625)) - (β₁₁ + dot θ₁ (F 3083)))
      + (223895 : ℚ) * ((β₀₀ + dot θ₀ (F 4889)) - (β₁₁ + dot θ₁ (F 3259)))
      + (544400 : ℚ) * ((β₁₁ + dot θ₁ (F 1379)) - (β₁₁ + dot θ₁ (F 3677)))
      + (384246 : ℚ) * ((β₀₁ + dot θ₀ (F 2809)) - (β₀₁ + dot θ₀ (F 3745)))
      + (191626 : ℚ) * ((β₀₁ + dot θ₀ (F 2929)) - (β₀₁ + dot θ₀ (F 3905)))
      = 62550 * θ₀ 3 + 62550 * θ₀ 4 + 334846 * θ₁ 6 + 40759 * θ₁ 9 + 40759 * θ₁ 10 + 40759 * θ₁ 13 + 40759 * θ₁ 14 := by
    rw [F_3, F_5, F_243, F_365, F_599, F_899, F_961, F_721, F_1079, F_1619, F_1363, F_2045, F_1369, F_1027, F_1671, F_2507, F_1819, F_2729, F_2345, F_1759, F_2401, F_1801, F_2731, F_4097, F_3083, F_4625, F_3259, F_4889, F_3677, F_1379, F_3745, F_2809, F_3905, F_2929]
    simp only [dot]
    push_cast
    ring
  rw [key] at hlt
  have hge : (0 : ℚ) ≤ 62550 * θ₀ 3 + 62550 * θ₀ 4 + 334846 * θ₁ 6 + 40759 * θ₁ 9 + 40759 * θ₁ 10 + 40759 * θ₁ 13 + 40759 * θ₁ 14 :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hθ₀ 3)) (mul_nonneg (by norm_num) (hθ₀ 4))) (mul_nonneg (by norm_num) (hθ₁ 6))) (mul_nonneg (by norm_num) (hθ₁ 9))) (mul_nonneg (by norm_num) (hθ₁ 10))) (mul_nonneg (by norm_num) (hθ₁ 13))) (mul_nonneg (by norm_num) (hθ₁ 14))
  exact absurd hlt (not_lt.mpr hge)

/-! ## 回歸驗證 -/

section Verification

#eval cert17.all fun t => Todd t.1 == t.2.1
#eval cert17.all fun t => ((F t.1).getD 5 0 == t.2.2.2.1) && ((F t.2.1).getD 5 0 == t.2.2.2.2.1)
#eval cert17.all fun t => (((run2 (1, Phase.K, 0) (extIn t.1)).2.2) == t.2.2.2.2.2.1) && (((run2 (1, Phase.K, 0) (extIn t.2.1)).2.2) == t.2.2.2.2.2.2)
#eval W17.all fun x => x % 2 == 1

end Verification

end CollatzFST.TwoMode
