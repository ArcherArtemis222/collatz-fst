/-
# LP 不可行性偵察：對方數據驗證 ＋ 我方強化憑證

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_Level2.lean`。
本檔為**驗證性偵察**（非定理批次）：以已證正確的 `occ2` 為裁判，
重算對方（Gemini 產出）的全部數據，並回報獨立實驗結果。

## A. 驗證結論：數據全部為真，僅敘述品質差

1. **特徵索引順序已逆向鎖定（12 選 1 唯一解）**：
   位置 1–6 = K 區塊（c-major、b-minor）：(0,K,0)b0, (0,K,0)b1, (1,K,0)b0, …, (2,K,0)b1；
   位置 7–18 = S 區塊（(c, d_prev, b) 字典序）：(0,S,0,0), (0,S,0,1), (0,S,1,0), …, (2,S,1,1)。
   在此順序下 ΔF₁–ΔF₄ 與我方 `occ2`（extIn、初始 (1,K,0)）**逐位吻合**，
   含 T₄ 的 5.7×10⁹ 大數對。
2. **四條 trajectory 都是真實前向 T_odd 軌道段**：
   7→11（1 步）、27→41（1 步）、41→167（**17 步**）、5709867599→7226551181（**4 步**）。
   多步段作為約束是合法的：逐 epoch 下降 ⇒ 逐段下降（和 ≤ −k ≤ −1）。
3. **Farkas 憑證成立**：λ = (5,5,5,1) 之組合 = [0,0,0,1,1,0,0,0,4,3,1,3,2,1,4,0,0,0] ≥ 0，
   與宣稱逐位一致。跨約束一致性也全過：四條 ΔF 的 K 區塊分量和 = 0,1,−1,2
   恰為 Δv₂（`sum_EK_components` 的差分形式）。

## B. 實質出入：差分維度是 10，不是 9

以 800 條單步 ΔF（x = 3,5,…,1601）做精確整數消去：
**rank = 10**（20 條樣本即穩定），左零空間 8 維，基底全部可解讀：
* e₁, e₂ —— 死狀態 (0,K,0)·b ≡ 0（已證 `occ2_deadState`）；
* e₃+e₆ = 1 —— 邊界步唯一（已證 `boundary_step_unique` 的分量形式）；
  e₄ = e₅+e₆ —— K 區交錯路徑的計數恆等式；
* 其餘四條 —— 自動機的 Kirchhoff 流守恆（各狀態出入次數差 = 初/末指示）。
對方的「9」與 10（差分秩）、8（不變量維度）皆不合，需要他們交出基底核對。

## C. 我方強化憑證：純單步、支撐 10、排除嚴格下降

對方憑證混用多步段；我方以 LP 對偶找到**只用單一 epoch 邊**的整數憑證：
x ∈ {231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511}，
權重 w = (100, 64, 119, 51, 56, 183, 164, 18, 191, 78)（Σ = 1024），
組合 S = 31·e₇（僅 (0,S,0,0) 分量 = +31，其餘全零）≥ 0。
由此連 θ·ΔF < 0（嚴格下降，不必 ≤ −1 正規化）都被排除：
θ ≥ 0 ⇒ θ·S = 31·θ₇ ≥ 0，但 Σ w·(θ·ΔF) < 0，矛盾。

## D. 建議定理形式（待對方確認後形式化）

`¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧ ∀ x ∈ W₁₀, θ ⬝ ΔF(x) < 0`
其中 ΔF 由已證機器 `occ2` **計算**而非外掛數據——這是我方形式化的價值：
特徵差分不是公理，是被證明正確的自動機的輸出。
-/
import Lean4RealConstruction.Core.Collatz_FST_Level2

namespace CollatzFST.LPRecon

open CollatzFST

/-- 鎖定的特徵順序（Kcb + S(c,p,b) 字典序）。 -/
def KEYS : List ((ℕ × Phase × ℕ) × ℕ) :=
  ([0,1,2].flatMap fun c => [0,1].map fun b => ((c, Phase.K, 0), b)) ++
  ([0,1,2].flatMap fun c => [0,1].flatMap fun p => [0,1].map fun b => ((c, Phase.S, p), b))

/-- 18 維特徵向量（ℤ，便於差分）。 -/
def F (x : ℕ) : List ℤ := KEYS.map (fun k => (occ2 (1, Phase.K, 0) (extIn x) k : ℤ))

/-- 端點特徵差分 ΔF = F(b) − F(a)。 -/
def dF (a b : ℕ) : List ℤ := (F b).zipWith (· - ·) (F a)

/-- 前向 T_odd 軌道成員（fuel 版；回傳步數）。 -/
def reach (tgt : ℕ) : ℕ → ℕ → Option ℕ
  | 0, cur => if cur = tgt then some 0 else none
  | n + 1, cur => if cur = tgt then some 0 else (reach tgt n (Todd cur)).map (· + 1)

/-- 對方提供的四條差分向量。 -/
def dF1 : List ℤ := [0,0,0,0,0,0, 0,0,0,0,0,1, 0,0,1,0,0,-1]
def dF2 : List ℤ := [0,0,1,0,1,-1, 0,0,1,2,-1,-1, 2,0,0,-1,-2,0]
def dF3 : List ℤ := [0,0,-1,0,-1,1, 0,0,0,0,1,0, 0,0,0,0,1,1]
def dF4 : List ℤ := [0,0,0,1,1,0, 0,0,-1,-7,1,3, -8,1,-1,5,5,0]

/-- 對方宣稱的 Farkas 組合。 -/
def geminiS : List ℤ := [0,0,0,1,1,0, 0,0,4,3,1,3, 2,1,4,0,0,0]

/-- 我方單步憑證：10 條 (x, 權重)。 -/
def W10 : List (ℕ × ℤ) :=
  [(231,100),(323,64),(403,119),(551,51),(681,56),(877,183),(983,164),(1079,18),(1305,191),(1511,78)]

def comboOf (ws : List (ℕ × ℤ)) : List ℤ :=
  ws.foldl (fun acc (xw : ℕ × ℤ) =>
    acc.zipWith (· + ·) ((dF xw.1 (Todd xw.1)).map (xw.2 * ·)))
    (List.replicate 18 0)

/-! ## 驗證（全部應輸出 `true` 或指定值） -/

section Verification

-- A.1 四條差分逐位吻合（含大數對）
#eval dF 7 11 == dF1
#eval dF 27 41 == dF2
#eval dF 41 167 == dF3
#eval dF 5709867599 7226551181 == dF4

-- A.2 軌道成員與步數
#eval reach 11 5 7 == some 1
#eval reach 41 5 27 == some 1
#eval reach 167 200 41 == some 17
#eval reach 7226551181 400 5709867599 == some 4

-- A.3 對方 Farkas 憑證：λ = (5,5,5,1)
#eval let S := (((dF 7 11).map (5 * ·)).zipWith (· + ·) ((dF 27 41).map (5 * ·))
        |>.zipWith (· + ·) ((dF 41 167).map (5 * ·))
        |>.zipWith (· + ·) (dF 5709867599 7226551181))
      S == geminiS && S.all (0 ≤ ·)

-- A.3b 跨約束一致性：K 區塊分量和 = Δv₂（sum_EK_components 的差分）
#eval [(7,11),(27,41),(41,167),(5709867599,7226551181)].all fun (a, b) =>
  ((dF a b).take 6).foldl (· + ·) 0
    == (padicValNat 2 (3 * b + 1) : ℤ) - (padicValNat 2 (3 * a + 1) : ℤ)

-- C 我方強化憑證：純單步、S = 31·e₇ ≥ 0
#eval comboOf W10 == [0,0,0,0,0,0, 31,0,0,0,0,0, 0,0,0,0,0,0]
#eval (comboOf W10).all (0 ≤ ·)
-- 憑證所用皆為合法單步（Todd 像即端點）
#eval W10.all fun xw => xw.1 % 2 == 1

-- B 不變量抽查（零空間基底之可解讀成員；完整秩計算見檔頭註記）
-- e₁, e₂（死狀態）：
#eval (List.range 200).all fun i => let x := 2*i+3
  ((dF x (Todd x)).take 2).all (· == 0)
-- e₃+e₆ = Δ(邊界步) = 0：
#eval (List.range 200).all fun i => let x := 2*i+3
  let d := dF x (Todd x); d[2]! + d[5]! == 0
-- e₄ − e₅ − e₆ = 0（K 區交錯路徑恆等式）：
#eval (List.range 200).all fun i => let x := 2*i+3
  let d := dF x (Todd x); d[3]! - d[4]! - d[5]! == 0

end Verification

end CollatzFST.LPRecon
