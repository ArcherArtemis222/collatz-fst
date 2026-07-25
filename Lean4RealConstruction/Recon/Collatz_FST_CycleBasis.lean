/-
# 循環基底的物理意義拆解 ＋ 10 = 9 + 1 維度和解

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_Level2.lean`。
回覆對方規格定案文件（四點皆收到），並完成其請求：拆解 9 維循環基底的物理意義。

## A. 資訊遺漏／需修正處（回覆對方）

1. **索引約定落差（必須書面釘死）**：C₁–C₉ 活在 **16 維邊空間**
   （腳本的 states 順序 × b 內層），而定理與 ΔF 活在 **18 維特徵空間**。
   對映：`特徵 i = 邊 (i−2)`，i = 3..18；特徵 1, 2 為死狀態 (0,K,0)·b，無對應邊。
2. **§2 的機制說明方向反了（結論沒錯，故事錯了）**：
   * 8 維是**左**零空間（線性不變量，對偶側）；9 維是**右**側的循環空間。
     兩者住在互為對偶的空間裡，不存在「9 被數論約束降到 8」這回事。
   * 真實差分空間也不是被「降維」，而是**升維**：
     **span(ΔF) = ker B ⊕ ℚ·t，維度 10 = 9（循環）+ 1（邊界）**。
     邊界方向 t 來自：兩次 run 同起點 (1,K,0)，但終點可為 (0,S,0) 或 (0,S,1)
     （末輸出位 d_last ∈ {0,1}），故 B·ΔF = k·(δ₍₀,S,1₎ − δ₍₀,S,0₎)，k = Δd_last ∈ {−1,0,1}。
     已對 800 條真實單步差分逐一驗證（本檔 #eval），並驗 span{Z ∪ t} 秩恰為 10、
     涵蓋全部樣本（Python 精確消去；係數見下）。
   * 一致性核對：18 − 10 = 8 ✓（我方不變量維度）；16 − 7 = 9 ✓（他方 nullity）。
3. 其餘三點（索引順序、放棄多步 Epoch、定理形式）皆確認無誤，可依規格開工。

## B. 九條循環的物理意義（標準有向循環基底 Z）

| 循環 | 邊 | 輸入/輸出 | 物理意義 |
|---|---|---|---|
| **Z₁** K 交錯泵 | e₂+e₃ | 讀 `1,0` / 出 `0,0` | (1,K)↔(2,K)：Theorem 3 的 v₂ 泵，每圈 v₂+2（`alt_of_one_mod_four`） |
| **Z₂** 零進位空轉 | e₅（自環） | 讀 `0` / 出 `0` | 進位已死的 0-gap 舒張：高位無擾動區 |
| **Z₃** 飽和 1-run | e₁₆（自環） | 讀 `1` / 出 `1` | Lemma 2 之 c=2：1-block 原樣穿過（高能延續的極限形） |
| **Z₄** S 區交錯進位 | e₁₀+e₁₃ | 讀 `1,0` / 出 `0,0` | (1,S,0)↔(2,S,0)：**存活區的進位記憶傳播**——Z₁ 的 S 側影子，輸出全零 |
| **Z₅** 交錯輸入→連續 1 | e₈+e₁₁ | 讀 `1,0` / 出 `1,1` | c 在 0↔1 擺盪：輸入 `…0101…` 凝聚成輸出 `…1111…`（區塊凝聚的機制核） |
| **Z₆** 孤立 11 區塊 | e₆+e₁₁+e₇ | 讀 `1,0,0` / 出 `1,1,0` | 誕生→延續→死亡的最小完整生命週期 |
| **Z₇** 死亡-舒張-誕生 | e₁₅+e₁₀+e₁₄ | 讀 `0,1,1` / 出 `0,0,1` | 高進位側的區塊交替（經 (2,S,·)） |
| **Z₈** 11 區塊＋00 間隙 | e₉+e₈+e₁₂+e₁₃ | 讀 `0,1,1,0` / 出 `1,1,0,0` | 完整的 block-gap 週期（進位路線 1→0→1→2→1） |
| **Z₉** 出口對換 | e₁+e₃−e₄+e₈+e₁₂+e₁₄ | — | 兩扇 K→S 出口（(1,K)b0 vs (2,K)b1）模循環同調；`boundary_step_unique`（E³+E⁶=1）的對偶 |

**邊界向量 t = e₆+e₁₁**（B·t = δ₍₀,S,1₎−δ₍₀,S,0₎）：d_last 的 0↔1 位移，
即 `birth_death_conservation` 中「串是否以 1 結尾」那一項的幾何身分。

換基（全 ±1，五條直接重合）：
C₁=Z₁, C₂=Z₂, C₃=Z₅−Z₆, C₄=Z₆, C₅=−Z₄−Z₅+Z₆+Z₈,
C₆=Z₄, C₇=−Z₁+Z₄−Z₈+Z₉, C₈=Z₁−Z₄+Z₇+Z₈−Z₉, C₉=Z₃。

註：C₃ = Z₅−Z₆ 是**分裂關係**：「延續」與「死亡+誕生」同調——
Theorem 1 裂變上限在循環空間裡的身影。
-/
import Lean4RealConstruction.Core.Collatz_FST_Level2

namespace CollatzFST.CycleBasis

open CollatzFST

/-! ## §29 邊、關聯矩陣、雙方基底 -/

/-- 16 條邊：(src, dst, b)，順序 = 對方腳本（states 序 × b 內層）。 -/
def edges : List ((ℕ × Phase × ℕ) × (ℕ × Phase × ℕ) × ℕ) :=
  [((1,.K,0),(0,.S,1),0), ((1,.K,0),(2,.K,0),1),
   ((2,.K,0),(1,.K,0),0), ((2,.K,0),(2,.S,1),1),
   ((0,.S,0),(0,.S,0),0), ((0,.S,0),(1,.S,1),1),
   ((0,.S,1),(0,.S,0),0), ((0,.S,1),(1,.S,1),1),
   ((1,.S,0),(0,.S,1),0), ((1,.S,0),(2,.S,0),1),
   ((1,.S,1),(0,.S,1),0), ((1,.S,1),(2,.S,0),1),
   ((2,.S,0),(1,.S,0),0), ((2,.S,0),(2,.S,1),1),
   ((2,.S,1),(1,.S,0),0), ((2,.S,1),(2,.S,1),1)]

/-- 邊列表忠實於已證機器：每條邊確為 `step2` 的一步。 -/
example : edges.all (fun e => step2 e.1 e.2.2 == e.2.1) := by decide

def stateList : List (ℕ × Phase × ℕ) :=
  [(1,.K,0),(2,.K,0),(0,.S,0),(0,.S,1),(1,.S,0),(1,.S,1),(2,.S,0),(2,.S,1)]

/-- 關聯矩陣 B（8×16；自環列為 0）。 -/
def B : List (List ℤ) :=
  stateList.map fun s =>
    edges.map fun e =>
      if e.1 == e.2.1 then 0
      else (if e.2.1 == s then 1 else 0) - (if e.1 == s then 1 else 0)

def matvec (M : List (List ℤ)) (v : List ℤ) : List ℤ :=
  M.map fun row => (row.zipWith (· * ·) v).foldl (· + ·) 0

def addV (u v : List ℤ) : List ℤ := u.zipWith (· + ·) v
def smul (a : ℤ) (v : List ℤ) : List ℤ := v.map (a * ·)
def zero16 : List ℤ := List.replicate 16 0
def zero8 : List ℤ := List.replicate 8 0

/-- 對方的 sympy 基底 C₁–C₉。 -/
def C : List (List ℤ) :=
  [[0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,-1,-1,1,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,1,1,0,0,0,1,0,0,0,0,0],
   [0,0,0,0,0,1,1,0,1,-1,0,1,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0],
   [1,-1,0,-1,0,0,0,0,-1,1,0,0,0,1,0,0],
   [-1,1,0,1,0,0,0,0,1,0,0,0,0,0,1,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]

/-- 帶符號邊組合的簡便構造。 -/
def eV (idxs : List ℤ) : List ℤ :=
  idxs.foldl (fun acc i =>
    acc.zipWith (· + ·)
      ((List.range 16).map fun j => if (j : ℤ) + 1 = |i| then (if i > 0 then 1 else -1) else 0))
    zero16

/-- 我方標準有向循環基底 Z₁–Z₉（物理意義見檔頭表）。 -/
def Z1 : List ℤ := eV [2,3]
def Z2 : List ℤ := eV [5]
def Z3 : List ℤ := eV [16]
def Z4 : List ℤ := eV [10,13]
def Z5 : List ℤ := eV [8,11]
def Z6 : List ℤ := eV [6,11,7]
def Z7 : List ℤ := eV [15,10,14]
def Z8 : List ℤ := eV [9,8,12,13]
def Z9 : List ℤ := eV [1,3,-4,8,12,14]

/-- 邊界向量 t = e₆+e₁₁：d_last 位移的幾何身分。 -/
def tB : List ℤ := eV [6,11]

/-- 邊界目標 δ₍₀,S,1₎ − δ₍₀,S,0₎（states 序中位置 4 與 3）。 -/
def bd : List ℤ := [0,0,-1,1,0,0,0,0]

/-! ## §30 核內檢查（`decide` 證成） -/

example : C.all (fun c => matvec B c == zero8) := by decide
example : [Z1,Z2,Z3,Z4,Z5,Z6,Z7,Z8,Z9].all (fun z => matvec B z == zero8) := by decide
example : matvec B tB == bd := by decide

/-- 換基（span C ⊆ span Z；配合 Python 秩檢查 rank C = rank Z = 9 得相等）。 -/
example : C[0]! == Z1 := by decide
example : C[1]! == Z2 := by decide
example : C[2]! == addV Z5 (smul (-1) Z6) := by decide
example : C[3]! == Z6 := by decide
example : C[4]! == addV (addV (smul (-1) Z4) (smul (-1) Z5)) (addV Z6 Z8) := by decide
example : C[5]! == Z4 := by decide
example : C[6]! == addV (addV (smul (-1) Z1) Z4) (addV (smul (-1) Z8) Z9) := by decide
example : C[7]! == addV (addV Z1 (smul (-1) Z4)) (addV Z7 (addV Z8 (smul (-1) Z9))) := by decide
example : C[8]! == Z3 := by decide

/-! ## §31 真實差分的 10 = 9 + 1 分解（對真實 Collatz 單步逐一驗證） -/

def KEYS : List ((ℕ × Phase × ℕ) × ℕ) :=
  ([0,1,2].flatMap fun c => [0,1].map fun b => ((c, Phase.K, 0), b)) ++
  ([0,1,2].flatMap fun c => [0,1].flatMap fun p => [0,1].map fun b => ((c, Phase.S, p), b))
def F (x : ℕ) : List ℤ := KEYS.map (fun k => (occ2 (1, Phase.K, 0) (extIn x) k : ℤ))
def dFedge (x : ℕ) : List ℤ := ((F (Todd x)).zipWith (· - ·) (F x)).drop 2

section Verification

-- B·ΔF = k·bd 且 k = Δ(d_last)：x = 3, 5, …, 801
#eval (List.range 400).all fun i =>
  let x := 2 * i + 3
  let k : ℤ := (lastD 0 (extOut (Todd x)) : ℤ) - (lastD 0 (extOut x) : ℤ)
  matvec B (dFedge x) == smul k bd

-- 死座標（特徵 1,2）在差分恆零（drop 2 的合法性）
#eval (List.range 400).all fun i =>
  let x := 2 * i + 3
  (((F (Todd x)).zipWith (· - ·) (F x)).take 2).all (· == 0)

end Verification

end CollatzFST.CycleBasis
