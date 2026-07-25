/-
# Level 3 + 雙模式：規格偵察、資料鑑識與憑證修復（資訊清單見檔頭 D 節）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_2Mode_NoGo.lean`。

## A. 對方資料的三處損壞（已定案）

1. **λ 總和矛盾**：表列 19 個 λ 之和 = 10116 > 宣稱總和 9379；
   缺格 λ₂₀ 需為 −737 才能湊上——Farkas 乘數不得為負，故非缺格而是損壞。
2. **159→89 不可能**：Todd(159) = 239（3·159+1 = 478 = 2·239）。
   鑑識：Todd(59) = 89（178 = 2·89），且 m(59) = 1、m(89) = 0
   與表列該行「1→0」**完全吻合**——該行應為 x = 59（「159」為擠壓黏字）。
3. **Level 3 轉移函數與 48 維排序未提供**（規格缺漏）。

## B. 我方提案（本檔實作並驗證；待對方確認即為定案）

* **Level 3 定義**：狀態 (c, P, H)，H = (d_{i-2}, d_{i-1})；
  更新為統一位移 H' = (H.2, d)（Level 2 之 `step2_dPrev` 的直接推廣；
  K 期間 H = (0,0) 自動成立，非約定）。初始 (1, K, (0,0))。
* **48 維排序**：index(c, P, h₂, h₁, b) = 16c + 8·[P=S] + 4h₂ + 2h₁ + b。
  此排序恰使 (2, K, 0, 0, 1) 落在 **33**，與其模式索引標註一致（本檔自檢）。
* **模式跨層恆等**：m_L3(x) = F3(x)[33] ≡ m_L2(x) = F(x)[5]（x < 250 全驗）——
  兩者數同一物理事件（(2,K) 高能出口），Level 3 的模式語義自動繼承
  `boundary_step_unique`；出口唯一性在 Level 3 為 F3[16] + F3[33] = 1。
* **可達性**：BFS 得 **14 個可達狀態**（K 側 2 個：(1,K,(0,0)), (2,K,(0,0))；
  S 側 12 個全活）→ 48 維特徵中 **20 維恆死**，有效維度 28。

## C. 憑證修復（我方精確整數憑證；對偶核一維，本支撐上本質唯一）

修復後的 W₂₀（159 → 59），λ =
(397, 1499, 1734, 2571, 1197, 800, 1046, 2027, 1387, 2648, 3051, 2373,
 160, 1734, 1947, 428, 2005, 1846, 1850, 1046)，**Σλ = 31746**。
96 維組合 S 逐分量 ≥ 0，正座標 27 個（θ₀ 側 15、θ₁ 側 12），本檔 #eval 精確驗證。
原 LP（96 變數、20 約束）經 HiGHS 判定 infeasible。

## D. 需要向對方確認／索取的資訊

1. Level 3 轉移函數與排序：確認 B 節提案，或提供原始定義（若不同，重算即可）。
2. 159 列：確認為 x = 59（或提供原始未損表格）。
3. 他們的原始 λ（Σ = 9379 版）：**可要可不要**——C 節憑證已可直接形式化；
   若堅持沿用其數值，需未損原稿。
4. 他們的 S 支撐座標（§4 未列出）：我方已算出，可供其交叉核對。

## E. 關於一般化猜想的備註（邏輯跳躍所在）

「任意 Level N + M-Mode 皆不可行」中，每個**固定** (N, M) 的 no-go 是
有限憑證可證的（本管線可機械化）；但**全稱**敘述（∀ N, M）無法由有限
憑證覆蓋，需要本質不同的論證（如統一憑證族／泵引理式構造）。
可觀察的正向線索：模式觀測量跨層恆等、可達狀態嚴重退化
（Level 2: 8/9、Level 3: 14/24）暗示加深歷史的「有效資訊」增長受限——
但此為啟發，不入定理。建議先落地固定 (3, 2) 版，全稱版另立研究議程。

## 待令開工之定理形式

```
theorem no_go_level3_2mode_potential :
    ¬ ∃ (θ₀ θ₁ : Fin 48 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W20,
        (if (F3 (Todd x)).getD 33 0 = 1 then dot48 θ₁ (F3 (Todd x)) else dot48 θ₀ (F3 (Todd x)))
          - (if (F3 x).getD 33 0 = 1 then dot48 θ₁ (F3 x) else dot48 θ₀ (F3 x)) < 0
```
（W20 為修復版；dot48 為 48 分量線性形式，仿 `dot` 顯式展開。）
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_2Mode_NoGo

namespace CollatzFST.L3

open CollatzFST

/-! ## §42 Level 3 定義（提案） -/

/-- Level 3 聯合轉移：H 統一位移 H' = (H.2, d)。 -/
def step3 (s : ℕ × Phase × ℕ × ℕ) (b : ℕ) : ℕ × Phase × ℕ × ℕ :=
  (nextCarry s.1 b, phaseStep s.2.1 (outBit s.1 b), s.2.2.2, outBit s.1 b)

def microTrace3 : (ℕ × Phase × ℕ × ℕ) → List ℕ → List ((ℕ × Phase × ℕ × ℕ) × ℕ)
  | _, [] => []
  | s, b :: bs => (s, b) :: microTrace3 (step3 s b) bs

def occ3 (s : ℕ × Phase × ℕ × ℕ) (w : List ℕ) (f : (ℕ × Phase × ℕ × ℕ) × ℕ) : ℕ :=
  (microTrace3 s w).count f

/-- 提議排序：index = 16c + 8·[P=S] + 4h₂ + 2h₁ + b。 -/
def KEYS3 : List ((ℕ × Phase × ℕ × ℕ) × ℕ) :=
  [0,1,2].flatMap fun c => [Phase.K, Phase.S].flatMap fun P =>
    [0,1].flatMap fun h2 => [0,1].flatMap fun h1 => [0,1].map fun b => ((c, P, h2, h1), b)

def F3 (x : ℕ) : List ℤ := KEYS3.map fun k => (occ3 (1, Phase.K, 0, 0) (extIn x) k : ℤ)

/-- 修復後的 W₂₀（159 → 59）。 -/
def W20 : List ℕ := [25, 81, 59, 175, 251, 449, 473, 523, 537, 591, 623, 679, 683, 713, 745, 783, 839, 891, 903, 971]

/-- 我方精確整數憑證 (x, λ)。 -/
def cert3 : List (ℕ × ℤ) := [(25, 397), (81, 1499), (59, 1734), (175, 2571), (251, 1197), (449, 800), (473, 1046), (523, 2027), (537, 1387), (591, 2648), (623, 3051), (679, 2373), (683, 160), (713, 1734), (745, 1947), (783, 428), (839, 2005), (891, 1846), (903, 1850), (971, 1046)]

/-! ## §43 驗證（全部應輸出 `true`） -/

section Verification

-- 排序自檢：KEYS3[33] = ((2,K,0,0),1)、共 48 維
#eval KEYS3.getD 33 ((99, Phase.K, 9, 9), 9) == ((2, Phase.K, 0, 0), 1) && KEYS3.length == 48

-- 模式跨層恆等：m_L3 ≡ m_L2（x < 250）
#eval (List.range 250).all fun x =>
  (F3 x).getD 33 0 == (CollatzFST.TwoMode.F x).getD 5 0

-- Level 3 出口唯一性：F3[16] + F3[33] = 1（端點 + 範圍）
#eval ((W20.flatMap fun x => [x, Todd x]) ++ (List.range 100).map (2 * · + 3)).all fun n =>
  (F3 n).getD 16 0 + (F3 n).getD 33 0 == 1

-- 可達狀態 = 14（K 側恰 2）
#eval
  let bfs3 : ℕ → List (ℕ × Phase × ℕ × ℕ) → List (ℕ × Phase × ℕ × ℕ) := fun n0 acc0 =>
    (List.range n0).foldl (fun acc _ =>
      let nxt := (acc.flatMap fun s => [step3 s 0, step3 s 1]).filter (fun g => !acc.contains g)
      if nxt.isEmpty then acc else acc ++ nxt.eraseDups) acc0
  let R := bfs3 40 [(1, Phase.K, 0, 0)]
  R.length == 14 && (R.filter (fun s => s.2.1 == Phase.K)).length == 2

-- 鑑識：Todd 159 = 239 ≠ 89；Todd 59 = 89
#eval Todd 159 == 239 && Todd 59 == 89

-- 修復版 20 對 Todd 與模式表
#eval [(25, 0, 1), (81, 0, 1), (59, 1, 0), (175, 1, 1), (251, 1, 0), (449, 0, 0), (473, 0, 1), (523, 1, 0), (537, 0, 1), (591, 1, 1), (623, 1, 1), (679, 1, 1), (683, 1, 0), (713, 0, 1), (745, 0, 1), (783, 1, 1), (839, 1, 1), (891, 1, 0), (903, 1, 1), (971, 1, 0)].all fun t =>
  (F3 t.1).getD 33 0 == t.2.1 && (F3 (Todd t.1)).getD 33 0 == t.2.2

-- 我方憑證：λ ≥ 0、Σλ = 31746、96 維組合逐分量 ≥ 0 且與計算值逐位一致
#eval cert3.all (fun p => 0 ≤ p.2) && cert3.foldl (fun a p => a + p.2) 0 == (31746 : ℤ)
#eval
  let step := fun (acc : List ℤ) (p : ℕ × ℤ) =>
    let Fx := F3 p.1
    let Fy := F3 (Todd p.1)
    let ms := Fx.getD 33 0
    let me := Fy.getD 33 0
    (List.range 96).map fun j =>
      acc.getD j 0
      + (if (j : ℤ) / 48 == me then p.2 * Fy.getD (j % 48) 0 else 0)
      - (if (j : ℤ) / 48 == ms then p.2 * Fx.getD (j % 48) 0 else 0)
  let S := cert3.foldl step (List.replicate 96 (0 : ℤ))
  S == ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 347, 112, 0, 640, 213, 0, 0, 0, 0, 0, 0, 0, 0, 0, 539, 0, 101, 539, 0, 296, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 296, 0, 145, 151, 243, 296, 151, 0, 0, 0, 0, 0, 0, 0, 0, 0, 544, 0, 988, 0, 0, 155, 0, 0, 0, 1499, 0, 0, 0, 0, 0, 0, 155, 0, 0, 155, 0, 155, 0, 0, 1499, 0, 0, 0, 0, 0, 0, 0, 155, 0, 0, 155, 0, 155, 155, 0] : List ℤ) && S.all (0 ≤ ·)

end Verification

end CollatzFST.L3
