/-
# Project B 第九批（上）：R-B-L3——B 側 L3 語義層（L2 核心 × 歷史暫存器；誠實重定義）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。設計核准 2026-10-03
（RB-L3-DESIGN-REPORT；Q1–Q7 作答與裁決點 E1–E11 全項通過：E7 單 PR 兩檔、E2 B 型字典序、
E3 歸納帳 5 條、E6 跨層恆等升格、E9「可達恰 14」以閉包＋見證合證）。

`Core/` 對 Level 3 **零暴露**（`step3`／`run3`／`S14`／`F3`／終態定理全在 ProjectA，`scripts/check_boundaries.py`
禁止 B 匯入），故 B 側 L3 是**誠實重定義**。本檔是語義層：機器、可達閉包、Inv3、終態定理、48 維座標、
佔用向量、雙門；Sel 實例在姊妹檔 `Collatz_FST_B3_L3SelInstance.lean`。import 僅 B3a（→ Core、B0、B1）。

**路線（E1，NOTES Q1 (a) 投影路線）**：Core `step2_eq` 給 `step2 (c,P,p) b = (nextCarry, phaseStep P d, d)`，
A 的 `step3 (c,P,h₂,h₁) b = (nextCarry, phaseStep P d, h₁, d)`——丟掉較舊位 h₂ 即 Level 2。B 把這件事寫成型別：
L3 態 = L2 核心 `(c, P, p)` × 一條延遲一拍的歷史暫存器 h（`L3State_B := L2State × ℕ`），一步 = 核心走 Core `step2`、
暫存器接收舊 p。對應：A 的 (c, P, h₂, h₁) ↔ B 的 ((c, P, h₁), h₂)（p = 較新位 = L2 的 dPrev，h = 較舊位）。

## 內容

* **§L.1 機器**：`L3State_B`、`step3_B`、`run3_B`（`List.foldl`，串接律 `List.foldl_append` 免費）、`microTrace3_B`、
  `init3_B`；兩條投影（歸納 ②③）：`microTrace3_B_proj`（trace → Core `microTrace2`）、`run3_B_proj`（run → Core `run2`）。
* **§L.2 可達閉包與 Inv3**：`S14_B`（14 態）、`S14_B_closed`（含初態、對兩位元封閉）、見證 `S14_B_wit`／`S14_B_wit_run`／
  `S14_B_reachable`、`S14_B_K`（K 區恰 2、歷史 (0,0)）；trace 閉包 `microTrace3_B_mem`（歸納 ①）；`Inv3` 為其 `decide`
  系理（`inv3_of_mem`、`trace3_inv`）。
* **§L.3 終態定理**：`carry_digits_mem`（Core 兩錨）、`sentinel3`、**`run3_extIn_terminal_B`**（全體 x，兩終態）。
* **§L.4 座標**：`featIdx3_B`（B 型字典序，48 維）、`featList3_B`、`F3_B`。
* **§L.5 雙門**：`bndK3`、`featIdx3_eq_33`、`mem_iff_33`、`gate_pointwise3`、**`boundary_sum3_B : F3_B x 16 + F3_B x 33 = 1`**、
  `count33_le_one`。
* **§L.V1 電池**：字面即 `tools/b3_attest.py` §J 的錨。

## 技術註記（設計定案）

1. **E3（歸納帳）**：兩檔合計恰 5 條記帳級歸納，本檔 3 條——① `microTrace3_B_mem`（trace 閉包）、
   ② `microTrace3_B_proj`（每步 `rfl`）、③ `run3_B_proj`（每步 `rfl`）；姊妹檔 2 條（走行、wpath）。
   R-B 的 Q5 估計列「Inv3、投影、run3 閉包、走行、wpath」：Inv3 由 ① 承擔（`S14_B` 恰為 Inv3 的解集，K：2、S：12），
   run3 閉包被 ③ 取代——終態定理要的是讀完 digits 的進位，不是閉包。自含路線 (b) 同為 5 條（`boundary_step_unique`
   只對 `microTrace2` 敘述，投影躲不掉；終態進位亦需一條），(a) 的紅利是每步 `rfl` 與跨層恆等免費。
2. **E9（「可達恰 14」）**：由閉包 `S14_B_closed`（含初態 `init3_B`、對兩位元封閉）與見證 `S14_B_wit_run`（14 個字之像
   恰為 `S14_B`）合證；本檔**不立** run 閉包定理（`run3_B … ∈ S14_B`），用到可達性之處只需 trace 閉包 ①。
3. **E4（終態）**：讀完 digits 的進位 ∈ {1,2} 由 Core `terminal_carry_ne_zero`（≠ 0）＋ `run_carry_lt_three`（< 3）直接給出，
   不重推 A 的 `runCarry_digits_mem`（digits 末位 = 1 路線）；兩個哨兵零把任一進位 ∈ {1,2} 的態送到兩終態之一，
   與 P、p、h 無關（`sentinel3`，4 案 `simp`）。A 當年的難點（`S14` 中進位 0 的態有 4 個）因此不出現。
4. **E2（座標）**：`featIdx3_B ((c,P,p),h) b = 16c + 8·[P=S] + 4p + 2h + b`——B 型 ((c,P,p),h) 的自然字典序接位元
   （B3a 精神；48 維不摺疊；`% 48` 全函數化，B3a D2）。不參照 A 的 `KEYS3`；與 A 座標的雙射 σ₃ 由 attest §J 以 key
   語義比對建立並認證（交換 p／h 兩權重的對合，移動 24 點）。雙門 B 座標 16、33 與 A 數值相同：σ₃ 只移動 h ≠ p 的
   座標，而可達 K 列 h = p = 0——結構後果，非抄錄。
5. 零 `Fintype`、零 `maxHeartbeats` 調整、零 native 求值；`#print axioms` 僅標準公理。
-/
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_L2Instance

namespace CollatzFST.ProjectB

/-! ## §L.1 機器：L2 核心 × 歷史暫存器 -/

/-- B 側 L3 狀態：L2 核心 `(c, P, p)`（p = 最近一次輸出，Core `step2_dPrev`）× 較舊歷史位 h。
A 的 `(c, P, h₂, h₁)` ↔ B 的 `((c, P, h₁), h₂)`。 -/
abbrev L3State_B := L2State × ℕ

/-- L3 一步：核心照 Core `step2`、歷史暫存器接收舊 p（歷史移位 (h, p) ↦ (p, outBit c b)，新 p 即 `step2` 的
第三分量 `outBit c b`）。 -/
def step3_B (s : L3State_B) (b : ℕ) : L3State_B := (step2 s.1 b, s.1.2.2)

/-- L3 走行（`List.foldl`，與 `SelCostAutomaton.evalFrom` 同形）。 -/
def run3_B (s : L3State_B) (w : List ℕ) : L3State_B := w.foldl step3_B s

/-- L3 trace（Core `microTrace2` 同形）。 -/
def microTrace3_B : L3State_B → List ℕ → List (L3State_B × ℕ)
  | _, [] => []
  | s, b :: bs => (s, b) :: microTrace3_B (step3_B s b) bs

/-- 初態 ((1,K,0), 0)（A 的 (1,K,0,0)）。 -/
def init3_B : L3State_B := ((1, Phase.K, 0), 0)

@[simp] lemma run3_B_nil (s : L3State_B) : run3_B s [] = s := rfl

lemma run3_B_cons (s : L3State_B) (b : ℕ) (bs : List ℕ) :
    run3_B s (b :: bs) = run3_B (step3_B s b) bs := rfl

/-- 串接律（`List.foldl_append`；零歸納）。 -/
lemma run3_B_append (s : L3State_B) (u v : List ℕ) :
    run3_B s (u ++ v) = run3_B (run3_B s u) v := List.foldl_append ..

/-- **歸納 ③（run 投影，記帳級）**：L3 走行的核心分量 = Core `run2`（每步 `rfl`）。 -/
theorem run3_B_proj : ∀ (w : List ℕ) (s : L2State) (h : ℕ), (run3_B (s, h) w).1 = run2 s w
  | [], _, _ => rfl
  | b :: bs, s, _ => run3_B_proj bs (step2 s b) s.2.2

/-- **歸納 ②（trace 投影，記帳級）**：忘掉歷史位 = Core `microTrace2`（每步 `rfl`）——Core
`boundary_step_unique` 由此搬到 L3 trace。 -/
theorem microTrace3_B_proj : ∀ (w : List ℕ) (s : L2State) (h : ℕ),
    (microTrace3_B (s, h) w).map (fun t => (t.1.1, t.2)) = microTrace2 s w
  | [], _, _ => rfl
  | b :: bs, s, _ => by
      show (s, b) :: (microTrace3_B (step2 s b, s.2.2) bs).map _
        = (s, b) :: microTrace2 (step2 s b) bs
      rw [microTrace3_B_proj bs]

/-! ## §L.2 可達閉包 S14_B 與 Inv3 -/

/-- 14 個可達態：K 側 2、S 側 12（A 的 `S14` 經 (c,P,h₂,h₁) ↦ ((c,P,h₁),h₂)）。 -/
def S14_B : List L3State_B :=
  [((1, .K, 0), 0), ((2, .K, 0), 0),
   ((0, .S, 0), 0), ((0, .S, 0), 1), ((0, .S, 1), 0), ((0, .S, 1), 1),
   ((1, .S, 0), 0), ((1, .S, 0), 1), ((1, .S, 1), 0), ((1, .S, 1), 1),
   ((2, .S, 0), 0), ((2, .S, 0), 1), ((2, .S, 1), 0), ((2, .S, 1), 1)]

/-- 閉包：`S14_B` 對兩位元封閉（`decide`）；初態 `init3_B` 是其首元。 -/
theorem S14_B_closed : ∀ s ∈ S14_B, ∀ b < 2, step3_B s b ∈ S14_B := by decide

/-- 可達見證字（BFS 最短，與 `S14_B` 同序）。 -/
def S14_B_wit : List (List ℕ) :=
  [[], [1], [0, 0, 0], [0, 0], [0], [0, 1, 0], [0, 1, 1, 0], [1, 1, 0], [0, 0, 1], [0, 1],
   [1, 1, 0, 1], [0, 1, 1], [1, 1], [1, 1, 1]]

/-- 見證之像恰為 `S14_B`（`decide`）。與 `S14_B_closed` 合證「可達恰 14」（E9）。 -/
theorem S14_B_wit_run : S14_B_wit.map (run3_B init3_B) = S14_B := by decide

/-- 每個 `S14_B` 態皆由某個位元字從初態到達（`S14_B_wit_run` 的逐元形）。 -/
theorem S14_B_reachable :
    ∀ s ∈ S14_B, ∃ w : List ℕ, (∀ b ∈ w, b < 2) ∧ run3_B init3_B w = s := by
  intro s hs
  rw [← S14_B_wit_run] at hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
  have hbits : ∀ v ∈ S14_B_wit, ∀ b ∈ v, b < 2 := by decide
  exact ⟨w, hbits w hw, rfl⟩

/-- **K 區可達恰兩態** ((1,K,0),0)、((2,K,0),0)（A 的 (1,K,0,0)、(2,K,0,0)）：歷史恆 (0,0)。 -/
theorem S14_B_K :
    S14_B.filter (fun s => s.1.2.1 == Phase.K) = [((1, .K, 0), 0), ((2, .K, 0), 0)] := by
  decide

/-- **歸納 ①（trace 閉包，記帳級）**：起點在 `S14_B`、讀位元 ⟹ trace 每筆的狀態在 `S14_B`、位元 < 2
（A `microTrace3_mem_S14`／Core `microTrace2_inv` 的鏡射）。 -/
theorem microTrace3_B_mem : ∀ (w : List ℕ) (s : L3State_B), s ∈ S14_B → (∀ b ∈ w, b < 2) →
    ∀ t ∈ microTrace3_B s w, t.1 ∈ S14_B ∧ t.2 < 2 := by
  intro w
  induction w with
  | nil => intro _ _ _ t ht; cases ht
  | cons b bs ih =>
      intro s hs hw t ht
      have hb : b < 2 := hw b (List.mem_cons_self ..)
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨hs, hb⟩
      · exact ih (step3_B s b) (S14_B_closed s hs b hb)
          (fun y hy => hw y (List.mem_cons_of_mem _ hy)) t ht'

/-- L3 不變量（Core `Inv` 的 L3 版）：進位 < 3、兩歷史位 < 2、K 相位 ⟹ 進位 ≠ 0 且歷史 = (0,0)。
最後一項即旗標接地的 K 區輸入。 -/
def Inv3 (s : L3State_B) : Prop :=
  s.1.1 < 3 ∧ s.1.2.2 < 2 ∧ s.2 < 2 ∧ (s.1.2.1 = Phase.K → s.1.1 ≠ 0 ∧ s.1.2.2 = 0 ∧ s.2 = 0)

/-- Inv3 是閉包的 `decide` 系理（零歸納；`S14_B` 恰為 Inv3 的解集：K 側 c ∈ {1,2}、p = h = 0 共 2，S 側 12）。 -/
theorem inv3_of_mem : ∀ s ∈ S14_B, Inv3 s := by
  unfold Inv3; decide

/-- `extIn x` 的 L3 trace 逐筆滿足 Inv3、位元 < 2（① ＋ `inv3_of_mem`）。 -/
theorem trace3_inv (x : ℕ) : ∀ t ∈ microTrace3_B init3_B (extIn x), Inv3 t.1 ∧ t.2 < 2 := by
  intro t ht
  have h := microTrace3_B_mem (extIn x) init3_B (by decide) (extIn_bits x) t ht
  exact ⟨inv3_of_mem _ h.1, h.2⟩

/-! ## §L.3 終態定理（B 自產；重推 A 的 `run3_extIn_terminal`） -/

/-- 讀完 digits 後進位 ∈ {1,2}：Core `terminal_carry_ne_zero`（≠ 0）＋ `run_carry_lt_three`（< 3）。零歸納。 -/
lemma carry_digits_mem (x : ℕ) :
    runCarry (Nat.digits 2 x) 1 = 1 ∨ runCarry (Nat.digits 2 x) 1 = 2 := by
  have h0 := terminal_carry_ne_zero x
  have h3 : (run 1 (Nat.digits 2 x)).1 < 3 :=
    run_carry_lt_three (by norm_num) (fun b hb => Nat.digits_lt_base (by norm_num) hb)
  unfold runCarry
  omega

/-- 兩個哨兵零：進位 ∈ {1,2} 的任一態讀 [0,0] 落兩終態之一——與相位、兩歷史位無關
（進位 1 ↦ ((0,S,0),1)、進位 2 ↦ ((0,S,1),0)）。 -/
lemma sentinel3 (s : L3State_B) (hc : s.1.1 = 1 ∨ s.1.1 = 2) :
    run3_B s [0, 0] = ((0, Phase.S, 1), 0) ∨ run3_B s [0, 0] = ((0, Phase.S, 0), 1) := by
  obtain ⟨⟨c, P, p⟩, h⟩ := s
  simp only at hc
  rcases hc with rfl | rfl <;> cases P <;>
    simp [run3_B, step3_B, step2_eq, outBit, nextCarry, phaseStep]

/-- **終態定理（B 自產）**：讀完 `extIn x` 的 L3 態恆為 ((0,S,1),0) 或 ((0,S,0),1)
（A 的 (0,S,0,1)、(0,S,1,0)）——對全體 x，零新歸納（③ ＋ Core `run2_fst` ＋ `carry_digits_mem` ＋ `sentinel3`）。
重推 A 的 `L3.run3_extIn_terminal`（B 不可 import）。 -/
theorem run3_extIn_terminal_B (x : ℕ) :
    run3_B init3_B (extIn x) = ((0, Phase.S, 1), 0)
      ∨ run3_B init3_B (extIn x) = ((0, Phase.S, 0), 1) := by
  have hc : (run3_B init3_B (Nat.digits 2 x)).1.1 = runCarry (Nat.digits 2 x) 1 := by
    rw [show init3_B = ((1, Phase.K, 0), 0) from rfl, run3_B_proj, run2_fst]
  rw [show extIn x = Nat.digits 2 x ++ [0, 0] from rfl, run3_B_append]
  apply sentinel3
  rw [hc]
  exact carry_digits_mem x

/-! ## §L.4 B 座標與佔用向量（48 維；自選枚舉序） -/

/-- B 自訂 L3 座標（E2）：B 狀態型 ((c, P, p), h) 與位元 b 的字典序（K < S；不摺疊）：
`16c + 8·[P = S] + 4p + 2h + b`。垃圾輸入以 `% 48` 收回 `Fin 48`（B3a D2）——`extIn` 走行上不出現。 -/
def featIdx3_B : L3State_B → ℕ → Fin 48
  | ((c, .K, p), h), b => ⟨(16 * c + 4 * p + 2 * h + b) % 48, Nat.mod_lt _ (by decide)⟩
  | ((c, .S, p), h), b => ⟨(16 * c + 8 + 4 * p + 2 * h + b) % 48, Nat.mod_lt _ (by decide)⟩

/-- L3 走行的特徵座標序列。 -/
def featList3_B (x : ℕ) : List (Fin 48) :=
  (microTrace3_B init3_B (extIn x)).map fun t => featIdx3_B t.1 t.2

/-- **B 的 L3 佔用向量**：座標 i 在走行上出現的次數。由 B 機器重新定義，不經 A 的 `KEYS3`／`occ3`；
與 A 的 `F3` 的座標雙射 σ₃ 由 `tools/b3_attest.py` §J 認證。 -/
def F3_B (x : ℕ) (i : Fin 48) : ℕ := (featList3_B x).count i

/-! ## §L.5 雙門 -/

/-- 高能出口門（L3）：((2,K,0),0) 讀 1 的 K→S 出口，B 座標 33。 -/
abbrev bndK3 : L3State_B := ((2, Phase.K, 0), 0)

/-- 座標 33 的唯一性（Inv3 之下）：K 列 `16c + 4p + 2h + b = 33` 且 p = h = 0 ⟹ c = 2、b = 1；
S 列 `16c + 8 + 4p + 2h + b = 33` 於 c < 3、p,h,b < 2 無解。皆 `omega`。 -/
lemma featIdx3_eq_33 {t : L3State_B × ℕ} (hinv : Inv3 t.1) (hb : t.2 < 2)
    (h33 : featIdx3_B t.1 t.2 = 33) : t = (bndK3, 1) := by
  obtain ⟨⟨⟨c, P, p⟩, h⟩, b⟩ := t
  simp only [Inv3] at hinv hb
  obtain ⟨hc, hp, hh, hK⟩ := hinv
  have h' := congrArg Fin.val h33
  cases P
  · simp only [featIdx3_B] at h'
    change (16 * c + 4 * p + 2 * h + b) % 48 = 33 at h'
    obtain ⟨-, hp0, hh0⟩ := hK rfl
    subst hp0 hh0
    have hc2 : c = 2 := by omega
    have hb1 : b = 1 := by omega
    subst hc2 hb1
    rfl
  · simp only [featIdx3_B] at h'
    change (16 * c + 8 + 4 * p + 2 * h + b) % 48 = 33 at h'
    omega

/-- 走行經過 (((2,K,0),0), 1) ⟺ 座標 33 出現在 `featList3_B x`（← 方向用 `trace3_inv` 取 Inv3）。 -/
lemma mem_iff_33 (x : ℕ) :
    (bndK3, 1) ∈ microTrace3_B init3_B (extIn x) ↔ (33 : Fin 48) ∈ featList3_B x := by
  constructor
  · intro h
    exact List.mem_map.mpr ⟨(bndK3, 1), h, rfl⟩
  · intro h
    obtain ⟨t, ht, hft⟩ := List.mem_map.mp h
    have hi := trace3_inv x t ht
    rw [featIdx3_eq_33 hi.1 hi.2 hft] at ht
    exact ht

/-- 雙門的逐點刻畫（Inv3 之下，R-B `gate_pointwise` 同形）：「K 相位且輸出 1」的步 ∧ 進位 = 2 ⟺ 座標 33
（門 33：((2,K,0),0) 讀 1）；∧ 進位 ≠ 2 ⟺ 座標 16（門 16：((1,K,0),0) 讀 0）。K 列由 Inv3 收成 c ∈ {1,2}、
p = h = 0；S 列 24 案 `decide`。 -/
lemma gate_pointwise3 {t : L3State_B × ℕ} (hinv : Inv3 t.1) (hb : t.2 < 2) :
    ((t.1.1.2.1 == Phase.K && outBit t.1.1.1 t.2 == 1) && (t.1.1.1 == 2)) = (featIdx3_B t.1 t.2 == 33)
    ∧ ((t.1.1.2.1 == Phase.K && outBit t.1.1.1 t.2 == 1) && !(t.1.1.1 == 2))
      = (featIdx3_B t.1 t.2 == 16) := by
  obtain ⟨⟨⟨c, P, p⟩, h⟩, b⟩ := t
  simp only [Inv3] at hinv hb
  obtain ⟨hc, hp, hh, hK⟩ := hinv
  cases P
  · obtain ⟨hc0, hp0, hh0⟩ := hK rfl
    subst hp0 hh0
    interval_cases c
    · exact absurd rfl hc0
    · interval_cases b <;> decide
    · interval_cases b <;> decide
  · interval_cases c <;> interval_cases p <;> interval_cases h <;> interval_cases b <;> decide

/-- **L3 邊界和（雙門讀法）**：K→S 的出口只有兩道門——門 16 = ((1,K,0),0) 讀 0、門 33 = ((2,K,0),0) 讀 1，
每條 `extIn` 走行恰穿過其中一道：`F3_B x 16 + F3_B x 33 = 1`，對全體 x（② 把 Core `boundary_step_unique` 搬到
L3 trace ＋ `countP_bool_split` 依「進位 = 2」拆分 ＋ `gate_pointwise3` 逐點對齊）。

此即 A 之 `L3.mode_bit_endpoints3`（`L3_2Mode_NoGo`，40 個端點 `decide`；當年補上雙模式第 65 條泛函
θ₀[16] + θ₁[33] = 0 缺口的那條引理）在 B 側的重生，且為全稱形（A 側的全稱形是 `L3_Flow` §72 `occ3_mode_bit_sum`）。
**L3 模式 = 走哪道 K 出口門**：`F3_B x 33 = 1` ⟺ 高能門、`F3_B x 16 = 1` ⟺ 低能門，互斥且窮盡。 -/
theorem boundary_sum3_B (x : ℕ) : F3_B x 16 + F3_B x 33 = 1 := by
  unfold F3_B featList3_B
  rw [List.count_eq_countP, List.count_eq_countP, List.countP_map, List.countP_map]
  have hsplit := countP_bool_split
    (fun t : L3State_B × ℕ => t.1.1.2.1 == Phase.K && outBit t.1.1.1 t.2 == 1)
    (fun t => t.1.1.1 == 2) (microTrace3_B init3_B (extIn x))
  have hbnd : (microTrace3_B init3_B (extIn x)).countP
      (fun t : L3State_B × ℕ => t.1.1.2.1 == Phase.K && outBit t.1.1.1 t.2 == 1) = 1 := by
    have hb := boundary_step_unique x
    rw [← microTrace3_B_proj (extIn x) (1, Phase.K, 0) 0, List.countP_map] at hb
    exact hb
  rw [hbnd] at hsplit
  have h33 : (microTrace3_B init3_B (extIn x)).countP
      ((fun i => i == (33 : Fin 48)) ∘ fun t => featIdx3_B t.1 t.2)
      = (microTrace3_B init3_B (extIn x)).countP
        (fun t => (t.1.1.2.1 == Phase.K && outBit t.1.1.1 t.2 == 1) && (t.1.1.1 == 2)) := by
    apply countP_congr'
    intro t ht
    have hi := trace3_inv x t ht
    exact (gate_pointwise3 hi.1 hi.2).1.symm
  have h16 : (microTrace3_B init3_B (extIn x)).countP
      ((fun i => i == (16 : Fin 48)) ∘ fun t => featIdx3_B t.1 t.2)
      = (microTrace3_B init3_B (extIn x)).countP
        (fun t => (t.1.1.2.1 == Phase.K && outBit t.1.1.1 t.2 == 1) && !(t.1.1.1 == 2)) := by
    apply countP_congr'
    intro t ht
    have hi := trace3_inv x t ht
    exact (gate_pointwise3 hi.1 hi.2).2.symm
  rw [h16, h33, Nat.add_comm]
  exact hsplit.symm

/-- **count33 ≤ 1**：邊界和的系理。 -/
theorem count33_le_one (x : ℕ) : F3_B x 33 ≤ 1 := by
  have := boundary_sum3_B x
  omega

/-! ## §L.V1 數據驗證（全部應輸出 `true`）

字面即 `tools/b3_attest.py` §J 的錨（`LEAN_RBL3_*`）。 -/

section Verification

private def bfs3 : ℕ → List L3State_B → List L3State_B
  | 0, acc => acc
  | n + 1, acc =>
      let nxt := (acc.flatMap fun s => [step3_B s 0, step3_B s 1]).filter (fun g => !acc.contains g)
      if nxt.isEmpty then acc else bfs3 n (acc ++ nxt.eraseDups)

-- 1 可達：BFS 恰 14 態 ≡ S14_B（集合相等）
#eval let R := bfs3 40 [init3_B]
      R.length == 14 && R.all (· ∈ S14_B) && S14_B.all (· ∈ R)
-- 2 trace 閉包數值形（x < 200）：每筆狀態 ∈ S14_B、位元 < 2
#eval (List.range 200).all fun x =>
  (microTrace3_B init3_B (extIn x)).all fun t => t.1 ∈ S14_B && t.2 < 2
-- 3 終態（x < 300 全體 ∈ 兩終態）＋ 兩終態皆出現：1787 ↦ ((0,S,1),0)、2681 ↦ ((0,S,0),1)
#eval (List.range 300).all fun x =>
  run3_B init3_B (extIn x) == ((0, Phase.S, 1), 0) || run3_B init3_B (extIn x) == ((0, Phase.S, 0), 1)
#eval run3_B init3_B (extIn 1787) == ((0, Phase.S, 1), 0)
  && run3_B init3_B (extIn 2681) == ((0, Phase.S, 0), 1)
-- 4 兩條投影數值形：trace（x < 100）、run 核心 = run2（x < 150）
#eval (List.range 100).all fun x =>
  (microTrace3_B init3_B (extIn x)).map (fun t => (t.1.1, t.2)) == microTrace2 (1, Phase.K, 0) (extIn x)
#eval (List.range 150).all fun x => (run3_B init3_B (extIn x)).1 == run2 (1, Phase.K, 0) (extIn x)
-- 5 雙門（x < 300）＋ 門的實例：25、2681 走門 16；3、1787 走門 33
#eval (List.range 300).all fun x => F3_B x 16 + F3_B x 33 == 1
#eval [25, 2681].all (fun x => F3_B x 16 == 1 && F3_B x 33 == 0)
  && [3, 1787].all (fun x => F3_B x 33 == 1 && F3_B x 16 == 0)
-- 6 featList3_B 字面（attest 錨；2011 = 1787 的兩個同錨閉走行對調，與 L2 同形）、走行長 13
#eval featList3_B 1787 == [17, 33, 44, 27, 41, 45, 47, 47, 46, 27, 41, 44, 26]
#eval featList3_B 2011 == [17, 33, 44, 27, 41, 44, 27, 41, 45, 47, 47, 46, 26]
#eval (featList3_B 1787).length == 13 && (featList3_B 2011).length == 13
-- 7 佔用向量總和 = 走行長度（x < 200）
#eval (List.range 200).all fun x => ((List.finRange 48).map (F3_B x)).sum == (extIn x).length
-- 8 死座標：S14_B × {0,1} 的 28 條邊之外的 20 個座標恆零（x < 200）
#eval ((List.finRange 48).filter fun i =>
  !(S14_B.flatMap fun s => [featIdx3_B s 0, featIdx3_B s 1]).contains i).length == 20
#eval (List.range 200).all fun x =>
  ((List.finRange 48).filter fun i => F3_B x i != 0).all fun i =>
    (S14_B.flatMap fun s => [featIdx3_B s 0, featIdx3_B s 1]).contains i

end Verification

end CollatzFST.ProjectB
