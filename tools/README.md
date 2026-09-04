# tools/ — 憑證的重算與搜尋

Lean 端三條 no-go 定理裡寫死的數字（見證集合 `W₁₀`/`W₁₂`/`W₂₀`、對偶權重 λ、
`Σλ = 1024 / 7826 / 31746`）不是憑空來的。這個資料夾是它們的出處。

分成兩層，**性質完全不同，不要混用**：

| | `certificates.py`、`a3_functionals.py`、`l3_recon.py` | `search/` |
|---|---|---|
| 做什麼 | 重算並驗證**既有**憑證與結構結論 | 搜尋**新的**憑證與反例 |
| 算術 | 精確有理（sympy），無浮點 | 浮點 LP / SMT |
| 決定性 | 完全決定性 | 有隨機取樣，結果會變 |
| 依賴 | numpy、sympy | 再加 scipy、z3-solver |
| 耗時 | 本機實測 0.9 / 2.6 / 15 秒（三次取樣；審查者沙盒實測 l3_recon 約 51 秒——機器差異可達 3 倍） | 數十秒到數十分鐘 |
| CI | **每次 push 都跑** | 不跑 |

## 環境

```bash
python3 -m venv .venv && source .venv/bin/activate
pip install -r tools/requirements.txt
python3 tools/certificates.py
```

只想跑 CI 那份驗證的話 `pip install numpy sympy` 就夠了。

## certificates.py 驗了什麼

1. **交叉驗證**：Python 這邊獨立重寫了一次特徵萃取（`F2` / `F3`），
   算出的 ΔF 與 Lean `occ2` 的 `#eval` 輸出逐位比對。
   兩邊獨立實作卻錯得一模一樣的機率極低，所以這是對「特徵定義是否忠實」的有效檢查。
2. **重算憑證**：不看答案，用精確有理算術從見證集合解出 λ，確認就是 Lean 裡那組整數。
   Level 2 單模式的解族是**唯一的**（相差一個正純量），
   也就是說 `(100, 64, 119, 51, 56, 183, 164, 18, 191, 78)` 是該見證集合的
   典範最小整數憑證，不是隨便挑的一組。
3. **模式流量平衡** `Σλ(e_{m(y)} − e_{m(x)}) = 0`。
   兩個雙模式憑證都通過——這正是 ROADMAP A-2 仿射截距升級成立的前提條件。
4. **Cramer 結構**（`--cramer`）：λ 垂直於「被組合湮滅」的那些座標列，該列集的秩恰為
   見證數 − 1，所以 λ 在相差尺度下唯一；由 Cramer，**λ 就是那些列的極大子式向量
   除以 gcd**，而憑證的整數值 `S_j` 就是 `det[被湮滅列 | 第 j 列] / gcd`。
   單模式那組退化成最乾淨的形式：`λ = adj(A_free)` 的第 2 列、`31 = det(A_free)`、
   gcd = 1，故最小整數尺度必然是 `|det| = 31`——上面第 2 點的「唯一性」與 A-3 下界
   用的 `det = 31`（`Collatz_FST_DimLower.lean`）因此是同一件事。
   注意 `Σλ`（1024 / 7826 / 31746）**不是**行列式，腳本有一條檢查專門守這個誤推。
   **B3a 補充（2026-09-04）**：「31 = det」是**目標 e₆ 相依**的子式——同一 W₁₀ 另有
   目標 e₈（det 31）與 e₁₇（det 1，么模、Σλ = 34）的單座標憑證，全域的 Farkas
   多胞形維度 ≥ 1；見 `b3_attest.py` 與 ROADMAP-B B3 完成紀錄第 5 點。

## a3_functionals.py 驗了什麼

ROADMAP A-3 的上界問題「到底要證哪幾條泛函、夠不夠」。同樣是精確有理、完全決定性，
但驗的不是憑證數字而是**結構結論**，所以另立一檔。**進 CI，每次 push 都跑**
（實測約 2 秒，掛在 `certificates.py` 那個 job 的第二步）：

* `dim span(ΔF) = 10`，故上界需要 8 條獨立泛函。
* 死狀態 2 條 + Kirchhoff 流守恆可用 7 條（秩 6）= 秩 8，**完備**。
* `boundary_step_unique` 與 K 區交錯計數落在上述列空間內，是被蘊含的推論，
  **不需要另證**——這是對 ROADMAP 舊表的修正，詳見 `docs/ROADMAP-A.md` A-3。
* **Lean↔Python 對帳（三條錨）**：`LEAN_INEDGES`（`Flow.inEdges` 的 16 邊關聯表）、
  `LEAN_DELTA_RELATIONS`（`FlowDelta` §53–54 的 9 條差分層恆等式係數向量）、
  `LEAN_FREE_IDX` + `LEAN_RECONSTRUCTION`（`DimUpper` §58 的 10 個自由座標，
  與另外 8 個座標的重建公式）。本腳本用自己的 `step2` 重算後逐條比對，並確認：
  那 9 條在 ΔF 上恆為零、秩 = 8、與「死狀態 + 可用流守恆」張出同一空間；
  自由座標全零迫使整個向量為零（對應 `pick_injective_on_Sol`）；
  重建公式與 9 條解出來的一致。
  與 `certificates.py` 的 `LEAN_DF10` 同一個模式——**沒有這些錨，腳本守的只是
  數學結論**，Lean 的 `step2`、那 9 條定理或自由座標選取被改動時不會叫。

ROADMAP A-3 現在寫進了具體秩數字，這支腳本就是它們在 repo 裡的出處。
沒有它，那些數字只是傳說——`W₁₂` / `W₂₀` 憑證當初就是這樣壞掉的。

## l3_recon.py 驗了什麼

ROADMAP A-3 的 **Level 3（31 維）**部分——在寫任何 Lean 之前先把數字釘住。
**進 CI**（本機約 15 秒、慢機可達 ~50 秒，秩計算為主；再加重就把重秩檢查移到 `--deep` 旗標）。

* 可達狀態 14、可達邊 28、48 維裡恆死 20（合 HandOver）。
* 終末狀態 **2 個**：`(0,S,0,1)`、`(0,S,1,0)`。`(0,S,0,0)` 從不出現。
* 流守恆 **12 乾淨 + 1 合併 = 13 條**（Level 2 是 6+1=7）。
* 單模式 `dim span(ΔF3) = 16`，死座標 20 + 流守恆 13 = 秩 32 ⇒ **完備**。
* 雙模式 `dim span = 31`（合 HandOver），需 65 條；提升家族 + 2 條區塊相依死座標
  = 秩 64 ⇒ **缺 1 條**，而那 1 條就是 `F3[16] + F3[33] = 1`（既有的
  `mode_bit_endpoints3`）提升到差分層，不是新數學。
* **維度與奇偶無關**（奇數 / 全部 x 都是 16/31）⇒ Lean 敘述不需要 `x % 2 = 1`。

這支腳本的存在本身是個教訓：第一版偵察因為 `bin(0)[2:] == "0"` 讓 `extIn 0`
多一個哨兵零，導出「終末 3 個、缺 5 條」兩個錯結論。`certificates.py` 的 `_bits`
有同一個 off-by-one，已一併修好——**Level 2 的見證集全是奇數 ≥ 25 所以不咬人，
一到 Level 3 掃 `x = 0` 就咬**。

## b3_attest.py 驗了什麼

B3a（ROADMAP-B B3 第一階段）在 `ProjectB/Collatz_FST_B3_L2Instance.lean` 用**零
ProjectA import** 的素材重推 Level 2 單模式 no-go；`check_boundaries.py` 禁止 B 匯入 A，
所以「兩個獨立重推導出同一數學」只能在 tools 層認證——這支腳本是唯一同時 import
兩側的橋。精確整數／有理、零浮點、**進 CI**（實測約 2 秒，含 §G、§H）：

* **B 側自含實作＋Lean 錨**：照 Lean 定義逐字重寫 `step2`／`lstep`／`featIdx`／
  `featList`／`F_B`；錨 `LEAN_B3_W`／`LEAN_B3_TODD`／`LEAN_B3_LAM`／
  `LEAN_B3_AGG_*`／`LEAN_B3_FEATLIST`（20 條，自 Lean §B3.V 電池抄錄）雙向對帳。
* **λ_B 獨立重解**：18 座標逐一「湮滅其餘 17 座標」的單座標憑證掃描（sympy 有理
  nullspace）——W₁₀ 上恰三個（B 座標 k = 2／4／17，Σλ = 1024／312／34，係數
  31／31／1），Lean 用最輕的 k = 17；全部 Farkas 條件純整數驗證；另以 sympy 精確
  單純形確認 Farkas 多胞形非空（第四頂點 Σλ = 1387、聚合 31·(e₉+e₁₄)，僅印出）。
* **三段式認證**：(i) σ(B→A) 由 key 比對建立並驗雙射，`F_B x ≡ F2 x ∘ σ` 對
  x < 4096 全體（含 x = 0、1）；(ii) `certificates.py` 的 `LAM10` 經 σ 恰為掃描的
  k = σ⁻¹(6) = 2 成員；(iii) Lean `lamB` = 掃描最輕成員。
* **B2 引擎 harness**（NOTES Q4）：`L2auto θ` 在 `{some 0, some 1, none}` 上的可達
  乘積態截斷（22 態、`none ↦ 2`）餵 `b2_engine`，四組 θ 覆蓋 pass／fail-循環／
  fail-邊界，見證去標記後恰為某 `extInM x`、引擎成本 = 直接求值。
* **負向測試**常駐：featList 錨、λ、聚合座標、σ 各竄改一筆必紅。
* **§G（B3b，2026-09-04）**：呼叫 `b3b_diff.py` 的 CI 段 `run_checks`（下節）；CI 維持
  attest 一步、`.github` 零變更（NOTES Q5）。
* **§H（B3c，2026-09-04）**：Lean↔tools **字面同步**——`ProjectB/Collatz_FST_B2_PassCert.lean`
  的驗證書 T3（`MposNeg` 四欄＋憑證 (R, C, d) = (全態, 全態, (−5, −3, −2))）與 T1 見證 `[0, 1]`
  vs `b2_engine` 實跑（T1／T3 verdict、`verify_pass_cert`；竄改 d₂／d₁ 必紅）；
  `ProjectB/Collatz_FST_B3_OpposingPair.lean` 的對立對 (25, 315)：Todd 值 (19, 473)、四條
  featList、ΔF_B(25) 向量 vs B 側重算、`b3b_diff.EXPECT_PAIR`、A 側 F2 通道；機制觀察
  （同一 4 步閉走行 `[9, 15, 17, 16]` 插進兩走行）入錨（觀察層）；負向三則。< 0.1 秒。

## b3b_diff.py 驗了什麼

B3b（ROADMAP-B B3 第二階段）把 B3a 的見證集 no-go 升到**全語言**——純 tools、零 Lean
（Lean 鏡射：B3c 已落地對立對定理與 P1–P5 驗證書；D(θ) 本體待排程）。函式庫形、**純標準庫**（`fractions.Fraction`，零浮點），CI 段由 `b3_attest.py`
§G 呼叫（實測約 1.4 秒），本檔自己的入口只有本機重掃 `--deep`（約 15 秒，不進 CI）：

* **差分自動機 `D(θ)`**：輸入側 Core Level-2 機器 ×（輸出側同一台機器，由輸入側發射位
  `d = outBit` 同步驅動、於 K→S 邊界啟動；idle ⟺ 輸入側在 K）× 7 態 ranking-domain DFA
  （B0 `lstep` 加 `one` 排除 `[1]`——x = 1 的終態與 x = 3, 13, 53, … 共用，接受集排除法不成立）。
  邊權向量 `e_{featIdx(out,d)} − e_{featIdx(in,b)}`、α = 0、尾聲 1+p 個哨兵零押進 β；
  `instantiate(θ)` 給 b2 `mk_automaton`。錨：可達 65／useful 39／邊 75／接受態 4（輸入分量恰
  A 的終末態對）、x = 3／x = 5 手算逐步邊權與 β、x = 1 拒絕。
* **成本橋**（通道分離）：向量形 `vec_cost(extInM x) = ΔF_B(x)` 對 x < 8192 全體（ΔF_B 經
  `b3_attest.py` 的 B 側自含實作）；引擎通道：b2_engine `_cost` 對 4 組固定種子隨機有理 θ
  （含負值）× 奇 x < 2048。
* **θ-LP 與圖憑證**：trim 圖 simple cycles 328（相異權向量 175）、elementary 接受路徑 8269
  （相異 5140）；`∃θ ≥ 0 AllNeg(θ)` ⟺ `{θ ≥ 0, θ·v(C) ≤ 0, θ·w(p) ≤ −1}` 可行。
  **自建精確兩階段單純形**（Bland 規則）解其 Farkas 對偶；**求解器輸出不受信任**——可行點
  與 Farkas 乘子都由呼叫端純有理／純整數驗證（設計階段 sympy `linprog` 曾對本實例回傳違反
  約束的點，故 LP 不用 sympy）。結果**不可行**，整數憑證三種、同一驗證器：LP 導出（6 循環 +
  1 路徑，只印不錨）、**對立對 (25, 315)**（ν = (1, 1)、零循環、聚合 = 0；三件套入錨：
  ΔF_B 和為零、兩走行皆 elementary、皆在域內）、**B3a 提升**（λ_B 沿 W₁₀ 走行切環分解：
  9 路徑生成元 Σν 34 + 5 循環生成元 Σμ 26、聚合 e₁₇ = Lean `agg_eq_e17`）。
* **負向測試**：刪一列／換一列／循環係數 +1 必紅；去掉路徑列（加 Σθ_活 = 1）⟹ LP 可行
  （θ = e₆：邊界座標 6／13 不在任何循環上）；去掉循環列 ⟹ 仍不可行（對立對只用路徑列）——
  障礙完全住在邊界（路徑）結構。
* **B2 引擎 harness**：25 組 θ ≥ 0 全數 fail，見證去標記解碼回奇數 x > 1、直接求值
  `D_θ(x) ≥ 0` 且 = 引擎成本；最小見證 x = 3；boundary 模式恰 {θ≡1, θ≡0, e₆, e₁₃, K/S}。
* **發現（D5）**：聚合 = 0 的憑證對**任意符號** θ 成立——ΔF_B(25) + ΔF_B(315) = 0 即
  Level 2 單模式無符號線性 ranking 的 2 見證 no-go（A 的定理需 θ ≥ 0、10 見證）。
  `--deep` 普查（向量類口徑）：x < 2¹⁶ 相異 ΔF_B 向量 12345、對立對 269；36 維雙模式差分
  對立對 30（最小 (1611, 2233)，A 側 `two_mode_delta` 複核）、38 維仿射亦 30（截距差對消）
  ——雙模式為觀察層，不入錨。paper 增補候選已轉交修訂線（見 ROADMAP-B B3 紀錄第 8 點）。

## search/ 各檔用途

原始檔名沿用上游（Codex 專案），對照表如下：

| 檔案 | 用途 | 狀態 |
|---|---|---|
| `IM.py` | 8 狀態 / 16 邊的關聯矩陣，rank B = 7、循環空間 9 維，sympy 精確循環基底 | 可跑。關聯結構本身已由 `Flow.inEdges` 在 Lean 裡就地算出，不需要抄這張表；剩餘用途是循環基底（A-3 下界） |
| `LV3_RK.py` | Level 3 下 12 條 W₁₂ 差分的秩（= 12，線性獨立） | 可跑 |
| `LP.py` | 割平面迴圈找 θ；不可行時縮到 IIS 並解 Farkas 對偶 | **已修 bug**（`A_eq_eq` → `A_eq`，原版會 TypeError） |
| `Z3.py` | Level 2 單模式 + K 步前瞻窗口的 SMT 可滿足性 | 可跑，需 z3 |
| `FSB.py` | Level 2 雙模式 SMT | 可跑，需 z3 |
| `LV3_1P.py` | Level 3 單模式 SMT | 可跑，需 z3 |
| `LV3_M2.py` | Level 3 雙模式 SMT | 可跑，需 z3 |
| `certificate.py` | 早期 4 條軌跡憑證（λ = 5,5,5,1，Σ = 16） | **已被取代**，保留供對照 `Recon/Collatz_FST_LP_Recon.lean` §A |

## 還沒補上的（誠實紀錄）

`search/` 的 SMT 腳本在 unsat 時只印一句「矛盾依然存在」，**不會吐出 λ**。
也就是說 `W₁₂` / `W₂₀` 這兩組見證與其對偶權重，目前只能**驗證**、不能從這裡**重新生成**——
`LP.py` 那條 IIS + Farkas 路徑只實作了 Level 2 單模式，雙模式版本還沒寫。

A-3 若需要新憑證，第一件事就是把 `LP.py` 的 IIS 邏輯推廣到雙模式（2n 維區塊差分），
並且把輸出從浮點改成精確有理再取整——`certificates.py` 裡的 sympy 解法可以直接抄。
