# Project B Roadmap：Weighted Automata Expressivity Limits

> 本文件取代 `docs/HANDOVER.md` 中的 Project B 戰略段。
> 落地紀錄（2026-08-01，Phase 0 PR-3）：原草稿標【待驗證】的終末不平衡
> 已由 `tools/b15_terminal_balance.py` 精確整數重算確認；標【浮點探測】者
> 維持標記（`tools/search/b15_lp_probe.py` 重跑，可行性結論再現），
> 精確化列為 B1.5 待辦的第一項。
> 落地紀錄（2026-08-08，B1.5 PR）：兩個【浮點探測】資料點已升級為
> 精確整數憑證與 Lean 定理——B1.5 **已完成**，見該節完成紀錄。

---

## 0. 範圍界定（先讀，論文與所有 B 敘述都受此約束）

有限狀態勢能不是一個類，至少分三層：

- **Class A — 單累加器**：`V(w) = α(q₀) + Σᵢ ω(qᵢ, bᵢ) + β(q_f)`。
  Project B 猜想的對象，本路線圖的主戰場。
- **Class B — 多暫存器 additive regular functions**（copyless CRA 等）。
- **Class C — 更強的 register / matrix-weighted 模型**。

**Project A 定理的精確歸類（論文 model-scoping 必寫）：**

- 單模式 no-go（`LP.no_nonneg_linear_ranking` 系列）落在 **Class A**。
- 雙模式 no-go（`TwoMode.*` / `L3.*`）**不是 Class A**：
  模板 `V(x) = θ_{m(x)}ᵀF(x)` 的 K 區前綴權重依賴尚未確定的模式，
  不是任何 one-accumulator edge cost。正確歸類是
  **2-register copyless CRA + final selection**（兩累加器並跑 θ₀ᵀF、θ₁ᵀF，
  由模式辨識位在終態選一）——Class B 的最小邊緣。
- 因此即使 B 的全稱猜想成立，結論也只是「one-accumulator additive rankings
  的不可能性」，不是「有限狀態方法整體不可能」。

---

## B0：語義層（**已完成** 2026-08-28）

把 Core 的 Phase K/S 邏輯封裝為正規的 subsequential transducer `U`。

1. canonical LSB-first odd language 的 DFA（`w ≠ 1` 的 domain 條款）。
2. `U` 的 subsequential 性：每個 transition 輸出有界字串 + final output；
   soundness **不需要新證**——`Core/Statements.lean` 的
   `ofDigits_transduce`、`transduce_split` 就是，B0 大半是包裝。
3. `U(w)` 仍為 canonical odd word（closure）。
4. **B0-3 哨兵驗證**：`extIn x = digits ++ [0,0]` 的兩個哨兵零在
   language-product 中應落在通往接受態的**無環尾段**（product 狀態含
   DFA 位置，哨兵邊不與任何普通邊同一 product 邊）。
   若成立，B1 的 end-marker 警告自動滿足；寫成一條 lemma 或 `#guard` 級檢查。
   【原註記；其推理缺陷與修正見下方完成紀錄第 4 點】

Mathlib 有 DFA/NFA/regular 基礎，無 weighted transducer 層；
自建小而專用的 API，不要等上游。

**完成紀錄（2026-08-28，B0 PR，分支 `b/b0-semantics`）**：

1. **B0-1 語言層**（`ProjectB/Collatz_FST_OddLanguage.lean`）：謂詞
   `IsCanonicalOdd`（位元 <2、LSB = 1、MSB = 1）與 6 狀態 DFA `oddDFA`
   （接受 `{acc}`）一致：`mem_oddDFA_accepts_iff`；與 ℕ 的往返
   `isCanonicalOdd_digits`／`digits_ofDigits_of_canonical`／`ofDigits_odd`
   （皆 mathlib digits 引理的包裝）。**Q1 定案**：語言含 `[1]`
   （`digits 5 ∈ L` 而 `Uacc ↦ [1]`，剔除即破 closure）；排除 1 是排名
   量詞的條款，以 `RankingDomain` 另立、`rankingDomain_iff`
   （`w ≠ [1] ↔ 1 < x`）接 no-go 量詞。
2. **B0-2 transducer**（`ProjectB/Collatz_FST_Transducer.lean`）：
   `SubTransducer`（states = 型參／`init`／`step`／per-transition 有界輸出
   （`bound`/`out_le` 結構欄位）／`finalOut`）；`U` = Core 進位機包裝
   （狀態 = 進位、init 1、每步恰一位、finalOut = 終端進位二進位無填零）。
   **soundness 零重證**：唯一結構歸納是橋接 `U_runOut`（與 `run` 同形遞迴、
   逐 case rfl）；acceptance 全 re-export——`ofDigits_U_output` ←
   `ofDigits_transduce`、`U_output_split` ← `transduce_split`、
   `ofDigits_Uacc` ← `Todd_eq_dropWhile`、`Uacc_digits` ← `digits_Todd_eq_drop`。
   **Q2 定案**：選項 (a)——K 步照發 0，加速輸出 `Uacc = dropWhile (·=0) ∘ output`
   收零；選項 (b)（K 步緩衝）需重推「緩衝發射 = dropWhile」歸納，違反
   re-export 紅線。K/S 相位語義錨在 `runP_K_iff`／`U_output_split`。
3. **closure**：`isCanonicalOdd_Uacc`——對**全體** L 成立、無需排除 `[1]`
   （`Uacc_one : Uacc [1] = [1]`，Todd 不動點落點）；最強形
   `Uacc_eq_digits_Todd`（`Uacc w = digits (Todd (ofDigits w))`）。
4. **B0-3 哨兵引理——原註記的推理缺陷、反例與修復**。原註記設想上述
   無環尾段可在未標記字母表 `{0,1}` 上形式化，**此設想不可能成立**：
   `extIn 1 = [1,0,0]` 是 `extIn 9 = [1,0,0,1,0,0]` 的前綴——識別 `L·00`
   的任何 DFA 讀完前者已在接受態、讀完後者再度接受，故接受態位於循環上，
   「哨兵邊」與詞中段普通邊重合（`digits 9 = [1,0,0,1]` 內含因子 `100`
   是同一現象的詞中段形式）。**修復（設計核准 2026-08-28）**：哨兵改讀
   **標記字母**——字母表 `Option ℕ`（`some b` = 一般位元、`none` = 哨兵），
   `extInM x = (digits x).map some ++ [none, none]`，`extInM_unmark`
   一行投影回 Core 的 `extIn`。此後 B0-3 成立且為枚舉／小歸納級：
   - `sentinel_positions`：前 `|digits x|` 步不觸尾段，兩哨兵步分別進
     `tail1`／`tail2`（= 接受態）；
   - `lstep_some_ne_tail1/2`：尾段唯哨兵字母可進入——「哨兵邊不與任何
     普通邊同一 product 邊」的機制；
   - `sentinel_edge₁_no_cycle`（`tail1 ⇝̸ acc`）、`sentinel_edge₂_no_cycle`
     （`tail2 ⇝̸ tail1`）：「邊在循環上 ⟺ 存在從邊頭回邊尾的路徑」的
     逐邊否定——兩條哨兵邊不在任何循環上；
   - `prodRun_snd`：product 走行的 DFA 分量 = `extDFA` 走行，上述事實
     對**任意**機器的 language-product 生效。
   **B1 end-marker 警告以此正式解除**：B1 的乘積圖在標記字母表上構造，
   哨兵邊是唯二通往接受態的邊且不在任何循環上，循環 pump 全程落在
   `some`-區段。extDFA 的完整語言 iff 刻畫非 B0-3 所需，留待 B1 實需時補。
5. **驗證**：`lake build` 全綠（新模組合計 <5 s，無 `maxHeartbeats` 調整、
   無 `decide` 重負載）；兩檔內建 #eval 回歸電池 18 項全 `true`；
   `check_boundaries.py` ProjectB 規則首次實測（含負向測試：暫存檔
   ProjectB import ProjectA 必紅）。

## B1：Nonnegative Reweighting Theorem（gauge normalization；**已完成** 2026-08-28）

> **定理（目標敘述）。** 對有限的 trimmed weighted product graph
> （automaton × language DFA，皆有理權重），以下等價：
> 1. 接受字的成本集合有一致下界；
> 2. 每個位於某條接受路徑上的 directed cycle 總權重非負；
> 3. 存在 `h : Q → ℚ` 使所有 **useful** transition edges 滿足
>    `w(e) + h(src e) − h(dst e) ≥ 0`。
>
> 且取 `α'(q₀) = α(q₀) − h(q₀)`、`β'(q) = β(q) + h(q)` 後 **V' ≡ V 恆等**
> （不只 drift 不變——嚴格下降、下界、任兩字差值全部原封不動）。

- 證明骨架：super-source 加零權邊 → shortest-path distance 當 `h`
  （Gallai potential / Johnson reweighting；有理 Bellman–Ford，精確算術）。
- 措辭紀律：只對 **trimmed useful graph** 的 ordinary edges 宣稱非負；
  非 co-reachable 區域明確排除（`Q_useful = {q : q₀ ⇝ q ⇝ F}`）。
- (1)⟹(2) 的關鍵：trimmed product 中每條循環都可在語言內 pump
  （可達 + 繞 k 圈 + 可出到接受態）。
- **直接紅利**：Level 2 單模式 no-go 由「θ ≥ 0」升級為「V 有下界」——
  非負假設變成 WLOG（gauge choice），不是實驗限制。
- **與 A 論文的互動**：corollary 只有在 B1 完成後才進 A 的 appendix；
  未完成前 A 維持 θ≥0 敘述 + discussion 一段。不用 forthcoming 撐主定理。

**完成紀錄（2026-08-28，B1a PR #41＋B1b PR，分支 `b/b1a-reweighting-defs`
→ `b/b1b-shortest-path-potential`；設計報告 B1-DESIGN-REPORT.md 核准後兩段落地）**：

1. **載體**（`ProjectB/Collatz_FST_B1_Reweighting.lean` 單檔；**import 純
   mathlib、零 Core**）：抽象 `CostAutomaton Q A`（Q1 定案完全抽象——trimmed
   product graph 是本定理的實例不是敘述成分，哨兵警告在抽象層自動消解，
   實例化時由 B0-3 標記字母表引理承擔）；witness 形
   `Reach`/`CoReach`/`Useful`/`UsefulEdge`（Q2）；端點
   `BoundedBelow`/`CyclesNonneg`/`HasPotential`。核准偏差點：**D1**
   `CyclesNonneg` 不帶 `c ≠ []`（空閉走行權重 0，逐字等價）；**D2**
   「位於接受路徑上的 cycle」形式化為「錨在 useful 態的閉走行」（等價；
   旋轉由全稱量詞自動涵蓋）；**D3** 勢能不吸收 α（super-source 版的等價
   簡化，α 留在 cost／下界處）。
2. **(1)⟹(2)** `cyclesNonneg_of_boundedBelow`：pump `u ++ cᵏ ++ v` 全程在
   語言內＋阿基米德（`exists_nat_gt`）；**(3)⟹(1)**
   `boundedBelow_of_hasPotential`：望遠鏡直接界
   `B = α − h(init) + min_{t∈accept}(β t + h t)`——接受字沿途每條邊自動
   useful（見證＝前綴／後綴）。兩條**零 Fintype 需求**。
3. **(2)⟹(3)** `hasPotential_of_cyclesNonneg`（Q3 定案選 (a) 有界長最短路；
   `[Fintype Q/A]`、`[DecidableEq Q/A]` 僅此蘊含需要）：`wordsLe` 字集
   Finset → 縮短 A（純鴿籠 `reachWords_nonempty`）→ 縮短 B
   （`exists_short_le_wpath`，全案樞紐：(2) 之下成本不升地縮到長 < card Q，
   剔除段錨 useful 態——可達＝前綴、可出＝後段＋終點出字；
   `DFA.evalFrom_split` 經 `toDFA` 橋做鴿籠萃取，rfl 級互通）→
   `potential` = `Finset.min'` 最短路（可 `#eval` 機算；死區任取 0）→
   `potential_triangle` → 主定理。縮短引理走 fuel 歸納（對長度上界歸納），
   P2 探針（橋接／歸納骨架／dite 膠水）一次通過。
4. **吸收恆等式** `reweight_cost`：`α′ = α − h(init)`、`β′ = β + h`、
   `w′ = w + h∘src − h∘dst` 之下 cost **逐字恆等**（對全體字、任意 h、
   與三條蘊含正交——B1.5 structured gauge 消費的正是此正交性）。
   `boundedBelow_tfae` 文件性收口（Q4：主要出口是三條具名單箭頭）。
5. **玩具電池**（17 項 `#eval` 全 `true`）：`Mneg` 負例（自環 usefulness
   具體見證、pump 遞減、機算 potential 在負自環邊三角必破——(2) 前提
   必要性的可見形）；`Mpos` 正例（機算 `potential` = 手寫 `hpos`、三角
   全過、reweight 後全邊非負、恆等式長 ≤ 6 全字枚舉正負例各一次）。
6. **明確不做（照設計）**：Collatz 實例化（B3）、A 定理 bounded-below
   corollary（B3 前置，另 PR）、B2 判定引擎、通用 API。**直接紅利與
   structured gauge lemma（B1.5 殘項）自此解鎖**，隨 B3 前置 PR 進行。
   （structured gauge 已於 2026-08-28 收口，見 B1.5 節完成紀錄二。）
7. **驗證**：`lake build` 全綠（模組 <4 s、零 `maxHeartbeats` 調整）；
   `check_boundaries.py` 35 模組；mathlib 發現：pinned rev 無
   `Mathlib.Data.Rat.Order`（ℚ 序結構 import 是
   `Mathlib.Algebra.Order.Field.Rat`）、除法比較是 `div_lt_iff₀`。

## B1.5：雙模式的 structured gauge（**已完成**：資料點／no-go 2026-08-08、structured gauge lemma 2026-08-28）

雙模式是 2-register 模型（§0），gauge 對兩個暫存器各作用一個 `h_m`，
校正項 `h_m(q₀) − h_m(q_f)` 依終末狀態而異 ⟹ 偏移類必須從
「每模式常數 β_m」（A-2 已證）擴大為「每 (模式, 終末) 一個 β_{m,t}」。

**資料點（2026-07-31；驗證狀態 2026-08-01）：**

1. 現有憑證的終末流量平衡 `Σλ(⟦end(y)=t⟧ − ⟦end(x)=t⟧)`：
   - Level 2（W₁₂, Σλ=7826）：**±428，不平衡**
   - Level 3（W₂₀, Σλ=31746）：**±753，不平衡**
   （已精確整數重算確認：`tools/b15_terminal_balance.py`，離線可重跑）
   ⟹ per-(mode, terminal) 偏移**不是**免費升級。
   四分量分解 `Σλ(⟦(m, end)(y) = (m, t)⟧ − ⟦(m, end)(x) = (m, t)⟧)`
   【精確整數】（`b15_terminal_balance.py` 已輸出此分解）：
   - Level 2（t 依序 `(0,S,0)`／`(0,S,1)`）：m=0：0／0；m=1：+428／−428
     ——L2 不平衡全集中於模式 1 ⟹ 雙平衡搜尋實際僅增一條有效約束；
   - Level 3（t 依序 `(0,S,0,1)`／`(0,S,1,0)`）：m=0：+80／−80；
     m=1：−833／+833。
2. LP 探測（奇數 3..3999，HiGHS）【浮點探測；已精確化，見完成紀錄】：
   - 原始 LP（θ≥0 + 自由 β_{m,t} 的勢能）：兩層皆**不可行**——池上無候選勢能；
   - 雙平衡 Farkas（四條 per-(mode, terminal) 平衡 `Σλ·Δ⟦(m,t)⟧ = 0`
     全零的憑證——探測程式的等式約束即為此四條版本）：兩層皆**可行**。
     支撐集：L2 = [3, 243, 599, 961, 1079, 1363, 1369, 1413, 1671, 1819,
     2343, 2345, 2401, 2731, 3083, 3259, 3377, 3677, 3745, 3905]（20 個）；
     L3 = [37, 487, 527, 779, 1423, 1819, 1911, 2091, 2209, 2337, 2407,
     2427, 2457, 2505, 2721, 2729, 2735, 2863, 3255, 3343, 3377, 3413,
     3639, 3641, 3825, 3913, 3937]（27 個）。
     （2026-08-01 `tools/search/b15_lp_probe.py` 重跑：兩層「不可行／可行」
     結論再現；支撐集為浮點解路徑產物，維持【浮點探測】標記。）

**完成紀錄（2026-08-08，B1.5 PR）**：

1. **精確重推**：雙平衡 λ 已以精確有理獨立重解
   （`tools/search/b15_exact_balance.py`：浮點僅提供支撐集與 tight 座標的
   組合資訊，λ 為 sympy 有理 nullspace 解，全部條件以純整數驗證）。
   「雙平衡」措辭自此收緊為**四條 per-(mode, terminal) 平衡全零**——
   這是收掉 4 個自由 β_{m,t} 的充要條件，嚴格強於「模式平衡＋終末平衡」
   （後兩者合計僅 3 條獨立約束，殘留 1 維）。精確支撐集為上列浮點支撐集
   的真子集：L2 剔 {1413, 2343, 3377} 餘 17 個、L3 剔 {3413} 餘 26 個。
2. **錨**：`W17`/Σλ = 6131365、`W26`/Σλ = 9592170791，λ、聚合向量與
   四條平衡值錨於 `tools/certificates.py --b15`（CI certs job 涵蓋；
   負向測試：竄改單一 λ 即 exit 1）。
3. **Lean 定理**（落點 `ProjectA/`——建立在 TwoMode／L3 機器上，
   `check_boundaries` 禁止 B 匯入 A）：
   - `CollatzFST.TwoMode.no_go_2mode_terminal_affine_potential`
     （`ProjectA/Collatz_FST_2Mode_Terminal_NoGo.lean`）
   - `CollatzFST.L3.no_go_level3_2mode_terminal_affine_potential`
     （`ProjectA/Collatz_FST_L3_2Mode_Terminal_NoGo.lean`）

   β 依 (模式, 終末) 各一、無符號約束；終末以單一位編碼
   （L2 `(run2 …).2.2`、L3 `(run3 …).2.2.1`），忠實性由
   `terminal_bit_faithful`／`terminal_bit_faithful3` 接地於終末狀態定理。
   兩定理目前非 paper-facing，不進 registry。
4. **殘項移轉**：structured gauge lemma（per-register `h_m`，吸收進
   β_{m,t}）依賴 B1 的 reweighting 機器，隨 B1 進行；屆時三條 no-go
   全數升級為 bounded-below。（已收口，見下方完成紀錄二。）

**完成紀錄二（2026-08-28，structured gauge PR，分支
`b/b15-structured-gauge`；設計報告 B15-GAUGE-DESIGN-REPORT 核准
（Q1–Q4、偏差點 D1–D5 全項通過）後落地）**：

1. **載體**（`ProjectB/Collatz_FST_B15_SelGauge.lean` 新檔；import 僅
   B1 檔——零 Core、零 ProjectA、零 Collatz 內容）：`SelCostAutomaton`
   ——單一底層機器（init/step/accept）＋終態選擇 `sel : Q → Fin 2`＋
   每暫存器邊權 `w : Fin 2 → Q → A → ℚ`＋共享 α β，即 §0 對雙模式模板
   歸類（2-register copyless CRA + final selection）的最小載體（Q1 定案
   獨立結構體：一對機器方案洩漏 step/init/accept/α/β 五處自由度）。
   投影 `restrict m`（同機器、接受集過濾 `sel · = m`、權重 `w m`）使
   B1 全 API 免費取得；`cost u = α + wpath_{sel(final u)} u + β(final u)`
   對全體字有定義（D5，B1 紀律）。
2. **Q3 分解**：`cost_restrict`（模式相符的字 restrict 成本 = 原成本）＋
   `boundedBelow_restrict`（量詞限縮一行，同一個 B 複用）。空接受集的
   m 空虛成立——逐條檢查 B1 (1)⟹(2)⟹(3) 全鏈零接受集非空前提
   （`potential` 只查 reachWords、三角只在 UsefulEdge 調用），無需特判，
   統一證明 type-check 即探針（一次通過）。
3. **β-吸收恆等式** `reweight_cost`（Q4）：`w′ m = w m + h m∘src − h m∘dst`、
   **α 不動**、`β′ q = β q + h (sel q) q − h (sel q) init` 之下 cost 對
   全體字恆等（任意 h、與蘊含正交）。α 不動的理由：α 是共享常數，
   per-mode 校正必須住在 per-state 的 β；β′ 對接受終態 t 的偏移
   `h (sel t) t − h (sel t) init` 恰為 per-(mode, terminal) 常數——與
   #39 兩條 terminal-affine no-go 的 β_{m,t} 對齊之處。唯一新歸納是
   list 層望遠鏡 `reweight_wpath`（D1，4 行、鏡像 B1 §B1.4 同名引理；
   零新圖論歸納——成因：`(S.reweight h).restrict m` 與
   `(S.restrict m).reweight (h m)` 的 w/step 逐點 defeq 但 α/β 不同，
   兩結構體不相等）。
4. **主定理** `structured_gauge`（＋端點 `HasPotential`、單箭頭
   `hasPotential_of_boundedBelow`；instance 需求全數繼承 B1 (2)⟹(3)）：
   BoundedBelow ⟹ ∃ h : Fin 2 → Q → ℚ，每個 m、每條
   `(restrict m).UsefulEdge` 的 reweighted 權重 ≥ 0 且 cost 恆等。
   證明主體 = B1 出口兩次應用＋`choose` 收族＋恆等式，純拼裝。
   措辭紀律（Q2）：逐 m 只對該模式 useful 邊宣稱；聯合 useful 邊的
   雙保證是假命題（反例進電池）。**「雙模式 bounded-below ⟹ WLOG
   θ_m ≥ 0 ＋自由 β_{m,t}」自此成立。**
5. **玩具電池**（19 項 `#eval` 全 `true`）：`Ssel`（Fin 4 × Fin 2，兩個
   異 sel 接受態、模式 1 循環 tight、q2 自環 w₁ = −1）——per-mode
   usefulness 具體見證、機算 `potential` 八格對手算（含負自環延長取值的
   pot₁(q2) = 2，B1 死區邊界實測）、per-mode 三角（顯式 useful 邊列表，
   不掃全邊）、Q2 反例（q2 自環對任意 h reduced w₁ 恆 −1 < 0）、恆等式
   長 ≤ 6 全字枚舉（junk h 正交性再跑一次）、α 不動＋β_{m,t} 偏移可見形。
6. **明確不做（照設計）**：**與 #39 的合成（三條 no-go 升級
   bounded-below = A 定理的實際升級）——見後續 PR**；逆向蘊含
   `HasPotential → BoundedBelow`（D3，非交付項）；`Fin k` 一般化；
   Collatz 實例化（B3）。

## B2：固定 topology 的全語言判定

> 對固定的 deterministic cost automaton，「所有接受字成本 < 0」
> 化約為有限圖問題：trim + super-source `s→q₀`（權 α）+ super-sink
> `q_f→t`（權 β）+ **權重取負** → reachable negative-cycle 偵測 +
> 一次 `s→t` shortest path；有正循環立即失敗，無正循環時最大成本由
> elementary path 達成，嚴格負 ⟺ 該最大值 < 0（有理格點自動給一致間距）。

- 文獻：Johnson 1977（reweighting，B1 主引用）；Karp 1978（cycle mean，
  **單獨不足**——mean = 0 時仍須查 boundary path）；Mohri 2002
  （semiring shortest-distance 背景）；Almagor–Boker–Kupferman survey
  （定位為 threshold universality 的 deterministic 特例，一般 tropical
  nondeterministic 情形困難得多，我們的唯一 run 特例退化為圖判定）。
- 分工照舊：搜尋/判定引擎在 `tools/`（精確有理），Lean 只驗證書。
- `D_A(x) = V(U(x)) − V(x)`：subsequential `U` 的每步輸出區塊權重
  push-back 到輸入轉移 + final output 進 β——標準 weighted composition。

**完成紀錄（2026-08-28，B2 PR，分支 `b/b2-engine`；設計核准
B2-DESIGN-REPORT，Q1–Q4 與偏差點 D1–D6 全項通過）**：

1. **引擎**（`tools/b2_engine.py` 單檔；純標準庫、`fractions.Fraction`
   精確有理、零浮點、零 Lean）：`mk_automaton`（規格鏡射 B1
   `CostAutomaton`）→ `trim`（可達∧可出）→ `decide_all_negative`。
   化約照上：取負 Bellman–Ford（嚴格改進鬆弛——零權循環不觸發，
   語義上 pump 不改成本本就無害）同時做可達正循環偵測與邊界最短路；
   super-source/sink 吸收（D1：α 作逐態值常數偏移、β 折進終端 max，
   呼應 B1 D3）；空語言 ⟺ init 非 useful，顯式真空分支。fail 見證
   `前綴 ++ 循環^k ++ 出綴`，k = max(0, ⌈−base/W_c⌉) 有理直接解；
   **Karp 單獨不足的角已在檔頭與判定處註解點名**（無正循環時仍須查
   邊界最大值 M* 並與 0 嚴格比較；α/β 是 boundary 貢獻），且由已知
   答案 T1 迴歸（`Mneg` 無正循環、M* = 0 而 fail）。
2. **憑證自驗**（不信引擎主流程、零圖搜尋）：pass 憑證 = `(R, C, d)`
   ——NOTES (a)(b)(c)（P3 三角/P4 接受/P5 對齊）之上**新增 R/C 封閉性
   檢查 P1/P2 把量化域「useful」局部化**（D2：P1 前向封閉、P2 對 R
   後向封閉 ⟹ R∩C ⊇ Useful）；健全性定理 P1–P5 ⟹ AllNeg 之證明只用
   B1 望遠鏡，即 B3 Lean 驗證書的敘述前身（P1–P5 為 `decide` 級 Bool
   合取）。fail 見證 = 平坦接受字直接求值（完整檢查）。引擎回傳前
   一律以驗證函數自檢輸出（D6）。
3. **已知答案 T1–T5**（`from_b1_toy`，Mneg/Mpos 逐字轉錄 B1 Lean 檔
   並註明行號）：T1 `Mneg` fail-邊界（Karp 角）；T2 `Mpos` fail-正循環
   （k = 0）；T3 `Mpos_neg`（取負，D4 定案的 pass 例）憑證三值
   d = {0: −5, 1: −3, 2: −2} 逐項錨定；T4 `Mneg_neg_shift`（取負＋
   α = −5/2）真 pump k = ⌈5/2⌉ = 3、見證成本 1/2、k−1 成本 −1/2 < 0
   （最小性；核准時勘誤：−3/2 是 k = 1 的值）；T5 真空 pass。
4. **oracle 性質測試**（D5 方向性判準矩陣）：固定種子 20260828、
   300 台 ≤ 4 態隨機機（權重偏正讓正循環夠多）× 有界窮舉
   （L = n_states + 2）——pass：憑證綠（健全性定理 ⟹ 已完備）∧
   窮舉無違例（防共模 bug 交叉探針）；fail：見證綠（求值即完備）∧
   短字無違例 ⟹ 必為循環模式。四類覆蓋（pass 21／fail-循環 151／
   fail-邊界 33／真空 95）門檻寫死。另做一次性淬煉（不進 repo）：
   2 萬台至 6 態、3 字母、權重含 1/3 全過。
5. **驗證**：`--selftest`（T1–T5＋負向測試四則＋oracle）全綠，
   實測 ~0.01 秒（任務上限 10 秒）；負向測試——竄改 pass 憑證單值
   （P4 破/P3 破各一）必紅、fail 見證換成本 < 0 或非接受字必紅。
   CI：`guard.yml` certs job 尾端加跑 `--selftest` 一步
   （專案主人具名授權，PR 描述照 #39 前例標明）；零新增 pip 依賴。
6. **明確不做（照設計）**：任何 Lean（B3 驗證書）、Collatz 實例化與
   `D_A` weighted composition（B3）、憑證序列化格式（B3 決定）。

## B3：重現 Project A（abstraction 驗收測試）

用 B2 引擎重推三條 no-go。`scripts/check_boundaries.py` 本來就禁止
ProjectB 匯入 ProjectA ⟹ 這是結構上誠實的重推導。
重推不出來 = abstraction 遺失了 A 的重要結構，先修 abstraction 再前進。

## B4：受限一般結果

依序：1-state → 狀態數 ≤ n → aperiodic transition monoid →
bounded history/suffix → 特定 mode partition。每一層都是獨立可發表的界。

## B5：Contextual Word-Family Sufficiency（重述後的地平線）

不再預設「兩個宏觀族產生矛盾」。改問判準：

> 給定一類 finite-state additive cost automata 𝒞，何種參數化
> word-family 集合 𝒲 足以對每個 A ∈ 𝒞 產生有限的
> contextual cycle / conic obstruction？

充分性的三個成分：**狀態對齊**（relevant subwords 落入 transition monoid
的相同 idempotent context）、**語境封閉**（允許左右 context 與跨 block
串接）、**錐矛盾**（λ ≥ 0、Σλ·Δ ≥ 0、Σλ > 0，或 coboundary-invariant 版本）。

三層推進：s-dependent families（狀態數 ≤ s）→ aperiodic/特定 monoid 類的
統一 families → 是否存在對所有 finite monoids 充分的固定 schema。

**證據**：Level 3 第 65 條泛函 `θ₀[16] + θ₁[33]` 只有跨區塊版本成立
（同區塊版本連關係都不是）——obstruction 可以住在 block interaction 裡，
單一 block signature 看不到。兩族 `2^k − 1`、`(4^{m+1} − 1)/3`
降格為第一組候選 family；注意此證據**尚未證明**兩族經 contextual
closure 後不充分。

## 不做的事

直接升 Level 4/5；大規模隨機 LP 盲搜；未經 B4 直接攻全稱猜想；
轉向 probabilistic Collatz（改變量詞與研究目標）。
