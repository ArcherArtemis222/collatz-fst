# 定理狀態索引（唯一真相來源）

最後更新：2026-09-04 ／ 對應 PR：`b/b3b-diff-engine`（B3b——差分自動機 D(θ)＋B2 引擎全語言重推＋θ-LP 圖憑證，tools 層）

> 本檔由 repo 現況生成：定理名逐條 grep 核實、一句話摘要取自各定理 docstring。
> 歷史敘述見 [HANDOVER.md](HANDOVER.md)（快照，不再更新）；待辦見
> [ROADMAP-A.md](ROADMAP-A.md) 與 ROADMAP-B.md。
> 標 ✦ 者列於 Audit.lean（`Lean4RealConstruction/` 根）的 `#print axioms` 信任基底
> （期望輸出僅 `propext` / `Classical.choice` / `Quot.sound`）。
> 標 ★ 者已收入 paper/registry.yaml（A-4 論文註冊表，括號內為 registry id）；
> 重述層 `ProjectA/PaperIndex.lean` 由 `tools/gen_paper_index.py` 生成、CI 強制再生性。

---

## Core（凍結）

轉換器與 Level 2 自動機的基底層。`Core/` 只有專案主人能改（AGENTS.md §1）。
下表只列信任基底與 ProjectA 直接依賴的結構定理；支撐層
（Statements / Monoid / Ext / Phase / Level2 五檔）的完整內容見各檔檔頭。

| 定理 | 檔案 | 一句話 |
|---|---|---|
| `CollatzFST.ofDigits_transduce` ✦ ★（`transducer-soundness`） | `Core/Collatz_FST_Statements.lean` | 轉換器正確性：`ofDigits 2 (transduce x) = 3x + 1`。 |
| `CollatzFST.transduce_split` ✦ ★（`transducer-split`） | `Core/Collatz_FST_Statements.lean` | 輸出串恰為「`v₂(3x+1)` 個 0」++ 消去後的串（位移對齊、不干擾高位）。 |
| `CollatzFST.Todd_eq_dropWhile` ✦ ★（`todd-eq-dropwhile`） | `Core/Collatz_FST_Statements.lean` | 尾零消去後的數值恰為加速映射 `T_o(x)`。 |
| `CollatzFST.padicValNat_eq_altPrefixLen` ✦ ★（`valuation-alt-prefix`） | `Core/Collatz_FST_Ext.lean` | `v₂(3x+1) = a(x)`（二進位交錯前綴長）。 |
| `CollatzFST.boundary_step_unique` ✦ ★（`boundary-step-unique`） | `Core/Collatz_FST_Level2.lean` | 邊界觸發步唯一：起始相位 K 且輸出 1 的步恰好一次（`E^K` 聚合形式）。 |
| `CollatzFST.birth_death_conservation` ✦ | `Core/Collatz_FST_Level2.lean` | 誕生−死亡守恆律：`#(0→1) + [p=1] = #(1→0) + [末位=1]`。 |
| `CollatzFST.occ2_deadState` | `Core/Collatz_FST_Level2.lean` | 死狀態 `(0,K,·)` 的兩個特徵計數恆為零（LP 的免費約束）。 |
| `CollatzFST.S8_closed` | `Core/Collatz_FST_Level2.lean` | 8 個可達狀態在 `step2` 下封閉——排除死狀態 `(0,K,0)`，終末狀態定理的關鍵。 |

## Project A — No-Go 定理

三個模板 × （有限見證版／全稱版／仿射版）共 8 條，另有 B1.5 雙平衡仿射版
2 條（見表末；非 paper-facing，不入 registry）。見證集與 Farkas 憑證：

| 憑證 | 見證集 | Σλ | 重算錨 |
|---|---|---|---|
| Level 2 單模式 | `CollatzFST.LP.W₁₀`（10 個） | 1024 | `tools/certificates.py`（解族唯一；`--cramer`：λ = adj(A_free) 第 2 列、31 = det） |
| Level 2 雙模式 | `CollatzFST.TwoMode.W12`（12 個） | 7826 | `tools/certificates.py`（模式流量平衡 = 0，A-2 前提） |
| Level 3 雙模式 | `CollatzFST.L3.W20`（20 個） | 31746 | `tools/certificates.py`（同上） |
| B1.5 Level 2 雙平衡 | `CollatzFST.TwoMode.W17`（17 個） | 6131365 | `tools/certificates.py --b15`（四條 per-(m,t) 平衡 = 0——β_{m,t} 對消的充要條件） |
| B1.5 Level 3 雙平衡 | `CollatzFST.L3.W26`（26 個） | 9592170791 | 同上；推導 `tools/search/b15_exact_balance.py` |

| 定理 | 檔案 | 一句話 |
|---|---|---|
| `CollatzFST.LP.no_nonneg_linear_ranking` ✦ ★（`nogo-l2-single-witness`） | `ProjectA/Collatz_FST_NoLinearRanking.lean` | 不存在非負權重使線性勢能在 `W₁₀` 每一步嚴格下降。 |
| `CollatzFST.LP.no_global_odd_ranking` ✦ ★（`nogo-l2-single-universal`） | `ProjectA/Collatz_FST_NoLinearRanking.lean` | 全稱版：對每個奇數 `x > 1` 皆嚴格下降的非負線性 ranking 不存在（量詞已排除 `x = 1`，A-1）。 |
| `CollatzFST.TwoMode.no_go_2mode_potential` ✦ ★（`nogo-l2-2mode-witness`） | `ProjectA/Collatz_FST_2Mode_NoGo.lean` | 不存在兩組非負權重使雙模式勢能在 `W12` 每一步嚴格下降。 |
| `CollatzFST.TwoMode.no_go_2mode_affine_potential` ★（`nogo-l2-2mode-affine`） | `ProjectA/Collatz_FST_2Mode_NoGo.lean` | 仿射版（A-2）：`V_m = β_m + θ_mᵀF`，截距不受非負限制，仍不可行。 |
| `CollatzFST.TwoMode.no_global_odd_2mode_potential` ★（`nogo-l2-2mode-universal`） | `ProjectA/Collatz_FST_2Mode_NoGo.lean` | 全稱版：對每個奇數 `x > 1` 皆嚴格下降的雙模式勢能不存在。 |
| `CollatzFST.L3.no_go_level3_2mode_potential` ✦ ★（`nogo-l3-2mode-witness`） | `ProjectA/Collatz_FST_L3_2Mode_NoGo.lean` | 不存在兩組非負權重使 Level 3 雙模式勢能在 `W20` 每一步嚴格下降。 |
| `CollatzFST.L3.no_go_level3_2mode_affine_potential` ★（`nogo-l3-2mode-affine`） | `ProjectA/Collatz_FST_L3_2Mode_NoGo.lean` | 仿射版（A-2）：Level 3 勢能加截距 `β₀ β₁` 仍不可行。 |
| `CollatzFST.L3.no_global_odd_level3_2mode_potential` ★（`nogo-l3-2mode-universal`） | `ProjectA/Collatz_FST_L3_2Mode_NoGo.lean` | 全稱版：對每個奇數 `x > 1` 皆嚴格下降的 Level 3 雙模式勢能不存在。 |
| `CollatzFST.TwoMode.no_go_2mode_terminal_affine_potential` | `ProjectA/Collatz_FST_2Mode_Terminal_NoGo.lean` | B1.5 雙平衡仿射版：截距升級為 per-(mode, terminal) β_{m,t}（4 個、無符號約束），仍不可行；終末位忠實性 `terminal_bit_faithful`。 |
| `CollatzFST.L3.no_go_level3_2mode_terminal_affine_potential` | `ProjectA/Collatz_FST_L3_2Mode_Terminal_NoGo.lean` | 同上（Level 3）；終末位忠實性 `terminal_bit_faithful3`。 |

註：`ProjectA/Collatz_FST_2Mode_Recon.lean` 與 `ProjectA/Collatz_FST_L3_2Mode_Recon.lean`
檔頭 docstring 內出現的同名「定理」是交接紀錄的引文，不是宣告；canonical 宣告
在上表兩個 NoGo 檔。`W12` / `W20` 的定義位於這兩個 Recon 檔。

## Project A — 流守恆與維度（Level 2）

Kirchhoff 鏈：trace 層流守恆 → 特徵層泛函 → 差分層 9 條（秩 8）→
上界 ≤ 10 → 見證下界 ≥ 10 → **dim span(ΔF) = 10**（18 維中）。

| 定理 | 檔案 | 一句話 |
|---|---|---|
| `CollatzFST.Flow.microTrace2_flow_conservation` | `ProjectA/Collatz_FST_Flow.lean` | trace 層流守恆：入流(g) + 初始指示 = 出流(g) + 終末指示。 |
| `CollatzFST.Flow.state_outflow_eq_occ2` | `ProjectA/Collatz_FST_Flow.lean` | 出流(g) = `occ2 (g,0) + occ2 (g,1)`。 |
| `CollatzFST.Flow.inflow_eq_sum_occ2` | `ProjectA/Collatz_FST_Flow.lean` | 入流(g) = 16 條轉移邊上的 `occ2` 和。 |
| `CollatzFST.Flow.kirchhoff_occ2` ★（`flow-kirchhoff-l2`） | `ProjectA/Collatz_FST_Flow.lean` | 純特徵層 Kirchhoff 泛函：18 維特徵上的線性關係（A-3 上界可用形式）。 |
| `CollatzFST.Flow.runCarry_extIn` | `ProjectA/Collatz_FST_Flow.lean` | 讀完 `extIn x` 後最終進位為 0（兩個哨兵零沖掉進位）。 |
| `CollatzFST.Flow.run2_extIn_terminal` ★（`terminal-l2`） | `ProjectA/Collatz_FST_Flow.lean` | 終末狀態定理：對所有 x 恆落在 `{(0,S,0), (0,S,1)}`。 |
| `CollatzFST.Flow.kirchhoff_occ2_extIn_clean` | `ProjectA/Collatz_FST_Flow.lean` | 非終末 6 條乾淨流守恆（終末指示恆 0）。 |
| `CollatzFST.Flow.kirchhoff_occ2_extIn_merged` | `ProjectA/Collatz_FST_Flow.lean` | 兩個可能終末合併成第 7 條（指示相加恆 1）。 |
| `CollatzFST.Flow.dF_zero_0`、`dF_zero_1` | `ProjectA/Collatz_FST_FlowDelta.lean` | 差分層死座標：`ΔF₀ = ΔF₁ = 0`。 |
| `CollatzFST.Flow.dF_flow_1K0`、`dF_flow_2K0` ★（`flow-2k0-alternating`）、`dF_flow_1S0`、`dF_flow_1S1`、`dF_flow_2S0`、`dF_flow_2S1` | `ProjectA/Collatz_FST_FlowDelta.lean` | 6 個非終末狀態的差分層流守恆；`dF_flow_2K0` 即舊表「K 區交錯 e₄ = e₅ + e₆」。 |
| `CollatzFST.Flow.dF_flow_terminal_merged` | `ProjectA/Collatz_FST_FlowDelta.lean` | 合併終末的差分層流守恆（第 9 條；9 條合計秩 8）。 |
| `CollatzFST.Flow.dFQ_mem_Sol` | `ProjectA/Collatz_FST_DimUpper.lean` | 每個 `ΔF x`（ℚ 向量 `dFQ`）都落在 9 條關係切出的解空間 `Sol`。 |
| `CollatzFST.Flow.pick_injective_on_Sol` | `ProjectA/Collatz_FST_DimUpper.lean` | 10 個自由座標 `{2,3,6,7,8,9,10,11,15,17}` 在 `Sol` 上單射（其餘 8 座標可重建）。 |
| `CollatzFST.Flow.finrank_span_dFQ_le_ten` | `ProjectA/Collatz_FST_DimUpper.lean` | 上界：`dim span(ΔF) ≤ 10`。 |
| `CollatzFST.Flow.dFW_linearIndependent` | `ProjectA/Collatz_FST_DimLower.lean` | `W₁₀` 的 10 條 ΔF 線性獨立（自由座標 10×10 行列式 = 31 ≠ 0）。 |
| `CollatzFST.Flow.ten_le_finrank_span_dFQ` | `ProjectA/Collatz_FST_DimLower.lean` | 下界：`10 ≤ dim span(ΔF)`。 |
| `CollatzFST.Flow.finrank_span_dFQ_eq_ten` ✦ ★（`dim-l2-eq-10`） | `ProjectA/Collatz_FST_DimLower.lean` | **維度定理**：Level 2 特徵差分空間恰為 10 維（HandOver 第一條維度主張）。 |

## Project A — 流守恆與維度（Level 3）

同法炮製：S14／28 邊 → 終末 2 態 → 差分層 65 條 → 上界 ≤ 31 →
下界 ≥ 31 → **dim span(dF96) = 31**（96 維中）。兩個 Dim 檔由
`tools/gen_l3dim.py` 機械生成，CI 強制逐位再生性。

| 定理 | 檔案 | 一句話 |
|---|---|---|
| `CollatzFST.L3.S14_closed` | `ProjectA/Collatz_FST_L3_Flow.lean` | 14 個可達狀態在 `step3` 下封閉（48 維中 20 座標恆死）。 |
| `CollatzFST.L3.microTrace3_flow_conservation` | `ProjectA/Collatz_FST_L3_Flow.lean` | trace 層流守恆（與 Level 2 逐字同型）。 |
| `CollatzFST.L3.state_outflow_eq_occ3`、`inflow_eq_sum_occ3`、`kirchhoff_occ3` | `ProjectA/Collatz_FST_L3_Flow.lean` | 出入流接特徵層（28 條轉移邊）→ 純特徵層 Kirchhoff 泛函。 |
| `CollatzFST.L3.run3_extIn_terminal` ★（`terminal-l3`） | `ProjectA/Collatz_FST_L3_Flow.lean` | 終末狀態定理：恆落在 `{(0,S,0,1), (0,S,1,0)}`——2 個，不是 4 個。 |
| `CollatzFST.L3.kirchhoff_occ3_extIn_clean`、`kirchhoff_occ3_extIn_merged` | `ProjectA/Collatz_FST_L3_Flow.lean` | 12 條乾淨 + 1 條合併 = 13 條可用流守恆。 |
| `CollatzFST.L3.occ3_mode_bit_sum` ★（`mode-bit-sum-l3`） | `ProjectA/Collatz_FST_L3_Flow.lean` | 模式位元恆等式全稱版：`F3[16] + F3[33] = 1` 對所有 x（`mode_bit_endpoints3` 的推廣）。 |
| `CollatzFST.L3.dF96_dead` | `ProjectA/Collatz_FST_L3_Delta.lean` | 提升死座標 40 條合一：不可達狀態的兩區塊座標恆零。 |
| `CollatzFST.L3.dF96_flow_clean` | `ProjectA/Collatz_FST_L3_Delta.lean` | 提升乾淨流守恆 22 條合一（`c = 0` 的 11 狀態 × 2 區塊）。 |
| `CollatzFST.L3.dF96_block0_mode`、`dF96_block1_exit` | `ProjectA/Collatz_FST_L3_Delta.lean` | 2 條區塊相依死座標：`θ₀[33]`、`θ₁[16]` 恆零（靠 `occ3_mode_bit_sum`）。 |
| `CollatzFST.L3.dF96_fstart` ★（`fstart-l3-crossblock`） | `ProjectA/Collatz_FST_L3_Delta.lean` | 第 65 條：初始狀態流守恆對兩區塊求和（常數 −1 對消，免模式分析）。 |
| `CollatzFST.L3.dFQ96_mem_Sol` | `ProjectA/Collatz_FST_L3_DimUpper.lean` | 每個 `dF96 x` 都落在 65 條泛函切出的解空間 `Sol96`。 |
| `CollatzFST.L3.pick96_injective_on_Sol` | `ProjectA/Collatz_FST_L3_DimUpper.lean` | 31 個自由座標在 `Sol96` 上單射。 |
| `CollatzFST.L3.finrank_span_dFQ96_le` | `ProjectA/Collatz_FST_L3_DimUpper.lean` | 上界：`dim span(dF96) ≤ 31`。 |
| `CollatzFST.L3.dFW96_linearIndependent` | `ProjectA/Collatz_FST_L3_DimLower.lean` | 31 條見證線性獨立（31×31 自由座標矩陣么模，det = 1）。 |
| `CollatzFST.L3.thirtyone_le_finrank_span_dFQ96` | `ProjectA/Collatz_FST_L3_DimLower.lean` | 下界：`31 ≤ dim span(dFQ96)`。 |
| `CollatzFST.L3.finrank_span_dFQ96_eq_31` ✦ ★（`dim-l3-eq-31`） | `ProjectA/Collatz_FST_L3_DimLower.lean` | **維度定理**：Level 3 雙模式有效差分空間恰為 31 維（HandOver 第二條維度主張；A-3 收官）。 |

### 模式分裂打破吸收（三行速記）

| 情境 | `[16]+[33]` 泛函的地位 |
|---|---|
| 單模式（48 維） | `ΔF3[16] + ΔF3[33] = 0` 成立，但**被家族吸收**（死 20 + 流 13 已張成，秩 32 完備）。 |
| 雙模式・同區塊（`θ_b[16] + θ_b[33]`） | **連關係都不是**（模式翻轉時殘留 ±1）。 |
| 雙模式・跨區塊（`θ₀[16] + θ₁[33]`） | 成立且為**唯一缺口**（第 65 條；Lean 以 `dF96_fstart` 重組落地）。 |

出處：`tools/l3_recon.py` ⑥（精確有理對帳，含推導打印）＋
`ProjectA/Collatz_FST_L3_Delta.lean` 檔頭「65 條的帳」＋ ROADMAP-A A-3。

## Project B — B0 語義層＋B1 reweighting＋B1.5 structured gauge＋B3a 實例化橋＋B3b 差分自動機（皆已完成）

ProjectB 分區首批實體（B0，2026-08-28）。全部非 paper-facing，不入 registry、
不入 Audit 信任基底。B0-3 的標記字母表修正（原 ROADMAP 註記在未標記字母表上
不可能成立：`extIn 1` 是 `extIn 9` 的前綴、接受態在循環上）與 Q1/Q2 設計定案
見 [ROADMAP-B.md](ROADMAP-B.md) 的 B0 完成紀錄。namespace 一律
`CollatzFST.ProjectB`。

B1（Nonnegative Reweighting Theorem）2026-08-28 兩段收官：B1a（PR #41——
定義層＋(1)⟹(2)＋(3)⟹(1)＋吸收恆等式）＋B1b（(2)⟹(3) 有界長最短路勢能＋
tfae 收口）。載體抽象、import 純 mathlib（零 Core）；設計定案（Q1–Q4、偏差點
D1/D2/D3）與完成紀錄見 ROADMAP-B.md 的 B1 節。

B1.5 殘項（structured gauge lemma）2026-08-28 收口：`SelCostAutomaton`——
雙暫存器＋終態選擇（§0 歸類 2-register copyless CRA + final selection 的
最小載體），主定理 = B1 出口兩次應用＋β-吸收恆等式（α 不動、偏移落在
per-(mode, terminal)，與 #39 β_{m,t} 對齊；合成 = A 定理升級，見後續 PR）。
設計定案（Q1–Q4、D1–D5）與完成紀錄見 ROADMAP-B.md 的 B1.5 節。

B3a（用 B 框架重推 A，第一階段）2026-09-04 收官：`L2auto θ` = Core Level-2
機器 × B0 `extDFA` 的 language-product（零 ProjectA import），B 自訂座標
`featIdx`（狀態 tuple 字典序，σ(B→A) 非平凡）與佔用向量 `F_B`，橋定理
`cost_eq_sum`，no-go 重推 `no_go_L2` = 抽象錐矛盾 `farkas_contra` ＋ kernel
`decide` 聚合（λ_B = 最輕單座標憑證，Σλ = 34——W₁₀ 上單座標憑證恰三個，
A 的 Σλ = 1024 是其一）；D7 語言層全稱形 `no_go_L2_lang`。交叉認證與 B2
harness 在 `tools/b3_attest.py`。設計定案（Q1–Q5、D1–D7）與完成紀錄見
ROADMAP-B.md 的 B3 節。

B3b（2026-09-04，**tools 層、零 Lean**）：差分自動機 `D(θ)`（`tools/b3b_diff.py`，由 attest §G
進 CI）——輸入側 Core Level-2 機器 × 輸出側同一台機器（發射位同步驅動）× 7 態 ranking-domain
DFA，成本橋 `cost_{D(θ)}(extInM x) = θ·ΔF_B(x)`；B2 引擎對 θ ≥ 0 樣本全語言 fail、見證解碼；
θ-LP（328 simple cycles／8269 elementary 路徑）以自建精確單純形判定**不可行**，整數圖憑證
三種（LP 導出、對立對 (25, 315)、B3a 提升 Σν = 34 聚合 e₁₇）。**發現**：ΔF_B(25) + ΔF_B(315) = 0
⟹ L2 單模式**任意符號**線性 ranking 的 2 見證 no-go（paper 增補候選，轉交修訂線）；雙模式
亦有對立對（觀察層）。無新定理；B3c（Lean 鏡射，含該 2 見證定理，落 ProjectB）待排程。

| 定理 | 檔案 | 一句話 |
|---|---|---|
| `ProjectB.mem_oddDFA_accepts_iff` | `ProjectB/Collatz_FST_OddLanguage.lean` | B0-1：6 狀態 DFA `oddDFA` 恰接受 canonical odd language（謂詞層 `IsCanonicalOdd` 一致）。 |
| `ProjectB.isCanonicalOdd_digits`、`digits_ofDigits_of_canonical`、`ofDigits_odd` | `ProjectB/Collatz_FST_OddLanguage.lean` | 語言與 ℕ 的往返（mathlib digits 引理的包裝）。 |
| `ProjectB.sentinel_positions` | `ProjectB/Collatz_FST_OddLanguage.lean` | B0-3 位置事實：`extInM x` 的走行恰在兩個哨兵步進入尾段 `tail1`/`tail2`（`tail2` = 接受態）。 |
| `ProjectB.lstep_some_ne_tail1`、`lstep_some_ne_tail2` | `ProjectB/Collatz_FST_OddLanguage.lean` | 尾段唯哨兵字母可進入——哨兵邊不與任何普通邊同一 product 邊。 |
| `ProjectB.sentinel_edge₁_no_cycle`、`sentinel_edge₂_no_cycle` | `ProjectB/Collatz_FST_OddLanguage.lean` | B0-3 無環性：兩條哨兵邊不在任何循環上（`tail1 ⇝̸ acc`、`tail2 ⇝̸ tail1`）。 |
| `ProjectB.prodRun_snd` | `ProjectB/Collatz_FST_OddLanguage.lean` | product 投影：DFA 分量 = `extDFA` 走行——哨兵事實對任意機器 × 語言 DFA 的乘積生效。 |
| `ProjectB.extInM_unmark` | `ProjectB/Collatz_FST_OddLanguage.lean` | 標記輸入 `extInM` 去標記後恰為 Core 的 `extIn`（一行投影橋）。 |
| `ProjectB.U_runOut` | `ProjectB/Collatz_FST_Transducer.lean` | 橋接：subsequential 包裝 `U` 的走行 = Core `run`（B0 唯一結構歸納，逐 case rfl）。 |
| `ProjectB.ofDigits_U_output`、`U_output_split`、`ofDigits_Uacc`、`Uacc_digits` | `ProjectB/Collatz_FST_Transducer.lean` | acceptance 全 re-export（← `ofDigits_transduce`／`transduce_split`／`Todd_eq_dropWhile`／`digits_Todd_eq_drop`）。 |
| `ProjectB.isCanonicalOdd_Uacc` | `ProjectB/Collatz_FST_Transducer.lean` | closure：`w ∈ L ⟹ Uacc w ∈ L`——對全體 L 成立、不排除 `[1]`（`Uacc_one` 落點示例）。 |
| `ProjectB.rankingDomain_iff` | `ProjectB/Collatz_FST_Transducer.lean` | 排名 domain 條款 `w ≠ [1] ↔ 1 < ofDigits w`（B1 對接 no-go 量詞的 hook）。 |
| `ProjectB.CostAutomaton`（＋`cost`／`Useful`／`UsefulEdge`／`BoundedBelow`／`CyclesNonneg`／`HasPotential`） | `ProjectB/Collatz_FST_B1_Reweighting.lean` | B1 載體：抽象確定性有理權重成本自動機與三個敘述端點（零 Collatz 內容、import 純 mathlib）。 |
| `ProjectB.CostAutomaton.cyclesNonneg_of_boundedBelow` | `ProjectB/Collatz_FST_B1_Reweighting.lean` | B1 (1)⟹(2)：成本有下界 ⟹ useful cycles 非負（pump k 圈＋阿基米德；零 Fintype）。 |
| `ProjectB.CostAutomaton.boundedBelow_of_hasPotential` | `ProjectB/Collatz_FST_B1_Reweighting.lean` | B1 (3)⟹(1)：useful-edge 勢能 ⟹ 成本一致下界（望遠鏡；零 Fintype）。 |
| `ProjectB.CostAutomaton.reweight_cost` | `ProjectB/Collatz_FST_B1_Reweighting.lean` | B1 吸收恆等式：Johnson reweighting（`α−h(init)`／`β+h`）之下 cost 逐字恆等（任意 h，與蘊含正交）。 |
| `ProjectB.CostAutomaton.hasPotential_of_cyclesNonneg` | `ProjectB/Collatz_FST_B1_Reweighting.lean` | B1 (2)⟹(3)：useful cycles 非負 ⟹ 存在勢能——見證 `potential`（有界長最短路，可 #eval 機算；死區任取 0）。 |
| `ProjectB.CostAutomaton.exists_short_le_wpath`、`potential_triangle` | `ProjectB/Collatz_FST_B1_Reweighting.lean` | 縮短 B（全案樞紐：(2) 之下成本不升地縮到長 < card Q）與 useful 邊三角不等式。 |
| `ProjectB.CostAutomaton.boundedBelow_tfae` | `ProjectB/Collatz_FST_B1_Reweighting.lean` | B1 文件性收口：(1)(2)(3) 三敘述 TFAE（主要出口仍是三條具名單箭頭）。 |
| `ProjectB.SelCostAutomaton`（＋`restrict`／`cost`／`BoundedBelow`／`HasPotential`） | `ProjectB/Collatz_FST_B15_SelGauge.lean` | B1.5 載體：雙暫存器＋終態選擇（單一機器＋`sel : Q → Fin 2`＋`w : Fin 2 → Q → A → ℚ`）；`restrict m` 投影到 `CostAutomaton`（B1 全 API 免費取得）。 |
| `ProjectB.SelCostAutomaton.boundedBelow_restrict` | `ProjectB/Collatz_FST_B15_SelGauge.lean` | B1.5 Q3 分解：一致下界對量詞限縮封閉（`cost_restrict` 一行；空接受集空虛成立、無特判）。 |
| `ProjectB.SelCostAutomaton.reweight_cost` | `ProjectB/Collatz_FST_B15_SelGauge.lean` | B1.5 β-吸收恆等式：`w′ m = w m + h m∘src − h m∘dst`、α 不動、`β′ = β + h(sel ·)· − h(sel ·)(init)` 之下 cost 對全體字恆等（任意 h、與蘊含正交；偏移 = per-(mode, terminal) 常數，#39 β_{m,t} 對齊處）。 |
| `ProjectB.SelCostAutomaton.structured_gauge`（＋`hasPotential_of_boundedBelow`） | `ProjectB/Collatz_FST_B15_SelGauge.lean` | B1.5 主定理：雙模式 bounded-below ⟹ ∃ h : Fin 2 → Q → ℚ，每個 m、每條 `(restrict m).UsefulEdge` reweighted 權重 ≥ 0 且 cost 恆等（B1 出口兩次應用＋choose 收族；Q2 措辭紀律逐 m 宣稱）。 |
| `ProjectB.L2auto`（＋`featIdx`／`featList`／`F_B`） | `ProjectB/Collatz_FST_B3_L2Instance.lean` | B3a 實例化橋：Core Level-2 機器 × B0 `extDFA` 的 language-product（`prodStep step2`），權重 `θ (featIdx q (unmark a))`、α = β = 0、接受集 `S8 ×ˢ {tail2}`（D1）；B 自訂座標（狀態 tuple 字典序、K 列摺疊）與佔用向量。 |
| `ProjectB.cost_eq_sum`（＋`wpath_prod`／`cost_eq_featList`） | `ProjectB/Collatz_FST_B3_L2Instance.lean` | 橋定理：`cost (L2auto θ) (extInM x) = ∑ i, θ i * F_B x i`（唯一實質歸納 `wpath_prod` ＋ mathlib list-count 求和）。 |
| `ProjectB.accepts_extInM` | `ProjectB/Collatz_FST_B3_L2Instance.lean` | 奇數 x 的 `extInM x` 被 `L2auto θ` 接受（Core `run2_mem_S8` ＋ B0 `sentinel_positions`）。 |
| `ProjectB.farkas_contra` | `ProjectB/Collatz_FST_B3_L2Instance.lean` | 抽象錐矛盾（B5 三成分之一）：λ > 0、聚合 Σλ·D 逐座標 ≥ 0 ⟹ 不存在 θ ≥ 0 使每列 θ·D_j < 0。 |
| `ProjectB.no_go_L2`（＋`agg_nonneg`／`agg_eq_e17`） | `ProjectB/Collatz_FST_B3_L2Instance.lean` | B3a no-go 重推：不存在 θ ≥ 0 使 `L2auto θ` 的成本在 `W_B` = W₁₀ 每步 Todd 迭代嚴格下降；λ_B = (3,2,4,2,2,6,5,1,6,3)（Σ 34、聚合 e₁₇），聚合由 kernel `decide`，Todd 值經 B0 `U`。 |
| `ProjectB.no_go_L2_lang` | `ProjectB/Collatz_FST_B3_L2Instance.lean` | 語言層全稱形（D7）：量詞走 B0 `RankingDomain`、動力學走 `Uacc`——`D_A(x) = V(U(x)) − V(x)` 的形狀。 |

## Tools 錨（CI 強制）

`.github/workflows/guard.yml` certs job 每次 push 都跑（精確有理、零浮點、決定性）：

| 腳本 | 驗什麼 | 本機耗時 |
|---|---|---|
| `tools/certificates.py` | ΔF 特徵萃取 Python↔Lean 交叉驗證；三組 λ 從見證集重解（`W₁₀` 解族唯一）；模式流量平衡 = 0（A-2 仿射升級前提）；B1.5 雙平衡錨（`--b15`：W17/W26 聚合向量＋四條 per-(m,t) 平衡 = 0）。 | ~1 s |
| `tools/b15_terminal_balance.py` | 既有 W₁₂/W₂₀ 憑證終末不平衡 ±428/±753 的精確整數重算（論文 §6 exact-integer 錨；B1.5 資料點 1）。CI 步驟經專案主人具名授權（B1.5 PR）。 | ~0.2 s |
| `tools/a3_functionals.py` | Level 2 上界泛函完備性（死 2 + 流守恆 7、秩 8 = 18 − 10）；Lean↔Python 三條錨（16 邊關聯表、9 條差分關係、自由座標＋重建公式）。 | ~2.6 s |
| `tools/l3_recon.py` | Level 3 全套偵察對帳：14 狀態／28 邊、終末 2 態、單模式 dim 16（完備）、雙模式 dim 31（缺口 = `θ₀[16]+θ₁[33]`）、65 條上界資料。 | ~15 s（沙盒可達 ~51 s） |
| `tools/gen_l3dim.py` | 重新生成兩個 L3 Dim 檔後 `git diff --exit-code`——「逐位可重現」是 CI 強制，不是宣稱。 | — |
| `tools/b2_engine.py` | B2 全語言判定引擎自測（`--selftest`）：B1 玩具機已知答案 T1–T5（含 Karp 角與真 pump）、負向測試四則（竄改憑證/見證必紅）、固定種子 300 台 oracle 判準矩陣。pass 憑證 (R, C, d) 過 P1–P5 局部檢查（B3 Lean 驗證書前身）、fail 見證字直接求值。CI 步驟經專案主人具名授權（B2 PR）。 | ~0.01 s |
| `tools/b3_attest.py` | B3a 交叉認證：B 側自含實作＋Lean 錨（見證／Todd 值／λ_B／聚合／20 條 `featList`）；λ_B 單座標掃描獨立重解（W₁₀ 上恰三個：Σλ 1024／312／34）＋精確單純形第四頂點；三段式認證（σ 雙射、`F_B ≡ F2∘σ` x < 4096、A 的 λ = 掃描 k = 2 成員、Lean 用最輕 k = 17）；B2 harness（22 態截斷、四組 θ 覆蓋 pass／循環／邊界）；負向測試四則。**§G（B3b）**：呼叫 `tools/b3b_diff.py` 的 CI 段——差分自動機構造與手算錨、成本橋兩通道、枚舉規模（65／39／75／4；328／175；8269／5140）、θ-LP 不可行的整數圖憑證三種（含對立對 (25, 315) 三件套、B3a 提升）、負向測試五則、引擎 harness 25 組 θ 全 fail 最小見證 3。CI 步驟經專案主人具名授權（B3a PR）；B3b 不加步。 | ~2 s |
| `tools/b3b_diff.py` | B3b 函式庫（純標準庫）：`build_diff_automaton`／`instantiate(θ)`／`decode_witness`／枚舉／自建精確單純形（輸出全數自驗）／`theta_lp`／`verify_graph_certificate`／`opposite_pairs`／`lift_b3a`；CI 段 `run_checks` 由 attest §G 呼叫；`--deep` 本機重掃（向量橋 x < 2¹⁶、對立對普查含雙模式觀察、θ sweep ×200、只留路徑列 LP）。 | 經 attest 進 CI ~1.4 s；`--deep` ~15 s（本機） |

另：**Cramer 定律**（λ = 被湮滅列的 adjugate／極大子式向量、憑證整數值 = 子式、
`Σλ ≠ det` 守則）由 `tools/certificates.py --cramer` 驗證，闡述見 ROADMAP-A A-4 段。
這是 **tools 層結果，非 Lean 定理**。

## 進行中

- **A-4 論文化**（[ROADMAP-A.md](ROADMAP-A.md)）——A-0～A-3 已全部完成，這是 Project A 唯一殘項。
- **外部文獻審計** `docs/audit/2506-21728.md` 已定稿（2026-08-01，PR-2；
  重現腳本 `tools/audit_falsifiers.py`）——僅低頻追蹤 arXiv 2506.21728 後續版本。
- **Project B**：戰略見 ROADMAP-B.md（Phase 0 PR-3 落地；HANDOVER 的
  Project B 段由其取代）。B1.5 雙平衡精確化已完成（2026-08-08）：
  兩條 per-(mode, terminal) 仿射 no-go 落地 `ProjectA/`（上表），
  錨 `tools/certificates.py --b15`；structured gauge lemma 隨 B1 進行。
  **B0 語義層已完成（2026-08-28）**：ProjectB 分區首批兩檔（上表），
  B1 end-marker 警告由 B0-3 哨兵引理正式解除；下一步 B1 reweighting。
  **B2 全語言判定引擎已完成（2026-08-28，tools 層、零 Lean）**：
  `tools/b2_engine.py`（上表；設計定案 Q1–Q4、D1–D6 與完成紀錄見
  ROADMAP-B.md B2 節）。
  **B3a 已完成（2026-09-04）**：Level 2 單模式實例化橋＋見證集 no-go 用 B 框架
  重推成功（上表；`tools/b3_attest.py` 三段式認證），W₁₀ 上單座標 Farkas 憑證
  恰三個的發現與「31 為目標相依子式」敘事修正見 ROADMAP-B.md B3 節。
  **B3b 已完成（2026-09-04，tools 層）**：差分自動機 `D(θ)` ＋ B2 引擎全語言重推 ＋ θ-LP
  圖憑證（`tools/b3b_diff.py`，attest §G 進 CI）；θ-LP 不可行、憑證三種；**對立對發現**
  ΔF_B(25) + ΔF_B(315) = 0 ⟹ L2 單模式任意符號線性 ranking 的 2 見證 no-go（paper 增補
  候選轉交修訂線；雙模式亦有對立對，觀察層），見 ROADMAP-B.md B3 節 B3b 紀錄；
  下一步 B3c（Lean 鏡射：`rdDFA`、`DiffAuto θ`、圖憑證驗證書、2 見證無符號定理，落 ProjectB）待排程。
