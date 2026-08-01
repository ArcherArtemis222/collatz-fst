# 定理狀態索引（唯一真相來源）

最後更新：2026-08-01 ／ 對應 commit：`fa7db50`（Audit Update 2, #24）

> 本檔由 repo 現況生成：定理名逐條 grep 核實、一句話摘要取自各定理 docstring。
> 歷史敘述見 [HANDOVER.md](HANDOVER.md)（快照，不再更新）；待辦見
> [ROADMAP-A.md](ROADMAP-A.md) 與 ROADMAP-B.md。
> 標 ✦ 者列於 Audit.lean（`Lean4RealConstruction/` 根）的 `#print axioms` 信任基底
> （期望輸出僅 `propext` / `Classical.choice` / `Quot.sound`）。

---

## Core（凍結）

轉換器與 Level 2 自動機的基底層。`Core/` 只有專案主人能改（AGENTS.md §1）。
下表只列信任基底與 ProjectA 直接依賴的結構定理；支撐層
（Statements / Monoid / Ext / Phase / Level2 五檔）的完整內容見各檔檔頭。

| 定理 | 檔案 | 一句話 |
|---|---|---|
| `CollatzFST.ofDigits_transduce` ✦ | `Core/Collatz_FST_Statements.lean` | 轉換器正確性：`ofDigits 2 (transduce x) = 3x + 1`。 |
| `CollatzFST.transduce_split` ✦ | `Core/Collatz_FST_Statements.lean` | 輸出串恰為「`v₂(3x+1)` 個 0」++ 消去後的串（位移對齊、不干擾高位）。 |
| `CollatzFST.Todd_eq_dropWhile` ✦ | `Core/Collatz_FST_Statements.lean` | 尾零消去後的數值恰為加速映射 `T_o(x)`。 |
| `CollatzFST.padicValNat_eq_altPrefixLen` ✦ | `Core/Collatz_FST_Ext.lean` | `v₂(3x+1) = a(x)`（二進位交錯前綴長）。 |
| `CollatzFST.boundary_step_unique` ✦ | `Core/Collatz_FST_Level2.lean` | 邊界觸發步唯一：起始相位 K 且輸出 1 的步恰好一次（`E^K` 聚合形式）。 |
| `CollatzFST.birth_death_conservation` ✦ | `Core/Collatz_FST_Level2.lean` | 誕生−死亡守恆律：`#(0→1) + [p=1] = #(1→0) + [末位=1]`。 |
| `CollatzFST.occ2_deadState` | `Core/Collatz_FST_Level2.lean` | 死狀態 `(0,K,·)` 的兩個特徵計數恆為零（LP 的免費約束）。 |
| `CollatzFST.S8_closed` | `Core/Collatz_FST_Level2.lean` | 8 個可達狀態在 `step2` 下封閉——排除死狀態 `(0,K,0)`，終末狀態定理的關鍵。 |

## Project A — No-Go 定理

三個模板 × （有限見證版／全稱版／仿射版）共 8 條。見證集與 Farkas 憑證：

| 憑證 | 見證集 | Σλ | 重算錨 |
|---|---|---|---|
| Level 2 單模式 | `CollatzFST.LP.W₁₀`（10 個） | 1024 | `tools/certificates.py`（解族唯一；`--cramer`：λ = adj(A_free) 第 2 列、31 = det） |
| Level 2 雙模式 | `CollatzFST.TwoMode.W12`（12 個） | 7826 | `tools/certificates.py`（模式流量平衡 = 0，A-2 前提） |
| Level 3 雙模式 | `CollatzFST.L3.W20`（20 個） | 31746 | `tools/certificates.py`（同上） |

| 定理 | 檔案 | 一句話 |
|---|---|---|
| `CollatzFST.LP.no_nonneg_linear_ranking` ✦ | `ProjectA/Collatz_FST_NoLinearRanking.lean` | 不存在非負權重使線性勢能在 `W₁₀` 每一步嚴格下降。 |
| `CollatzFST.LP.no_global_odd_ranking` ✦ | `ProjectA/Collatz_FST_NoLinearRanking.lean` | 全稱版：對每個奇數 `x > 1` 皆嚴格下降的非負線性 ranking 不存在（量詞已排除 `x = 1`，A-1）。 |
| `CollatzFST.TwoMode.no_go_2mode_potential` ✦ | `ProjectA/Collatz_FST_2Mode_NoGo.lean` | 不存在兩組非負權重使雙模式勢能在 `W12` 每一步嚴格下降。 |
| `CollatzFST.TwoMode.no_go_2mode_affine_potential` | `ProjectA/Collatz_FST_2Mode_NoGo.lean` | 仿射版（A-2）：`V_m = β_m + θ_mᵀF`，截距不受非負限制，仍不可行。 |
| `CollatzFST.TwoMode.no_global_odd_2mode_potential` | `ProjectA/Collatz_FST_2Mode_NoGo.lean` | 全稱版：對每個奇數 `x > 1` 皆嚴格下降的雙模式勢能不存在。 |
| `CollatzFST.L3.no_go_level3_2mode_potential` ✦ | `ProjectA/Collatz_FST_L3_2Mode_NoGo.lean` | 不存在兩組非負權重使 Level 3 雙模式勢能在 `W20` 每一步嚴格下降。 |
| `CollatzFST.L3.no_go_level3_2mode_affine_potential` | `ProjectA/Collatz_FST_L3_2Mode_NoGo.lean` | 仿射版（A-2）：Level 3 勢能加截距 `β₀ β₁` 仍不可行。 |
| `CollatzFST.L3.no_global_odd_level3_2mode_potential` | `ProjectA/Collatz_FST_L3_2Mode_NoGo.lean` | 全稱版：對每個奇數 `x > 1` 皆嚴格下降的 Level 3 雙模式勢能不存在。 |

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
| `CollatzFST.Flow.kirchhoff_occ2` | `ProjectA/Collatz_FST_Flow.lean` | 純特徵層 Kirchhoff 泛函：18 維特徵上的線性關係（A-3 上界可用形式）。 |
| `CollatzFST.Flow.runCarry_extIn` | `ProjectA/Collatz_FST_Flow.lean` | 讀完 `extIn x` 後最終進位為 0（兩個哨兵零沖掉進位）。 |
| `CollatzFST.Flow.run2_extIn_terminal` | `ProjectA/Collatz_FST_Flow.lean` | 終末狀態定理：對所有 x 恆落在 `{(0,S,0), (0,S,1)}`。 |
| `CollatzFST.Flow.kirchhoff_occ2_extIn_clean` | `ProjectA/Collatz_FST_Flow.lean` | 非終末 6 條乾淨流守恆（終末指示恆 0）。 |
| `CollatzFST.Flow.kirchhoff_occ2_extIn_merged` | `ProjectA/Collatz_FST_Flow.lean` | 兩個可能終末合併成第 7 條（指示相加恆 1）。 |
| `CollatzFST.Flow.dF_zero_0`、`dF_zero_1` | `ProjectA/Collatz_FST_FlowDelta.lean` | 差分層死座標：`ΔF₀ = ΔF₁ = 0`。 |
| `CollatzFST.Flow.dF_flow_1K0`、`dF_flow_2K0`、`dF_flow_1S0`、`dF_flow_1S1`、`dF_flow_2S0`、`dF_flow_2S1` | `ProjectA/Collatz_FST_FlowDelta.lean` | 6 個非終末狀態的差分層流守恆；`dF_flow_2K0` 即舊表「K 區交錯 e₄ = e₅ + e₆」。 |
| `CollatzFST.Flow.dF_flow_terminal_merged` | `ProjectA/Collatz_FST_FlowDelta.lean` | 合併終末的差分層流守恆（第 9 條；9 條合計秩 8）。 |
| `CollatzFST.Flow.dFQ_mem_Sol` | `ProjectA/Collatz_FST_DimUpper.lean` | 每個 `ΔF x`（ℚ 向量 `dFQ`）都落在 9 條關係切出的解空間 `Sol`。 |
| `CollatzFST.Flow.pick_injective_on_Sol` | `ProjectA/Collatz_FST_DimUpper.lean` | 10 個自由座標 `{2,3,6,7,8,9,10,11,15,17}` 在 `Sol` 上單射（其餘 8 座標可重建）。 |
| `CollatzFST.Flow.finrank_span_dFQ_le_ten` | `ProjectA/Collatz_FST_DimUpper.lean` | 上界：`dim span(ΔF) ≤ 10`。 |
| `CollatzFST.Flow.dFW_linearIndependent` | `ProjectA/Collatz_FST_DimLower.lean` | `W₁₀` 的 10 條 ΔF 線性獨立（自由座標 10×10 行列式 = 31 ≠ 0）。 |
| `CollatzFST.Flow.ten_le_finrank_span_dFQ` | `ProjectA/Collatz_FST_DimLower.lean` | 下界：`10 ≤ dim span(ΔF)`。 |
| `CollatzFST.Flow.finrank_span_dFQ_eq_ten` ✦ | `ProjectA/Collatz_FST_DimLower.lean` | **維度定理**：Level 2 特徵差分空間恰為 10 維（HandOver 第一條維度主張）。 |

## Project A — 流守恆與維度（Level 3）

同法炮製：S14／28 邊 → 終末 2 態 → 差分層 65 條 → 上界 ≤ 31 →
下界 ≥ 31 → **dim span(dF96) = 31**（96 維中）。兩個 Dim 檔由
`tools/gen_l3dim.py` 機械生成，CI 強制逐位再生性。

| 定理 | 檔案 | 一句話 |
|---|---|---|
| `CollatzFST.L3.S14_closed` | `ProjectA/Collatz_FST_L3_Flow.lean` | 14 個可達狀態在 `step3` 下封閉（48 維中 20 座標恆死）。 |
| `CollatzFST.L3.microTrace3_flow_conservation` | `ProjectA/Collatz_FST_L3_Flow.lean` | trace 層流守恆（與 Level 2 逐字同型）。 |
| `CollatzFST.L3.state_outflow_eq_occ3`、`inflow_eq_sum_occ3`、`kirchhoff_occ3` | `ProjectA/Collatz_FST_L3_Flow.lean` | 出入流接特徵層（28 條轉移邊）→ 純特徵層 Kirchhoff 泛函。 |
| `CollatzFST.L3.run3_extIn_terminal` | `ProjectA/Collatz_FST_L3_Flow.lean` | 終末狀態定理：恆落在 `{(0,S,0,1), (0,S,1,0)}`——2 個，不是 4 個。 |
| `CollatzFST.L3.kirchhoff_occ3_extIn_clean`、`kirchhoff_occ3_extIn_merged` | `ProjectA/Collatz_FST_L3_Flow.lean` | 12 條乾淨 + 1 條合併 = 13 條可用流守恆。 |
| `CollatzFST.L3.occ3_mode_bit_sum` | `ProjectA/Collatz_FST_L3_Flow.lean` | 模式位元恆等式全稱版：`F3[16] + F3[33] = 1` 對所有 x（`mode_bit_endpoints3` 的推廣）。 |
| `CollatzFST.L3.dF96_dead` | `ProjectA/Collatz_FST_L3_Delta.lean` | 提升死座標 40 條合一：不可達狀態的兩區塊座標恆零。 |
| `CollatzFST.L3.dF96_flow_clean` | `ProjectA/Collatz_FST_L3_Delta.lean` | 提升乾淨流守恆 22 條合一（`c = 0` 的 11 狀態 × 2 區塊）。 |
| `CollatzFST.L3.dF96_block0_mode`、`dF96_block1_exit` | `ProjectA/Collatz_FST_L3_Delta.lean` | 2 條區塊相依死座標：`θ₀[33]`、`θ₁[16]` 恆零（靠 `occ3_mode_bit_sum`）。 |
| `CollatzFST.L3.dF96_fstart` | `ProjectA/Collatz_FST_L3_Delta.lean` | 第 65 條：初始狀態流守恆對兩區塊求和（常數 −1 對消，免模式分析）。 |
| `CollatzFST.L3.dFQ96_mem_Sol` | `ProjectA/Collatz_FST_L3_DimUpper.lean` | 每個 `dF96 x` 都落在 65 條泛函切出的解空間 `Sol96`。 |
| `CollatzFST.L3.pick96_injective_on_Sol` | `ProjectA/Collatz_FST_L3_DimUpper.lean` | 31 個自由座標在 `Sol96` 上單射。 |
| `CollatzFST.L3.finrank_span_dFQ96_le` | `ProjectA/Collatz_FST_L3_DimUpper.lean` | 上界：`dim span(dF96) ≤ 31`。 |
| `CollatzFST.L3.dFW96_linearIndependent` | `ProjectA/Collatz_FST_L3_DimLower.lean` | 31 條見證線性獨立（31×31 自由座標矩陣么模，det = 1）。 |
| `CollatzFST.L3.thirtyone_le_finrank_span_dFQ96` | `ProjectA/Collatz_FST_L3_DimLower.lean` | 下界：`31 ≤ dim span(dFQ96)`。 |
| `CollatzFST.L3.finrank_span_dFQ96_eq_31` ✦ | `ProjectA/Collatz_FST_L3_DimLower.lean` | **維度定理**：Level 3 雙模式有效差分空間恰為 31 維（HandOver 第二條維度主張；A-3 收官）。 |

### 模式分裂打破吸收（三行速記）

| 情境 | `[16]+[33]` 泛函的地位 |
|---|---|
| 單模式（48 維） | `ΔF3[16] + ΔF3[33] = 0` 成立，但**被家族吸收**（死 20 + 流 13 已張成，秩 32 完備）。 |
| 雙模式・同區塊（`θ_b[16] + θ_b[33]`） | **連關係都不是**（模式翻轉時殘留 ±1）。 |
| 雙模式・跨區塊（`θ₀[16] + θ₁[33]`） | 成立且為**唯一缺口**（第 65 條；Lean 以 `dF96_fstart` 重組落地）。 |

出處：`tools/l3_recon.py` ⑥（精確有理對帳，含推導打印）＋
`ProjectA/Collatz_FST_L3_Delta.lean` 檔頭「65 條的帳」＋ ROADMAP-A A-3。

## Tools 錨（CI 強制）

`.github/workflows/guard.yml` certs job 每次 push 都跑（精確有理、零浮點、決定性）：

| 腳本 | 驗什麼 | 本機耗時 |
|---|---|---|
| `tools/certificates.py` | ΔF 特徵萃取 Python↔Lean 交叉驗證；三組 λ 從見證集重解（`W₁₀` 解族唯一）；模式流量平衡 = 0（A-2 仿射升級前提）。 | ~0.9 s |
| `tools/a3_functionals.py` | Level 2 上界泛函完備性（死 2 + 流守恆 7、秩 8 = 18 − 10）；Lean↔Python 三條錨（16 邊關聯表、9 條差分關係、自由座標＋重建公式）。 | ~2.6 s |
| `tools/l3_recon.py` | Level 3 全套偵察對帳：14 狀態／28 邊、終末 2 態、單模式 dim 16（完備）、雙模式 dim 31（缺口 = `θ₀[16]+θ₁[33]`）、65 條上界資料。 | ~15 s（沙盒可達 ~51 s） |
| `tools/gen_l3dim.py` | 重新生成兩個 L3 Dim 檔後 `git diff --exit-code`——「逐位可重現」是 CI 強制，不是宣稱。 | — |

另：**Cramer 定律**（λ = 被湮滅列的 adjugate／極大子式向量、憑證整數值 = 子式、
`Σλ ≠ det` 守則）由 `tools/certificates.py --cramer` 驗證，闡述見 ROADMAP-A A-4 段。
這是 **tools 層結果，非 Lean 定理**。

## 進行中

- **A-4 論文化**（[ROADMAP-A.md](ROADMAP-A.md)）——A-0～A-3 已全部完成，這是 Project A 唯一殘項。
- **外部文獻審計** `docs/audit/2506-21728.md`（Phase 0 PR-2，進行中）。
- **Project B**：戰略見 ROADMAP-B.md（Phase 0 PR-3 落地；HANDOVER 的
  Project B 段由其取代）。
