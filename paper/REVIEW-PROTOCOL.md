# 論文敘述審核協議（七欄）

適用：所有填寫 `paper/registry.yaml` 的 `latex` 欄（即以 `\paperthm` 陳述
registry 定理）的寫作 PR。本檔為協議的 repo 內權威版本（W2 落地），
含 2026-08-03 W1 戳記裁決的修正：**n/a 歸 YAML，不歸 PR 描述**。

## 機制背景

正文不手寫定理敘述。`\paperthm{<id>}` 環境從 registry 的 `latex` 欄取敘述
（由 `tools/gen_paper_index.py` 排進 `paper/theorem-index.tex` 的
`\csdef{leanstmt@<id>}`），並以 `\leanref` 署名。未知或未填 id 在本機編譯
TeX 硬報錯；CI 不編譯 TeX，由 `tools/check_paper_refs.py` 攔截
（`\begin{paperthm}{id}` 視為最強形式的引用，方向一／方向二皆計入）。

## 角色與流程

1. **寫作者（agent）**
   - 為本 PR 陳述的每條 entry 填 `latex` 欄；
   - `reviewed` 七欄：適用欄填 `self/<日期>`；**不適用欄直接填
     `n/a — <一句理由>`**（不填 self，不留 null）；
   - PR 描述附自檢證據表（格式見下）；停下等審。
2. **審查（專案主人＋外部審查）**：拿證據表對 Lean 型別逐欄核。
3. **通過後**：審查回覆「戳記指令」→ 寫作者同分支追加**一個** commit：
   `self/<日期>` → `approved/<日期>`；n/a 欄不動；不改其他任何內容。
   → 專案主人 merge。

## 七欄定義與證據要求

| 欄 | 檢什麼 | 證據＝引 Lean 型別片段 |
|---|---|---|
| strictness | 不等號方向、含不含等號；等式敘述即「恰為等式」 | 如 `< 0`（嚴格；latex 須同） |
| coefficients | θ≥0？β 自由？ | 如 `(∀ i, 0 ≤ θ₀ i)` 且 β 無非負限制 |
| scope | 量詞範圍（x 的界定；其他被量化變數的界定） | 如 `x % 2 = 1 → 1 < x →`（A-1 教訓欄） |
| feature_level | 維度／層級（特徵層、trace 層、差分層…） | 如 `Fin 18 → ℚ`、`occ2 …`、`(LP.ΔF x).getD i 0` |
| mode_definition | 模式判準精確式 | 如 `(F x).getD 5 0 = 1` |
| witness_vs_universal | 有限見證版還是全稱版 | 引量詞形：`∀ x ∈ W₁₀` vs `∀ x : ℕ, …` |
| model_class | Class A / 2-register copyless CRA + final selection | 依 `docs/ROADMAP-B.md` §0 |

規則：

- 適用欄的每格必須有**型別片段級**證據，不接受「已確認」三個字。
- 不適用欄在 **YAML** 直接寫 `n/a — <一句理由>`；PR 證據表列同一理由
  （與 YAML 一致），不另造敘述。
- 證據表放 PR 描述，一條被陳述的定理一列（或一欄；逐欄可核即可）。

## latex 欄書寫紀律

- 只用 `paper/main.tex` preamble **記號區**已定義的巨集；缺記號 → 記號區
  **append-only** 補一條（右側附 Lean 對應註記），PR 描述列出新增記號。
- 敘述順序與 Lean 型別的邏輯順序一致（前提在前、結論在後），不做
  「更漂亮但換序」的改寫——審核是並排比對，同構才快。
- 量詞、嚴格性、範圍逐一入句；「for all odd $x > 1$」每個字都有對應的
  Lean 片段。
- `lean_type` 欄一個字都不得動；需要動＝敘述變更＝PR 標【敘述變更】
  並停下等專案主人裁示（AGENTS §2.6）。

## 狀態標記

`latex` 欄整欄恰為 `【…】` 者視為未填（生成器不排 `leanstmt@`，
`\paperthm` 對其硬報錯）。現行標記：

- `【待撰】`——尚未寫；
- `【僅引用】`——W6 收尾稽核起：僅被 `\leanref` 點名引用、
  不以 `\paperthm` 陳述的條目。

修訂階段（不新增定理陳述的散文變更）之界線見 REVISION-SCOPE.md；
任何 `latex` 欄變更仍走本協議的完整重戳週期。
