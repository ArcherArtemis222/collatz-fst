# paper/ 修訂階段操作規章（REVISION-SCOPE）

> 適用：A-4 收官後對 `paper/main.tex` 的讀者導向修訂（P1 摘要＋導言重寫、
> P2 數學線／驗證線分離、P3 running example）。內容審查由具名審查者負責，
> 本 repo 的 AI 審查僅做**合規閘門**。與七欄審核協議的分工：不新增定理
> 陳述的散文變更走本規章；任何 `latex` 欄變更退出本快車道，走
> `REVIEW-PROTOCOL.md` 的完整七欄重戳週期。

## 三層界線

**可動（免簽核）**：保護區外之散文；記號區（`main.tex` preamble
`% ---- Notation (append-only) ----` 區塊）append-only 新增；
`references.bib` 新條目（逐欄核實紀律照舊）；P3 範例的**已錨定**資料
（數值必須由 `tools/` 腳本輸出，掛既有 CI 腳本內，不動 `.github/`）。

**需專案主人簽核**：逐字保護區（精確範圍見下節）；標題／作者／日期；
**任何已戳記條目的 `latex` 欄**——改敘述＝退出修訂快車道，
走 REVIEW-PROTOCOL 完整七欄重戳週期。

**不可動**：registry `lean_type`；生成檔手改（`PaperIndex.lean`、
`theorem-index.tex`）；凍結區（`Core/`／`Audit.lean`／toolchain／
lakefile／manifest／`.github/`／`scripts/`）。

## 逐字保護區（需簽核的精確範圍）

1. **§6 模型界定三段**——`main.tex` 註解標 VERBATIM 的三段
   （docs/ROADMAP-B.md §0 的英譯）：Class A 歸類段（"The single-mode
   no-go theorems fall in **Class A**…"）、2-register copyless CRA
   歸類段（"The two-mode no-go theorems are *not* Class A…"）、
   推論段（"Consequently, even if the universal Class-A conjecture
   holds…"）。W5 新增的三層設定段（"'Finite-state method' is not a
   single class…"）屬 surrounding prose，不在逐字保護內，但依
   `main.tex` 註解原文：其宣稱不得被弱化或改述。
2. **§7 之 2506.21728 段**——"That work (arXiv:2506.21728) proposes a
   finite-state symbolic encoding…" 整段（docs/audit/2506-21728.md
   中性措辭的逐字英譯；書目掛 `\nocite`，不改寫入句）。
3. **摘要末句之兩個非宣稱子句**（實際措辭，2026-08-08 對 `main.tex`
   核實）：

   > This paper does not prove the Collatz conjecture, and it does not
   > establish the impossibility of all finite-state methods; the scope
   > boundary is made precise by a three-layer classification of
   > finite-state potentials.

## 每個修訂 PR 的機械合規清單（AI 閘門執行）

1. 單一分支、自 main head 開；`main.tex` 單線寫作（一次一個修訂 PR）。
2. 生成器重跑雙零 diff（`tools/gen_paper_index.py` →
   `PaperIndex.lean`＋`theorem-index.tex`）；`PaperIndex.lean` 逐位不變。
3. registry diff 分類：零觸碰，或僅【僅引用】↔ 引用狀態且經簽核；
   `latex` 欄變更一律退回重戳週期。
4. 保護區特徵句 grep（攤平換行後）：copyless CRA／one-accumulator／
   2-register／symbolic encoding／do not yet suffice／does not prove the
   Collatz conjecture／impossibility of all finite-state methods——零觸碰
   或附主人簽核。
5. 數字 census 增量：每個新數字帶**四擇一**歸屬——`\leanref`／tools
   出處（正文同位標明腳本）／信任標籤／repo 釘定事實（可逐一對 repo
   釘定狀態核驗）；排除項照 W6 定義（排版產物：頁碼、節號、定理編號、
   參考文獻編號；書目識別：arXiv id、DOI 前綴、年份、版本號）。
   P3 範例數據須指向錨腳本。錨腳本重算範圍的量詞照 W4b 修正措辭
   （"every hard-coded certificate, functional, and reconnaissance
   datum"），不得回流 "every hard-coded number"。
6. `latexmk`＋`lacheck`＋`check_paper_refs` 全綠（`check_paper_refs.py`
   三方向：引用必有出處／出處必被引用／陳述必已填）。
7. PR 描述**具名內容審查者**（人或 AI）；合規通過 ≠ 內容背書，兩者分離。
