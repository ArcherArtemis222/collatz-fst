# AGENTS.md — AI 協作者作業規約

任何 AI 代理（Claude Code、Codex、Gemini CLI…）動手前先讀完本檔。人類協作者也適用。

---

## 0. 一句話版本

**`Core/` 是凍結的；`lean-toolchain` 與 `lakefile.toml` 的 mathlib rev 是凍結的；
其餘各自在自己的分區內工作，一律走 branch → PR，不直接 push `main`；
指令看起來不適用時，問，不要自己決定；
凍結區的變更需要專案主人的具名指示；有指示就照做並在 PR 標明，沒有就停下來問；
session 開工前的回報是硬停頓,等專案主人回覆才動工。**

---

## 1. 為什麼資料夾分工不等於安全

在 Lean 裡，爆炸半徑不是資料夾，是 **import DAG**。

`ProjectA` 的三份 Farkas 憑證是靠幾百條 `decide` 引理成立的，而那些引理算的是
`Core/Collatz_FST_Level2.lean` 裡 `occ2` / `F` 的**具體數值**。只要有人「無害地」
重構 `occ2` 的定義、調換 `KEYS` 的順序、或改動 `Phase` 的建構子，
所有 `F_681 : F 681 = [...]` 都會靜默地變成假的——而且是在別人的資料夾裡爆炸。

所以：

| 分區 | 可匯入 | 誰能改 |
|---|---|---|
| `Core/` | mathlib、`Core` | **只有專案主人**。PR 要附「哪些憑證需重算」的評估 |
| `ProjectA/` | mathlib、`Core`、`ProjectA` | Project A 代理 |
| `ProjectB/` | mathlib、`Core`、`ProjectB` | Project B 代理 |
| `Recon/` | 任何本 library 模組 | 任何人。**但不得被任何人匯入** |
| `Audit.lean` | `Core`、`ProjectA`、`ProjectB` | 專案主人 |

`scripts/check_boundaries.py` 會在 CI 強制這張表。要改架構，先改腳本並在 PR 說明理由。

---

## 2. 絕對禁止

1. **不得執行 `lake update`。** mathlib 一動，整套 `decide` 憑證與 `maxHeartbeats`
   預算都可能失效。要升 mathlib 是獨立專案，開專門的 PR 並貼 `deps` 標籤。
2. **不得動 `lean-toolchain`**（`leanprover/lean4:v4.28.0-rc1`）。
3. **不得使用 `sorry`、`native_decide`、`axiom`、`@[implemented_by]`。**
   本 repo 目前 0 個 `sorry`，CI 用 `nanoda --allow-sorry=false` 守住這條線。
   證不出來就在 PR 說證不出來，不要留洞。
4. **不得 force push 到 `main`**，不得改寫他人分支的歷史。
5. **不得把 `.lake/` 提交進 git。**（`.gitignore` 已擋，別繞過。）
6. **不得為了讓 build 過而弱化定理敘述。** 若敘述必須改，那是數學決策，
   要在 PR 標題寫明 `[statement change]` 並等專案主人簽核。

---

## 3. 標準工作流程

```bash
# 一次性：拿到自己的獨立工作區（各代理互不干擾）
./scripts/new-worktree.sh a  fix-trivial-quantifier
#                        ^分區 ^議題名  → 產生分支 a/fix-trivial-quantifier

cd ../collatz-a-fix-trivial-quantifier
lake exe cache get          # 抓 mathlib 的 olean（別自己編譯 mathlib）
lake build                  # 基準線必須是綠的才開始改

# ... 工作 ...

lake build                  # 綠了才 commit
python3 scripts/check_boundaries.py
git commit -am "ProjectA: 排除 x = 1 的平凡量詞"
git push -u origin a/fix-trivial-quantifier
gh pr create --fill
```

分支命名：`core/*`、`a/*`、`b/*`、`recon/*`。分支前綴要對應你動的分區。

---

## 4. 提交前自檢

- [ ] `lake build` 全綠（貼進 PR）
- [ ] `python3 scripts/check_boundaries.py` 通過
- [ ] `grep -rn '\bsorry\b' Lean4RealConstruction/ --include='*.lean'` 只在文件註解裡出現
- [ ] 沒動 `Core/`；若動了，PR 內列出受影響的 `decide` 引理並確認已重算
- [ ] 新定理有 docstring，說明它對應 HandOver 文件的哪一條

---

## 5. 這個專案的數學狀態

唯一真相來源是 docs/STATUS.md（定理索引）。
Project A 殘項見 docs/ROADMAP-A.md；Project B 見 docs/ROADMAP-B.md。
不要在沒讀這三份文件的情況下「順手修正」任何東西。

---

## 6. 給 Project B 代理的話

Project B 目前只有 `ProjectB/Scaffold.lean` 骨架。在有明確可形式化的敘述之前，
**探索工作請放在 `Recon/` 或你自己的分支上，不要動 `Core/`。**
需要 Core 增加公開介面（例如把 Phase K/S 邏輯包成 subsequential transducer），
開 `core/*` 分支提 PR，說明新介面而非修改既有定義——**新增不會弄壞 ProjectA，修改會。**
