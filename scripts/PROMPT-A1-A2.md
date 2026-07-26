# 給本機 AI 協作者的任務指令：ROADMAP A-1 + A-2

> 用法：在 repo 根目錄開 Claude Code（或其他本機 agent），把底下 `---` 之間的整段貼進去。
> 這兩項都只動 `ProjectA/`，不會碰到需要人類簽核的凍結區，所以適合當第一輪。

---

你是這個 Lean 4 專案的協作者。動手前先完整讀 `AGENTS.md` 與 `docs/ROADMAP-A.md`。

## 任務

依序完成 **A-1** 和 **A-2**，**各自獨立一個 PR**，不要合併成一個。

### A-1：排除平凡量詞

`CollatzFST.LP.no_global_odd_ranking` 現在的量詞是 `∀ x, x % 2 = 1`。因為 `Todd 1 = 1`
所以 `ΔF 1 = 0`，`dot θ 0 = 0 < 0` 恆假——這個敘述存在平凡見證，不夠強。

加上 `1 < x`。`W₁₀ = [231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511]` 全部大於 1，
補一條 `W₁₀_gt_one` 用 `decide` 即可，主證明不動。

同時替另外兩條主定理補上對應的「全體奇數 `> 1`」推論：
`CollatzFST.TwoMode.no_go_2mode_potential` 和
`CollatzFST.L3.no_go_level3_2mode_potential` 目前只對有限集 `W12` / `W20` 敘述，
沒有全稱版本。三條定理的形式要一致。

### A-2：仿射截距 β_m

三條主定理目前都是純線性 `dot θ (F x)`。升級成含截距的仿射形式
`V_m(x) = β_m + θ_mᵀ F(x)`，其中 **`β₀ β₁` 不受非負限制**（截距本來就可正可負，
這才是真正的一般化）。

`docs/ROADMAP-A.md` A-2 段落有敘述的完整寫法，照抄。

**這一項的前提已經被驗證過了**：跑 `python3 tools/certificates.py`，
你會看到兩組雙模式憑證的模式流量平衡 `Σλ(e_{m(y)} − e_{m(x)})` 都等於 `[0, 0]`。
這代表 β 項會在 Farkas 組合裡自動抵消，所以：

- 證明骨架完全不用改：同一組 λ、同一批 `Todd_*` / `hm_*` 引理、同樣的 `rw [if_pos/if_neg]`。
- 收尾那個 `ring` 應該**原封不動**就過。

如果 `ring` 失敗，**停下來回報，不要硬湊**。那代表我們對憑證的理解有誤，是數學問題不是戰術問題。

## 邊界（違反就停下來回報，不要繞路）

**不可以碰**：

- `Lean4RealConstruction/Core/` 底下任何檔案，以及 `Core.lean`
- `lean-toolchain`、`lakefile.toml`、`lake-manifest.json`
- `.github/`、`scripts/`
- 不可以執行 `lake update`
- 不可以用 `sorry`、`native_decide`、`axiom`
- 不可以 push 到 `main`，不可以 merge 自己的 PR

A-1 和 A-2 **都只需要動 `Lean4RealConstruction/ProjectA/`**。如果你發現自己想改 Core，
那表示方向錯了——先停下來說明為什麼。

**不可以為了讓 build 過而弱化定理敘述。** 敘述要改是數學決策，回報等指示。

## 流程

```bash
./scripts/new-worktree.sh a fix-trivial-quantifier
cd ../collatz-fst-a-fix-trivial-quantifier
lake build                      # 基準線必須先是綠的
# ... 工作 ...
lake build
python3 scripts/check_boundaries.py
python3 tools/certificates.py   # 憑證數字不該被動到，這裡必須全綠
git commit -am "ProjectA: 排除 x = 1 的平凡量詞"
git push -u origin a/fix-trivial-quantifier
gh pr create --fill
```

A-2 用另一個 worktree、另一條分支（`a/affine-offsets`），從 `main` 開，不要疊在 A-1 上。

## 交付

每個 PR 要有：

1. `lake build` 的完整輸出（貼進 PR 描述）
2. 新增/修改的定理**全名**清單
3. 一句話說明對既有定理的影響（A-1、A-2 都應該是「無」——舊定理保留，新的是加強版）
4. A-2 完成後，順手把 `docs/ROADMAP-A.md` 的 A-2 段落從「尚未發生」改成已完成，
   並註明模式流量平衡已由 `tools/certificates.py` 驗證

做完 A-1 先停下來等我看過，再開始 A-2。
