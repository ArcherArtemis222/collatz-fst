# Collatz 有限狀態平攤勢能

3x+1 加速映射的有限狀態轉換器形式化，以及「不存在單調下降之加權平攤勢能」的
一系列 no-go 定理。Lean 4 + mathlib，**0 個 `sorry`**。

- 專案背景與數學全貌：[`docs/HANDOVER.md`](docs/HANDOVER.md)
- Project A 待辦：[`docs/ROADMAP-A.md`](docs/ROADMAP-A.md)
- **協作規約（AI 與人都要讀）**：[`AGENTS.md`](AGENTS.md)

## 主定理

| 定理 | 位置 | 內容 |
|---|---|---|
| `CollatzFST.LP.no_nonneg_linear_ranking` | `ProjectA/…NoLinearRanking` | Level 2 單模式，10 條單步軌跡的 Farkas 憑證 |
| `CollatzFST.TwoMode.no_go_2mode_potential` | `ProjectA/…2Mode_NoGo` | Level 2 雙模式（valuation-parity），Σλ = 7826 |
| `CollatzFST.L3.no_go_level3_2mode_potential` | `ProjectA/…L3_2Mode_NoGo` | Level 3 × 雙模式，Σλ = 31746 |

底層轉換器的正確性（soundness、區塊重寫、`Todd` 與 dropWhile 的等價）在 `Core/`。

## 環境

工具鏈與 mathlib 都是**硬釘**的，不要改：

- `leanprover/lean4:v4.28.0-rc1`
- mathlib `c66c0c58f2770d2f264035b0229a6d1712e00dc5`

## 上手

```bash
git clone <this-repo> && cd <this-repo>
lake exe cache get     # 抓 mathlib 的預編譯 olean，別自己編（會編好幾小時）
lake build             # 全綠約需 10–30 分鐘
```

沒有 Lean 環境的話，先裝 elan：

```bash
curl -sSf https://elan.lean-lang.org | sh     # 之後開新終端機
```

`lean-toolchain` 會讓 elan 自動抓對版本，不用手動指定。

## 目錄結構

```
Lean4RealConstruction/
├─ Core/        共用轉換器核心 ── 凍結區，改動會讓 ProjectA 的憑證失效
├─ ProjectA/    有限狀態模板 no-go 定理（收尾階段）
├─ ProjectB/    加權自動機表達力極限（啟動階段，目前僅骨架）
├─ Recon/       偵察與 #eval 驗證，不得被上面三區匯入
└─ Audit.lean   把主定理的信任基底印進 build log
```

分區規則由 `scripts/check_boundaries.py` 在 CI 強制執行。

## CI

- `guard` — 秒級。匯入邊界 + 依賴釘選未被動過。
- `build` — 完整 `lake build`，加上 `leanchecker` 以 kernel 重新型別檢查。
- `no-sorry` — `nanoda` 獨立型別檢查器，`--allow-sorry=false`。誰都無法偷偷留洞。
