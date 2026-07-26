# Project A 待辦：從「已證」到「符合定案規格」

`docs/HANDOVER.md` 記的是**規格**，`Lean4RealConstruction/ProjectA/` 裡的是**現況**。
兩者目前有落差。以下按「一個 PR 一項」拆開，難度由低到高。

---

## A-0 建立基準線（先做這個）

在任何人動手之前，確認 `lake build` 在乾淨環境下是綠的，把該次 commit 打上 tag
（例如 `v0-frozen-baseline`）。之後任何紅燈都能二分定位。

同時跑一次 `lake build Lean4RealConstruction.Audit`，把四條主定理的公理列印出來存檔——
那就是這份工作的信任基底。

---

## A-1 非平凡量詞：排除 `x = 1` ★ 小

**問題。** `CollatzFST.LP.no_global_odd_ranking` 現在寫的是

```lean
¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧ ∀ x : ℕ, x % 2 = 1 → dot θ (ΔF x) < 0
```

因為 `Todd 1 = 1`，所以 `ΔF 1 = 0`，`dot θ 0 = 0 < 0` 恆假——這個敘述**存在平凡見證**。
現有證明沒有用這個漏洞（它走 `W₁₀`），但敘述本身不夠強，論文寫出去會被審稿人抓。

**做法。** 加上 `1 < x`，被否定的東西變弱，定理變強：

```lean
lemma W₁₀_gt_one : ∀ x ∈ W₁₀, 1 < x := by decide

theorem no_global_odd_ranking :
    ¬ ∃ θ : Fin 18 → ℚ, (∀ i, 0 ≤ θ i) ∧
      ∀ x : ℕ, x % 2 = 1 → 1 < x → dot θ (ΔF x) < 0 := by
  rintro ⟨θ, hθ, h⟩
  exact no_nonneg_linear_ranking
    ⟨θ, hθ, fun x hx => h x (W₁₀_odd x hx) (W₁₀_gt_one x hx)⟩
```

`W₁₀ = [231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511]`，全部 `> 1`，`decide` 直接過。

**同時要做。** 雙模式與 Level 3 的主定理是對有限集 `W12` / `W20` 敘述的，
沒有全稱量詞版本。順手補上對應的「全體奇數 `> 1`」推論，三條定理形式才一致。

---

## A-2 仿射截距 `β_m` ★★ 中 ——【已完成】

**狀態（2026-07-26，分支 `a/affine-offsets`）。** 升級已落地：
`CollatzFST.TwoMode.no_go_2mode_affine_potential` 與
`CollatzFST.L3.no_go_level3_2mode_affine_potential`，`β₀ β₁` 皆不受非負限制。
兩組雙模式憑證的 mode-flow balance `Σλ(e_{m(y)} − e_{m(x)}) = [0, 0]` 已由
`tools/certificates.py` 重算驗證；一如下方驗收點的預期，收尾 `ring` 原封不動通過。
原線性版定理保留未動。以下為原始工作描述，留作紀錄。

**問題。** HandOver 宣稱定理「已直接升級」到 `V_m(x) = β_m + θ_mᵀ F(x)`，
理由是雙模式 Farkas 憑證滿足 mode-flow balance：

$$\sum_i \lambda_i\,(e_{m(y_i)} - e_{m(x_i)}) = 0$$

但 Lean 裡三條主定理過去仍是純線性的 `dot θ (F x)`（本項已補齊）。

**做法。** 以 2-mode 為例，敘述改成

```lean
theorem no_go_2mode_affine_potential :
    ¬ ∃ (β₀ β₁ : ℚ) (θ₀ θ₁ : Fin 18 → ℚ),
      (∀ i, 0 ≤ θ₀ i) ∧ (∀ i, 0 ≤ θ₁ i) ∧
      ∀ x ∈ W12,
        (if (F (Todd x)).getD 5 0 = 1 then β₁ + dot θ₁ (F (Todd x))
                                       else β₀ + dot θ₀ (F (Todd x)))
      - (if (F x).getD 5 0 = 1 then β₁ + dot θ₁ (F x) else β₀ + dot θ₀ (F x)) < 0
```

注意 `β₀ β₁` **不受非負限制**（截距本來就可正可負），這才是真正的一般化。

證明骨架與現版完全相同：同一組 `λ`、同一批 `Todd_*` / `hm_*` 引理、同樣 `rw [if_pos/if_neg]`。
唯一的差別在最後那條 `key : ... = 31 * θ 6` 的組合恆等式——現在左邊會多出
`c₀ * β₀ + c₁ * β₁`，而 mode-flow balance 恰好說 `c₀ = c₁ = 0`。

**驗收點：** 如果憑證真的滿足 mode-flow balance，收尾的 `ring` 應該**原封不動**就過。
若 `ring` 失敗，代表 balance 不成立，那就是 HandOver 的宣稱有誤——這時候**回報，不要硬湊**。
先用 `#eval` 把 `Σλᵢ(e_{m(yᵢ)} − e_{m(xᵢ)})` 算出來確認是零向量，再開始形式化。

Level 3 同理，模式判準是 `(F3 x).getD 33 0 = 1`。

---

## A-3 維度精確化 ★★★ 大（真正的數學工作）

HandOver 主張兩件事，目前都只活在註解與 `#eval` 裡，還不是定理：

1. **Level 2 差分空間 = 精確的 10 維有理線性子空間**，且 `span(ΔF) = ker B ⊕ ℚ·t`
   （9 維循環 + 1 維邊界）。
2. **Level 3 雙模式的有效差分生成空間 = 31 維**（不是 96；可達邊只有 28 條）。

**下界（≥ 10）容易：** 挑 10 個具體的 `ΔF xᵢ`，證明線性獨立。
`Matrix.rank` 或直接算一個 10×10 子式的行列式 ≠ 0，`decide` / `norm_num` 可處理。

**上界（≤ 10）才是重點：** 要對**所有**奇數 `x` 證明 8 條線性泛函在 `ΔF x` 上為零。

### 泛函對照表（2026-07-26 修訂，經精確有理秩驗算）

舊版的表是憑 `Core/Collatz_FST_Level2.lean` 檔頭推的，沒實算。實際跑過
`python3 tools/a3_functionals.py`（sympy 精確有理，非浮點）後，需要的東西比原本少：

| 泛函 | 條數 | 秩 | 對應材料 |
|---|---|---|---|
| 死狀態（座標 0、1 恆為零） | 2 | 2 | `occ2_deadState` |
| Kirchhoff 流守恆（可用形式） | 7 | 6 | `Flow.kirchhoff_occ2` |
| **合計** | | **8** | ＝ 18 − dim span(ΔF) = 18 − 10 ⇒ **完備** |

也就是說舊表另列的 `boundary_step_unique`（`e₃+e₆=1`）與 K 區交錯計數
（`e₄=e₅+e₆`）**是被流守恆蘊含的推論，不需要另證**——兩者都落在上表的列空間內
（腳本逐條驗過）。下一輪不要再去證這兩條。

**流守恆為何是「7 條、秩 6」而非 8 條。** 每個可達狀態一條共 8 條，但

1. 8 條之和恆為零（每步恰出一次、入一次），故至多 7 條獨立；
2. 終末狀態恆落在 `(0,S,0)` / `(0,S,1)` 兩者之一（非唯一！）。這兩條的端點指示
   在 `ΔF` 上不個別對消，**必須相加合併**成一條（合併後指示恆為 1 而對消）。

6 條乾淨 + 1 條合併 = 7 條，秩 6。

### 進度

把「各狀態出入次數差 = 初/末指示」寫成對 `microTrace2` 的歸納引理，是這一項的
核心技術債，已完成（見 `ProjectA/Collatz_FST_Flow.lean`）：

- `Flow.microTrace2_flow_conservation`：入流(g) + [初始=g] = 出流(g) + [終末=g]
- `Flow.state_outflow_eq_occ2`：出流(g) = occ2 (g,0) + occ2 (g,1)
- `Flow.inflow_eq_sum_occ2`：入流(g) = Σ_{(h,b) : step2 h b = g} occ2 (h,b)（16 條轉移邊）
- `Flow.kirchhoff_occ2`：合併後的特徵層線性關係，即上表第二列

上表第二列的「7 條」也已經是 Lean 定理了（§51）。關鍵是終末狀態：

- `Flow.runCarry_extIn`：讀完 `extIn x` 後最終進位為 0（兩個哨兵零沖掉進位）
- `Flow.run2_extIn_terminal`：故終末狀態對**所有** x 恆落在 `{(0,S,0), (0,S,1)}`
  ——`S8` 已排除死狀態 `(0,K,0)`（即「K 相位進位 ∈ {1,2}」，Core 的 `Inv`/`S8_closed`），
  所以「進位 = 0」把 8 個候選砍到只剩兩個
- `Flow.kirchhoff_occ2_extIn_clean`（6 條）／`Flow.kirchhoff_occ2_extIn_merged`（1 條）：
  終末指示消去後的常數關係

**差分層也完成了**（`ProjectA/Collatz_FST_FlowDelta.lean`）：對 `x` 與 `Todd x`
各用一次 §51 的關係再相減，初始指示對消，得到 9 條純 `LP.ΔF` 座標恆等式（秩 8）
（對**所有** x，不限奇數——`Todd x` 不需要奇偶假設）：

| 來源 | 差分層恆等式（0-based 座標） |
|---|---|
| 死狀態 ×2 | `dF_zero_0`、`dF_zero_1`：`ΔF₀ = ΔF₁ = 0` |
| flow (1,K,0) | `dF_flow_1K0`：`ΔF₄ = ΔF₂ + ΔF₃` |
| flow (2,K,0) | `dF_flow_2K0`：`ΔF₃ = ΔF₄ + ΔF₅` ← 舊表的「K 區交錯 e₄ = e₅ + e₆」就是這條 |
| flow (1,S,0) | `dF_flow_1S0`：`ΔF₁₄ + ΔF₁₆ = ΔF₁₀ + ΔF₁₁` |
| flow (1,S,1) | `dF_flow_1S1`：`ΔF₇ + ΔF₉ = ΔF₁₂ + ΔF₁₃` |
| flow (2,S,0) | `dF_flow_2S0`：`ΔF₁₁ + ΔF₁₃ = ΔF₁₄ + ΔF₁₅` |
| flow (2,S,1) | `dF_flow_2S1`：`ΔF₅ + ΔF₁₅ = ΔF₁₆` |
| flow 合併終末 | `dF_flow_terminal_merged`：`ΔF₂ + ΔF₁₀ + ΔF₁₂ = ΔF₇ + ΔF₉` |

**上界也完成了**（`ProjectA/Collatz_FST_DimUpper.lean`）：

- `Flow.dFQ`：`ΔF x` 的 ℚ 座標向量；`Flow.Sol`：9 條關係切出的解空間
- `Flow.dFQ_mem_Sol`：每個 `ΔF x` 都落在 `Sol` 裡（就是那 9 條）
- `Flow.pick_injective_on_Sol`：選出 10 個自由座標
  `{2,3,6,7,8,9,10,11,15,17}` 的映射在 `Sol` 上單射（其餘 8 個座標可重建）
- **`Flow.finrank_span_dFQ_le_ten`：`dim span(ΔF) ≤ 10`**

這一半不需要新數學——9 條關係就已經蘊含它，本檔只是把它說出口。
自由座標集與 8 條重建公式由 `tools/a3_functionals.py` 對帳（CI 每次 push 跑）。

**下界也完成了**（`ProjectA/Collatz_FST_DimLower.lean`）——Level 2 的維度精確化到此收尾：

- `Flow.dFQ_231` … `dFQ_1511`：`W₁₀` 那 10 條 ΔF 的 ℚ 字面向量（由 §34 的 `LP.ΔF_xxx` 得出）
- `Flow.dFW_linearIndependent`：10 條線性獨立。判準是投影到 §58 那 10 個自由座標，
  該 10×10 矩陣的行列式 = **31** ≠ 0
- `Flow.ten_le_finrank_span_dFQ`：`10 ≤ dim span(ΔF)`
- **`Flow.finrank_span_dFQ_eq_ten`：`dim span(ΔF) = 10`** ← HandOver 第一條主張的形式化

見證集直接用現成的 `W₁₀`（`no_nonneg_linear_ranking` 那組 Farkas 見證），不必另外搜。
行列式 31 與 Farkas 憑證的 `Σλ·ΔF = 31·e₇` 同值——僅記為觀察，**未主張因果關係**；
`tools/a3_functionals.py` 有對帳。

**A-3 剩下的只有 Level 3 的 31 維。** 偵察已完成（`tools/l3_recon.py`，進 CI），
數字如下——**寫 Lean 前先看這裡，不要假設與 Level 2 同構**：

| | Level 2 | Level 3 |
|---|---|---|
| 可達狀態 / 邊 | 8 / 16 | **14 / 28** |
| 恆死座標 | 2（18 維裡） | **20**（48 維裡） |
| 終末狀態 | 2 | **2**：`(0,S,0,1)`、`(0,S,1,0)` |
| 流守恆可用 | 6 乾淨 + 1 合併 = 7 | **12 + 1 = 13** |
| `dim span` | 10（18 維） | 單模式 **16**（48 維）／雙模式 **31**（96 維） |
| 家族完備嗎 | 完備（秩 8 = 18−10） | 單模式完備（秩 32）；**雙模式秩 64，缺 1 條** |

`(0,S,0,0)` 從不出現的理由：`Nat.digits 2 x` 的最後一位是 MSB = 1，故讀完 digits
後進位恆 ∈ {1,2}；終末 `H = (c%2, (c//2)%2)`，`c=1 → (1,0)`、`c=2 → (0,1)`，
要 `(0,0)` 得 `c=0`，不可能。

**雙模式缺的那 1 條不是新數學**：最簡形式 `θ₀[16] + θ₁[33] = 0`，就是既有的
`L3.mode_bit_endpoints3`（`F3[16] + F3[33] = 1`，Level 3 出口唯一性）提升到差分層。
推導：`F3[16] = 1 − m`，故 `θ₀[16] = [m(y)=0] − [m(x)=0]`、
`θ₁[33] = [m(y)=1] − [m(x)=1]`，相加 = 1 − 1 = 0。
Lean 那條目前只 `decide` 了 40 個端點，**需要推廣成全稱版**。

另外兩點：雙模式多出 2 個**區塊相依**的死座標（`θ₀[33]`、`θ₁[16]`，恆零座標
共 42 個 > 提升的 40 個）；`θ₁[43] = θ₁[46]` 雖然成立但**已被家族蘊含**，
不是缺口（曾誤認過，腳本留了一條對照檢查）。

**維度與奇偶無關**（奇數 / 全部 x / 全部 x ≥ 1 都是 16/31），
所以 Level 3 的 Lean 敘述**不需要** `x % 2 = 1` 假設，`Flow.lean` 的
「對所有 x」寫法可以照抄。

方法本身沿用 Level 2：流守恆 → 差分層泛函 → 解空間上界 → 具體見證下界。
第一步是可達性閉包（`S8` / `S8_closed` / `run2_mem_S8` 的 Level 3 版）——
`step3` / `occ3` / `KEYS3` / `F3` 都已在 `ProjectA/Collatz_FST_L3_2Mode_Recon.lean`，
**不需要動 `Core/`**。

---

## A-4 論文化 ★★ 中

三條定理 + A-1/A-2/A-3 的結果整理成 no-go theorem 論文。
建議在 repo 開 `paper/`，用 `doc-gen4`（`lakefile.toml` 裡已備好註解掉的 require）
產生定理清單，確保論文敘述與 Lean 敘述逐字對應——這是形式化專案最容易出錯的地方。

**A-3 過程中出現一個值得寫一段的化約**（別漏掉）：本來以為「K 區交錯路徑計數
`e₄ = e₅ + e₆`」是一條獨立引理，需要引用 `Collatz_FST_Ext.alt_of_one_mod_four`
來證。實際上它**就是狀態 (2,K,0) 的 Kirchhoff 流守恆**——見
`Flow.dF_flow_2K0 : ΔF₃ = ΔF₄ + ΔF₅`。

這比「秩計算說它被蘊含所以不用證」強：後者是負面結論（不必做什麼），
前者是正面的——那條關係有名字、有出處，是同一個守恆律在某個狀態上的實例。
`boundary_step_unique`（`e₃+e₆=1`）同屬這一類。論文裡把「一堆看似獨立的計數引理
其實是單一守恆律的各個狀態」講清楚，比逐條列出來有價值。

### Farkas 憑證的整數值就是見證矩陣的子式（Cramer）

**這一段已經算完了，不是待辦。** 由 `python3 tools/certificates.py --cramer` 驗證
（精確有理，CI 每次 push 跑）。

把見證矩陣 `D`（列 = 見證、行 = 特徵座標）按組合 `S = λᵀD` 是否為零分成兩堆：
被湮滅的那堆 `Z`（`S_j = 0`）與非零的那堆。則

1. **λ 垂直於 `Z`**，且 `Z` 的秩恰為 `m − 1`（`m` = 見證數），所以 λ 在相差尺度下唯一
   ——這正是當初「解族唯一」那個觀察的來源。
2. 取 `Z` 裡 `m − 1` 個獨立列成 `B`，則 **λ = (B 的極大子式向量)/gcd**
   （Cramer 的餘因子向量）。
3. 對每個非零座標 `j`：**`S_j = ε · det[B | 第 j 列] / gcd`**，全域符號 `ε` 由任一座標
   定出後對所有座標一致。

三組憑證實測：

| 憑證 | 見證數 | `Z` 的秩 | gcd | 例 |
|---|---|---|---|---|
| Level 2 單模式 `W₁₀` | 10 | 9 | **1** | `31 = det(A_free)/1` |
| Level 2 雙模式 `W₁₂` | 12 | 11 | **1** | `36 = −det/1` |
| Level 3 雙模式 `W₂₀` | 20 | 19 | **2** | `347 = 694/2` |

單模式那組因為 `S` 只有一個非零座標（`31·e₇`）且 gcd = 1，退化成最乾淨的形式：
**`λ = adj(A_free)` 的第 2 列（row），`31 = det(A_free)`**，該列 gcd = 1 故為本原向量
——所以最小整數尺度必然就是 `|det| = 31`。這回答了「為什麼 `t = 31` 剛好解回整數」：
31 不是湊出來的，它是行列式。

**一個要避免的誤推**：`Σλ`（1024 / 7826 / 31746）**不是**上述任何行列式。
單模式那組自己就是反例——`Σλ = 1024` 而 `det = 31`。`Σλ` 只是規一化尺度，
Cramer 量是**組合的座標值**（31、36、347…）。腳本裡有一條檢查專門守這件事。

論文價值：這把兩個原本看似獨立的結果接起來——Farkas 憑證的整數權重與見證矩陣的
子式是同一件事的兩面。A-3 下界用的 `det = 31`（`Collatz_FST_DimLower.lean`）
與 A-0 憑證裡的 `31·e₇` 因此是同一個 31。

---

## 不屬於 Project A 的東西

`Recon/` 裡的循環基底拆解、LP 偵察，是**已完成的偵察成果**，不需要形式化為定理，
除非 A-3 用得上。Project B 的加權自動機路線見 `docs/HANDOVER.md`，別混進來。
