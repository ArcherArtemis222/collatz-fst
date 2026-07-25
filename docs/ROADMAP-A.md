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

## A-2 仿射截距 `β_m` ★★ 中

**問題。** HandOver 宣稱定理「已直接升級」到 `V_m(x) = β_m + θ_mᵀ F(x)`，
理由是雙模式 Farkas 憑證滿足 mode-flow balance：

$$\sum_i \lambda_i\,(e_{m(y_i)} - e_{m(x_i)}) = 0$$

但 Lean 裡三條主定理仍是純線性的 `dot θ (F x)`，**升級尚未發生**。

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
好消息是 `Core/Collatz_FST_Level2.lean` 已經備好材料：

| 泛函 | 對應已證定理 |
|---|---|
| `e₁, e₂`（死狀態） | `occ2_deadState` |
| `e₃ + e₆ = 1`（邊界步唯一） | `boundary_step_unique` |
| `e₄ = e₅ + e₆` | K 區交錯路徑計數，`Collatz_FST_Ext.alt_of_one_mod_four` |
| 其餘四條（Kirchhoff 流守恆） | `run2_mem_S8` + `count2_pair` + `birth_death_conservation` |

把「各狀態出入次數差 = 初/末指示」寫成一條對 `microTrace2` 的歸納引理，
是這一項的核心技術債。建議**先只做這一條**，當成獨立 PR。

Level 3 的 31 維同理，但先要形式化「可達邊恰 28 條」（`S8_reachable` 的 Level 3 版本）。

---

## A-4 論文化 ★★ 中

三條定理 + A-1/A-2/A-3 的結果整理成 no-go theorem 論文。
建議在 repo 開 `paper/`，用 `doc-gen4`（`lakefile.toml` 裡已備好註解掉的 require）
產生定理清單，確保論文敘述與 Lean 敘述逐字對應——這是形式化專案最容易出錯的地方。

---

## 不屬於 Project A 的東西

`Recon/` 裡的循環基底拆解、LP 偵察，是**已完成的偵察成果**，不需要形式化為定理，
除非 A-3 用得上。Project B 的加權自動機路線見 `docs/HANDOVER.md`，別混進來。
