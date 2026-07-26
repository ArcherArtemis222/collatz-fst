/-
# ProjectA 的具名 simp set 宣告

Lean 4 規定：`register_simp_attr` 宣告的屬性**不能在同一個檔案裡使用**
（Mathlib 也是為此把所有 `register_simp_attr` 集中在 `Mathlib/Tactic/Attr/Register.lean`）。
所以這個檔案只放宣告，不放任何數學。

## `coord_bridge` 是什麼、為什麼要具名

`Collatz_FST_FlowDelta.lean` §52 的 18 條座標橋（`dF_00` … `dF_17`）把
`(LP.ΔF x).getD i 0` 展開成端點 `occ2` 之差。它們原本掛在**全域** simp set 上，
後果是任何用到 `simp` / `norm_num` 的證明都可能被它們波及：目標會突然變成
18 個 `occ2` 差的算式，既不可讀也不可控——`DimUpper` 與 `DimLower` 兩個 PR
都為此繞過了 `simp`。

現在改成具名：要展開時明確寫 `simp [coord_bridge]`，不要展開時全域 simp 碰不到。
-/
import Lean

/-- 座標橋：`LP.ΔF` 的座標 ↔ 端點 `occ2` 之差（`Collatz_FST_FlowDelta.lean` §52）。
預設**不**參與全域 simp；需要展開時寫 `simp [coord_bridge]`。 -/
register_simp_attr coord_bridge
