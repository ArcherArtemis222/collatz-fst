/-
# Audit：主定理的信任基底

本檔不含任何新數學。它的唯一工作是把「這些定理到底依賴什麼」印進 build log，
讓多方協作時任何人（含 AI）都能一眼看出信任基底有沒有被動過。

期望輸出：每條都只依賴 `propext` / `Classical.choice` / `Quot.sound`。
若出現 `sorryAx`，代表有人在依賴鏈上留了洞——CI 的 `nanoda` 步驟會直接擋下 PR。

## 想把它從「可見」升級成「強制」

先在本機跑一次 `lake build Lean4RealConstruction.Audit`，把實際輸出抄進下面的
`#guard_msgs` 註解，再取消註解。之後只要信任基底有任何變動，編譯就會失敗。
（若某條定理的公理更少，是好事，照抄即可。）
-/
import Lean4RealConstruction.Core
import Lean4RealConstruction.ProjectA

namespace Lean4RealConstruction.Audit

/-! ## Core：轉換器正確性 -/

#print axioms CollatzFST.ofDigits_transduce
#print axioms CollatzFST.transduce_split
#print axioms CollatzFST.Todd_eq_dropWhile
#print axioms CollatzFST.padicValNat_eq_altPrefixLen
#print axioms CollatzFST.boundary_step_unique
#print axioms CollatzFST.birth_death_conservation

/-! ## Project A：三大不可行性定理 -/

/-- Level 2 單模式（10 維差分子空間）。 -/
#print axioms CollatzFST.LP.no_nonneg_linear_ranking

/-- Level 2 單模式，全體奇數版。⚠ 目前量詞尚未排除 `x = 1`，見 docs/ROADMAP-A.md A-1。 -/
#print axioms CollatzFST.LP.no_global_odd_ranking

/-- Level 2 雙模式（valuation-parity），Σλ = 7826。 -/
#print axioms CollatzFST.TwoMode.no_go_2mode_potential

/-- Level 3 × valuation-parity 雙模式，Σλ = 31746。 -/
#print axioms CollatzFST.L3.no_go_level3_2mode_potential

/-! ## 強制版樣板（見檔頭說明，確認實際輸出後取消註解）

/-- info: 'CollatzFST.LP.no_nonneg_linear_ranking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CollatzFST.LP.no_nonneg_linear_ranking

-/

end Lean4RealConstruction.Audit
