/-
# Core：共用轉換器核心（**凍結區**）

本區含 3x+1 有限狀態轉換器的定義與已證性質，是 Project A 與 Project B 的共同地基。
**任何改動都會使 ProjectA 的 Farkas 憑證失效**（那些 `decide` 引理算的是 `occ2` / `F` 的值），
所以 Core 只由專案主人簽核（見 .github/CODEOWNERS）。
-/
import Lean4RealConstruction.Core.Collatz_FST_Statements
import Lean4RealConstruction.Core.Collatz_FST_Ext
import Lean4RealConstruction.Core.Collatz_FST_Monoid
import Lean4RealConstruction.Core.Collatz_FST_Phase
import Lean4RealConstruction.Core.Collatz_FST_Level2
