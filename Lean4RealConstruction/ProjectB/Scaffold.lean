/-
# Project B 骨架

戰略路徑（見 docs/HANDOVER.md）：
1. Subsequential Transducer：把 Core 的 Phase K/S 邏輯封裝為正規字串轉換器 `U`。
2. Difference Automaton：`D_A(x) = V(U(x)) - V(x)`。
3. Cycle Incompatibility：純增長族 `2^k - 1` 與純碎裂族 `(4^(m+1) - 1)/3`
   在 `D_A` 上的宏觀循環產生互斥的拓撲不等式，再由泵引理導出一般性矛盾。

本檔目前只固定命名空間與匯入方向，讓 CI 的邊界檢查有東西可檢。
-/
import Lean4RealConstruction.Core

namespace CollatzFST.ProjectB

end CollatzFST.ProjectB
