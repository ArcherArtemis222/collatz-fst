/-
# Project B：Weighted Automata Expressivity Limits

B0 語義層已落地：canonical odd language + 哨兵語言 DFA（OddLanguage）、
subsequential transducer 介面與 `U` 實例（Transducer）。
B1 reweighting 已收官：定義層＋三條蘊含＋吸收恆等式（B1_Reweighting）。
B1.5 structured gauge：雙暫存器＋終態選擇的 gauge 升級（B15_SelGauge）。
B3a：Level 2 單模式實例化橋＋見證集 no-go 重推——用 B 框架重推 A（B3_L2Instance）。
B3c：B2 驗證書 P1–P5 的泛型層與健全性（B2_PassCert）；無符號對立對定理——
L2 單模式任意符號線性 ranking 的 2 見證 no-go（B3_OpposingPair）。
R-B：B 側雙模式 Sel 實例化——B1.5 `SelCostAutomaton` 於模式追蹤乘積 × 旗標上的 L2 實例、
旗標接地、成本橋、三層定理（軌道恆等／無符號 2 見證／BoundedBelow 形）（B3_SelInstance）。
R-B-L3：B 側 L3 語義層（L2 核心 × 歷史暫存器、可達閉包、終態定理、48 維座標、雙門）（B3_L3Machine）與
L3 雙模式 Sel 實例（成本橋、三層定理、跨層恆等）（B3_L3SelInstance）——B3 三條重推至此全數收口。
路線圖見 docs/ROADMAP-B.md。
-/
import Lean4RealConstruction.ProjectB.Scaffold
import Lean4RealConstruction.ProjectB.Collatz_FST_OddLanguage
import Lean4RealConstruction.ProjectB.Collatz_FST_Transducer
import Lean4RealConstruction.ProjectB.Collatz_FST_B1_Reweighting
import Lean4RealConstruction.ProjectB.Collatz_FST_B15_SelGauge
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_L2Instance
import Lean4RealConstruction.ProjectB.Collatz_FST_B2_PassCert
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_OpposingPair
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_SelInstance
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_L3Machine
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_L3SelInstance
