/-
# Project B：Weighted Automata Expressivity Limits

B0 語義層已落地：canonical odd language + 哨兵語言 DFA（OddLanguage）、
subsequential transducer 介面與 `U` 實例（Transducer）。
B1 reweighting 已收官：定義層＋三條蘊含＋吸收恆等式（B1_Reweighting）。
B1.5 structured gauge：雙暫存器＋終態選擇的 gauge 升級（B15_SelGauge）。
B3a：Level 2 單模式實例化橋＋見證集 no-go 重推——用 B 框架重推 A（B3_L2Instance）。
路線圖見 docs/ROADMAP-B.md。
-/
import Lean4RealConstruction.ProjectB.Scaffold
import Lean4RealConstruction.ProjectB.Collatz_FST_OddLanguage
import Lean4RealConstruction.ProjectB.Collatz_FST_Transducer
import Lean4RealConstruction.ProjectB.Collatz_FST_B1_Reweighting
import Lean4RealConstruction.ProjectB.Collatz_FST_B15_SelGauge
import Lean4RealConstruction.ProjectB.Collatz_FST_B3_L2Instance
