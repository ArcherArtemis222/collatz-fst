/-
# Project B：Weighted Automata Expressivity Limits

B0 語義層已落地：canonical odd language + 哨兵語言 DFA（OddLanguage）、
subsequential transducer 介面與 `U` 實例（Transducer）。
B1 reweighting 進行中：定義層＋(1)⟹(2)＋(3)⟹(1)＋吸收恆等式（B1_Reweighting，
B1a 份；(2)⟹(3) 見 B1b）。路線圖見 docs/ROADMAP-B.md。
-/
import Lean4RealConstruction.ProjectB.Scaffold
import Lean4RealConstruction.ProjectB.Collatz_FST_OddLanguage
import Lean4RealConstruction.ProjectB.Collatz_FST_Transducer
import Lean4RealConstruction.ProjectB.Collatz_FST_B1_Reweighting
