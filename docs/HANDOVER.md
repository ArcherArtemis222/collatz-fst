# [Handover Document] Collatz 有限狀態平攤勢能：模板極限定理與一般化猜想
**Document Purpose:** 供新加入之 AI 協作者快速掌握專案歷史、當前數學邊界，以及兩大專案分流之定位。
**Date:** 2026-07

## 專案全貌與戰略分流
本研究旨在探討「有限狀態自動機 (FST)」所萃取之特徵，能否為 Collatz 猜想建構嚴格單調下降之「加權平攤勢能 (Additive Ranking Potential)」。
經大量 Z3 SMT 求解與 LP 幾何分析，我們已確立既有線性模板之極限。依據外部專家審閱，本研究正式分流為兩大獨立專案：
*   **專案 A (收尾階段)：Finite-State Template No-Go Theorems**。將已確認之具體有限狀態模板矛盾，形式化為精確之不可行性定理。
*   **專案 B (啟動階段)：Weighted Automata Expressivity Limits**。放棄單純升維，改以加權自動機、差分圖循環與泵引理，證明一般化之不可行性。

---

## 專案 A：已確立之核心定理與修正規格 (The Bedrock)
本專案已對三個明確的有限狀態加權模板，給出精確整數之 Farkas 矛盾證書。以下為經外部專家鑑識並修正後之最終規格：

### 1. 核心數學修正 (Crucial Corrections)
*   **非平凡量詞 (The Trivial Trap):** 所有定理之量詞必須嚴格排除 $x=1$。因 $Todd_{odd}(1)=1$，若不排除將導致 $0 \le -1$ 之平凡矛盾。精確形式為：$\forall x \in \mathbb{N}_{odd}, x > 1 \implies V(Todd(x)) - V(x) \le -1$。
*   **仿射截距強健性 (Affine Offsets):** 原測試為純線性形式 $V_m(x) = \theta_m^T F(x)$。因我方萃取之雙模式 Farkas 證書完美滿足「模式流量平衡 (Mode-flow balance) $\sum \lambda_i (e_{m(y_i)} - e_{m(x_i)}) = 0$」，現有定理已直接升級，可擊破包含任意截距 $\beta_m$ 之仿射勢能：$V_m(x) = \beta_m + \theta_m^T F(x)$。
*   **維度精確化 (Dimensionality):** 
    *   Level 2 差分空間非單純「流形」，而是精確的 **10 維有理線性子空間 (10-dimensional rational linear subspace)**。
    *   Level 3 雙模式雖具備 48 維原始特徵 (Raw features)，但可達邊 (Reachable edges) 僅 28 條，其雙模式之有效差分生成空間 (Span) 實為 **31 維**（非 96 維）。

### 2. 三大不可行性定理 (No-Go Theorems)
1.  **Level 2 單模式 (10D Subspace):** 10 條單步軌跡 ($W_{10}$) 的加權組合構成 Farkas 證書，證明單一量尺必然崩塌。
2.  **Level 2 雙模式 (Valuation-Parity 2-Mode):** 模式精確定義為 $m(x) = \nu_2(3x+1) \bmod 2$。12 條跨模式軌跡構成 Farkas 證書 ($\sum\lambda=7826$)。
3.  **Level 3 雙模式 (Level 3 × Valuation-Parity 2-Mode):** 歷史記憶升級為 $H=(d_{i-2}, d_{i-1})$。20 條軌跡構成 Farkas 證書 ($\sum\lambda=31746$)，96 維對撞組合中有 27 個正座標，其餘為零。

---

## 專案 B：一般化加權自動機猜想 (The Horizon)
本專案將探討更深層的自動機表達力極限。不再依賴特定 Level 之特徵與求解器盲搜，而是改採圖論與正規語言理論。

### 猜想敘述 (Finite-State Additive Ranking No-Go Conjecture)
令 $\mathcal{L}_{odd>1}$ 為 LSB-first 的標準奇數二進位語言。令 $U$ 為 Collatz 加速轉換器 (Accelerated Collatz Transduction)。
對任意在 $\mathcal{L}_{odd>1}$ 上有下界之確定性加權有限狀態成本函數 (Deterministic Finite-State Additive Rational Cost Function) $V$，必然存在某個奇數 $x > 1$，使得：
$$ V(U(x)) \ge V(x) $$

*(其中 $V(w)$ 允許狀態權重、轉移權重及終態修正：$V(w) = \alpha(q_0) + \sum \omega(q_i, b_i) + \beta(q_{final})$。)*

### 專案 B 的戰略路徑
1.  **Subsequential Transducer:** 將現有 Phase K/S 邏輯封裝為正規的字串轉換器 $U$。
2.  **Difference Automaton:** 建構複合自動機 $D_A(x) = V(U(x)) - V(x)$。
3.  **Cycle Incompatibility:** 證明純增長族 $2^k-1$ 與純碎裂族 $(4^{m+1}-1)/3$ 在 $D_A$ 上的宏觀循環，必定產生無法同時滿足的拓撲不等式，進而利用泵引理 (Pumping Lemma) 導出一般性矛盾。