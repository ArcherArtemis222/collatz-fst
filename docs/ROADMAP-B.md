# Project B Roadmap：Weighted Automata Expressivity Limits

> 本文件取代 `docs/HANDOVER.md` 中的 Project B 戰略段。
> 落地紀錄（2026-08-01，Phase 0 PR-3）：原草稿標【待驗證】的終末不平衡
> 已由 `tools/b15_terminal_balance.py` 精確整數重算確認；標【浮點探測】者
> 維持標記（`tools/search/b15_lp_probe.py` 重跑，可行性結論再現），
> 精確化列為 B1.5 待辦的第一項。

---

## 0. 範圍界定（先讀，論文與所有 B 敘述都受此約束）

有限狀態勢能不是一個類，至少分三層：

- **Class A — 單累加器**：`V(w) = α(q₀) + Σᵢ ω(qᵢ, bᵢ) + β(q_f)`。
  Project B 猜想的對象，本路線圖的主戰場。
- **Class B — 多暫存器 additive regular functions**（copyless CRA 等）。
- **Class C — 更強的 register / matrix-weighted 模型**。

**Project A 定理的精確歸類（論文 model-scoping 必寫）：**

- 單模式 no-go（`LP.no_nonneg_linear_ranking` 系列）落在 **Class A**。
- 雙模式 no-go（`TwoMode.*` / `L3.*`）**不是 Class A**：
  模板 `V(x) = θ_{m(x)}ᵀF(x)` 的 K 區前綴權重依賴尚未確定的模式，
  不是任何 one-accumulator edge cost。正確歸類是
  **2-register copyless CRA + final selection**（兩累加器並跑 θ₀ᵀF、θ₁ᵀF，
  由模式辨識位在終態選一）——Class B 的最小邊緣。
- 因此即使 B 的全稱猜想成立，結論也只是「one-accumulator additive rankings
  的不可能性」，不是「有限狀態方法整體不可能」。

---

## B0：語義層

把 Core 的 Phase K/S 邏輯封裝為正規的 subsequential transducer `U`。

1. canonical LSB-first odd language 的 DFA（`w ≠ 1` 的 domain 條款）。
2. `U` 的 subsequential 性：每個 transition 輸出有界字串 + final output；
   soundness **不需要新證**——`Core/Statements.lean` 的
   `ofDigits_transduce`、`transduce_split` 就是，B0 大半是包裝。
3. `U(w)` 仍為 canonical odd word（closure）。
4. **B0-3 哨兵驗證**：`extIn x = digits ++ [0,0]` 的兩個哨兵零在
   language-product 中應落在通往接受態的**無環尾段**（product 狀態含
   DFA 位置，哨兵邊不與任何普通邊同一 product 邊）。
   若成立，B1 的 end-marker 警告自動滿足；寫成一條 lemma 或 `#guard` 級檢查。

Mathlib 有 DFA/NFA/regular 基礎，無 weighted transducer 層；
自建小而專用的 API，不要等上游。

## B1：Nonnegative Reweighting Theorem（gauge normalization）

> **定理（目標敘述）。** 對有限的 trimmed weighted product graph
> （automaton × language DFA，皆有理權重），以下等價：
> 1. 接受字的成本集合有一致下界；
> 2. 每個位於某條接受路徑上的 directed cycle 總權重非負；
> 3. 存在 `h : Q → ℚ` 使所有 **useful** transition edges 滿足
>    `w(e) + h(src e) − h(dst e) ≥ 0`。
>
> 且取 `α'(q₀) = α(q₀) − h(q₀)`、`β'(q) = β(q) + h(q)` 後 **V' ≡ V 恆等**
> （不只 drift 不變——嚴格下降、下界、任兩字差值全部原封不動）。

- 證明骨架：super-source 加零權邊 → shortest-path distance 當 `h`
  （Gallai potential / Johnson reweighting；有理 Bellman–Ford，精確算術）。
- 措辭紀律：只對 **trimmed useful graph** 的 ordinary edges 宣稱非負；
  非 co-reachable 區域明確排除（`Q_useful = {q : q₀ ⇝ q ⇝ F}`）。
- (1)⟹(2) 的關鍵：trimmed product 中每條循環都可在語言內 pump
  （可達 + 繞 k 圈 + 可出到接受態）。
- **直接紅利**：Level 2 單模式 no-go 由「θ ≥ 0」升級為「V 有下界」——
  非負假設變成 WLOG（gauge choice），不是實驗限制。
- **與 A 論文的互動**：corollary 只有在 B1 完成後才進 A 的 appendix；
  未完成前 A 維持 θ≥0 敘述 + discussion 一段。不用 forthcoming 撐主定理。

## B1.5：雙模式的 structured gauge（新增里程碑）

雙模式是 2-register 模型（§0），gauge 對兩個暫存器各作用一個 `h_m`，
校正項 `h_m(q₀) − h_m(q_f)` 依終末狀態而異 ⟹ 偏移類必須從
「每模式常數 β_m」（A-2 已證）擴大為「每 (模式, 終末) 一個 β_{m,t}」。

**資料點（2026-07-31；驗證狀態 2026-08-01）：**

1. 現有憑證的終末流量平衡 `Σλ(⟦end(y)=t⟧ − ⟦end(x)=t⟧)`：
   - Level 2（W₁₂, Σλ=7826）：**±428，不平衡**
   - Level 3（W₂₀, Σλ=31746）：**±753，不平衡**
   （已精確整數重算確認：`tools/b15_terminal_balance.py`，離線可重跑）
   ⟹ per-(mode, terminal) 偏移**不是**免費升級。
   四分量分解 `Σλ(⟦(m, end)(y) = (m, t)⟧ − ⟦(m, end)(x) = (m, t)⟧)`
   【精確整數】（`b15_terminal_balance.py` 已輸出此分解）：
   - Level 2（t 依序 `(0,S,0)`／`(0,S,1)`）：m=0：0／0；m=1：+428／−428
     ——L2 不平衡全集中於模式 1 ⟹ 雙平衡搜尋實際僅增一條有效約束；
   - Level 3（t 依序 `(0,S,0,1)`／`(0,S,1,0)`）：m=0：+80／−80；
     m=1：−833／+833。
2. LP 探測（奇數 3..3999，HiGHS）【浮點探測】：
   - 原始 LP（θ≥0 + 自由 β_{m,t} 的勢能）：兩層皆**不可行**——池上無候選勢能；
   - 雙平衡 Farkas（模式平衡 + 終末平衡同時成立的憑證）：兩層皆**可行**。
     支撐集：L2 = [3, 243, 599, 961, 1079, 1363, 1369, 1413, 1671, 1819,
     2343, 2345, 2401, 2731, 3083, 3259, 3377, 3677, 3745, 3905]（20 個）；
     L3 = [37, 487, 527, 779, 1423, 1819, 1911, 2091, 2209, 2337, 2407,
     2427, 2457, 2505, 2721, 2729, 2735, 2863, 3255, 3343, 3377, 3413,
     3639, 3641, 3825, 3913, 3937]（27 個）。
     （2026-08-01 `tools/search/b15_lp_probe.py` 重跑：兩層「不可行／可行」
     結論再現；支撐集為浮點解路徑產物，維持【浮點探測】標記。）

**待辦順序**：精確有理重推雙平衡 λ（sympy，`certificates.py` 模式）→
掛錨進 CI → Lean 憑證（同 A 的 `ring` 機器，多兩條平衡恆等式）→
structured gauge lemma（per-register `h_m`，吸收進 β_{m,t}）。
完成後三條 no-go 全數升級為 bounded-below。

## B2：固定 topology 的全語言判定

> 對固定的 deterministic cost automaton，「所有接受字成本 < 0」
> 化約為有限圖問題：trim + super-source `s→q₀`（權 α）+ super-sink
> `q_f→t`（權 β）+ **權重取負** → reachable negative-cycle 偵測 +
> 一次 `s→t` shortest path；有正循環立即失敗，無正循環時最大成本由
> elementary path 達成，嚴格負 ⟺ 該最大值 < 0（有理格點自動給一致間距）。

- 文獻：Johnson 1977（reweighting，B1 主引用）；Karp 1978（cycle mean，
  **單獨不足**——mean = 0 時仍須查 boundary path）；Mohri 2002
  （semiring shortest-distance 背景）；Almagor–Boker–Kupferman survey
  （定位為 threshold universality 的 deterministic 特例，一般 tropical
  nondeterministic 情形困難得多，我們的唯一 run 特例退化為圖判定）。
- 分工照舊：搜尋/判定引擎在 `tools/`（精確有理），Lean 只驗證書。
- `D_A(x) = V(U(x)) − V(x)`：subsequential `U` 的每步輸出區塊權重
  push-back 到輸入轉移 + final output 進 β——標準 weighted composition。

## B3：重現 Project A（abstraction 驗收測試）

用 B2 引擎重推三條 no-go。`scripts/check_boundaries.py` 本來就禁止
ProjectB 匯入 ProjectA ⟹ 這是結構上誠實的重推導。
重推不出來 = abstraction 遺失了 A 的重要結構，先修 abstraction 再前進。

## B4：受限一般結果

依序：1-state → 狀態數 ≤ n → aperiodic transition monoid →
bounded history/suffix → 特定 mode partition。每一層都是獨立可發表的界。

## B5：Contextual Word-Family Sufficiency（重述後的地平線）

不再預設「兩個宏觀族產生矛盾」。改問判準：

> 給定一類 finite-state additive cost automata 𝒞，何種參數化
> word-family 集合 𝒲 足以對每個 A ∈ 𝒞 產生有限的
> contextual cycle / conic obstruction？

充分性的三個成分：**狀態對齊**（relevant subwords 落入 transition monoid
的相同 idempotent context）、**語境封閉**（允許左右 context 與跨 block
串接）、**錐矛盾**（λ ≥ 0、Σλ·Δ ≥ 0、Σλ > 0，或 coboundary-invariant 版本）。

三層推進：s-dependent families（狀態數 ≤ s）→ aperiodic/特定 monoid 類的
統一 families → 是否存在對所有 finite monoids 充分的固定 schema。

**證據**：Level 3 第 65 條泛函 `θ₀[16] + θ₁[33]` 只有跨區塊版本成立
（同區塊版本連關係都不是）——obstruction 可以住在 block interaction 裡，
單一 block signature 看不到。兩族 `2^k − 1`、`(4^{m+1} − 1)/3`
降格為第一組候選 family；注意此證據**尚未證明**兩族經 contextual
closure 後不充分。

## 不做的事

直接升 Level 4/5；大規模隨機 LP 盲搜；未經 B4 直接攻全稱猜想；
轉向 probabilistic Collatz（改變量詞與研究目標）。
