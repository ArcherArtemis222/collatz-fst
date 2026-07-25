/-
# Survey：3x+1 有限狀態進位轉換器的 Mathlib 背景工具支援

Mathlib rev c66c0c58（Lean v4.28.0-rc1）實地查證。本檔所有 `#check` 皆經編譯器驗證。

## 一句話結論

**核心載體（二進位表示、2-adic 賦值、List 操作）齊備；轉換器本體缺件，需自建。**

## A. 有的

| 用途 | 名稱 | import |
|---|---|---|
| 二進位位元串（**LSB-first**，docstring 明載） | `Nat.bits : ℕ → List Bool` | `Mathlib.Data.Nat.Bits` |
| 數字串 ↔ 數值（主力載體） | `Nat.digits` / `Nat.ofDigits` | `Mathlib.Data.Nat.Digits.Defs` |
| digits↔bits 橋 | `Nat.digits_two_eq_bits` | `Mathlib.Data.Nat.Digits.Lemmas` |
| 串接拆解（區塊重寫的骨幹） | `Nat.ofDigits_append` | 同上 |
| 補零不變 | `Nat.ofDigits_append_replicate_zero` | 同上 |
| 往返 | `Nat.ofDigits_digits` | 同上 |
| 位元值域 | `Nat.digits_lt_base` | 同上 |
| 2-adic 賦值 | `padicValNat 2` | `Mathlib.NumberTheory.Padics.PadicVal.Defs` |
| 同上（另一介面，數值上一致） | `Nat.maxPowDiv 2` | `Mathlib.Data.Nat.MaxPowDiv` |
| 區塊 / 計數 / 尾零消去 | `List.replicate`, `List.count`, `List.dropWhile` | Lean core |

## B. 沒有的（需自建或繞道）

1. **Collatz 本身**：整庫零命中（`grep -ri collatz` 無結果）。T_o、軌跡、停止時間全無。
2. **帶輸出的轉換器（Mealy/Moore/transducer）**：`Mathlib/Computability/` 只有
   `DFA`、`NFA`、`EpsilonNFA`、`MyhillNerode`、`ContextFreeGrammar` 等**接受器**
   （判定語言歸屬），沒有「邊走邊吐輸出串」的機器。`grep -ri "mealy\|transducer"` 零命中。
3. **左折帶狀態掃描 `List.mapAccumL`：core 與 Mathlib 都沒有。**
   現存只有：
   * `List.mapAccumr`（`Mathlib.Data.List.Defs`）——**方向相反**，先遞迴到串尾再回頭，
     對 LSB-first 串等於 MSB→LSB，與本題的進位傳播方向不符；
   * `List.mapAccumLM` / `mapAccumRM`（`Mathlib.Control.Basic`）——monadic 版，殺雞用牛刀。

   → **結論：`run` 用結構遞迴自定義**（見 Statements 檔），語意最直白也最好證。

## C. 方向約定（極易踩雷，特此標明）

本題規格為 **LSB → MSB**，`Nat.bits` / `Nat.digits` 同為 LSB-first（head = 最低位），
兩者一致，不需反轉。但 `List.mapAccumr` 是 MSB→LSB，若誤用會得到錯誤的進位鏈。
-/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Bits
import Mathlib.Data.List.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.MaxPowDiv

namespace CollatzFSTSurvey

/-! ## 二進位載體 -/

#check @Nat.bits              -- ℕ → List Bool，LSB-first
#check @Nat.digits            -- ℕ → ℕ → List ℕ
#check @Nat.ofDigits          -- [Semiring α] → α → List ℕ → α
#check @Nat.digits_two_eq_bits
#check @Nat.ofDigits_digits
#check @Nat.digits_lt_base
#check @Nat.digits_len

/-! ## 區塊重寫要用的串接引理 -/

#check @Nat.ofDigits_append
#check @Nat.ofDigits_append_replicate_zero
#check @Nat.ofDigits_cons

/-! ## 2-adic（Theorem 2 的尾零消去） -/

#check @padicValNat
#check @Nat.maxPowDiv

/-! ## List 基礎（區塊、計數、尾零） -/

#check @List.replicate
#check @List.count
#check @List.dropWhile

/-! ## 缺件示範：只有 mapAccumr（方向相反），無 mapAccumL -/

#check @List.mapAccumr

end CollatzFSTSurvey
