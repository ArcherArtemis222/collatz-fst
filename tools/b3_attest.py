#!/usr/bin/env python3
"""Collatz FST：B3a 交叉認證——F_B ≡ F2∘σ、λ_B 獨立重解、B2 引擎 harness
（ROADMAP-B B3；設計核准 2026-09-04）。

Lean 端 `ProjectB/Collatz_FST_B3_L2Instance.lean` 用**零 ProjectA import** 的素材
（Core 機器＋B0 語言層＋B1 載體）重推 Level 2 單模式 no-go。`check_boundaries.py`
禁止 B 匯入 A，所以「兩個獨立重推導出同一數學」只能在 tools 層認證——本腳本是
唯一允許同時 import 兩側的橋。精確整數／有理，零浮點。它做六件事：

1. **B 側自含實作＋Lean 錨**（§A、§B）：照 Lean 定義逐字重寫 `step2`／`lstep`／
   `featIdx`／`featList`／`F_B`（B 側不 import certificates.py），與 Lean 檔 §B3.V
   電池抄來的錨（見證、Todd 值、λ_B、聚合、20 條 featList）雙向對帳。
2. **λ_B 獨立重解**（§C）：單座標憑證掃描——對 18 個座標 k 逐一嘗試湮滅其餘 17 個
   （sympy 有理 nullspace 一維、生成元可取非負、第 k 座標聚合 > 0），不看答案。
   **結果：W₁₀ 上恰三個**（B 座標 k = 2／4／17；Σλ = 1024／312／34；係數 31／31／1），
   取最輕（k = 17）為 λ_B；全部 Farkas 條件再以純整數驗證。另以 sympy 精確單純形
   確認 Farkas 多胞形非空（其頂點是第四個、非單座標的憑證，僅印出不入錨）。
   「31 = det」（tools/README、ROADMAP-A A-4）是**目標 e₆ 相依**的子式：換目標
   e₁₇ 得 det = 1（么模）。
3. **三段式認證**（§D）：(i) σ 由 key 比對建立並驗雙射，`F_B x ≡ F2 x ∘ σ` 對
   x < 4096 全體（含 x = 0、1 邊界）；(ii) A 的 `LAM10` 經 σ **恰等於**掃描的
   k = σ⁻¹(6) 成員（A 的 31·e₆ ↔ B 的 31·e₂）；(iii) Lean 的 `lamB` 恰等於掃描的
   最輕成員（k = 17）。
4. **B2 引擎 harness**（§E，NOTES Q4 的誠實用法）：`L2auto θ` 在字母表
   `{some 0, some 1, none}` 上的可達乘積態截斷餵 `b2_engine`（`none ↦ 2`），四組 θ
   覆蓋 pass／fail-循環／fail-邊界，引擎判定與直接求值逐項交叉。引擎不重推 no-go
   （∃θ 量詞是 B3b 差分自動機的事），這裡只測「B3 實例化 ↔ B2 輸入格式」相容。
5. **B3b 差分自動機（§G，2026-09-04 起）**：呼叫 `tools/b3b_diff.py` 的 CI 段
   `run_checks`——差分自動機 `D(θ)` 構造與手算錨、成本橋（向量形 x < 8192 ＋ b2_engine
   求值器通道）、trim 圖枚舉規模、θ-LP 不可行的整數圖憑證三種（LP 導出／對立對 (25, 315)
   三件套／B3a 提升）、負向測試、引擎對 θ ≥ 0 樣本全語言 fail 的 harness。
   NOTES Q5：CI 維持 attest 一步，`.github` 零變更。
6. **B3c Lean↔tools 字面同步（§H，2026-09-04 起）**：`ProjectB/Collatz_FST_B2_PassCert.lean`
   （驗證書 T3 `MposNeg` 四欄＋憑證 (R, C, d)、T1 見證）與 `Collatz_FST_B3_OpposingPair.lean`
   （對立對 (25, 315)：Todd 值、四條 featList、ΔF_B(25) 向量）的電池字面，逐項對 `b2_engine`
   實跑輸出（T1／T3 verdict、`verify_pass_cert`）、B 側重算、`b3b_diff.EXPECT_PAIR`、
   A 側 F2 通道對帳；負向測試三則。
負向測試（§F）常駐：竄改 featList 錨、λ、σ、聚合各一則必紅。

    python3 tools/b3_attest.py            # 全部（CI）

依賴：numpy、sympy（既有）；import `tools/certificates.py`（A 側）、`tools/b2_engine.py`、
`tools/b3b_diff.py`（B3b，純標準庫）。
"""

from __future__ import annotations

import sys
import time
from collections import deque
from fractions import Fraction
from functools import reduce
from math import gcd
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parent))

OK, BAD = "  [OK]  ", "  [!!]  "
_failures: list[str] = []


def check(cond: bool, msg: str) -> bool:
    print((OK if cond else BAD) + msg)
    if not cond:
        _failures.append(msg)
    return cond


# ────────────────────────────────────────────────────────────────────
# §A B 側自含實作（照 Lean 定義逐字；不 import certificates.py）
# ────────────────────────────────────────────────────────────────────

def out_bit(c: int, b: int) -> int:
    """Core `outBit`。"""
    return (3 * b + c) % 2


def next_carry(c: int, b: int) -> int:
    """Core `nextCarry`。"""
    return (3 * b + c) // 2


def step2(s: tuple, b: int) -> tuple:
    """Core `step2`：(c, P, dPrev) 讀位元 b。"""
    c, P, _p = s
    d, c2 = out_bit(c, b), next_carry(c, b)
    if P == 'K':
        return (c2, 'K', 0) if d == 0 else (c2, 'S', 1)
    return (c2, 'S', d)


def lstep(s: str, a) -> str:
    """B0 `lstep`：字母 None = 哨兵 `none`、int = `some b`。"""
    if s == 'start' and a == 1:
        return 'acc'
    if s == 'acc' and a == 1:
        return 'acc'
    if s == 'acc' and a == 0:
        return 'mid'
    if s == 'acc' and a is None:
        return 'tail1'
    if s == 'mid' and a == 1:
        return 'acc'
    if s == 'mid' and a == 0:
        return 'mid'
    if s == 'tail1' and a is None:
        return 'tail2'
    return 'dead'


def unmark(a) -> int:
    """B0 `unmark`：`none ↦ 0`。"""
    return 0 if a is None else a


def digits(x: int) -> list[int]:
    """`Nat.digits 2`（LSB-first；`digits 0 = []`——`bin(0)[2:]` 教訓）。"""
    d = []
    while x:
        d.append(x % 2)
        x //= 2
    return d


def ext_in_m(x: int) -> list:
    """B0 `extInM x = (digits x).map some ++ [none, none]`。"""
    return digits(x) + [None, None]


def ext_in(x: int) -> list[int]:
    """Core `extIn x`（= `extInM x` 去標記）。"""
    return [unmark(a) for a in ext_in_m(x)]


def feat_idx(s: tuple, b: int) -> int:
    """Lean `featIdx`：(c, P, p) 與 b 的字典序，K 列 p 摺疊。"""
    c, P, p = s
    if P == 'K':
        return (6 * c + b) % 18
    return (6 * c + 2 + 2 * p + b) % 18


INIT2 = (1, 'K', 0)


def feat_list(x: int) -> list[int]:
    """Lean `featList x`：走行 (1,K,0) ⊢ extIn x 逐步 featIdx。"""
    s, out = INIT2, []
    for b in ext_in(x):
        out.append(feat_idx(s, b))
        s = step2(s, b)
    return out


def F_B(x: int) -> list[int]:
    """Lean `F_B x`：18 維計數。"""
    v = [0] * 18
    for i in feat_list(x):
        v[i] += 1
    return v


def prod_run(x: int):
    """乘積走行（機器 × extDFA）：回傳 (trace, 終態)。"""
    s, t, tr = INIT2, 'start', []
    for a in ext_in_m(x):
        tr.append((s, t, a, feat_idx(s, unmark(a))))
        s, t = step2(s, unmark(a)), lstep(t, a)
    return tr, (s, t)


def todd_via_U(x: int) -> int:
    """Todd 經 B0 的 U：`run 1 (digits x)` ++ finalOut（進位二進位）→ dropWhile 0 → ofDigits。"""
    c, out = 1, []
    for b in digits(x):
        out.append(out_bit(c, b))
        c = next_carry(c, b)
    out += digits(c)
    while out and out[0] == 0:
        out.pop(0)
    return sum(d << i for i, d in enumerate(out))


def todd(x: int) -> int:
    """算術 Todd（對照用）。"""
    n = 3 * x + 1
    while n % 2 == 0:
        n //= 2
    return n


# B 座標的 key（c, p, b, P）；K 列 p 恆 0
KEYS_B = [None] * 18
for _c in (0, 1, 2):
    for _b in (0, 1):
        KEYS_B[feat_idx((_c, 'K', 0), _b)] = (_c, 0, _b, 'K')
    for _p in (0, 1):
        for _b in (0, 1):
            KEYS_B[feat_idx((_c, 'S', _p), _b)] = (_c, _p, _b, 'S')
assert all(k is not None for k in KEYS_B)


# ────────────────────────────────────────────────────────────────────
# §B Lean 錨（自 ProjectB/Collatz_FST_B3_L2Instance.lean 逐字抄錄）
# ────────────────────────────────────────────────────────────────────

LEAN_B3_W = [231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511]          # W_B
LEAN_B3_TODD = [347, 485, 605, 827, 511, 329, 1475, 1619, 979, 2267]      # tB
LEAN_B3_LAM = [3, 2, 4, 2, 2, 6, 5, 1, 6, 3]                              # lamB（Σ = 34）
LEAN_B3_AGG_COORD, LEAN_B3_AGG_COEF = 17, 1                               # agg_eq_e17
# §B3.V 電池：W_B.map featList／(W_B.map Todd).map featList
LEAN_B3_FEATLIST = {
    231: [7, 13, 17, 16, 8, 5, 11, 15, 16, 8],
    323: [7, 13, 16, 8, 4, 2, 3, 10, 5, 10, 4],
    403: [7, 13, 16, 8, 5, 10, 4, 3, 11, 14, 8],
    551: [7, 13, 17, 16, 8, 5, 10, 4, 2, 3, 10, 4],
    681: [7, 12, 6, 5, 10, 5, 10, 5, 10, 5, 10, 4],
    877: [7, 12, 7, 13, 16, 9, 15, 16, 9, 15, 16, 8],
    983: [7, 13, 17, 16, 9, 14, 9, 15, 17, 17, 16, 8],
    1079: [7, 13, 17, 16, 9, 15, 16, 8, 4, 2, 3, 10, 4],
    1305: [7, 12, 6, 5, 11, 14, 8, 4, 3, 10, 5, 10, 4],
    1511: [7, 13, 17, 16, 8, 5, 11, 15, 17, 16, 9, 14, 8],
    347: [7, 13, 16, 9, 15, 16, 9, 14, 9, 14, 8],
    485: [7, 12, 7, 12, 6, 5, 11, 15, 17, 16, 8],
    605: [7, 12, 7, 13, 17, 16, 9, 14, 8, 5, 10, 4],
    827: [7, 13, 16, 9, 15, 17, 16, 8, 5, 11, 14, 8],
    511: [7, 13, 17, 17, 17, 17, 17, 17, 17, 16, 8],
    329: [7, 12, 6, 5, 10, 4, 3, 10, 5, 10, 4],
    1475: [7, 13, 16, 8, 4, 2, 3, 11, 15, 16, 9, 14, 8],
    1619: [7, 13, 16, 8, 5, 10, 5, 10, 4, 3, 11, 14, 8],
    979: [7, 13, 16, 8, 5, 10, 5, 11, 15, 17, 16, 8],
    2267: [7, 13, 16, 9, 15, 16, 9, 15, 16, 8, 4, 3, 10, 4],
}
# 三個單座標憑證的期望（掃描門檻寫死；設計報告 §6 D5）
EXPECT_SCAN = {2: (1024, 31), 4: (312, 31), 17: (34, 1)}


def verify_featlist_anchors(anchors: dict[int, list[int]]) -> bool:
    return all(feat_list(x) == fl for x, fl in anchors.items())


def delta_rows(W: list[int]) -> list[list[int]]:
    """ΔF_B 列：F_B(Todd x) − F_B(x)。"""
    return [[F_B(todd_via_U(x))[i] - F_B(x)[i] for i in range(18)] for x in W]


def run_anchors() -> list[list[int]]:
    print("\n=== §A/§B B 側實作與 Lean 錨 ===")
    tr, fin = prod_run(3)
    check([t[3] for t in tr] == [7, 13, 16, 8] and fin == ((0, 'S', 1), 'tail2')
          and [t[1] for t in tr] == ['start', 'acc', 'acc', 'tail1'],
          "x = 3 手算對照：featList [7, 13, 16, 8]、DFA start/acc/acc/tail1 → tail2")
    check(feat_list(5) == [7, 12, 7, 12, 6], "x = 5（Todd 3）：featList [7, 12, 7, 12, 6]")
    check(all(todd_via_U(x) == todd(x) for x in range(1, 5000)),
          "Todd 經 U（B0 runOut + finalOut + dropWhile + ofDigits）= 算術 Todd，x < 5000")
    check([todd_via_U(x) for x in LEAN_B3_W] == LEAN_B3_TODD,
          f"Lean tB = Todd 經 U：{LEAN_B3_TODD}")
    check(set(LEAN_B3_FEATLIST) == set(LEAN_B3_W) | set(LEAN_B3_TODD)
          and verify_featlist_anchors(LEAN_B3_FEATLIST),
          "20 條 Lean featList 錨與 B 側重算逐位吻合")
    check(all(sum(F_B(x)) == len(ext_in(x)) and F_B(x)[0] == F_B(x)[1] == 0
              for x in range(400)),
          "守恆量：Σ F_B = |extIn|、死座標 0/1 恆零（x < 400）")
    D = delta_rows(LEAN_B3_W)
    agg = [sum(LEAN_B3_LAM[j] * D[j][i] for j in range(10)) for i in range(18)]
    e = [0] * 18
    e[LEAN_B3_AGG_COORD] = LEAN_B3_AGG_COEF
    check(agg == e and sum(LEAN_B3_LAM) == 34 and all(v > 0 for v in LEAN_B3_LAM),
          f"Lean λ_B 之聚合 = {LEAN_B3_AGG_COEF}·e{LEAN_B3_AGG_COORD}、Σλ = 34、逐項 > 0")
    return D


# ────────────────────────────────────────────────────────────────────
# §C λ_B 獨立重解：單座標憑證掃描（不看答案、零浮點）
# ────────────────────────────────────────────────────────────────────

def _primitive(v: sp.Matrix) -> list[int]:
    L = sp.lcm([sp.fraction(c)[1] for c in v])
    lam = [int(c * L) for c in v]
    if sum(lam) < 0:
        lam = [-c for c in lam]
    g = reduce(gcd, (abs(c) for c in lam))
    return [c // g for c in lam]


def scan_single_coordinate(D: list[list[int]]) -> dict[int, tuple[list[int], list[int]]]:
    """對每個座標 k：湮滅其餘座標（nullspace of D[:, ≠k]ᵀ）；一維、可取非負、
    第 k 座標聚合 > 0 者即單座標憑證。回傳 k ↦ (λ, 聚合)。"""
    Dm = sp.Matrix(D)
    found = {}
    for k in range(Dm.cols):
        Z = [i for i in range(Dm.cols) if i != k]
        ns = Dm[:, Z].T.nullspace()
        if len(ns) != 1:
            continue
        lam = _primitive(ns[0])
        agg = [sum(lam[j] * D[j][i] for j in range(len(D))) for i in range(Dm.cols)]
        if all(c >= 0 for c in lam) and agg[k] > 0:
            found[k] = (lam, agg)
    return found


def verify_certificate(D, lam, coord: int, coef: int) -> bool:
    """純整數 Farkas 條件：λ 逐項 > 0、聚合逐座標 ≥ 0 且恰為 coef·e_coord。"""
    if not all(c > 0 for c in lam):
        return False
    agg = [sum(lam[j] * D[j][i] for j in range(len(D))) for i in range(18)]
    e = [0] * 18
    e[coord] = coef
    return all(v >= 0 for v in agg) and agg == e


def run_scan(D: list[list[int]]) -> dict[int, tuple[list[int], list[int]]]:
    print("\n=== §C λ_B 獨立重解：單座標憑證掃描 ===")
    Dm = sp.Matrix(D)
    check(Dm.rank() == 10, f"rank ΔF_B = {Dm.rank()}（10 見證線性獨立）")
    found = scan_single_coordinate(D)
    summary = {k: (sum(lam), agg[k]) for k, (lam, agg) in found.items()}
    check(summary == EXPECT_SCAN,
          f"單座標憑證恰三個 {{k: (Σλ, 係數)}} = {summary}（期望 {EXPECT_SCAN}）")
    for k, (lam, _agg) in sorted(found.items()):
        Z = [i for i in range(18) if i != k]
        rk = Dm[:, Z].rank()
        check(rk == 9 and verify_certificate(D, lam, k, summary[k][1]),
              f"k = {k}（key {KEYS_B[k]}）：湮滅列秩 9、λ = {lam} 純整數驗證通過")
    lightest = min(found, key=lambda k: sum(found[k][0]))
    check(lightest == LEAN_B3_AGG_COORD and found[lightest][0] == LEAN_B3_LAM,
          f"最輕成員 k = {lightest}（Σλ = {sum(found[lightest][0])}）= Lean lamB")
    # 精確單純形：Farkas 多胞形 {λ ≥ 0, Σλ = 1, λᵀD ≥ 0} 非空（第四頂點觀察；不入錨）
    from sympy.solvers.simplex import linprog
    _val, sol = linprog(sp.zeros(1, 10), -Dm.T, sp.zeros(18, 1), sp.ones(1, 10), sp.Matrix([1]))
    lamLP = list(sol)
    aggLP = [sum(lamLP[j] * D[j][i] for j in range(10)) for i in range(18)]
    feasible = all(c >= 0 for c in lamLP) and sum(lamLP) == 1 and all(v >= 0 for v in aggLP)
    L = sp.lcm([sp.fraction(sp.nsimplify(c))[1] for c in lamLP])
    check(feasible, "精確單純形：Farkas 多胞形非空（頂點為合法憑證）")
    nz = [(i, int(v * L)) for i, v in enumerate(aggLP) if v != 0]
    print(f"        頂點 λ·{L} = {[int(c * L) for c in lamLP]}；聚合·{L} 非零座標 {nz}"
          f"（{'非' if len(nz) != 1 else ''}單座標——僅印出，不入錨）")
    return found


# ────────────────────────────────────────────────────────────────────
# §D 三段式認證（唯一允許同時 import 兩側之處）
# ────────────────────────────────────────────────────────────────────

def build_sigma(A) -> list[int]:
    """σ : B 座標 → A 座標，由 key（c, p, b, phase）比對。"""
    keysA = ([(k[0], k[1], k[2], 'K') for k in A.KEYS_K]
             + [(k[0], k[1], k[2], 'S') for k in A.KEYS_S])
    return [keysA.index(KEYS_B[i]) for i in range(18)]


def verify_sigma(A, sigma: list[int], xs) -> bool:
    if sorted(sigma) != list(range(18)):
        return False
    return all(F_B(x)[i] == int(A.F2(x)[sigma[i]]) for x in xs for i in range(18))


def run_certify(D, found) -> list[int]:
    print("\n=== §D 三段式認證（F_B ≡ F2∘σ、A 的 λ ∈ 掃描、Lean 用最輕）===")
    import certificates as A
    sigma = build_sigma(A)
    print(f"        σ (B → A) = {sigma}")
    check(sorted(sigma) == list(range(18)) and sigma != list(range(18)),
          "(i) σ 為雙射且非恆等（座標順序確實不同）")
    check(verify_sigma(A, sigma, range(4096)),
          "(i) F_B x ≡ F2 x ∘ σ，x < 4096 全體（含 x = 0、1 邊界）")
    check(list(A.W10) == LEAN_B3_W and [A.todd(x) for x in A.W10] == LEAN_B3_TODD,
          "(i) 見證集與 Todd 值兩側一致")
    DA = [[int(v) for v in (A.F2(A.todd(x)) - A.F2(x))] for x in A.W10]
    check(all(D[j][i] == DA[j][sigma[i]] for j in range(10) for i in range(18)),
          "(i) ΔF 十列在 σ 下逐位相等")
    kA = sigma.index(6)
    check(kA in found and found[kA][0] == list(A.LAM10) and found[kA][1][kA] == 31,
          f"(ii) A 的 LAM10 恰為掃描成員 k = σ⁻¹(6) = {kA}（31·e₆ ↔ 31·e{kA}）")
    check(verify_certificate(D, list(A.LAM10), kA, 31),
          "(ii) A 的 λ 以 B 側 ΔF 純整數驗證通過（A 憑證在 B 座標下成立）")
    check(sigma.index(A.MODE_IDX_L2) == 13,
          f"(ii) A 的模式位 {A.MODE_IDX_L2} = (2,K,0,1) ↔ B 座標 13")
    lightest = min(found, key=lambda k: sum(found[k][0]))
    check(found[lightest][0] == LEAN_B3_LAM and lightest == 17
          and list(A.LAM10) != LEAN_B3_LAM,
          "(iii) Lean lamB = 掃描最輕成員（k = 17，Σλ = 34）；與 A 的 λ 不同、皆合法")
    return sigma


# ────────────────────────────────────────────────────────────────────
# §E B2 引擎 harness（NOTES Q4）
# ────────────────────────────────────────────────────────────────────

LETTERS = [0, 1, None]           # some 0、some 1、none


def enc(a) -> int:
    return 2 if a is None else a


def dec(k: int):
    return None if k == 2 else k


def truncate(E, theta, alpha=Fraction(0)):
    """`L2auto θ` 在字母表 {some 0, some 1, none} 上的可達乘積態截斷 → b2 `mk_automaton`。"""
    init = (INIT2, 'start')
    idx, order, dq = {init: 0}, [init], deque([init])
    while dq:
        q = dq.popleft()
        for a in LETTERS:
            t = (step2(q[0], unmark(a)), lstep(q[1], a))
            if t not in idx:
                idx[t] = len(order)
                order.append(t)
                dq.append(t)
    step = [{enc(a): idx[(step2(q[0], unmark(a)), lstep(q[1], a))] for a in LETTERS}
            for q in order]
    w = [{enc(a): Fraction(theta[feat_idx(q[0], unmark(a))]) for a in LETTERS} for q in order]
    accept = {idx[q] for q in order if q[1] == 'tail2'}
    return E.mk_automaton(len(order), (0, 1, 2), step, w, 0, accept, alpha,
                          [Fraction(0)] * len(order)), order


def cost_direct(theta, word_marked, alpha=Fraction(0)):
    """Lean `cost` 的直接求值（α + Σ θ(featIdx) + 0）；回傳 (成本, 是否 DFA 接受)。"""
    q, t, tot = INIT2, 'start', Fraction(0)
    for a in word_marked:
        tot += Fraction(theta[feat_idx(q, unmark(a))])
        q, t = step2(q, unmark(a)), lstep(t, a)
    return alpha + tot, t == 'tail2'


def harness_case(E, name, theta, expect_kind, expect_mode, alpha=Fraction(0)) -> None:
    M, order = truncate(E, theta, alpha)
    v = E.decide_all_negative(M)
    check(v.kind == expect_kind and v.info.get("mode") == expect_mode,
          f"{name}：判定 {v.kind}/{v.info.get('mode')}（期望 {expect_kind}/{expect_mode}）")
    samples = list(range(3, 2000, 2))
    if v.kind == "fail":
        word = [dec(k) for k in v.witness.word]
        c, acc = cost_direct(theta, word, alpha)
        x = sum(unmark(a) << i for i, a in enumerate(word[:-2]))
        check(acc and word == ext_in_m(x) and c >= 0 and c == E._cost(M, v.witness.word),
              f"{name}：見證 = extInM({x})、DFA 接受、直接成本 {c} = 引擎成本 ≥ 0")
    else:
        ok, why = E.verify_pass_cert(M, v.cert)
        bad = [x for x in samples if cost_direct(theta, ext_in_m(x), alpha)[0] >= 0]
        check(ok and not bad, f"{name}：憑證 {why}；樣本奇數 x < 2000 成本全 < 0")
    check(all(cost_direct(theta, ext_in_m(x), alpha)[0]
              == E._cost(M, [enc(a) for a in ext_in_m(x)]) for x in samples[:300]),
          f"{name}：300 個樣本字引擎成本 = 直接求值")
    return M, order


def run_harness() -> None:
    print("\n=== §E B2 引擎 harness（L2auto θ 有限截斷 ↔ b2_engine）===")
    import b2_engine as E
    M, order = truncate(E, [1] * 18)
    acc_states = sorted(q for q in order if q[1] == 'tail2')
    check(M.n_states == 22 and acc_states == [((0, 'S', 0), 'tail2'), ((0, 'S', 1), 'tail2')],
          f"截斷：可達乘積態 {M.n_states}、接受態 {acc_states}（引擎 trim 重現終末態對）")
    harness_case(E, "θ ≡ 1", [1] * 18, "fail", "cycle")
    harness_case(E, "θ ≡ −1", [-1] * 18, "pass", "boundary")
    thetaK = [1 if (i % 6) < 2 else -1 for i in range(18)]
    harness_case(E, "θ = +1 於 K 座標／−1 於 S 座標", thetaK, "fail", "cycle")
    harness_case(E, "θ ≡ −1、α = 5", [-1] * 18, "fail", "boundary", alpha=Fraction(5))


# ────────────────────────────────────────────────────────────────────
# §F 負向測試（錨不是空的：改一筆必紅）
# ────────────────────────────────────────────────────────────────────

def run_negative(D, sigma) -> None:
    print("\n=== §F 負向測試（竄改必紅）===")
    import certificates as A
    tam = {k: list(v) for k, v in LEAN_B3_FEATLIST.items()}
    tam[231][2] = 16
    check(not verify_featlist_anchors(tam), "竄改 featList 錨一位（231 第 3 步 17→16）⟹ 紅")
    lam = list(LEAN_B3_LAM)
    lam[0] += 1
    check(not verify_certificate(D, lam, LEAN_B3_AGG_COORD, LEAN_B3_AGG_COEF),
          "竄改 λ_B 一項（λ₀ 3→4）⟹ 聚合驗證紅")
    check(not verify_certificate(D, LEAN_B3_LAM, 16, LEAN_B3_AGG_COEF),
          "竄改聚合座標（17→16）⟹ 紅")
    sig = list(sigma)
    sig[2], sig[3] = sig[3], sig[2]
    check(not verify_sigma(A, sig, range(64)), "σ 交換兩座標 ⟹ F_B ≡ F2∘σ 對帳紅")


# ────────────────────────────────────────────────────────────────────
# §G B3b 差分自動機 D(θ)、θ-LP 圖憑證、引擎全語言 harness（tools/b3b_diff.py 的 CI 段）
# ────────────────────────────────────────────────────────────────────

def run_diff() -> None:
    print("\n=== §G B3b 差分自動機 D(θ)：成本橋、θ-LP 圖憑證、引擎全語言 harness ===")
    import b3b_diff
    b3b_diff.run_checks(check)
# ────────────────────────────────────────────────────────────────────
# §H B3c Lean↔tools 字面同步對帳（`ProjectB/Collatz_FST_B2_PassCert.lean` §B2.V 與
#     `ProjectB/Collatz_FST_B3_OpposingPair.lean` §B3c.V 的電池字面 vs b2_engine 實跑／B 側重算）
# ────────────────────────────────────────────────────────────────────

# Lean 字面（自兩檔電池逐字抄錄；Lean 端以 #eval 比對同一字面，兩邊漂移 CI 即紅）
LEAN_B3C_T3 = {                                   # `MposNeg`／`certMposNeg`（電池 14–19）
    "step": [[1, 2], [0, 2], [2, 2]],
    "w": [[2, 0], [-3, 1], [0, 0]],
    "alpha": -5, "beta": [0, 0, -7], "accept": [2],
    "R": [0, 1, 2], "C": [0, 1, 2], "d": [-5, -3, -2],
}
LEAN_B3C_T3_MSTAR = -9                            # d + β 於接受態 2
LEAN_B3C_T1 = {"witness": [0, 1], "cost": 0}      # `Mneg_witness`（電池 20）
LEAN_B3C_PAIR = (25, 315)                         # `no_signed_ranking_pair`
LEAN_B3C_PAIR_TODD = (19, 473)                    # `Todd_25`／`Todd_315`
LEAN_B3C_DF25 = [0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 1, -1, -1, 1, -1, 0, 1, 0]   # `ΔF_B_25_eq`
LEAN_B3C_FEATLIST = {                             # 電池 2–5
    25: [7, 12, 6, 5, 11, 14, 8],
    19: [7, 13, 16, 8, 5, 10, 4],
    315: [7, 13, 16, 9, 15, 17, 16, 8, 5, 10, 4],
    473: [7, 12, 6, 5, 11, 14, 9, 15, 17, 16, 8],
}
LEAN_B3C_NEG_COORD = 4                            # `single_witness_insufficient` 的 θ = −e₄
LEAN_B3C_BLOCK = [9, 15, 17, 16]                  # 機制觀察（設計報告 §4.2）：插進兩走行的同一閉走行


def _lean_cert_T3(E):
    return E.PassCert(frozenset(LEAN_B3C_T3["R"]), frozenset(LEAN_B3C_T3["C"]),
                      {q: Fraction(v) for q, v in enumerate(LEAN_B3C_T3["d"])})


def run_b3c() -> None:
    print("\n=== §H B3c Lean↔tools 字面同步（驗證書 T3／T1、對立對 (25, 315)）===")
    import b2_engine as E
    import b3b_diff
    import certificates as A
    toys = E.from_b1_toy()
    # ── 驗證書 T3（pass）──
    M3, lit = toys["Mpos_neg"], LEAN_B3C_T3
    check(all(M3.step[q][a] == lit["step"][q][a] and M3.w[q][a] == lit["w"][q][a]
              for q in range(3) for a in range(2))
          and M3.alpha == lit["alpha"] and list(M3.beta) == lit["beta"]
          and sorted(M3.accept) == lit["accept"],
          "T3：Lean `MposNeg` 四欄（step／w／α／β）與 accept ≡ b2_engine `Mpos_neg`")
    v3 = E.decide_all_negative(M3)
    cert = _lean_cert_T3(E)
    check(v3.kind == "pass" and v3.cert.R == cert.R and v3.cert.C == cert.C
          and v3.cert.d == cert.d and v3.info["Mstar"] == LEAN_B3C_T3_MSTAR,
          f"T3：引擎 pass 憑證 (R, C, d) ≡ Lean `certMposNeg`、M* = {LEAN_B3C_T3_MSTAR}")
    ok, why = E.verify_pass_cert(M3, cert)
    check(ok, f"T3：Lean 字面憑證過 verify_pass_cert（{why}）——Lean 端 `MposNeg_passOK` 同判")
    d = dict(cert.d)
    ok4, why4 = E.verify_pass_cert(M3, E.PassCert(cert.R, cert.C, {**d, 2: d[2] + 10}))
    ok3, why3 = E.verify_pass_cert(M3, E.PassCert(cert.R, cert.C, {**d, 1: d[1] - 10}))
    check(not ok4 and why4.startswith("P4") and not ok3 and why3.startswith("P3"),
          "T3 負向：d₂ += 10 ⟹ P4 紅、d₁ −= 10 ⟹ P3 紅（與 Lean 電池 21–22 同兩則）")
    # ── 驗證書 T1（fail 見證）──
    M1 = toys["Mneg"]
    v1 = E.decide_all_negative(M1)
    okw, whyw = E.verify_fail_witness(M1, E.FailWitness(tuple(LEAN_B3C_T1["witness"])))
    check(v1.kind == "fail" and list(v1.witness.word) == LEAN_B3C_T1["witness"]
          and E._cost(M1, v1.witness.word) == LEAN_B3C_T1["cost"] and okw,
          f"T1：引擎見證字 {LEAN_B3C_T1['witness']}、成本 {LEAN_B3C_T1['cost']} "
          f"≡ Lean `Mneg_witness`（{whyw}）")
    # ── 對立對 ──
    x, y = LEAN_B3C_PAIR
    check((todd_via_U(x), todd_via_U(y)) == LEAN_B3C_PAIR_TODD,
          f"對立對：Todd 經 U = {LEAN_B3C_PAIR_TODD} ≡ Lean `Todd_25`／`Todd_315`")
    check(set(LEAN_B3C_FEATLIST) == {x, y, *LEAN_B3C_PAIR_TODD}
          and verify_featlist_anchors(LEAN_B3C_FEATLIST),
          "對立對：四條 Lean featList 錨（25／19／315／473）與 B 側重算逐位吻合")
    D2 = delta_rows([x, y])
    check(D2[0] == LEAN_B3C_DF25 and D2[1] == [-v for v in LEAN_B3C_DF25]
          and all(a + b == 0 for a, b in zip(D2[0], D2[1])),
          "對立對：ΔF_B(25) ≡ Lean `ΔF_B_25_eq`、ΔF_B(315) = −ΔF_B(25)、和零（`pair_sum_zero`）")
    check(b3b_diff.EXPECT_PAIR == LEAN_B3C_PAIR,
          f"對立對：b3b_diff 錨 EXPECT_PAIR = {LEAN_B3C_PAIR}（B3b 三件套；elementary 仍為 tools 錨）")
    check(all(x_ % 2 == 1 and x_ > 1 for x_ in LEAN_B3C_PAIR),
          "對立對：兩見證奇且 > 1（`no_signed_ranking_odd` 的 a fortiori 前提）")
    check(LEAN_B3C_DF25[LEAN_B3C_NEG_COORD] == 1,
          f"負向對照座標：ΔF_B(25)[{LEAN_B3C_NEG_COORD}] = 1（θ = −e₄ ⟹ θ·ΔF_B(25) = −1 < 0）")
    check(all(int(v) == 0 for v in (A.F2(19) + A.F2(473) - A.F2(25) - A.F2(315))),
          "對立對：A 側 F2 通道和零（B3b 已驗，此處入錨）")
    fl, blk = LEAN_B3C_FEATLIST, LEAN_B3C_BLOCK
    s, seq = (1, 'S', 0), []
    for b in (1, 1, 1, 0):
        seq.append(feat_idx(s, b))
        s = step2(s, b)
    check(fl[315] == fl[19][:3] + blk + fl[19][3:] and fl[473] == fl[25][:6] + blk + fl[25][6:]
          and seq == blk and s == (1, 'S', 0),
          f"機制觀察：featList 315／473 = featList 19／25 插入同一區塊 {blk}"
          "（Core 機器在 (1,S,0) 讀 1,1,1,0 的閉走行；設計報告 §4.2，不入定理）")
    # ── 負向 ──
    tam = {k: list(v) for k, v in LEAN_B3C_FEATLIST.items()}
    tam[25][1] = 13
    check(not verify_featlist_anchors(tam), "負向：竄改 featList 25 一位（12→13）⟹ 紅")
    bad = list(LEAN_B3C_DF25)
    bad[LEAN_B3C_NEG_COORD] = 0
    check(D2[0] != bad and any(a + b != 0 for a, b in zip(bad, D2[1])),
          "負向：竄改 ΔF_B(25) 一位 ⟹ 字面對帳紅、和零檢查紅")



def main() -> int:
    t0 = time.time()
    D = run_anchors()
    found = run_scan(D)
    sigma = run_certify(D, found)
    run_harness()
    run_negative(D, sigma)
    run_diff()
    run_b3c()
    print(f"\n耗時 {time.time() - t0:.2f} 秒。")
    if _failures:
        print(f"失敗 {len(_failures)} 項：")
        for f in _failures:
            print("   -", f)
        return 1
    print("全部通過。B 側重推、Lean 錨、λ_B 獨立重解、與 A 的三段式認證、B2 harness、"
          "B3b 差分自動機（成本橋、θ-LP 圖憑證、全語言 harness）、B3c Lean 字面同步一致。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
