#!/usr/bin/env python3
"""Level 3（31 維）的偵察數字：精確有理，決定性，進 CI。

ROADMAP A-3 的 Level 2 部分已收尾（`dim span(ΔF) = 10`）。Level 3 的目標是
HandOver 第二條主張：**雙模式有效差分生成空間 = 31 維（不是 96）**。

這支腳本在**寫任何 Lean 之前**把該有的數字釘死，並照 `certificates.py` /
`a3_functionals.py` 的模式，一開始就建 Lean 端的錨（`LEAN_*` 常數）。
不這樣做的後果我們已經吃過一次：見下面「為什麼有這支腳本」。

    python3 tools/l3_recon.py

## 為什麼有這支腳本

第一版偵察（未進 repo）算出「終末狀態 3 個、雙模式缺 5 條泛函」，兩個結論都錯。
根因是 `bin(0)[2:] == "0"`，讓 `extIn 0` 多了一個哨兵零——只有 `x = 0` 一個點，
卻同時製造出一個假的終末狀態 `(0,S,0,0)`、一個假的「奇數限制多買一維」現象
（17/32 vs 16/31），以及連帶把缺口從 1 條放大成 5 條。
`certificates.py` 的 `_bits` 有同一個 off-by-one（本 PR 一併修）。

教訓：Level 3 的定義域包含 `x = 0`，而 Level 2 的見證集全是奇數 ≥ 25，
所以這個 bug 在 Level 2 完全不咬人，一到 Level 3 就咬。

## 結論（本腳本輸出即證據）

* 可達狀態 **14**、可達邊 **28**、48 維裡恆死 **20**（合 HandOver）。
* 終末狀態 **2 個**：`(0,S,0,1)`、`(0,S,1,0)`。`(0,S,0,0)` **從不出現**——
  讀完 `Nat.digits 2 x` 後進位恆 ∈ {1,2}（MSB = 1 ⇒ 進位 = (3+c)//2 ≥ 1），
  而終末 `H = (c%2, (c//2)%2)`，`c=1 → (1,0)`、`c=2 → (0,1)`，要 `(0,0)` 得 `c=0`。
* 流守恆：**12 條乾淨 + 1 條合併 = 13 條可用**（Level 2 是 6+1=7）。
* 單模式：`dim span(ΔF3) = 16`，需 32 條；死座標 20 + 流守恆 13 = **秩 32，完備**。
* 雙模式：`dim span = 31` ✓ 合 HandOver，需 65 條。單模式家族提升到兩區塊
  + 2 條區塊相依死座標（`θ₀[33]`、`θ₁[16]`）= **秩 64，缺 1 條**。
* **缺的那 1 條不是新數學**：最簡形式 `θ₀[16] + θ₁[33] = 0`，就是既有的
  `mode_bit_endpoints3`／`F3[16] + F3[33] = 1`（Level 3 出口唯一性）
  提升到差分層。推導見 `check_missing_relation`。
* **維度與奇偶無關**：奇數 / 全部 x / 全部 x ≥ 1 都是 16/31，
  所以 Level 3 的 Lean 敘述**不需要** `x % 2 = 1` 假設，`Flow.lean` 的
  「對所有 x」寫法可以照抄。
"""

from __future__ import annotations

import sys
from functools import reduce
from math import gcd

import sympy as sp

# ────────────────────────────────────────────────────────────────────
# Level 3 狀態機（獨立實作，對照 ProjectA/Collatz_FST_L3_2Mode_Recon.lean）
# ────────────────────────────────────────────────────────────────────

INIT = (1, 'K', 0, 0)


def ext_in(x: int) -> list[int]:
    """`extIn x = Nat.digits 2 x ++ [0, 0]`；`x = 0` 給 `[0, 0]`（不是 `[0,0,0]`）。"""
    digits = [] if x == 0 else [int(t) for t in bin(x)[2:]][::-1]
    return digits + [0, 0]


def step3(s: tuple, b: int) -> tuple:
    """對照 Lean `L3.step3`：H 統一位移 H' = (H.2, d)。"""
    c, P, _h2, h1 = s
    d, cn = (3 * b + c) % 2, (3 * b + c) // 2
    return (cn, ('K' if d == 0 else 'S') if P == 'K' else 'S', h1, d)


def todd(x: int) -> int:
    n = 3 * x + 1
    while n % 2 == 0:
        n //= 2
    return n


# 48 維 KEYS3 順序（同 Lean）：index = 16c + 8·[P=S] + 4h₂ + 2h₁ + b
KEYS3 = [((c, P, h2, h1), b)
         for c in (0, 1, 2) for P in ('K', 'S')
         for h2 in (0, 1) for h1 in (0, 1) for b in (0, 1)]
IDX = {k: i for i, k in enumerate(KEYS3)}

MODE_IDX = 33          # 模式判準 m(x) = F3(x)[33]，即 ((2,K,0,0), 1)
EXIT_IDX = 16          # 出口唯一性的另一半，即 ((1,K,0,0), 0)

SCAN = 4001            # 秩計算用的掃描上界（更大範圍已離線確認同值）
SCAN_TERMINAL = 40000   # 終末狀態的掃描上界（離線另驗過 200000，同結果）

# ── Lean 端的錨（照 a3_functionals.py 的模式，一開始就建）────────────
# 這些數字一旦寫進 Lean（`ProjectA/Collatz_FST_L3*.lean`），兩邊必須對得上。
LEAN_L3_REACHABLE_COUNT = 14
LEAN_L3_EDGE_COUNT = 28
LEAN_L3_DEAD_COORDS = 20
LEAN_L3_TERMINALS = [(0, 'S', 0, 1), (0, 'S', 1, 0)]
LEAN_L3_DIM_SINGLE = 16
LEAN_L3_DIM_TWOMODE = 31
LEAN_L3_BLOCK_DEAD = ['θ0[33]', 'θ1[16]']

OK, BAD = "  [OK]  ", "  [!!]  "
_failures: list[str] = []


def check(cond: bool, msg: str) -> bool:
    print((OK if cond else BAD) + msg)
    if not cond:
        _failures.append(msg)
    return cond


def F3(x: int) -> list[int]:
    s, v = INIT, [0] * 48
    for b in ext_in(x):
        v[IDX[(s, b)]] += 1
        s = step3(s, b)
    return v


def run3(x: int) -> tuple:
    s = INIT
    for b in ext_in(x):
        s = step3(s, b)
    return s


def two_mode(x: int) -> list[int]:
    y = todd(x)
    Fx, Fy = F3(x), F3(y)
    mx, my = int(Fx[MODE_IDX] == 1), int(Fy[MODE_IDX] == 1)
    d = [0] * 96
    for i in range(48):
        d[my * 48 + i] += Fy[i]
        d[mx * 48 + i] -= Fx[i]
    return d


def reachable() -> list[tuple]:
    R, frontier = {INIT}, {INIT}
    while frontier:
        nxt = {step3(s, b) for s in frontier for b in (0, 1)} - R
        R |= nxt
        frontier = nxt
    return sorted(R, key=lambda s: (s[0], s[1], s[2], s[3]))


def flow_functional(g: tuple, R: list[tuple]) -> list[int]:
    f = [0] * 48
    for h in R:
        for b in (0, 1):
            if step3(h, b) == g:
                f[IDX[(h, b)]] += 1
    for b in (0, 1):
        f[IDX[(g, b)]] -= 1
    return f


def annihilates(D: sp.Matrix, f: list[int]) -> bool:
    return (D * sp.Matrix(f)) == sp.zeros(D.rows, 1)


def main() -> int:
    odds = list(range(3, SCAN, 2))
    R = reachable()

    print(f"\n=== ① 可達性（BFS）===")
    check(len(R) == LEAN_L3_REACHABLE_COUNT, f"可達狀態 = {len(R)}")
    check(2 * len(R) == LEAN_L3_EDGE_COUNT, f"可達邊 = {2 * len(R)}（HandOver 宣稱 28）")
    check(48 - 2 * len(R) == LEAN_L3_DEAD_COORDS, f"48 維裡恆死 = {48 - 2 * len(R)}")
    check(sum(1 for s in R if s[1] == 'K') == 2, "K 側可達狀態 = 2")

    print(f"\n=== ② 終末狀態（所有 0 ≤ x < {SCAN_TERMINAL}）===")
    terms = sorted({run3(x) for x in range(SCAN_TERMINAL)})
    check(terms == LEAN_L3_TERMINALS, f"終末狀態 = {terms}（2 個，非 3 個）")
    check((0, 'S', 0, 0) not in terms,
          "(0,S,0,0) 從不出現——讀完 digits 後進位恆 ∈ {1,2}，終末 H 拿不到 (0,0)")
    carries = {reduce(step3, ([] if x == 0 else
                              [int(t) for t in bin(x)[2:]][::-1]), INIT)[0]
               for x in range(1, 20000)}
    check(carries <= {1, 2}, f"讀完 digits 後的進位集合 = {sorted(carries)} ⊆ {{1, 2}}")

    print(f"\n=== ③ 流守恆的可用條數 ===")
    clean = [g for g in R if g not in terms]
    check(len(clean) == 12, f"乾淨（終末不可能為 g）= {len(clean)} 條")
    check(len(terms) == 2, f"須合併的終末 = {len(terms)} 條 → 合併成 1 條")
    print(f"        可用 = {len(clean)} + 1 = {len(clean) + 1} 條（Level 2 是 6+1=7）")

    print(f"\n=== ④ 維度與奇偶（奇數限制有沒有多買到一維）===")
    D1 = sp.Matrix([[F3(todd(x))[j] - F3(x)[j] for j in range(48)] for x in odds])
    D2 = sp.Matrix([two_mode(x) for x in odds])
    r1, r2 = D1.rank(), D2.rank()
    check(r1 == LEAN_L3_DIM_SINGLE, f"單模式 dim span(ΔF3) = {r1}")
    check(r2 == LEAN_L3_DIM_TWOMODE, f"雙模式 dim span = {r2}（HandOver 宣稱 31）")
    allx = list(range(0, SCAN))
    r1a = sp.Matrix([[F3(todd(x))[j] - F3(x)[j] for j in range(48)] for x in allx]).rank()
    r2a = sp.Matrix([two_mode(x) for x in allx]).rank()
    check((r1a, r2a) == (r1, r2),
          f"全部 x（含 0 與偶數）也是 {r1a}/{r2a} ⇒ **維度與奇偶無關**，"
          "Lean 敘述不需要 x % 2 = 1 假設")

    print(f"\n=== ⑤ 泛函家族的完備性 ===")
    deaths1 = [[1 if j == i else 0 for j in range(48)]
               for i, k in enumerate(KEYS3) if k[0] not in R]
    usable = ([flow_functional(g, R) for g in clean]
              + [[sum(t) for t in zip(*[flow_functional(g, R) for g in terms])]])
    check(all(annihilates(D1, f) for f in usable), "可用流守恆全部湮滅 ΔF3")
    fam1 = deaths1 + usable
    check(sp.Matrix(fam1).rank() == 48 - r1,
          f"單模式：死座標 {len(deaths1)} + 流守恆 {len(usable)} 的秩 = "
          f"{sp.Matrix(fam1).rank()}（需要 {48 - r1}）⇒ 完備")

    lift = [f + [0] * 48 for f in fam1] + [[0] * 48 + f for f in fam1]
    have = [f for f in lift if annihilates(D2, f)]
    dead2 = [j for j in range(96) if all(D2[i, j] == 0 for i in range(D2.rows))]
    lifted_dead = {j for j, k in enumerate(KEYS3) if k[0] not in R}
    extra = [j for j in dead2 if j % 48 not in lifted_dead]
    check([f"θ{j // 48}[{j % 48}]" for j in extra] == LEAN_L3_BLOCK_DEAD,
          f"額外的**區塊相依**死座標 = {[f'θ{j // 48}[{j % 48}]' for j in extra]}"
          f"（恆零座標共 {len(dead2)} 個 > 提升的 {2 * len(lifted_dead)} 個）")
    base = sp.Matrix(have + [[1 if j == d else 0 for j in range(96)] for d in extra])
    check(base.rank() == 96 - r2 - 1,
          f"雙模式：提升家族 + 區塊死座標 的秩 = {base.rank()}"
          f"（需要 {96 - r2}）⇒ 缺 1 條")

    print(f"\n=== ⑥ 缺的那 1 條 = 模式位元恆等式提升到差分層（不是新數學）===")
    check(all(F3(x)[EXIT_IDX] + F3(x)[MODE_IDX] == 1 for x in range(SCAN_TERMINAL)),
          f"F3[{EXIT_IDX}] + F3[{MODE_IDX}] = 1 對所有 0 ≤ x < {SCAN_TERMINAL}"
          "（Lean 的 mode_bit_endpoints3 只 decide 了 40 個端點，需推廣成全稱）")
    missing = [0] * 96
    missing[EXIT_IDX] = 1          # θ₀[16]
    missing[48 + MODE_IDX] = 1     # θ₁[33]
    check(annihilates(D2, missing), "θ₀[16] + θ₁[33] = 0 湮滅雙模式 Δ")
    check(sp.Matrix(base.tolist() + [missing]).rank() == 96 - r2,
          f"把它加進家族 ⇒ 秩 {sp.Matrix(base.tolist() + [missing]).rank()} = {96 - r2}，補滿")
    print("        推導：F3[16] = 1 − F3[33] = 1 − m，故")
    print("          θ₀[16] = [m(y)=0] − [m(x)=0]，θ₁[33] = [m(y)=1] − [m(x)=1]")
    print("          相加 = 1 − 1 = 0")

    # 一個已被蘊含、容易誤認為缺口的關係（留下記錄避免重複踩）
    redundant = [0] * 96
    redundant[48 + 43] = 1
    redundant[48 + 46] = -1
    check(annihilates(D2, redundant) and
          sp.Matrix(base.tolist() + [redundant]).rank() == base.rank(),
          "對照：θ₁[43] − θ₁[46] 也湮滅，但**已在家族張成中**（加進去秩不變），"
          "不是缺口")

    print()
    if _failures:
        print(f"失敗 {len(_failures)} 項：")
        for f in _failures:
            print("   -", f)
        return 1
    print("全部通過。Level 3 偵察數字與此腳本一致。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
