#!/usr/bin/env python3
"""B1.5 精確化：雙平衡 Farkas 憑證的精確有理重推（推導腳本）。

    python3 tools/search/b15_exact_balance.py

從 ROADMAP-B B1.5 記錄的浮點支撐集出發，對 Level 2 / Level 3 各重推一組
**精確整數** λ，滿足（certificates.py 新錨段驗的就是同一組條件）：

    λ > 0（支撐上逐項）、Σλ·Δ(雙模式特徵) 逐分量 ≥ 0 且非零、
    Σλ·Δ⟦(m,t)⟧ = 0 —— 四條 per-(mode, terminal) 平衡。
    （四條蘊含模式平衡「對 t 求和」與終末平衡「對 m 求和」；
    反向不成立——模式＋終末平衡合計只有 3 條獨立，收不掉 4 個自由 β_{m,t}。）

流程紀律：浮點（HiGHS）只用來取「哪些聚合座標是 tight 的」這個組合資訊；
λ 本身由 sympy 有理 nullspace 精確解出，所有條件再以純整數算術驗證，
**判定不經過浮點**。支撐集以 ROADMAP-B 記錄者為起點；若精確算術下某支撐
元素的 λ 解為 0，縮支撐重解（支撐集允許與記錄不同）。若精確驗證失敗，
以非零碼結束——那是真發現，停下回報，不要改寫結論。

輸出為 tools/certificates.py 錨段常數的貼入格式。
不進 CI（CI 錨在 certificates.py 新段）。依賴：numpy、scipy、sympy。
"""
from __future__ import annotations

import sys
from functools import reduce
from math import gcd
from pathlib import Path

import numpy as np
import sympy as sp
from scipy.optimize import linprog

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from b15_terminal_balance import TERM2, TERM3, run2, run3  # noqa: E402
from certificates import F2, F3, MODE_IDX_L2, MODE_IDX_L3, todd  # noqa: E402

# ROADMAP-B B1.5 記錄的浮點支撐集（起點；獨立求解，允許不同）
SUPP_L2 = [3, 243, 599, 961, 1079, 1363, 1369, 1413, 1671, 1819,
           2343, 2345, 2401, 2731, 3083, 3259, 3377, 3677, 3745, 3905]
SUPP_L3 = [37, 487, 527, 779, 1423, 1819, 1911, 2091, 2209, 2337, 2407,
           2427, 2457, 2505, 2721, 2729, 2735, 2863, 3255, 3343, 3377,
           3413, 3639, 3641, 3825, 3913, 3937]

ok = True


def check(cond: bool, msg: str) -> bool:
    global ok
    print(("  [OK]  " if cond else "  [!!]  ") + msg)
    ok = ok and cond
    return cond


def build_rows(W: list[int], feat, mode_idx: int, run, terms: list):
    """每個見證 x 一列：D = 2n 維雙模式特徵差、B = 4 維 (m,t) 指示差。純 int。"""
    n = len(feat(3))
    ti = {t: i for i, t in enumerate(terms)}
    D, B = [], []
    for x in W:
        y = todd(x)
        Fx, Fy = feat(x), feat(y)
        mx, my = int(Fx[mode_idx] == 1), int(Fy[mode_idx] == 1)
        d = [0] * (2 * n)
        for j in range(n):
            d[my * n + j] += int(Fy[j])
            d[mx * n + j] -= int(Fx[j])
        b = [0] * 4
        b[my * 2 + ti[run(y)]] += 1
        b[mx * 2 + ti[run(x)]] -= 1
        D.append(d)
        B.append(b)
    return D, B


def float_vertex(D, B):
    """浮點 LP 只提供組合資訊：頂點解的支撐與聚合 tight 座標集合。"""
    Dn, Bn = np.array(D, float), np.array(B, float)
    k, n2 = Dn.shape
    res = linprog(c=np.zeros(k),
                  A_ub=-Dn.T, b_ub=np.zeros(n2),
                  A_eq=np.vstack([Bn.T, np.ones((1, k))]),
                  b_eq=np.concatenate([np.zeros(4), [1.0]]),
                  bounds=[(0, None)] * k, method="highs")
    if res.status != 0:
        return None, None
    with np.errstate(all="ignore"):
        comb = res.x @ Dn
    supp = [i for i in range(k) if res.x[i] > 1e-9]
    Z = [j for j in range(n2) if comb[j] < 1e-7]
    return supp, Z


def exact_lambda(W, D, B, Z) -> list[int] | None:
    """tight 座標 + 四條平衡 → sympy 有理 nullspace → 互質整數 λ。"""
    A = sp.Matrix([[D[i][j] for j in Z] + B[i] for i in range(len(W))])
    ns = A.T.nullspace()
    if len(ns) != 1:
        print(f"        nullspace 維度 = {len(ns)}（需要 1；tight 集大小 {len(Z)}）")
        return None
    v = ns[0]
    dens = [sp.fraction(c)[1] for c in v]
    v = v * sp.lcm(dens)
    lam = [int(c) for c in v]
    if sum(lam) < 0:
        lam = [-c for c in lam]
    g = reduce(gcd, (abs(c) for c in lam))
    return [c // g for c in lam]


def derive(title: str, supp: list[int], feat, mode_idx: int, run, terms: list) -> None:
    print(f"=== {title}（起點支撐集 {len(supp)} 個）===")
    W = list(supp)
    lam = None
    for _ in range(len(supp)):        # 支撐可縮：浮點頂點或精確解出 0 的元素剔除後重解
        D, B = build_rows(W, feat, mode_idx, run, terms)
        fsupp, Z = float_vertex(D, B)
        if fsupp is None:
            check(False, "浮點階段：支撐集上 LP 不可行——停下回報")
            return
        if len(fsupp) < len(W):
            print(f"        浮點頂點支撐 {len(fsupp)} 個 < 候選 {len(W)} 個，縮支撐重跑")
            W = [W[i] for i in fsupp]
            continue
        lam = exact_lambda(W, D, B, Z)
        if lam is None:
            check(False, "精確重推失敗（nullspace 非一維）——停下回報")
            return
        if all(c > 0 for c in lam):
            break
        if any(c < 0 for c in lam):
            check(False, f"λ 出現負分量 {lam}——支撐集與 tight 結構不符，停下回報")
            return
        W = [x for x, c in zip(W, lam) if c > 0]
        print(f"        精確 λ 含 0 分量，縮支撐至 {len(W)} 個重解")

    # ── 全條件純整數驗證（判定不經過浮點）──
    D, B = build_rows(W, feat, mode_idx, run, terms)
    n2 = len(D[0])
    agg = [sum(lam[i] * D[i][j] for i in range(len(W))) for j in range(n2)]
    bal = [sum(lam[i] * B[i][t] for i in range(len(W))) for t in range(4)]
    check(all(c > 0 for c in lam), f"λ 於支撐上逐項 > 0（{len(W)} 個）")
    check(all(v >= 0 for v in agg), "Σλ·Δ特徵 逐分量 ≥ 0")
    check(any(v > 0 for v in agg), "Σλ·Δ特徵 非零")
    check(all(v == 0 for v in bal), f"四條 per-(m,t) 平衡 = {bal}（需全零）")
    check(reduce(gcd, (abs(c) for c in lam)) == 1, "λ 已互質")

    n = n2 // 2
    nz = [(j, v) for j, v in enumerate(agg) if v != 0]
    print(f"        Σλ = {sum(lam)}；聚合非零座標（{len(nz)} 個）："
          + ", ".join(f"θ{j // n}[{j % n}]={v}" for j, v in nz))
    print("        —— certificates.py 貼入格式 ——")
    print(f"        W = {W}")
    print(f"        LAM = {lam}")
    print(f"        AGG = {{{', '.join(f'{j}: {v}' for j, v in nz)}}}")
    print()


def main() -> int:
    derive("Level 2 雙模式 + β_(m,t)", SUPP_L2, F2, MODE_IDX_L2, run2, TERM2)
    derive("Level 3 雙模式 + β_(m,t)", SUPP_L3, F3, MODE_IDX_L3, run3, TERM3)
    print("全部通過。" if ok else "有失敗項——精確化未完成，停下回報。")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
