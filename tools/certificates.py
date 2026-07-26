#!/usr/bin/env python3
"""Collatz FST：Farkas 憑證的重算與交叉驗證。

這支腳本是 Lean 端三條 no-go 定理的「數據來源」。它做兩件事：

1. **交叉驗證**：用獨立實作的特徵萃取（Python）重算 ΔF，
   逐位對照 Lean `occ2` 的輸出。兩邊都錯得一模一樣的機率極低，
   所以這是對「特徵定義是否忠實」的有效檢查。
2. **重算憑證**：不看答案，用精確有理算術（sympy，無浮點）
   從見證集合解出 Farkas 對偶權重 λ，並確認它就是 Lean 裡寫死的那組整數。

    python3 tools/certificates.py            # 全部驗一遍
    python3 tools/certificates.py --level2   # 只驗 Level 2 單模式

依賴：numpy、sympy。不需要 z3（z3 是用來「搜尋」的，這裡只做重算與驗證）。
"""

from __future__ import annotations

import argparse
import sys

import numpy as np
import sympy as sp

# ────────────────────────────────────────────────────────────────────
# 動力學：Todd 映射與兩級特徵萃取
# ────────────────────────────────────────────────────────────────────

def todd(x: int) -> int:
    """T_odd(x) = (3x+1) / 2^v2(3x+1)。"""
    nx = 3 * x + 1
    while nx % 2 == 0:
        nx //= 2
    return nx


KEYS_K = [(c, 0, b) for c in (0, 1, 2) for b in (0, 1)]
KEYS_S = [(c, p, b) for c in (0, 1, 2) for p in (0, 1) for b in (0, 1)]
KEYS_L2 = KEYS_K + KEYS_S                                    # 18 維

KEYS_L3 = [(c, P, h1, h2, b)
           for c in (0, 1, 2) for P in ('K', 'S')
           for h1 in (0, 1) for h2 in (0, 1) for b in (0, 1)]  # 48 維

# 模式判準（0-based 索引，與 Lean 的 `getD` 一致）
MODE_IDX_L2 = 5    # = E^K_{(2,K,0), b=1}
MODE_IDX_L3 = 33


def _bits(x: int) -> list[int]:
    """extIn x：LSB-first 二進位 + 兩個哨兵零。"""
    return [int(b) for b in bin(x)[2:]][::-1] + [0, 0]


def F2(x: int) -> np.ndarray:
    """18 維 occupation 特徵。對應 Lean `occ2 (1, Phase.K, 0) (extIn x)`。"""
    c, P, dp = 1, 'K', 0
    cnt = {'K': {k: 0 for k in KEYS_K}, 'S': {k: 0 for k in KEYS_S}}
    for b in _bits(x):
        cnt[P][(c, dp, b)] += 1
        d, cn = (3 * b + c) % 2, (3 * b + c) // 2
        if P == 'K':
            P, dp = ('K', 0) if d == 0 else ('S', 1)
        else:
            P, dp = 'S', d
        c = cn
    return np.array([cnt['K'][k] for k in KEYS_K] + [cnt['S'][k] for k in KEYS_S], dtype=int)


def F3(x: int) -> np.ndarray:
    """48 維 Level 3 特徵（歷史記憶 H = (d_{i-2}, d_{i-1})）。"""
    c, P, H = 1, 'K', (0, 0)
    cnt = {k: 0 for k in KEYS_L3}
    for b in _bits(x):
        cnt[(c, P, H[0], H[1], b)] += 1
        d, cn = (3 * b + c) % 2, (3 * b + c) // 2
        P = ('K' if d == 0 else 'S') if P == 'K' else 'S'
        c, H = cn, (H[1], d)
    return np.array([cnt[k] for k in KEYS_L3], dtype=int)


# ────────────────────────────────────────────────────────────────────
# Lean 端的既有憑證（唯一來源：ProjectA/*.lean）
# ────────────────────────────────────────────────────────────────────

W10 = [231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511]
LAM10 = [100, 64, 119, 51, 56, 183, 164, 18, 191, 78]                    # Σ = 1024

W12 = [25, 161, 353, 391, 471, 481, 583, 663, 681, 683, 711, 779]
LAM12 = [72, 936, 864, 1107, 1502, 900, 588, 326, 648, 162, 163, 558]    # Σ = 7826

W20 = [25, 81, 59, 175, 251, 449, 473, 523, 537, 591, 623, 679,
       683, 713, 745, 783, 839, 891, 903, 971]
LAM20 = [397, 1499, 1734, 2571, 1197, 800, 1046, 2027, 1387, 2648,
         3051, 2373, 160, 1734, 1947, 428, 2005, 1846, 1850, 1046]       # Σ = 31746

# Lean `Collatz_FST_NoLinearRanking.lean` §37 的 #eval 回歸值
LEAN_DF10 = {
    231:  [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 3, 0, -1, 2, 0, 0, -1],
    323:  [0, 0, 1, 1, 2, -1, -1, -1, -2, 0, 0, 0, -2, 1, 0, 1, 0, 1],
    403:  [0, 0, 0, 1, 1, 0, 0, -1, 0, 0, -1, 1, 0, -1, 0, 0, 0, 1],
    551:  [0, 0, 0, 0, 0, 0, -1, -1, -2, 0, 1, 1, -2, 1, 1, 1, 1, 0],
    681:  [0, 0, -1, 0, -1, 1, 0, 0, -1, -4, 1, 0, -4, 0, 0, 0, 1, 7],
    877:  [0, 0, 1, -1, 0, -1, 0, 1, 2, 2, -1, -2, 3, 0, 0, -2, -3, 0],
    983:  [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, -1, 0, 1, 0, 0, 0, -3],
    1079: [0, 0, 0, 0, 0, 0, -1, 0, -1, 2, 1, -1, 1, 1, 1, -1, -1, -1],
    1305: [0, 0, -1, 0, -1, 1, 0, -1, -2, 0, 1, 0, -1, 0, -1, 1, 2, 1],
    1511: [0, 0, 0, 0, 0, 0, 0, 1, 2, -1, -1, 1, 1, -1, -1, 1, 1, -2],
}

OK, BAD = "  [OK]  ", "  [!!]  "
_failures: list[str] = []


def check(cond: bool, msg: str) -> bool:
    print((OK if cond else BAD) + msg)
    if not cond:
        _failures.append(msg)
    return cond


# ────────────────────────────────────────────────────────────────────
# 單模式（Level 2）
# ────────────────────────────────────────────────────────────────────

def run_level2() -> None:
    print("\n=== Level 2 單模式：W10 / no_nonneg_linear_ranking ===")

    dF = {x: F2(todd(x)) - F2(x) for x in W10}
    check(all((dF[x] == np.array(v)).all() for x, v in LEAN_DF10.items()),
          "Python ΔF 與 Lean #eval 逐位吻合（10/10）")

    A = np.array([dF[x] for x in W10])
    comb = np.array(LAM10) @ A
    target = np.eye(18, dtype=int)[6] * 31
    check(sum(LAM10) == 1024, f"Σλ = {sum(LAM10)}（規格：1024）")
    check((comb == target).all(), f"Σλ·ΔF = 31·e₇（1-based）：{comb.tolist()}")

    # 不看答案重解：λᵀA = t·e₆，精確有理
    lam = sp.symbols('l0:10')
    t = sp.Symbol('t')
    eqs = [sum(lam[i] * int(A[i, j]) for i in range(10)) - (t if j == 6 else 0)
           for j in range(18)]
    sol = sp.solve(eqs, list(lam) + [t], dict=True)
    check(len(sol) == 1, "解族唯一（憑證在相差正純量下唯一）")
    if sol:
        s = sol[0]
        recovered = [sp.nsimplify(s[lam[i]].subs(t, 31)) for i in range(10)]
        check([int(v) for v in recovered] == LAM10,
              f"t = 31 時解回整數 λ：{[int(v) for v in recovered]}")


# ────────────────────────────────────────────────────────────────────
# 雙模式（valuation-parity）：Level 2 與 Level 3 共用
# ────────────────────────────────────────────────────────────────────

def two_mode_delta(x: int, feat, mode_idx: int, n: int) -> np.ndarray:
    """2n 維差分：區塊 m(y) 加 F(y)，區塊 m(x) 減 F(x)。"""
    y = todd(x)
    Fx, Fy = feat(x), feat(y)
    mx, my = int(Fx[mode_idx] == 1), int(Fy[mode_idx] == 1)
    d = np.zeros(2 * n, dtype=int)
    d[my * n:(my + 1) * n] += Fy
    d[mx * n:(mx + 1) * n] -= Fx
    return d


def run_two_mode(title: str, W, LAM, feat, mode_idx: int, n: int,
                 expect_sum: int, expect_nonzero: int | None) -> None:
    print(f"\n=== {title} ===")
    D = np.array([two_mode_delta(x, feat, mode_idx, n) for x in W])
    comb = np.array(LAM) @ D

    check(sum(LAM) == expect_sum, f"Σλ = {sum(LAM)}（規格：{expect_sum}）")
    check((comb >= 0).all(), "組合向量逐分量 ≥ 0（Farkas 條件）")

    nz = [(i, int(v)) for i, v in enumerate(comb) if v != 0]
    print(f"        非零座標（{len(nz)} 個）："
          + ", ".join(f"θ{i // n}[{i % n}]={v}" for i, v in nz))
    if expect_nonzero is not None:
        check(len(nz) == expect_nonzero, f"非零座標數 = {expect_nonzero}")

    # 模式流量平衡：仿射截距 β_m 能否消掉，全看這一條
    flow = np.zeros(2, dtype=int)
    for l, x in zip(LAM, W):
        y = todd(x)
        flow[int(feat(y)[mode_idx] == 1)] += l
        flow[int(feat(x)[mode_idx] == 1)] -= l
    check((flow == 0).all(),
          f"模式流量平衡 Σλ(e_m(y) − e_m(x)) = {flow.tolist()}"
          "  ← 這決定 ROADMAP A-2 的仿射升級是否成立")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--level2", action="store_true")
    ap.add_argument("--twomode", action="store_true")
    ap.add_argument("--level3", action="store_true")
    a = ap.parse_args()
    everything = not (a.level2 or a.twomode or a.level3)

    if everything or a.level2:
        run_level2()
    if everything or a.twomode:
        run_two_mode("Level 2 雙模式：W12 / no_go_2mode_potential",
                     W12, LAM12, F2, MODE_IDX_L2, 18, 7826, 8)
    if everything or a.level3:
        run_two_mode("Level 3 雙模式：W20 / no_go_level3_2mode_potential",
                     W20, LAM20, F3, MODE_IDX_L3, 48, 31746, 27)

    print()
    if _failures:
        print(f"失敗 {len(_failures)} 項：")
        for f in _failures:
            print("   -", f)
        return 1
    print("全部通過。Lean 端寫死的憑證與此腳本重算的結果一致。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
