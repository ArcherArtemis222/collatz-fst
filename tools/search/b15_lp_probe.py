#!/usr/bin/env python3
"""B1.5 資料點 2：per-(mode, terminal) 偏移勢能的 LP 探測重跑。【浮點探測】

    python3 tools/search/b15_lp_probe.py

奇數池 3..3999，scipy linprog（HiGHS 後端）。兩層各跑兩個 LP：

1. 原始 LP（候選勢能）：θ_m ≥ 0（每模式一組特徵權重）、β_{m,t} 自由
   （每 (模式, 終末) 一個截距），約束 V(Todd x) − V(x) ≤ −1 對池上全部奇數。
   ROADMAP-B B1.5 宣稱：兩層皆 infeasible。
2. 雙平衡 Farkas（上述 LP 的對偶不可行憑證）：λ ≥ 0、Σλ = 1、
   Σλ·Δ(雙模式特徵) ≥ 0 逐分量、Σλ·Δ(四個 (m,t) 指示) = 0。
   宣稱：兩層皆 feasible。

【浮點探測紀律】本腳本只承載**可行性結論**（infeasible / feasible）；
支撐集內容依 LP 解路徑而異，與 ROADMAP-B 記錄的支撐集不同屬預期。
精確化（sympy 有理重推雙平衡 λ）是 B1.5 待辦的第一項，不在本腳本。
不進 CI。依賴：numpy、scipy（見 tools/requirements.txt 的 search/ 區）。
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from b15_terminal_balance import TERM2, TERM3, run2, run3  # noqa: E402
from certificates import F2, F3, MODE_IDX_L2, MODE_IDX_L3, todd  # noqa: E402

POOL = list(range(3, 4000, 2))

ok = True


def check(cond: bool, msg: str) -> bool:
    global ok
    print(("  [OK]  " if cond else "  [!!]  ") + msg)
    ok = ok and cond
    return cond


def build(feat, mode_idx: int, run, terms: list) -> tuple[np.ndarray, np.ndarray]:
    """回傳 (Δθ, Δβ)：每列一個池元素 x。

    Δθ：2n 維雙模式特徵差（區塊 m(y) 加 F(y)、區塊 m(x) 減 F(x)）。
    Δβ：4 維 (m,t) 指示差（β_{m,t} 的係數）。
    """
    n = len(feat(3))
    ti = {t: i for i, t in enumerate(terms)}
    D, B = [], []
    for x in POOL:
        y = todd(x)
        Fx, Fy = feat(x), feat(y)
        mx, my = int(Fx[mode_idx] == 1), int(Fy[mode_idx] == 1)
        d = np.zeros(2 * n, dtype=float)
        d[my * n:(my + 1) * n] += Fy
        d[mx * n:(mx + 1) * n] -= Fx
        b = np.zeros(4, dtype=float)
        b[my * 2 + ti[run(y)]] += 1.0
        b[mx * 2 + ti[run(x)]] -= 1.0
        D.append(d)
        B.append(b)
    return np.array(D), np.array(B)


def probe(title: str, feat, mode_idx: int, run, terms: list) -> None:
    print(f"=== {title}（池 = 奇數 3..3999，共 {len(POOL)} 個）===")
    D, B = build(feat, mode_idx, run, terms)
    m, n2 = D.shape

    # 1. 原始 LP：變數 [θ (2n, ≥0) | β (4, 自由)]，D·θ + B·β ≤ −1
    res1 = linprog(c=np.zeros(n2 + 4),
                   A_ub=np.hstack([D, B]), b_ub=-np.ones(m),
                   bounds=[(0, None)] * n2 + [(None, None)] * 4,
                   method="highs")
    check(res1.status == 2, f"原始 LP（θ≥0 + 自由 β_mt）infeasible：{res1.message.strip()}")

    # 2. 雙平衡 Farkas：λ ≥ 0、Σλ = 1、λᵀD ≥ 0 逐分量、λᵀB = 0
    A_ub = -D.T                                   # −(λᵀD)ᵢ ≤ 0
    A_eq = np.vstack([B.T, np.ones((1, m))])      # λᵀB = 0、Σλ = 1
    b_eq = np.concatenate([np.zeros(4), [1.0]])
    res2 = linprog(c=np.zeros(m),
                   A_ub=A_ub, b_ub=np.zeros(n2),
                   A_eq=A_eq, b_eq=b_eq,
                   bounds=[(0, None)] * m, method="highs")
    feas = res2.status == 0
    check(feas, f"雙平衡 Farkas（模式平衡 + 終末平衡）feasible：{res2.message.strip()}")
    if feas:
        supp = [POOL[i] for i in np.nonzero(res2.x > 1e-9)[0]]
        print(f"        本次支撐集（{len(supp)} 個，浮點解路徑相依，僅供參考）：{supp}")
    print()


def main() -> int:
    probe("Level 2 雙模式 + β_{m,t}", F2, MODE_IDX_L2, run2, TERM2)
    probe("Level 3 雙模式 + β_{m,t}", F3, MODE_IDX_L3, run3, TERM3)
    print("全部通過。" if ok else "有失敗項——結論層級未再現，停下回報。")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
