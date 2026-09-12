#!/usr/bin/env python3
"""軌道回歸普查、機制觀察與 R1 邊粒度 LP（任務 (2) 設計探測的可重跑版；ROADMAP-A A-5）。

    python3 tools/search/orbit_census.py            # §1 普查 x < 2^16 ＋ §2 機制（≈ 3 s）
    python3 tools/search/orbit_census.py --lp       # 再加 §3 R1 邊粒度 LP（需 scipy；≈ 3 s）

§1 **普查（A 側通道：certificates.F2/F3、b15_terminal_balance.run2/run3）**，x 奇 < 2¹⁶：
   軌道回歸 `F(T²x) = F(x)`（Level 2 恰 21 個、Level 3 恰 2 個，最小皆 1787）；`F(Tx) = F(x)` 無；
   F-恆等對立對 `F(Tx₁) = F(x₂) ∧ F(Tx₂) = F(x₁)`（71／4 組）；雙模式對立對（`two_mode_delta` 之和為零）
   含／不含 (m,t) 終末指示皆 30／4 組（B3b D5(4) 的 30 組全部終末平衡）；「F 決定終態」零違例。
§2 **機制**（B 側 `b3_attest.feat_list`）：`featList 2011` = `featList 1787` 把機器態 (2,S,1) 錨定的
   兩個閉走行 `[17,17,17]`（三個自環）與 `[16,9,15]`（3-cycle）對調——佔用統計對同錨閉走行的置換不變。
§3 **R1 邊粒度 LP**（指令原案；設計報告 §2.3）：模式追蹤乘積 `((c,P,p), LSt, flag)`、`sel = flag`，
   在 per-mode useful 邊空間上的雙平衡 Farkas——LP1（邊聚合 ≥ 0 ＋ 四條 (m,t) 平衡）可行、LP2（邊聚合 ≡ 0，
   無符號版）亦可行、LP3（A 側 feature 層 ≡ 0 ＋ 四平衡）亦可行；精確化（支撐上以 `b3b_diff` 的精確單純形
   取頂點、純整數自驗）。W17/LAM17 在邊層有 6 個負座標（feature 層憑證不升到逐邊）。
   **覆活判準（ROADMAP-B B1.5）**：若某新模板使 LP1 可行而 LP2 不可行，gauge 路線才有非平凡消費者。

【紀律】浮點（HiGHS）只提供支撐集；λ 由精確單純形解出並以純整數驗證；本檔不進 CI
（CI 錨在 `tools/certificates.py --orbit`）。依賴：numpy、sympy（經 b3_attest）；`--lp` 另需 scipy。
"""
from __future__ import annotations

import argparse
import sys
import time
from collections import Counter, defaultdict, deque
from fractions import Fraction
from functools import reduce
from math import gcd, lcm
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import certificates as A                                  # noqa: E402
from b15_terminal_balance import TERM2, TERM3, run2, run3  # noqa: E402

ok = True


def check(cond: bool, msg: str) -> bool:
    global ok
    print(("  [OK]  " if cond else "  [!!]  ") + msg)
    ok = ok and cond
    return cond


LEVELS = {
    "L2": dict(feat=A.F2, mode=A.MODE_IDX_L2, n=18, run=run2, terms=TERM2),
    "L3": dict(feat=A.F3, mode=A.MODE_IDX_L3, n=48, run=run3, terms=TERM3),
}

# 設計報告 §2.4 的數字（錨）
EXPECT = {
    "L2": dict(ret2=21, ret2_min=[1787, 3577, 3579, 7161, 7163, 13179, 14075, 14329], ret1=0,
               fid_pairs=71, fid_min=[(1611, 2233), (1787, 2537), (1787, 2681), (2683, 3577), (3131, 4809)],
               tm_vecs=16407, tm_pairs=30, tm_min=[(1611, 2233), (1787, 2537), (2683, 3577), (3131, 4809), (3579, 5097)],
               distinct_F=6689),
    "L3": dict(ret2=2, ret2_min=[1787, 3577], ret1=0,
               fid_pairs=4, fid_min=[(1787, 2681), (2683, 3577), (14075, 19065), (19067, 28153)],
               tm_vecs=24893, tm_pairs=4, tm_min=[(1787, 2681), (2683, 3577), (14075, 19065), (19067, 28153)],
               distinct_F=14939),
}
N_CENSUS = 1 << 16


# ────────────────────────────────────────────────────────────────────
# §1 普查
# ────────────────────────────────────────────────────────────────────

def census(name: str) -> None:
    L, E = LEVELS[name], EXPECT[name]
    t0 = time.time()
    cache: dict[int, tuple] = {}

    def F(x: int) -> tuple:
        if x not in cache:
            cache[x] = tuple(int(v) for v in L["feat"](x))
        return cache[x]

    print(f"\n=== §1 {name} 普查（x 奇 < {N_CENSUS}）===")
    # F 決定終態
    seen: dict[tuple, tuple] = {}
    bad = 0
    for x in range(1, N_CENSUS, 2):
        k, t = F(x), L["run"](x)
        if k in seen and seen[k] != t:
            bad += 1
        seen.setdefault(k, t)
    check(bad == 0 and len(seen) == E["distinct_F"],
          f"F 決定終態：違例 {bad}；相異 F 向量 {len(seen)}（期望 {E['distinct_F']}）")
    # 軌道回歸
    ret2 = [x for x in range(3, N_CENSUS, 2) if F(A.todd(A.todd(x))) == F(x)]
    ret1 = [x for x in range(3, N_CENSUS, 2) if F(A.todd(x)) == F(x)]
    check(len(ret2) == E["ret2"] and ret2[:len(E["ret2_min"])] == E["ret2_min"] and len(ret1) == E["ret1"],
          f"軌道回歸 F(T²x) = F(x)：{len(ret2)} 個，最小 {ret2[:8]}；F(Tx) = F(x)：{len(ret1)} 個")
    for x in ret2[:2]:
        y = A.todd(x)
        z = A.todd(y)
        print(f"        {x} → {y} → {z}；終態 {L['run'](x)} / {L['run'](y)} / {L['run'](z)}；"
              f"m = {int(F(x)[L['mode']] == 1)} / {int(F(y)[L['mode']] == 1)}")
    # F-恆等對立對
    byF: dict[tuple, list[int]] = defaultdict(list)
    for x in range(3, N_CENSUS, 2):
        byF[F(x)].append(x)
    pairs = set()
    for x1 in range(3, N_CENSUS, 2):
        for x2 in byF.get(F(A.todd(x1)), ()):
            if x2 != x1 and F(A.todd(x2)) == F(x1):
                pairs.add(tuple(sorted((x1, x2))))
    fid = sorted(pairs, key=lambda p: (p[1], p[0]))
    check(len(fid) == E["fid_pairs"] and fid[:len(E["fid_min"])] == E["fid_min"],
          f"F-恆等對立對（F(Tx₁)=F(x₂) ∧ F(Tx₂)=F(x₁)）：{len(fid)} 組，max 最小 {fid[:5]}")
    # 雙模式對立對（含終末指示）
    def key(x: int):
        d = tuple(int(v) for v in A.two_mode_delta(x, L["feat"], L["mode"], L["n"]))
        mt = lambda z: (int(F(z)[L["mode"]] == 1), L["terms"].index(L["run"](z)))
        return d, mt(A.todd(x)), mt(x)

    def neg(k):
        d, a, b = k
        return tuple(-v for v in d), b, a
    tbl: dict = defaultdict(list)
    for x in range(3, N_CENSUS, 2):
        tbl[key(x)].append(x)
    tm = sorted({tuple(sorted((xs[0], tbl[neg(k)][0]))) for k, xs in tbl.items() if neg(k) in tbl})
    tbl2: dict = defaultdict(list)
    for k, xs in tbl.items():
        tbl2[k[0]].extend(xs)
    tm2 = sorted({tuple(sorted((min(xs), min(tbl2[tuple(-v for v in k)]))))
                  for k, xs in tbl2.items() if tuple(-v for v in k) in tbl2})
    check(len(tbl) == E["tm_vecs"] and len(tm) == E["tm_pairs"] and len(tm2) == E["tm_pairs"]
          and tm[:len(E["tm_min"])] == E["tm_min"],
          f"雙模式對立對：相異 (Δ,(m,t)) 向量 {len(tbl)}；含 (m,t) 平衡 {len(tm)} 組、不計終態 {len(tm2)} 組"
          f"（相等 ⟹ 全部終末平衡）；最小 {tm[:5]}")
    print(f"        耗時 {time.time() - t0:.1f} s")


# ────────────────────────────────────────────────────────────────────
# §2 機制（B 側 featList）
# ────────────────────────────────────────────────────────────────────

def mechanism() -> None:
    import b3_attest as B
    print("\n=== §2 機制：featList 2011 = featList 1787 的閉走行對調 ===")
    fa, fb = B.feat_list(1787), B.feat_list(2011)
    check(Counter(fa) == Counter(fb) and len(fa) == len(fb) == 13,
          f"featList 1787 = {fa}\n        featList 2011 = {fb}：同多重集、等長 13")
    i = 0
    while fa[i] == fb[i]:
        i += 1
    j = 0
    while fa[-1 - j] == fb[-1 - j]:
        j += 1
    mid_a, mid_b = fa[i:len(fa) - j], fb[i:len(fb) - j]
    check(mid_a == [17, 17, 17, 16, 9, 15] and mid_b == [16, 9, 15, 17, 17, 17] and i == 5 and j == 2,
          f"共同前綴 {fa[:i]}、共同後綴 {fa[len(fa) - j:]}；中段 {mid_a} ↔ {mid_b}（兩塊對調）")
    # 兩塊皆為 (2,S,1) 錨定的閉走行：讀 1,1,1 與 讀 0,1,1
    s0 = (2, 'S', 1)
    for bits, blk in (((1, 1, 1), [17, 17, 17]), ((0, 1, 1), [16, 9, 15])):
        s, seq = s0, []
        for b in bits:
            seq.append(B.feat_idx(s, b))
            s = B.step2(s, b)
        check(seq == blk and s == s0, f"閉走行 {bits} 自 {s0}：featIdx 序列 {seq}、回到 {s}")
    # 位元串層：2011 的 extIn 是 1787 的 extIn 把兩塊對調
    ea, eb = B.ext_in(1787), B.ext_in(2011)
    check(ea[:5] == eb[:5] and ea[5:11] == [1, 1, 1, 0, 1, 1] and eb[5:11] == [0, 1, 1, 1, 1, 1] and ea[11:] == eb[11:],
          f"extIn 1787 = {''.join(map(str, ea))}、extIn 2011 = {''.join(map(str, eb))}：位元區塊 111·011 ↔ 011·111")


# ────────────────────────────────────────────────────────────────────
# §3 R1 邊粒度 LP（模式追蹤乘積；需 scipy）
# ────────────────────────────────────────────────────────────────────

LETTERS = (0, 1, None)


def step3(s, b):
    """ProjectA `step3`：(c, P, h₂, h₁) ↦ (nextCarry, phaseStep, h₁, d)。"""
    c, P, h2, h1 = s
    d, c2 = (3 * b + c) % 2, (3 * b + c) // 2
    return (c2, ('K' if d == 0 else 'S') if P == 'K' else 'S', h1, d)


PRODUCTS = {
    "L2": dict(init=(1, 'K', 0), boundary=(2, 'K', 0), finals=[(0, 'S', 0), (0, 'S', 1)],
               step="step2", feat=A.F2, mode=A.MODE_IDX_L2, n=18,
               expect=dict(states=38, edges=114, useful=(23, 21), inter=3, lp1_supp=21, lp1_sum=2092292034,
                           lp1_nz=2, lp2_supp=22, lp3_supp=20, lp3_sum=53124, w17_neg=6)),
    "L3": dict(init=(1, 'K', 0, 0), boundary=(2, 'K', 0, 0), finals=[(0, 'S', 0, 1), (0, 'S', 1, 0)],
               step="step3", feat=A.F3, mode=A.MODE_IDX_L3, n=48,
               expect=dict(states=64, edges=192, useful=(39, 37), inter=3, lp1_supp=38, lp1_sum=14077282203,
                           lp1_nz=3, lp2_supp=40, lp3_supp=32, lp3_sum=18620824722, w17_neg=None)),
}


def edge_lp(name: str) -> None:
    import numpy as np
    from scipy.optimize import linprog
    import b3_attest as B
    from b3b_diff import feasible_point_or_farkas, verify_point
    P, E = PRODUCTS[name], PRODUCTS[name]["expect"]
    mstep = B.step2 if P["step"] == "step2" else step3
    t0 = time.time()
    print(f"\n=== §3 {name} R1 邊粒度 LP（模式追蹤乘積；池 = 奇數 3..3999）===")

    def pstep(q, a):
        s, l, f = q
        b = B.unmark(a)
        return (mstep(s, b), B.lstep(l, a), 1 if (s == P["boundary"] and b == 1) else f)
    INIT = (P["init"], 'start', 0)
    seen, order, dq, trans = {INIT}, [INIT], deque([INIT]), {}
    while dq:
        q = dq.popleft()
        for a in LETTERS:
            t = pstep(q, a)
            trans[(q, a)] = t
            if t not in seen:
                seen.add(t); order.append(t); dq.append(t)
    rev = defaultdict(list)
    for (q, a), t in trans.items():
        rev[t].append(q)
    U = {}
    for m in (0, 1):
        acc = {q for q in order if q[1] == 'tail2' and q[2] == m}
        co, dq = set(acc), deque(acc)
        while dq:
            t = dq.popleft()
            for q in rev[t]:
                if q not in co:
                    co.add(q); dq.append(q)
        U[m] = [(q, a) for (q, a), t in trans.items() if q in co and t in co]
    inter = len(set(U[0]) & set(U[1]))
    check(len(order) == E["states"] and len(trans) == E["edges"] and (len(U[0]), len(U[1])) == E["useful"] and inter == E["inter"],
          f"乘積可達態 {len(order)}、邊 {len(trans)}；useful 邊 mode 0/1 = {len(U[0])}/{len(U[1])}（交集 {inter}：起步邊＋K 泵兩邊）")
    rows = [(m, e) for m in (0, 1) for e in U[m]]
    ridx = {r: i for i, r in enumerate(rows)}
    finals = [(s, 'tail2', m) for m in (0, 1) for s in P["finals"]]
    fidx = {s: i for i, s in enumerate(finals)}
    nr = len(rows)

    def run(x):
        q, edges = INIT, []
        for a in B.ext_in_m(x):
            edges.append((q, a)); q = pstep(q, a)
        return edges, q
    pool = list(range(3, 4000, 2))
    rowvec, fdiff = {}, {}
    for x in pool:
        y = A.todd(x)
        ex, fx = run(x); ey, fy = run(y)
        v = [0] * (nr + 4)
        for e in ey:
            v[ridx[(fy[2], e)]] += 1
        for e in ex:
            v[ridx[(fx[2], e)]] -= 1
        v[nr + fidx[fy]] += 1
        v[nr + fidx[fx]] -= 1
        rowvec[x] = v
        fdiff[x] = [int(c) for c in A.two_mode_delta(x, P["feat"], P["mode"], P["n"])] + v[nr:]
    D = np.array([rowvec[x] for x in pool], dtype=float)
    Fm = np.array([fdiff[x] for x in pool], dtype=float)
    m_ = len(pool)

    def exact(vec_of, S, eq_rows, ineq_rows):
        A_, b_ = [], []
        for r in ineq_rows:
            A_.append([-vec_of(x)[r] for x in S]); b_.append(0)
        for r in eq_rows:
            A_.append([vec_of(x)[r] for x in S]); b_.append(0)
            A_.append([-vec_of(x)[r] for x in S]); b_.append(0)
        A_.append([1] * len(S)); b_.append(1)
        A_.append([-1] * len(S)); b_.append(-1)
        kind, xs = feasible_point_or_farkas(A_, b_)
        if kind != "feasible" or not verify_point(A_, b_, xs):
            return None
        Lc = reduce(lcm, [Fraction(v).denominator for v in xs], 1)
        lam = [int(Fraction(v) * Lc) for v in xs]
        g = reduce(gcd, [abs(v) for v in lam if v], 0)
        lam = [v // g for v in lam]
        return [x for x, l in zip(S, lam) if l > 0], [l for l in lam if l > 0]

    # W17/LAM17 邊層（只有 L2）
    if E["w17_neg"] is not None:
        agg = [sum(l * rowvec[x][r] for x, l in zip(A.W17, A.LAM17)) for r in range(nr)]
        neg = sorted(((rows[r], agg[r]) for r in range(nr) if agg[r] < 0), key=lambda kv: kv[1])
        check(len(neg) == E["w17_neg"], f"W17/LAM17 邊層聚合負座標 {len(neg)} 個（feature 層憑證不升到逐邊）")
        for k, v in neg:
            print(f"        {k} = {v}")
    # LP1
    res = linprog(c=np.zeros(m_), A_ub=-D[:, :nr].T, b_ub=np.zeros(nr),
                  A_eq=np.vstack([D[:, nr:].T, np.ones((1, m_))]), b_eq=np.concatenate([np.zeros(4), [1.0]]),
                  bounds=[(0, None)] * m_, method="highs")
    S1 = [pool[i] for i in np.nonzero(res.x > 1e-9)[0]] if res.status == 0 else []
    ex1 = exact(lambda x: rowvec[x], S1, list(range(nr, nr + 4)), list(range(nr))) if S1 else None
    if ex1:
        W, lam = ex1
        agg = [sum(l * rowvec[x][r] for x, l in zip(W, lam)) for r in range(nr + 4)]
        nz = [(rows[r], agg[r]) for r in range(nr) if agg[r]]
        check(all(v >= 0 for v in agg[:nr]) and all(v == 0 for v in agg[nr:]) and len(W) == E["lp1_supp"]
              and sum(lam) == E["lp1_sum"] and len(nz) == E["lp1_nz"],
              f"LP1（邊聚合 ≥ 0 ＋ 四平衡）可行：精確支撐 {len(W)}、Σλ′ = {sum(lam)}、聚合非零 {len(nz)} 個（單一循環）")
        print(f"        W = {W}")
        for k, v in nz:
            print(f"        agg{k} = {v}")
    else:
        check(False, f"LP1 status {res.status}：不可行或精確化失敗——gauge 路線的覆活訊號之一，停下回報")
    # LP2
    res2 = linprog(c=np.zeros(m_), A_eq=np.vstack([D.T, np.ones((1, m_))]),
                   b_eq=np.concatenate([np.zeros(nr + 4), [1.0]]), bounds=[(0, None)] * m_, method="highs")
    S2 = [pool[i] for i in np.nonzero(res2.x > 1e-9)[0]] if res2.status == 0 else []
    ex2 = exact(lambda x: rowvec[x], S2, list(range(nr + 4)), []) if S2 else None
    if ex2:
        W, lam = ex2
        agg = [sum(l * rowvec[x][r] for x, l in zip(W, lam)) for r in range(nr + 4)]
        check(all(v == 0 for v in agg) and len(W) == E["lp2_supp"],
              f"LP2（邊聚合 ≡ 0，無符號版）可行：精確支撐 {len(W)}、Σλ = {sum(lam)}、全零 ✓ ⟹ 符號假設可整個移除")
    else:
        check(False, f"LP2 status {res2.status}：不可行——此時 LP1 可行而 LP2 不可行 = gauge 路線覆活訊號")
    # LP3
    res3 = linprog(c=np.zeros(m_), A_eq=np.vstack([Fm.T, np.ones((1, m_))]),
                   b_eq=np.concatenate([np.zeros(Fm.shape[1]), [1.0]]), bounds=[(0, None)] * m_, method="highs")
    S3 = [pool[i] for i in np.nonzero(res3.x > 1e-9)[0]] if res3.status == 0 else []
    ex3 = exact(lambda x: fdiff[x], S3, list(range(Fm.shape[1])), []) if S3 else None
    if ex3:
        W, lam = ex3
        agg = [sum(l * fdiff[x][r] for x, l in zip(W, lam)) for r in range(Fm.shape[1])]
        check(all(v == 0 for v in agg) and len(W) == E["lp3_supp"] and sum(lam) == E["lp3_sum"],
              f"LP3（A 側 feature 層 ≡ 0 ＋ 四平衡）可行：精確支撐 {len(W)}、Σλ = {sum(lam)}、全零 ✓")
    else:
        check(False, f"LP3 status {res3.status}")
    print(f"        耗時 {time.time() - t0:.1f} s")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--lp", action="store_true", help="再跑 §3 R1 邊粒度 LP（需 scipy）")
    args = ap.parse_args()
    t0 = time.time()
    census("L2")
    census("L3")
    mechanism()
    if args.lp:
        edge_lp("L2")
        edge_lp("L3")
    print(f"\n耗時 {time.time() - t0:.1f} 秒。")
    print("全部通過。" if ok else "有失敗項——數字與設計報告不符，停下回報，不要改寫結論。")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
