#!/usr/bin/env python3
"""A-3 上界：泛函對照表的精確有理秩驗算。

ROADMAP A-3 的上界要對所有奇數 x 證明「若干條線性泛函在 ΔF x 上恆為零」。
這支腳本回答的是：**到底需要哪幾條、夠不夠**。全程精確有理（sympy），無浮點。

    python3 tools/a3_functionals.py

結論（本腳本輸出即證據，數字寫在 docs/ROADMAP-A.md A-3 段）：

* dim span(ΔF) = 10 —— 與 HandOver 的「10 維有理線性子空間」一致。
* 上界需要的獨立泛函數 = 18 − 10 = 8。
* 死狀態 2 條（座標 0、1 恆為零）＋ 流守恆可用 7 條（秩 6）＝ 秩 8，**完備**。
* ROADMAP 舊表列的 `boundary_step_unique` 與 K 區交錯計數落在上述列空間內，
  是被蘊含的推論，不需要另證。

流守恆為何是「7 條、秩 6」而非 8 條：8 條之和恆為零（每步恰出一次、入一次），
故至多 7 條獨立；又因終末狀態恆落在 (0,S,0)/(0,S,1) 兩者之一，這兩條的端點指示
在 ΔF 上不個別對消，必須相加合併成一條（合併後指示恆為 1）。
6 條乾淨 + 1 條合併 = 7 條，秩 6。

與 `certificates.py` 的分工：那支驗「既有憑證的數字對不對」，這支驗
「上界要證哪幾條引理」。兩支都是精確有理、完全決定性，都在 CI 每次 push 跑。

## Lean 端的錨

`LEAN_INEDGES` 是從 Lean `ProjectA/Collatz_FST_Flow.lean` 的 `#guard`（`Flow.inEdges`
的實際內容）抄過來的，本腳本用自己的 `step2` 重算後逐條對帳——與 `certificates.py`
的 `LEAN_DF10` 同一個模式。**沒有這一條，本腳本守的只是「數學結論」而非
「Lean↔Python 一致性」**：有人改了 Lean 的 `step2`，Python 這邊不會叫。
"""

from __future__ import annotations

import sys

import sympy as sp

# ────────────────────────────────────────────────────────────────────
# Level 2 狀態機（獨立實作，對照 Core 的 step2 / occ2）
# ────────────────────────────────────────────────────────────────────

def step2(s: tuple, b: int) -> tuple:
    """對照 `Core/Collatz_FST_Level2.lean` 的 `step2`。"""
    c, P, _ = s
    d, cn = (3 * b + c) % 2, (3 * b + c) // 2
    if P == 'K':
        return (cn, 'K', 0) if d == 0 else (cn, 'S', 1)
    return (cn, 'S', d)


S8 = [(1, 'K', 0), (2, 'K', 0),
      (0, 'S', 0), (0, 'S', 1), (1, 'S', 0), (1, 'S', 1), (2, 'S', 0), (2, 'S', 1)]

# 18 維 KEYS 順序（同 Lean `LP.KEYS`）：先 6 個 (c,K,0)×b，再 12 個 (c,S,p)×b
KEYS = ([((c, 'K', 0), b) for c in (0, 1, 2) for b in (0, 1)]
        + [((c, 'S', p), b) for c in (0, 1, 2) for p in (0, 1) for b in (0, 1)])
IDX = {k: i for i, k in enumerate(KEYS)}

# 終末狀態的兩種可能（本腳本自行驗證，非假設）
TERMINALS = [(0, 'S', 0), (0, 'S', 1)]

ODD_MAX = 4000

# Lean `ProjectA/Collatz_FST_Flow.lean` 的 `#guard`（`S8.map inEdges` 的實際內容）。
# 這是本腳本與 Lean 之間唯一的錨：兩邊都寫死同一張 16 邊關聯表，各自獨立重算後對帳。
LEAN_INEDGES: dict[tuple, list] = {
    (1, 'K', 0): [((2, 'K', 0), 0)],
    (2, 'K', 0): [((1, 'K', 0), 1)],
    (0, 'S', 0): [((0, 'S', 0), 0), ((0, 'S', 1), 0)],
    (0, 'S', 1): [((1, 'K', 0), 0), ((1, 'S', 0), 0), ((1, 'S', 1), 0)],
    (1, 'S', 0): [((2, 'S', 0), 0), ((2, 'S', 1), 0)],
    (1, 'S', 1): [((0, 'S', 0), 1), ((0, 'S', 1), 1)],
    (2, 'S', 0): [((1, 'S', 0), 1), ((1, 'S', 1), 1)],
    (2, 'S', 1): [((2, 'K', 0), 1), ((2, 'S', 0), 1), ((2, 'S', 1), 1)],
}

# Lean `ProjectA/Collatz_FST_FlowDelta.lean` §53–54 的 9 條差分層恆等式（秩 8）。
# 每條抄成 {座標: 係數} 的字典，語意是 Σ coeff[i] * ΔF[i] = 0（0-based 座標）。
# 第二條錨：Lean 那邊的定理若被改動、或 Python 這邊的模型漂移，都會對不上。
LEAN_DELTA_RELATIONS: list[tuple[str, dict[int, int]]] = [
    ("dF_zero_0",               {0: 1}),
    ("dF_zero_1",               {1: 1}),
    ("dF_flow_1K0",             {4: 1, 2: -1, 3: -1}),
    ("dF_flow_2K0",             {3: 1, 4: -1, 5: -1}),
    ("dF_flow_1S0",             {14: 1, 16: 1, 10: -1, 11: -1}),
    ("dF_flow_1S1",             {7: 1, 9: 1, 12: -1, 13: -1}),
    ("dF_flow_2S0",             {11: 1, 13: 1, 14: -1, 15: -1}),
    ("dF_flow_2S1",             {5: 1, 15: 1, 16: -1}),
    ("dF_flow_terminal_merged", {2: 1, 10: 1, 12: 1, 7: -1, 9: -1}),
]

# Lean `ProjectA/Collatz_FST_DimUpper.lean` §58 的 `freeIdx`：10 個自由座標。
LEAN_FREE_IDX: list[int] = [2, 3, 6, 7, 8, 9, 10, 11, 15, 17]

# 同檔檔頭那張表：另外 8 個座標由自由座標重建的公式（{來源座標: 係數}）。
LEAN_RECONSTRUCTION: dict[int, dict[int, int]] = {
    0:  {},
    1:  {},
    4:  {2: 1, 3: 1},
    5:  {2: -1},
    12: {7: 1, 9: 1, 10: -1, 2: -1},
    13: {10: 1, 2: 1},
    14: {10: 1, 11: 1, 2: 1, 15: -1},
    16: {15: 1, 2: -1},
}

# Lean `LP.W₁₀` 與 `Collatz_FST_NoLinearRanking.lean` §35 的 λ（同 certificates.py）。
W10: list[int] = [231, 323, 403, 551, 681, 877, 983, 1079, 1305, 1511]
LAM10: list[int] = [100, 64, 119, 51, 56, 183, 164, 18, 191, 78]

# Lean `ProjectA/Collatz_FST_DimLower.lean` §61–63 的下界資料：見證集用 W₁₀，
# 投影到自由座標的 10×10 矩陣行列式 = 31（≠ 0 ⇒ 10 條線性獨立 ⇒ 下界 10）。
LEAN_LOWER_WITNESSES: list[int] = W10
LEAN_LOWER_DET: int = 31


def todd(x: int) -> int:
    n = 3 * x + 1
    while n % 2 == 0:
        n //= 2
    return n


def ext_in(x: int) -> list[int]:
    """`extIn x = Nat.digits 2 x ++ [0, 0]`。

    `x = 0` 要特別處理：`Nat.digits 2 0 = []`，而 `bin(0)[2:] == "0"`
    會多給一個零。詳見 `certificates.py` 的 `_bits`。
    """
    digits = [] if x == 0 else [int(t) for t in bin(x)[2:]][::-1]
    return digits + [0, 0]


def trace(x: int):
    """(微觀轉移串, 終末狀態)；輸入為 extIn x = LSB-first + 兩個哨兵零。"""
    s, out = (1, 'K', 0), []
    for b in ext_in(x):
        out.append((s, b))
        s = step2(s, b)
    return out, s


def F(x: int) -> sp.Matrix:
    v = [0] * 18
    for t in trace(x)[0]:
        v[IDX[t]] += 1
    return sp.Matrix([v])


# ────────────────────────────────────────────────────────────────────
# 泛函
# ────────────────────────────────────────────────────────────────────

def death(i: int) -> list[int]:
    """死狀態：座標 i 恆為零（i = 0, 1，即 (0,K,0) 的兩個位元）。"""
    f = [0] * 18
    f[i] = 1
    return f


def flow(g: tuple) -> list[int]:
    """狀態 g 的流守恆：in-flow(g) − out-flow(g)。"""
    f = [0] * 18
    for h in S8:
        for b in (0, 1):
            if step2(h, b) == g:
                f[IDX[(h, b)]] += 1
    for b in (0, 1):
        f[IDX[(g, b)]] -= 1
    return f


OK, BAD = "  [OK]  ", "  [!!]  "
_failures: list[str] = []


def check(cond: bool, msg: str) -> bool:
    print((OK if cond else BAD) + msg)
    if not cond:
        _failures.append(msg)
    return cond


def rank(rows: list[list[int]]) -> int:
    return sp.Matrix(rows).rank() if rows else 0


def annihilates(D: sp.Matrix, f: list[int]) -> bool:
    return (D * sp.Matrix(f)) == sp.zeros(D.rows, 1)


def in_edges(g: tuple) -> list:
    """落點為 g 的入邊（allEdges 順序：S8 序 × b = 0, 1）。對照 Lean `Flow.inEdges`。"""
    return [(h, b) for h in S8 for b in (0, 1) if step2(h, b) == g]


def check_lean_anchor() -> None:
    """與 Lean `#guard` 寫死的 16 邊關聯表逐條對帳。"""
    print("\n=== Lean↔Python 錨：16 邊關聯表 ===")
    mine = {g: in_edges(g) for g in S8}
    check(mine == LEAN_INEDGES,
          "本腳本重算的入邊表與 Lean `Flow.inEdges` 的 #guard 逐條吻合（8 狀態 / 16 邊）")
    if mine != LEAN_INEDGES:
        for g in S8:
            if mine[g] != LEAN_INEDGES.get(g):
                print(f"        {g}: Python {mine[g]} vs Lean {LEAN_INEDGES.get(g)}")
    check(sum(len(v) for v in LEAN_INEDGES.values()) == 16,
          "入邊表總邊數 = 16（每條轉移邊恰屬一個狀態）")


def relation_vector(coeff: dict[int, int]) -> list[int]:
    v = [0] * 18
    for i, c in coeff.items():
        v[i] = c
    return v


def check_delta_relations(D: sp.Matrix) -> None:
    """與 Lean `FlowDelta` 的 9 條差分層恆等式對帳（秩 8）。"""
    print("\n=== Lean↔Python 錨：9 條差分層恆等式（FlowDelta §53–54）===")
    rows = []
    for name, coeff in LEAN_DELTA_RELATIONS:
        v = relation_vector(coeff)
        rows.append(v)
        check(annihilates(D, v), f"{name} 在 ΔF 上恆為零")
    check(rank(rows) == 18 - D.rank(),
          f"9 條的秩 = {rank(rows)}（需要 18 − dim span(ΔF) = {18 - D.rank()}）⇒ 完備")

    # 這 9 條應該就是「死狀態 + 可用流守恆」張出的同一個空間，不多不少
    deaths = [death(0), death(1)]
    usable = ([flow(g) for g in S8 if g not in TERMINALS]
              + [[a + b for a, b in zip(flow(TERMINALS[0]), flow(TERMINALS[1]))]])
    check(rank(rows + deaths + usable) == rank(rows),
          "Lean 的 9 條與『死狀態 + 可用流守恆』張出同一個空間")


def check_upper_bound_data() -> None:
    """與 Lean `DimUpper` 的自由座標集與重建公式對帳（上界 ≤ 10 的資料面）。"""
    print("\n=== Lean↔Python 錨：上界的自由座標與重建公式（DimUpper §58）===")
    free = LEAN_FREE_IDX
    det = [i for i in range(18) if i not in free]
    check(len(free) == 10 and len(set(free)) == 10 and all(0 <= i < 18 for i in free),
          f"自由座標 {free}：10 個、互異、皆 < 18")
    check(sorted(LEAN_RECONSTRUCTION) == det,
          f"重建公式的座標集 = 被決定的 8 個 {det}")

    a = sp.symbols('a0:18')
    rels = [sum(c * a[i] for i, c in coeff.items())
            for _, coeff in LEAN_DELTA_RELATIONS]

    # 1. 自由座標全零 ⇒ 整個向量為零（即 Lean 的 pick_injective_on_Sol）
    zeroed = [r.subs({a[i]: 0 for i in free}) for r in rels]
    sol = sp.solve(zeroed, [a[i] for i in det], dict=True)
    check(len(sol) == 1 and all(sp.simplify(sol[0].get(a[i], 0)) == 0 for i in det),
          "自由座標全零 ⇒ 被決定的 8 個也全零（對應 pick_injective_on_Sol）")

    # 2. 重建公式與 9 條解出來的一致
    solved = sp.solve(rels, [a[i] for i in det], dict=True)
    check(len(solved) == 1, "9 條可唯一解出那 8 個座標")
    if solved:
        s = solved[0]
        for i, coeff in LEAN_RECONSTRUCTION.items():
            expected = sum(c * a[j] for j, c in coeff.items())
            check(sp.simplify(s[a[i]] - expected) == 0,
                  f"重建公式 a{i} = {expected if coeff else 0} 與解一致")


def check_lower_bound_data() -> None:
    """與 Lean `DimLower` 的下界資料對帳：W₁₀ 投影後的 10×10 矩陣可逆。"""
    print("\n=== Lean↔Python 錨：下界的見證與行列式（DimLower §61–63）===")
    check(LEAN_LOWER_WITNESSES == W10,
          f"下界見證集 = W₁₀ = {W10}")
    dF = {x: F(todd(x)) - F(x) for x in LEAN_LOWER_WITNESSES}
    full = sp.Matrix([list(dF[x]) for x in LEAN_LOWER_WITNESSES])
    check(full.rank() == 10, f"10 條 ΔF 在 18 維裡的秩 = {full.rank()}（需要 10）")
    M = sp.Matrix([[int(dF[x][j]) for j in LEAN_FREE_IDX]
                   for x in LEAN_LOWER_WITNESSES])
    det = M.det()
    check(det == LEAN_LOWER_DET,
          f"投影到自由座標的 10×10 行列式 = {det}（Lean 檔頭記的是 {LEAN_LOWER_DET}）")
    check(det != 0, "行列式 ≠ 0 ⇒ 投影後仍線性獨立 ⇒ 下界 10 成立")
    # 觀察（非定理）：這個 31 與 Farkas 憑證的 Σλ·ΔF = 31·e₇ 是同一個數字
    A = sp.Matrix([list(dF[x]) for x in W10])
    comb = (sp.Matrix([LAM10]) * A).tolist()[0]
    check(comb[6] == LEAN_LOWER_DET,
          f"觀察：Farkas 組合的第 7 座標也是 {comb[6]}（與行列式同值，僅記錄不主張因果）")


def main() -> int:
    check_lean_anchor()
    check_upper_bound_data()
    check_lower_bound_data()

    odds = list(range(3, ODD_MAX, 2))
    D = sp.Matrix.vstack(*[F(todd(x)) - F(x) for x in odds])
    check_delta_relations(D)

    print(f"\n=== A-3 上界：需要哪幾條泛函（奇數 3 ≤ x < {ODD_MAX}）===")

    rank_D = D.rank()
    need = 18 - rank_D
    check(rank_D == 10, f"dim span(ΔF) = {rank_D}（HandOver 宣稱 10）")
    print(f"        上界需要的獨立泛函數 = 18 − {rank_D} = {need}")

    # 終末狀態：對**所有** x 檢查（含 0、1 與偶數），不只奇數——這性質與奇偶無關
    finals = ({trace(x)[1] for x in range(ODD_MAX)}
              | {trace(todd(x))[1] for x in odds})
    check(finals <= set(TERMINALS),
          f"終末狀態 ⊆ {TERMINALS}（所有 0 ≤ x < {ODD_MAX}），實測 = {sorted(finals)}")

    deaths = [death(0), death(1)]
    check(all(annihilates(D, f) for f in deaths), "死狀態 2 條皆湮滅 ΔF")

    flows = [flow(g) for g in S8]
    check(rank(flows) == 7, f"流守恆 8 條，秩 {rank(flows)}（8 條之和恆為零 ⇒ 至多 7）")

    not_annih = [g for g, f in zip(S8, flows) if not annihilates(D, f)]
    check(sorted(not_annih) == sorted(TERMINALS),
          f"不個別湮滅 ΔF 的恰為兩個可能終末：{sorted(not_annih)}")

    clean = [flow(g) for g in S8 if g not in TERMINALS]
    merged = [[a + b for a, b in zip(flow(TERMINALS[0]), flow(TERMINALS[1]))]]
    usable = clean + merged
    check(all(annihilates(D, f) for f in usable),
          f"可用流守恆 {len(clean)} 條乾淨 + {len(merged)} 條合併 = {len(usable)} 條，皆湮滅 ΔF")
    check(rank(usable) == 6, f"可用流守恆秩 = {rank(usable)}")

    base = deaths + usable
    check(rank(base) == need,
          f"死狀態 + 可用流守恆 合併秩 = {rank(base)}（需要 {need}）⇒ 完備")

    # ROADMAP 舊表另列的兩條：是否被蘊含（在列空間內）
    # 1-based e₃+e₆=1 → 0-based 座標 2、5；1-based e₄=e₅+e₆ → 0-based 3 = 4 + 5
    extras = {
        "boundary_step_unique（e₃+e₆=1）": [0, 0, 1, 0, 0, 1] + [0] * 12,
        "K 區交錯計數（e₄=e₅+e₆）": [0, 0, 0, 1, -1, -1] + [0] * 12,
    }
    for name, f in extras.items():
        check(annihilates(D, f) and rank(base + [f]) == rank(base),
              f"{name} 落在『死狀態+流守恆』列空間內 ⇒ 被蘊含，不需另證")

    print()
    if _failures:
        print(f"失敗 {len(_failures)} 項：")
        for f in _failures:
            print("   -", f)
        return 1
    print("全部通過。ROADMAP A-3 的泛函對照表與此腳本一致。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
