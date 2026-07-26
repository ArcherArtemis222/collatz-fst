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


def todd(x: int) -> int:
    n = 3 * x + 1
    while n % 2 == 0:
        n //= 2
    return n


def trace(x: int):
    """(微觀轉移串, 終末狀態)；輸入為 extIn x = LSB-first + 兩個哨兵零。"""
    s, out = (1, 'K', 0), []
    for b in [int(t) for t in bin(x)[2:]][::-1] + [0, 0]:
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


def main() -> int:
    check_lean_anchor()

    odds = list(range(3, ODD_MAX, 2))
    D = sp.Matrix.vstack(*[F(todd(x)) - F(x) for x in odds])

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
