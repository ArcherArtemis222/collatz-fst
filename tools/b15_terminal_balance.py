#!/usr/bin/env python3
"""B1.5 資料點 1：既有雙模式憑證的「終末流量平衡」精確整數重算。

    python3 tools/b15_terminal_balance.py

對兩組已在 Lean 落地的雙模式 Farkas 憑證（W12/Σλ=7826、W20/Σλ=31746），
計算每個終末狀態 t 的

    B(t) = Σᵢ λᵢ · (⟦end(Todd Wᵢ) = t⟧ − ⟦end(Wᵢ) = t⟧)

全程整數運算，無浮點。ROADMAP-B B1.5 的宣稱：兩層皆**不平衡**，
Level 2 為 ±428、Level 3 為 ±753 ⟹ per-(mode, terminal) 偏移 β_{m,t}
不是既有憑證的免費升級（對照：模式平衡 Σλ(e_{m(y)}−e_{m(x)}) = 0
成立，見 certificates.py 第 3 項，那是 A-2 仿射 β_m 升級的前提）。

λ、見證集、特徵與模式判準全部 import 自 certificates.py（其唯一來源為
ProjectA/*.lean）；狀態機另照 Lean 定義重寫（step2 對照
Core/Collatz_FST_Level2.lean、step3 對照 ProjectA/Collatz_FST_L3_Flow.lean），
與 a3_functionals.py / l3_recon.py 的實作互為獨立對照。
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from certificates import (  # noqa: E402
    F2, F3, MODE_IDX_L2, MODE_IDX_L3, LAM12, LAM20, W12, W20, _bits, todd,
)

ok = True


def check(cond: bool, msg: str) -> bool:
    global ok
    print(("  [OK]  " if cond else "  [!!]  ") + msg)
    ok = ok and cond
    return cond


# ── 狀態機（照 Lean 定義；獨立於 a3_functionals / l3_recon 的同名實作）──

def run2(x: int) -> tuple:
    """讀完 extIn x 後的 Level 2 狀態 (c, P, dPrev)。"""
    c, P, dp = 1, 'K', 0
    for b in _bits(x):
        d, c = (3 * b + c) % 2, (3 * b + c) // 2
        P, dp = (('K', 0) if d == 0 else ('S', 1)) if P == 'K' else ('S', d)
    return (c, P, dp)


def run3(x: int) -> tuple:
    """讀完 extIn x 後的 Level 3 狀態 (c, P, h₂, h₁)。"""
    c, P, H = 1, 'K', (0, 0)
    for b in _bits(x):
        d, c = (3 * b + c) % 2, (3 * b + c) // 2
        P = ('K' if d == 0 else 'S') if P == 'K' else 'S'
        H = (H[1], d)
    return (c, P, H[0], H[1])


TERM2 = [(0, 'S', 0), (0, 'S', 1)]            # Flow.run2_extIn_terminal
TERM3 = [(0, 'S', 0, 1), (0, 'S', 1, 0)]      # L3.run3_extIn_terminal


def balance(title: str, W: list, LAM: list, run, terms: list, feat, mode_idx: int,
            expect: int, sigma: int) -> None:
    print(f"=== {title} ===")
    check(sum(LAM) == sigma, f"Σλ = {sum(LAM)}（規格：{sigma}）")
    ends = {}
    for x in W:
        for z in (x, todd(x)):
            if z not in ends:
                e = run(z)
                assert e in terms, f"終末 {e} 不在定理宣稱的兩態內（x={z}）"
                ends[z] = e
    B = {t: 0 for t in terms}
    for lam, x in zip(LAM, W):
        y = todd(x)
        for t in terms:
            B[t] += lam * ((ends[y] == t) - (ends[x] == t))
    vals = [B[t] for t in terms]
    print(f"        B{terms[0]} = {vals[0]:+d}, B{terms[1]} = {vals[1]:+d}")
    check(vals[0] + vals[1] == 0, "兩終末分量相加 = 0（每字恰居其一，必然）")
    check(sorted(map(abs, vals)) == [expect, expect],
          f"終末不平衡 = ±{abs(vals[0])}（宣稱：±{expect}）")
    check(any(v != 0 for v in vals), "不平衡 ≠ 0 ⟹ β_{m,t} 偏移非免費升級")
    # 補充：per-(mode, terminal) 四分量（β_{m,t} 的對偶係數）
    Bmt = {(m, t): 0 for m in (0, 1) for t in terms}
    for lam, x in zip(LAM, W):
        y = todd(x)
        mx, my = int(feat(x)[mode_idx] == 1), int(feat(y)[mode_idx] == 1)
        Bmt[(my, ends[y])] += lam
        Bmt[(mx, ends[x])] -= lam
    print("        per-(mode, terminal)：" + ", ".join(
        f"(m={m}, t={t}) {v:+d}" for (m, t), v in Bmt.items()))
    check(sum(v for (m, t), v in Bmt.items() if m == 0) == 0
          and sum(v for (m, t), v in Bmt.items() if m == 1) == 0,
          "對 t 求和退回模式平衡 = 0（certificates.py 第 3 項的再現）")
    print()


def main() -> int:
    balance("Level 2 雙模式（W12, Σλ=7826）", W12, LAM12, run2, TERM2,
            F2, MODE_IDX_L2, expect=428, sigma=7826)
    balance("Level 3 雙模式（W20, Σλ=31746）", W20, LAM20, run3, TERM3,
            F3, MODE_IDX_L3, expect=753, sigma=31746)
    print("全部通過。" if ok else "有失敗項——停下回報，不要改寫結論。")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
