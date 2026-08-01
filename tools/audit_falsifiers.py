#!/usr/bin/env python3
"""arXiv 2506.21728 審計的可計算 falsifier 重現。離線、零依賴、決定性。

    python3 tools/audit_falsifiers.py

(b)(d) 為腳本重現；(a)(c) 為引文核對，見 docs/audit/2506-21728.md。
w(n) 的正負另用精確整數判定交叉驗證（w > 0 ⟺ 3^to > 2^(to+tz)），
浮點只用於顯示數值，不承載結論。
"""
import math, sys

def to(n):                       # 二進位尾端 1 的個數
    k = 0
    while n & 1: k += 1; n >>= 1
    return k

def tz(n):                       # 二進位尾端 0 的個數
    k = 0
    while n and not (n & 1): k += 1; n >>= 1
    return k

def T3(n): return (3 * n + 1) // 2

L32 = math.log2(1.5)
ok = True
def check(cond, msg):
    global ok
    print(("  [OK]  " if cond else "  [!!]  ") + msg)
    ok = ok and cond

print("=== falsifier (b)：w(n) 的 pointwise 反例 ===")
n = 11
k = to(n)
np = n
for _ in range(k): np = T3(np)
w11 = k * L32 - tz(np)
check(k == 2 and np == 26 and tz(np) == 1, f"to(11)={k}, 11→17→{np}, tz={tz(np)}")
check(w11 > 0, f"w(11) = {w11:+.5f} > 0（論文宣稱每個 block 嚴格下降）")
check(3**k > 2**(k + tz(np)),
      f"精確整數判定：3^{k} = {3**k} > 2^{k + tz(np)} = {2**(k + tz(np))}（不依賴浮點）")
check(1 + tz(np) / k > L32, "論文的不等式 1+tz/to > log2(3/2) 成立——但推不出 w<0")
pos = 0
agree = True
for m in range(3, 100001, 2):
    c = to(m); v = m
    for _ in range(c): v = T3(v)
    t = tz(v)
    exact = 3**c > 2**(c + t)          # w > 0 ⟺ c·log2(3) > c + t
    if exact: pos += 1
    agree = agree and (exact == (c * L32 - t > 0))
check(pos > 0, f"奇數 < 10^5 中 w > 0 者共 {pos} 個（非孤例）")
check(agree, "全範圍逐點：精確整數判定與浮點判定一致")

print("\n=== falsifier (d)：能量函數 f 不沿奇數點鏈接 ===")
def f(nv, n0): return math.log2(nv) / math.log2(n0) + to(nv) - tz(nv)
f9, f7 = f(9, 9), f(7, 9)   # 軌道 9 → 28 → 14 → 7 的奇數點；n0 = 9 固定（忠於論文定義）
check(f9 < f7, f"軌道 9→7：f(9)={f9:.3f} < f(7)={f7:.3f}——f 沿同一軌道的奇數點上升")

print("\n=== falsifier (a)(c) 為引文核對，見 docs/audit/2506-21728.md ===")
print("    (a) Table 5 的 (9,1,0) 列（兩個自環）＋ §4.3 自列 (8,1,0)↔(9,1,0)")
print("    (c) Lemma 4.14 證明 base case vs Appendix C（Table 4）n=13 的 s₁ 欄")

print("\n" + ("全部通過。" if ok else "有失敗項——停下回報，不要改寫結論。"))
sys.exit(0 if ok else 1)
