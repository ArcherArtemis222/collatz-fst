#!/usr/bin/env python3
"""Collatz FST：B2 全語言判定引擎（ROADMAP-B B2；設計核准 2026-08-28）。

對「給定權重」的確定性成本自動機（鏡射 Lean `ProjectB/
Collatz_FST_B1_Reweighting.lean` 的 `CostAutomaton`：cost u = α + Σ邊權 + β(終態)）
判定 **AllNeg**：所有接受字成本 < 0。純 tools 層、精確有理
（`fractions.Fraction`，零浮點）、零 Lean。這支腳本做三件事：

1. **判定**（`decide_all_negative`）：trim（可達∧可出）→ 權重取負 →
   Bellman–Ford 可達正循環偵測 ＋ 一次邊界最短路。有正循環 → fail
   （pump 見證，k 由有理算術直接解）；無正循環 → 接受字成本最大值
   M* 由 elementary path 達成，pass ⟺ M* < 0。
   **Karp（1978）單獨不足的角**：max cycle mean ≤ 0（無正循環）時判定
   尚未完成——sup 落在有限的 boundary path 上，仍須算 M* 並與 0 嚴格
   比較；α/β 是 boundary 貢獻，循環量看不到；零均值循環 pump 不改成本，
   fail 與否完全由 M* 決定。已知答案 T1（B1 的 Mneg）恰落此角。
2. **憑證自驗**（`verify_pass_cert` / `verify_fail_witness`）：不信引擎
   主流程、只做局部檢查。pass 憑證 = (R, C, d)——R/C 兩集合把量化域
   「useful」也局部化（P1 前向封閉、P2 後向封閉 ⟹ R∩C ⊇ Useful），
   d 逐態勢能值過 P3 三角、P4 接受、P5 對齊；健全性定理
   P1–P5 ⟹ AllNeg 即 B3 的 Lean 驗證書鏡射對象。fail 見證 = 平坦
   接受字，直接求值成本 ≥ 0（完整檢查）。引擎回傳前一律以驗證函數
   自檢自己的輸出，主流程 bug 當場拋例外而非流出。
3. **oracle 性質測試**（`--selftest` 內）：固定種子隨機小機器（≤ 4 態）
   × 引擎判定 vs 有界窮舉 oracle 的方向性判準矩陣（fail 靠見證求值、
   pass 靠憑證健全性；窮舉為防共模 bug 的交叉探針）。

    python3 tools/b2_engine.py --selftest   # 已知答案＋負向測試＋oracle（CI；< 10 秒）
    python3 tools/b2_engine.py              # 同 --selftest

依賴：**純標準庫**（fractions／dataclasses／argparse／random／
itertools／collections）。不需 numpy/sympy。oracle 的隨機只有名字是
隨機——種子固定、完全決定性，屬 tools/README 表格左欄。

文獻定位（照 ROADMAP-B B2，不新增宣稱）：Johnson 1977（reweighting，
B1 主引用）；Karp 1978（cycle mean，單獨不足——見上）；Mohri 2002
（semiring shortest-distance 背景）；Almagor–Boker–Kupferman survey
（threshold universality 的 deterministic 特例）。
"""

from __future__ import annotations

import argparse
import itertools
import math
import random
import sys
import time
from collections import deque
from dataclasses import dataclass, field
from fractions import Fraction

OK, BAD = "  [OK]  ", "  [!!]  "
_failures: list[str] = []


def check(cond: bool, msg: str) -> bool:
    print((OK if cond else BAD) + msg)
    if not cond:
        _failures.append(msg)
    return cond


# ────────────────────────────────────────────────────────────────────
# 自動機規格（Q2 定案：鏡射 Lean CostAutomaton；狀態 0..n−1、字母任意 int）
# ────────────────────────────────────────────────────────────────────

def _frac(x) -> Fraction:
    """輸入容許 int / Fraction / "p/q" 字串，一律正規化為 Fraction。"""
    if isinstance(x, Fraction):
        return x
    if isinstance(x, int) or isinstance(x, str):
        return Fraction(x)
    raise TypeError(f"權重須為 int / Fraction / 'p/q' 字串，得到 {type(x)}")


@dataclass(frozen=True)
class CostAutomatonPy:
    """確定性有理權重成本自動機（勿直接建構，走 `mk_automaton` 取得驗證）。"""
    n_states: int
    alphabet: tuple[int, ...]            # 已排序去重
    step: tuple[dict[int, int], ...]     # step[q][a]，對 (q, a) 全定義
    w: tuple[dict[int, Fraction], ...]   # w[q][a]，同上
    init: int
    accept: frozenset[int]
    alpha: Fraction
    beta: tuple[Fraction, ...]           # beta[q]，全定義


def mk_automaton(n_states, alphabet, step, w, init, accept, alpha, beta) -> CostAutomatonPy:
    """正規化＋驗證：轉移/權重對 (q, a) 全定義、目標入界、init/accept 入界。"""
    ab = tuple(sorted(set(alphabet)))
    if n_states < 1:
        raise ValueError("至少一個狀態")
    if not (0 <= init < n_states):
        raise ValueError("init 出界")
    if not all(0 <= q < n_states for q in accept):
        raise ValueError("accept 出界")
    if len(step) != n_states or len(w) != n_states or len(beta) != n_states:
        raise ValueError("step / w / beta 長度須 = n_states")
    st, wt = [], []
    for q in range(n_states):
        sq, wq = {}, {}
        for a in ab:
            if a not in step[q] or a not in w[q]:
                raise ValueError(f"step/w 在 ({q}, {a}) 未定義（轉移須完全）")
            t = step[q][a]
            if not (0 <= t < n_states):
                raise ValueError(f"step[{q}][{a}] = {t} 出界")
            sq[a], wq[a] = t, _frac(w[q][a])
        st.append(sq)
        wt.append(wq)
    return CostAutomatonPy(n_states, ab, tuple(st), tuple(wt), init,
                           frozenset(accept), _frac(alpha), tuple(_frac(b) for b in beta))


# ────────────────────────────────────────────────────────────────────
# 憑證資料與 Verdict
# ────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class PassCert:
    """pass 憑證：R ⊇ Reach、C ⊇ CoReach∩R（P1/P2 局部封閉 ⟹ R∩C ⊇ Useful）、
    d = R∩C 上的逐態勢能值（引擎輸出恰為 useful 集上的最長路值）。"""
    R: frozenset[int]
    C: frozenset[int]
    d: dict[int, Fraction]


@dataclass(frozen=True)
class FailWitness:
    """fail 見證：平坦接受字，成本 ≥ 0 直接可驗。結構形（前綴/循環/k/出綴）
    只放 Verdict.info 供人讀，不進信任基底。"""
    word: tuple[int, ...]


@dataclass(frozen=True)
class Verdict:
    kind: str                        # "pass" | "fail"
    cert: PassCert | None
    witness: FailWitness | None
    info: dict = field(default_factory=dict)
    # info 鍵：mode ∈ {"vacuous", "boundary", "cycle"}；boundary 另附 Mstar；
    # cycle 另附 prefix/cycle/pumps/suffix/cycle_weight（人讀，不受信任）。


class EngineError(AssertionError):
    """引擎自檢失敗（回傳前以驗證函數檢自己的輸出，主流程 bug 當場現形）。"""


# ────────────────────────────────────────────────────────────────────
# trim（可達∧可出）與 BFS 見證字
# ────────────────────────────────────────────────────────────────────

def trim(M: CostAutomatonPy) -> tuple[frozenset[int], frozenset[int]]:
    """回傳 (R, C)：init 前向可達集、可出（可達 accept）集。useful = R ∩ C。"""
    R: set[int] = {M.init}
    dq = deque([M.init])
    while dq:
        q = dq.popleft()
        for a in M.alphabet:
            t = M.step[q][a]
            if t not in R:
                R.add(t)
                dq.append(t)
    rev: list[list[tuple[int, int]]] = [[] for _ in range(M.n_states)]
    for q in range(M.n_states):
        for a in M.alphabet:
            rev[M.step[q][a]].append((q, a))
    C: set[int] = set(M.accept)
    dq = deque(sorted(M.accept))
    while dq:
        t = dq.popleft()
        for (q, _a) in rev[t]:
            if q not in C:
                C.add(q)
                dq.append(q)
    return frozenset(R), frozenset(C)


def _bfs_words(M: CostAutomatonPy, R: frozenset[int], C: frozenset[int]
               ) -> tuple[dict[int, tuple[int, ...]], dict[int, tuple[int, ...]]]:
    """BFS 樹見證字（狀態/字母依序迭代 ⟹ 決定性）：
    reach_word[q]（init ⇝ q，q ∈ R）、exit_word[q]（q ⇝ accept，q ∈ C）。
    以 D 中的 q 為端點的走行中途態自動 useful（中途態經 q 可出、經前綴可達），
    故全圖 BFS 的字對 useful 端點而言全程落在 D 內，作見證安全。"""
    reach: dict[int, tuple[int, ...]] = {M.init: ()}
    dq = deque([M.init])
    while dq:
        q = dq.popleft()
        for a in M.alphabet:
            t = M.step[q][a]
            if t not in reach:
                reach[t] = reach[q] + (a,)
                dq.append(t)
    rev: list[list[tuple[int, int]]] = [[] for _ in range(M.n_states)]
    for q in range(M.n_states):
        for a in M.alphabet:
            rev[M.step[q][a]].append((q, a))
    exit_: dict[int, tuple[int, ...]] = {f: () for f in sorted(M.accept)}
    dq = deque(sorted(M.accept))
    while dq:
        t = dq.popleft()
        for (q, a) in rev[t]:
            if q not in exit_:
                exit_[q] = (a,) + exit_[t]
                dq.append(q)
    assert set(reach) == set(R) and set(exit_) == set(C)
    return reach, exit_


# ────────────────────────────────────────────────────────────────────
# 判定引擎
# ────────────────────────────────────────────────────────────────────

def decide_all_negative(M: CostAutomatonPy) -> Verdict:
    """AllNeg 判定：pass → (R, C, d) 憑證；fail → 顯式見證字。
    回傳前一律以 verify_* 自檢輸出。化約與正確性論證見 B2-DESIGN-REPORT
    §1（僞碼、pred 無環性、Karp 角）。"""
    R, C = trim(M)
    D = frozenset(R & C)

    # 真空分支（顯式）：語言空 ⟺ init ∉ D（init 恆可達；可出 ⟺ 語言非空）。
    if M.init not in D:
        v = Verdict("pass", PassCert(R, C, {}), None, {"mode": "vacuous"})
        ok, why = verify_pass_cert(M, v.cert)
        if not ok:
            raise EngineError(f"真空 pass 憑證自檢失敗：{why}")
        return v

    # super-source/sink 已吸收（D1）：α 作 d 的常數偏移、β 折進終端 max。
    edges = [(q, a) for q in sorted(D) for a in M.alphabet if M.step[q][a] in D]
    n = len(D)

    # 取負 Bellman–Ford（嚴格改進鬆弛 ⟹ 零權循環不觸發偵測——語義上
    # 零循環 pump 不改成本，本就無害；pred 循環必嚴格負（取負圖），
    # 論證見設計報告 §1.2 技術註記 (a)）。
    NEG = {(q, a): -M.w[q][a] for (q, a) in edges}
    dist: dict[int, Fraction] = {M.init: Fraction(0)}
    pred: dict[int, tuple[int, int]] = {}
    changed = True   # n = 1 時零輪，仍須進偵測掃描（正權自環）
    for _ in range(n - 1):
        changed = False
        for (q, a) in edges:
            if q in dist:
                t = M.step[q][a]
                nd = dist[q] + NEG[(q, a)]
                if t not in dist or nd < dist[t]:
                    dist[t] = nd
                    pred[t] = (q, a)
                    changed = True
        if not changed:
            break   # 整輪不動 = 不動點，之後永不鬆弛 ⟹ 無可達負循環

    relax = None
    if changed:
        for (q, a) in edges:
            t = M.step[q][a]
            if dist[q] + NEG[(q, a)] < dist[t]:   # D 全體此時必有 dist 值
                relax = (q, a)
                break

    reach_w, exit_w = _bfs_words(M, R, C)

    if relax is not None:
        # ── 正循環（原權）偵測命中：第 n 輪仍可嚴格鬆弛。──
        # 套用該鬆弛後沿 pred 走 n 步必落入 pred 循環（設計報告 §1.2：
        # 若 pred 鏈無環則其 ≤ n−1 邊走行與第 n 輪嚴格改進矛盾），
        # 且 pred 循環在取負圖嚴格負 = 原權嚴格正。
        q0, a0 = relax
        t0 = M.step[q0][a0]
        dist[t0] = dist[q0] + NEG[(q0, a0)]
        pred[t0] = (q0, a0)
        x = t0
        for _ in range(n):
            x = pred[x][0]
        cyc_rev: list[tuple[int, int]] = []
        y = x
        while True:
            p, a = pred[y]
            cyc_rev.append((p, a))
            y = p
            if y == x:
                break
        cyc_word = tuple(a for (_p, a) in reversed(cyc_rev))   # 錨 x 出發的前向字
        w_cyc = sum((M.w[p][a] for (p, a) in cyc_rev), Fraction(0))
        if not w_cyc > 0:
            raise EngineError(f"萃取的循環原權 {w_cyc} 非正——pred 無環性論證被違反")
        prefix, suffix = reach_w[x], exit_w[x]
        base = _cost(M, prefix + suffix)                       # k = 0 的成本
        k = max(0, math.ceil(-base / w_cyc))                   # Fraction 精確 ceil
        word = prefix + cyc_word * k + suffix
        v = Verdict("fail", None, FailWitness(word),
                    {"mode": "cycle", "prefix": prefix, "cycle": cyc_word,
                     "pumps": k, "suffix": suffix, "cycle_weight": w_cyc})
        ok, why = verify_fail_witness(M, v.witness)
        if not ok:
            raise EngineError(f"pump 見證自檢失敗：{why}")
        return v

    # ── 無正循環：sup 由 elementary path 達成（Karp 角——此處仍須查
    # 邊界最大值 M* 並與 0 嚴格比較，循環量看不到 α/β 的 boundary 貢獻）。──
    d = {q: M.alpha - dist[q] for q in sorted(D)}
    f = None
    mstar = None
    for q in sorted(D):
        if q in M.accept:
            val = d[q] + M.beta[q]
            if mstar is None or val > mstar:
                f, mstar = q, val
    assert mstar is not None   # init ∈ D ⟹ 語言非空 ⟹ 有 useful 接受態
    if mstar < 0:
        v = Verdict("pass", PassCert(R, C, d), None,
                    {"mode": "boundary", "Mstar": mstar})
        ok, why = verify_pass_cert(M, v.cert)
        if not ok:
            raise EngineError(f"pass 憑證自檢失敗：{why}")
        return v
    # M* ≥ 0：沿 pred 重建 elementary path（收斂後 pred 無環、逐邊 tight，
    # 字成本恰 = M*）。
    path_rev: list[int] = []
    y = f
    while y != M.init:
        p, a = pred[y]
        path_rev.append(a)
        y = p
    word = tuple(reversed(path_rev))
    v = Verdict("fail", None, FailWitness(word),
                {"mode": "boundary", "Mstar": mstar})
    ok, why = verify_fail_witness(M, v.witness)
    if not ok:
        raise EngineError(f"邊界見證自檢失敗：{why}")
    return v


def _cost(M: CostAutomatonPy, word) -> Fraction:
    """定義級成本求值（鏡射 Lean `cost`；引擎與測試共用，驗證器自帶一份）。"""
    q, tot = M.init, Fraction(0)
    for a in word:
        tot += M.w[q][a]
        q = M.step[q][a]
    return M.alpha + tot + M.beta[q]


# ────────────────────────────────────────────────────────────────────
# 憑證自驗（不信引擎主流程：零圖搜尋、只做有限合取的局部檢查；
# B3 的 Lean 驗證書將鏡射此形——P1–P5 是 decide 級 Bool 合取，
# 健全性 P1–P5 ⟹ AllNeg 的證明只用 B1 既有望遠鏡）
# ────────────────────────────────────────────────────────────────────

def verify_pass_cert(M: CostAutomatonPy, cert: PassCert) -> tuple[bool, str]:
    """P1 R 前向封閉（含 init ∈ R）；P2 C 對 R 後向封閉（含 R∩accept ⊆ C）；
    P3 三角 d q + w ≤ d(step q a)（D = R∩C 內邊）；P4 接受態 d q + β q < 0；
    P5 init ∈ D → α ≤ d init。P1/P2 ⟹ D ⊇ Useful，故 P3–P5 覆蓋一切接受走行。"""
    R, C, d = cert.R, cert.C, cert.d
    if not all(0 <= q < M.n_states for q in R | C):
        return False, "R/C 含出界狀態"
    if M.init not in R:
        return False, "P1：init ∉ R"
    for q in sorted(R):
        for a in M.alphabet:
            if M.step[q][a] not in R:
                return False, f"P1：R 非前向封閉（step({q},{a}) = {M.step[q][a]} ∉ R）"
    for q in sorted(R):
        if q in M.accept and q not in C:
            return False, f"P2：接受態 {q} ∈ R 但 ∉ C"
        for a in M.alphabet:
            if M.step[q][a] in C and q not in C:
                return False, f"P2：C 非後向封閉（{q} →{a}→ {M.step[q][a]} ∈ C）"
    D = R & C
    for q in sorted(D):
        if q not in d:
            return False, f"P3/P4 前置：d 在 {q} ∈ R∩C 未定義"
    for q in sorted(D):
        for a in M.alphabet:
            t = M.step[q][a]
            if t in D and not d[q] + M.w[q][a] <= d[t]:
                return False, (f"P3：三角破於 ({q},{a})："
                               f"{d[q]} + {M.w[q][a]} > {d[t]}")
    for q in sorted(D):
        if q in M.accept and not d[q] + M.beta[q] < 0:
            return False, f"P4：接受態 {q} 之 d + β = {d[q] + M.beta[q]} ≥ 0"
    if M.init in D and not M.alpha <= d[M.init]:
        return False, f"P5：α = {M.alpha} > d(init) = {d[M.init]}"
    return True, "P1–P5 全過"


def verify_fail_witness(M: CostAutomatonPy, wit: FailWitness) -> tuple[bool, str]:
    """直接求值（完整檢查）：見證字被接受且成本 ≥ 0。自帶 cost 三行。"""
    q, tot = M.init, Fraction(0)
    for a in wit.word:
        if a not in M.step[q]:
            return False, f"字母 {a} 不在字母表"
        tot += M.w[q][a]
        q = M.step[q][a]
    if q not in M.accept:
        return False, f"見證字終態 {q} 非接受態"
    c = M.alpha + tot + M.beta[q]
    if not c >= 0:
        return False, f"見證字成本 {c} < 0"
    return True, f"接受且成本 {c} ≥ 0"


# ────────────────────────────────────────────────────────────────────
# 已知答案測資 T1–T5（Mneg/Mpos 逐字轉錄 Collatz_FST_B1_Reweighting.lean；
# 變體照設計報告 §5：pass 例定案 = Mpos 取負）
# ────────────────────────────────────────────────────────────────────

def from_b1_toy() -> dict[str, CostAutomatonPy]:
    """B1 玩具機與 B2 變體。

    `Mneg`（Lean 行 513–521）：`0 →ₐ 1`、`1 →ₐ 1`（自環 w −1）、`1 →_b 2`、
    accept {2}、α = 0、β ≡ 0（字母 a = 0、b = 1；其餘轉移收到 2 的自環）。
    `Mpos`（Lean 行 534–550）：`0 →ₐ 1`（w −2）、`1 →ₐ 0`（w 3）、
    `1 →_b 2`（w −1）、`0 →_b 2`（w 0）、accept {2}、α = 5、β(2) = 7。
    `Mpos_neg` = Mpos 之 w/α/β 全取負（設計定案的 pass 例）。
    `Mneg_neg_shift` = Mneg 之 w 取負（自環 +1）再取 α = −5/2
    （覆蓋 k > 0 真 pump 與有理 ceil）。
    `Mempty` = accept 不可達（真空 pass 分支）。"""
    Mneg = mk_automaton(
        3, (0, 1),
        step=[{0: 1, 1: 1}, {0: 1, 1: 2}, {0: 2, 1: 2}],
        w=[{0: 0, 1: 0}, {0: -1, 1: 0}, {0: 0, 1: 0}],
        init=0, accept={2}, alpha=0, beta=[0, 0, 0])
    Mpos = mk_automaton(
        3, (0, 1),
        step=[{0: 1, 1: 2}, {0: 0, 1: 2}, {0: 2, 1: 2}],
        w=[{0: -2, 1: 0}, {0: 3, 1: -1}, {0: 0, 1: 0}],
        init=0, accept={2}, alpha=5, beta=[0, 0, 7])
    Mpos_neg = mk_automaton(
        3, (0, 1),
        step=[dict(s) for s in Mpos.step],
        w=[{a: -x for a, x in wq.items()} for wq in Mpos.w],
        init=0, accept={2}, alpha=-Mpos.alpha, beta=[-b for b in Mpos.beta])
    Mneg_neg_shift = mk_automaton(
        3, (0, 1),
        step=[dict(s) for s in Mneg.step],
        w=[{a: -x for a, x in wq.items()} for wq in Mneg.w],
        init=0, accept={2}, alpha=Fraction(-5, 2), beta=[0, 0, 0])
    Mempty = mk_automaton(
        2, (0,),
        step=[{0: 0}, {0: 1}],
        w=[{0: 0}, {0: 0}],
        init=0, accept={1}, alpha=0, beta=[0, 0])
    return {"Mneg": Mneg, "Mpos": Mpos, "Mpos_neg": Mpos_neg,
            "Mneg_neg_shift": Mneg_neg_shift, "Mempty": Mempty}


def run_known_answers() -> dict[str, Verdict]:
    print("\n=== B2 已知答案 T1–T5（B1 玩具機與變體）===")
    toys = from_b1_toy()

    # T1 Mneg：FAIL 且走 Karp 角——無正循環（自環 −1、accept 零自環
    # 不觸發嚴格偵測）、M* = 0 ≥ 0、邊界路徑重建。
    v1 = decide_all_negative(toys["Mneg"])
    check(v1.kind == "fail" and v1.info["mode"] == "boundary",
          "T1 Mneg：fail（邊界路徑，無正循環——Karp 單獨不足的角）")
    check(v1.info["Mstar"] == 0 and _cost(toys["Mneg"], v1.witness.word) == 0,
          "T1 Mneg：M* = 0、見證字成本 = 0（≥ 0 可驗）")
    check(v1.witness.word == (0, 1), "T1 Mneg：見證字 = [0, 1]（決定性重建）")

    # T2 Mpos（原樣作 B2 輸入）：FAIL——正循環 0→1→0 權 +1；base 已 ≥ 0 ⟹ k = 0。
    v2 = decide_all_negative(toys["Mpos"])
    check(v2.kind == "fail" and v2.info["mode"] == "cycle"
          and v2.info["cycle_weight"] == 1,
          "T2 Mpos：fail（正循環 0→1→0，原權 +1）")
    check(v2.info["pumps"] == 0 and v2.witness.word == (1,)
          and _cost(toys["Mpos"], v2.witness.word) == 12,
          "T2 Mpos：base = 12 已 ≥ 0 ⟹ k = 0、見證字 = [1]")

    # T3 Mpos_neg：設計定案的 pass 例；憑證三值逐項對（含 accept 態零自環
    # 的 tight 三角）。
    v3 = decide_all_negative(toys["Mpos_neg"])
    check(v3.kind == "pass" and v3.info["mode"] == "boundary"
          and v3.info["Mstar"] == -9,
          "T3 Mpos_neg：pass、M* = −9 < 0")
    check(v3.cert.d == {0: Fraction(-5), 1: Fraction(-3), 2: Fraction(-2)}
          and v3.cert.R == v3.cert.C == frozenset({0, 1, 2}),
          "T3 Mpos_neg：憑證 d = {0: −5, 1: −3, 2: −2}、R = C = 全態")
    check(verify_pass_cert(toys["Mpos_neg"], v3.cert)[0],
          "T3 Mpos_neg：verify_pass_cert 綠（P1–P5）")

    # T4 Mneg_neg_shift：真 pump——W_c = 1、base = −5/2 ⟹ k = ⌈5/2⌉ = 3，
    # 見證 [0,0,0,0,1] 成本 1/2；k−1 = 2 時成本 −1/2 < 0（k 最小性；
    # 核准時勘誤：−3/2 是 k = 1 的值）。
    M4 = toys["Mneg_neg_shift"]
    v4 = decide_all_negative(M4)
    check(v4.kind == "fail" and v4.info["mode"] == "cycle"
          and v4.info["pumps"] == 3 and v4.info["cycle_weight"] == 1,
          "T4 Mneg_neg_shift：fail（pump k = 3，有理 ceil ⌈5/2⌉）")
    check(v4.witness.word == (0, 0, 0, 0, 1)
          and _cost(M4, v4.witness.word) == Fraction(1, 2),
          "T4 Mneg_neg_shift：見證字 = [0,0,0,0,1]、成本 = 1/2")
    check(_cost(M4, (0, 0, 0, 1)) == Fraction(-1, 2)
          and _cost(M4, (0, 0, 1)) == Fraction(-3, 2),
          "T4 Mneg_neg_shift：k−1 成本 −1/2 < 0（最小性）、k=1 成本 −3/2")

    # T5 Mempty：真空分支顯式；(R, C, ∅) 憑證過 P1–P5（D = ∅，P3–P5 真空真）。
    v5 = decide_all_negative(toys["Mempty"])
    check(v5.kind == "pass" and v5.info["mode"] == "vacuous"
          and v5.cert.d == {} and v5.cert.R == frozenset({0})
          and v5.cert.C == frozenset({1}),
          "T5 Mempty：真空 pass、憑證 (R = {0}, C = {1}, d = ∅)")
    check(verify_pass_cert(toys["Mempty"], v5.cert)[0],
          "T5 Mempty：verify_pass_cert 綠（P3–P5 真空）")
    return {"T1": v1, "T2": v2, "T3": v3, "T4": v4, "T5": v5}


# ────────────────────────────────────────────────────────────────────
# 負向測試（驗證器必紅：竄改 pass 憑證一值；fail 見證換成本 < 0 的字）
# ────────────────────────────────────────────────────────────────────

def run_negative_tests(verdicts: dict[str, Verdict]) -> None:
    print("\n=== B2 負向測試（驗證器對壞輸入必紅）===")
    toys = from_b1_toy()
    good = verdicts["T3"].cert

    tam1 = PassCert(good.R, good.C, {**good.d, 2: good.d[2] + 10})
    ok1, why1 = verify_pass_cert(toys["Mpos_neg"], tam1)
    check(not ok1 and why1.startswith("P4"),
          f"竄改 d[2] += 10 ⟹ verify_pass_cert 紅（{why1}）")

    tam2 = PassCert(good.R, good.C, {**good.d, 1: good.d[1] - 10})
    ok2, why2 = verify_pass_cert(toys["Mpos_neg"], tam2)
    check(not ok2 and why2.startswith("P3"),
          f"竄改 d[1] −= 10 ⟹ verify_pass_cert 紅（{why2}）")

    ok3, why3 = verify_fail_witness(toys["Mneg"], FailWitness((0, 0, 1)))
    check(not ok3 and "成本" in why3,
          f"fail 見證換成成本 −1 的接受字 [0,0,1] ⟹ verify_fail_witness 紅（{why3}）")

    ok4, why4 = verify_fail_witness(toys["Mneg"], FailWitness((0,)))
    check(not ok4 and "接受" in why4,
          f"fail 見證換成非接受字 [0] ⟹ verify_fail_witness 紅（{why4}）")


# ────────────────────────────────────────────────────────────────────
# oracle 性質測試（固定種子 ⟹ 決定性；方向性判準矩陣見設計報告 §4.2）
# ────────────────────────────────────────────────────────────────────

ORACLE_SEED = 20260828
ORACLE_MACHINES = 300
# 權重格點偏正，讓正循環例出現得夠多（NOTES Q3 要求）。
_WGRID = [Fraction(-2), Fraction(-1), Fraction(-1, 2), Fraction(0),
          Fraction(1, 2), Fraction(1), Fraction(1), Fraction(2)]
# 類別覆蓋門檻：以固定種子實跑一次後寫死（實際分布
# pass 21 / fail-cycle 151 / fail-boundary 33 / vacuous 95）。
_MIN_COVER = {"pass": 15, "cycle": 100, "boundary": 25, "vacuous": 60}


def _random_machine(rng: random.Random) -> CostAutomatonPy:
    n = rng.randint(1, 4)
    k = rng.choice([1, 2, 2, 2])
    ab = tuple(range(k))
    step = [{a: rng.randrange(n) for a in ab} for _ in range(n)]
    w = [{a: rng.choice(_WGRID) for a in ab} for _ in range(n)]
    accept = {q for q in range(n) if rng.random() < 0.5}
    # α/β 自 {−3..3} ∪ 半整數（設計報告 §4.1）
    alpha = Fraction(rng.randint(-6, 6), 2)
    beta = [Fraction(rng.randint(-6, 6), 2) for _ in range(n)]
    return mk_automaton(n, ab, step, w, rng.randrange(n), accept, alpha, beta)


def _oracle_violation(M: CostAutomatonPy, L: int):
    """有界窮舉 oracle：長 ≤ L 的接受字中成本 ≥ 0 者（無則 None）。"""
    for length in range(L + 1):
        for word in itertools.product(M.alphabet, repeat=length):
            q = M.init
            tot = Fraction(0)
            for a in word:
                tot += M.w[q][a]
                q = M.step[q][a]
            if q in M.accept and M.alpha + tot + M.beta[q] >= 0:
                return word
    return None


def run_oracle() -> None:
    print(f"\n=== B2 oracle 性質測試（{ORACLE_MACHINES} 台 ≤ 4 態隨機機、"
          f"種子 {ORACLE_SEED}）===")
    rng = random.Random(ORACLE_SEED)
    counts = {"pass": 0, "cycle": 0, "boundary": 0, "vacuous": 0}
    bad = 0
    for i in range(ORACLE_MACHINES):
        M = _random_machine(rng)
        v = decide_all_negative(M)          # 引擎已自檢輸出；例外即紅
        L = M.n_states + 2                  # elementary path 字長 ≤ |D|−1，留裕度
        viol = _oracle_violation(M, L)
        if v.kind == "pass":
            counts["vacuous" if v.info["mode"] == "vacuous" else "pass"] += 1
            # pass 完備性靠憑證健全性定理；窮舉為防共模 bug 的交叉探針。
            okc, whyc = verify_pass_cert(M, v.cert)
            if not okc or viol is not None:
                bad += 1
                print(BAD + f"機器 #{i}：pass 但 {'憑證紅：' + whyc if not okc else '窮舉違例 ' + str(viol)}")
        else:
            counts[v.info["mode"]] += 1
            okw, whyw = verify_fail_witness(M, v.witness)
            if not okw:
                bad += 1
                print(BAD + f"機器 #{i}：fail 見證紅：{whyw}")
            # 短字（≤ L）無違例的 fail 只可能因需要 pump ⟹ 必為 cycle 模式；
            # 邊界模式的見證本身即長 ≤ n−1 ≤ L 的違例，oracle 必見。
            if viol is None and v.info["mode"] != "cycle":
                bad += 1
                print(BAD + f"機器 #{i}：邊界 fail 但窮舉（L={L}）無違例")
    check(bad == 0, f"{ORACLE_MACHINES} 台逐台通過方向性判準矩陣"
                    "（pass：憑證綠∧窮舉無違例；fail：見證綠∧短字無違例⟹cycle）")
    cover_ok = all(counts[c] >= _MIN_COVER[c] for c in counts)
    check(cover_ok,
          f"四類覆蓋達門檻：pass {counts['pass']}（≥{_MIN_COVER['pass']}）、"
          f"fail-循環 {counts['cycle']}（≥{_MIN_COVER['cycle']}）、"
          f"fail-邊界 {counts['boundary']}（≥{_MIN_COVER['boundary']}）、"
          f"真空 {counts['vacuous']}（≥{_MIN_COVER['vacuous']}）")


# ────────────────────────────────────────────────────────────────────
# 進入點
# ────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--selftest", action="store_true",
                    help="已知答案＋負向測試＋oracle（無旗標時同義；CI 用）")
    ap.parse_args()

    t0 = time.time()
    verdicts = run_known_answers()
    run_negative_tests(verdicts)
    run_oracle()

    print(f"\n耗時 {time.time() - t0:.2f} 秒。")
    if _failures:
        print(f"失敗 {len(_failures)} 項：")
        for f in _failures:
            print("   -", f)
        return 1
    print("全部通過。判定引擎與憑證自驗一致；oracle 判準矩陣全綠。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
