#!/usr/bin/env python3
"""Collatz FST：B3b 差分自動機 D(θ)、B2 引擎全語言重推、θ-LP 圖憑證
（ROADMAP-B B3 第二階段；設計核准 2026-09-04，B3B-DESIGN-REPORT D1–D8）。

B3a 把 A 的 Level 2 單模式 no-go 在**見證集**上重生；本檔把它升到**全語言**——純 tools、
零 Lean（Lean 鏡射為 B3c）。函式庫形：CI 段 `run_checks` 由 `tools/b3_attest.py` §G 呼叫
（`.github` 零變更）；本檔自己的入口只有本機重掃 `--deep`（不進 CI）。它做四件事：

1. **構造器**（§B）`build_diff_automaton`：D = 輸入側 Core Level-2 機器 ×（輸出側**同一台**
   機器，由輸入側發射位 d = outBit 同步驅動、於 K→S 邊界啟動；idle ⟺ 輸入側在 K）× 7 態
   ranking-domain DFA `rdstep`（B0 `lstep` 加 `one` 排除 `[1]`——D2：x = 1 的終態與
   x = 3, 13, 53, … 共用，接受集排除法不成立）。邊權**向量** v = e_{featIdx(out,d)} −
   e_{featIdx(in,b)} ∈ ℤ¹⁸、α = 0；輸入耗盡後輸出側尚欠的 1+p 個零（p = 終態第三分量）是
   終態的確定函數，押進 β（D1）。權重線性於 θ：`instantiate(θ)` 交給 b2 `mk_automaton`，
   `cost_{D(θ)}(extInM x) = θ·ΔF_B(x)`。
2. **成本橋**（§G）：向量形對 x < 8192 全體（ΔF_B 經 b3_attest 的 B 側自含實作），引擎
   通道對固定種子隨機有理 θ（b2_engine `_cost` vs θ·ΔF_B；NOTES Q3 通道分離）。
3. **θ-LP 與圖憑證**（§C–§E）：trim 圖枚舉 simple cycles（328；相異權向量 175）與
   elementary 接受路徑（8269；相異 5140）。∃θ ≥ 0 AllNeg(θ) ⟺ {θ ≥ 0, θ·v(C) ≤ 0,
   θ·w(p) < 0} 可行 ⟺（齊次縮放）{…, θ·w(p) ≤ −1} 可行。自建**精確兩階段單純形**
   （Bland 規則、`fractions.Fraction`、純標準庫）解其 **Farkas 對偶**：對偶可行 ⟹ 原 LP
   不可行、y 即憑證（直接落在循環／路徑生成元）；對偶不可行 ⟹ 其 Farkas 乘子即可行 θ
   （= 保險絲）。**LP 求解器不受信任**：兩種輸出都由呼叫端純有理／純整數驗證（D3）。
   憑證三種：LP 導出（只印不錨）、極小典範**對立對 (25, 315)**、B3a 提升（λ_B 沿走行切環分解）。
4. **引擎 harness**（§F）：θ ≥ 0 樣本 → 引擎全數 fail、見證解碼回奇數 x、直接求值
   D_θ(x) ≥ 0、統計最小見證。

**發現（D5）**：對立對 ΔF_B(25) + ΔF_B(315) = 0——聚合 = 0 的憑證對**任意符號**的 θ 成立，
即 Level 2 單模式無符號線性 ranking 的 2 見證 no-go（`--deep` 另做 x < 2¹⁶ 普查與雙模式觀察）。

    python3 tools/b3b_diff.py          # 本機：CI 段（同 b3_attest §G）
    python3 tools/b3b_diff.py --deep   # 本機：＋向量橋 x < 2^16、對立對普查（單模式＋雙模式觀察）、
                                       #   θ sweep ×200、只留路徑列的對偶 LP（≈ 12 s）

依賴：**純標準庫**；import `tools/b3_attest.py`（B 側語義，不新寫第三套）、`tools/b2_engine.py`。
"""

from __future__ import annotations

import argparse
import random
import sys
import time
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from math import lcm
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import b2_engine as E          # noqa: E402
import b3_attest as B          # noqa: E402

OK, BAD = "  [OK]  ", "  [!!]  "
_failures: list[str] = []


def check(cond: bool, msg: str) -> bool:
    print((OK if cond else BAD) + msg)
    if not cond:
        _failures.append(msg)
    return cond


# ────────────────────────────────────────────────────────────────────
# 錨（設計報告 §3.4／§7／§8；裁決點 D6）
# ────────────────────────────────────────────────────────────────────

EXPECT_REACH, EXPECT_USEFUL, EXPECT_EDGES, EXPECT_ACCEPT = 65, 39, 75, 4
EXPECT_EDGES_BY_LETTER = {0: 27, 1: 28, 2: 20}
EXPECT_ACCEPT_STATES = [((0, 'S', 0), (1, 'S', 0)), ((0, 'S', 1), (1, 'S', 1)),
                        ((0, 'S', 1), (2, 'K', 0)), ((0, 'S', 1), (2, 'S', 0))]
EXPECT_CYCLES, EXPECT_CYCLE_VECS, EXPECT_CYCLE_LEN = 328, 175, (1, 18)
EXPECT_PATHS, EXPECT_PATH_VECS, EXPECT_PATH_LEN = 8269, 5140, (4, 29)
EXPECT_OPP_PAIRS_ELEM = 42                 # 相異 elementary 路徑向量的對立對（無序）
EXPECT_PAIR = (25, 315)                    # 極小典範對立對（D5 三件套入錨）
EXPECT_LIFT = {"paths": 9, "cycles": 5, "sum_nu": 34, "sum_mu": 26, "agg_coord": 17}
EXPECT_LIFT_CYCLES = {681: [2, 2, 2], 877: [3], 983: [7], 1305: [7], 1511: [6]}
EXPECT_LIFT_ELEMENTARY = [231, 323, 403, 551, 1079]
EXPECT_MIN_WITNESS = 3
EXPECT_BOUNDARY_THETAS = {"θ≡1", "θ≡0", "e6", "e13", "K=1/S=2"}
EXPECT_TERMINAL_FAMILY = (1, 3, 13, 53, 213)   # (5·2^j − 1)/3、j 奇：Todd = 5
# x = 3 手算（設計報告 §3.3）：逐步邊權向量與 β 的非零座標
EXPECT_HAND_3 = ([{7: -1}, {13: -1, 7: 1}, {16: -1, 12: 1}, {8: -1, 7: 1}], {6: 1, 12: 1})
EXPECT_HAND_5 = ([{7: -1}, {12: -1}, {7: -1}, {12: -1}, {6: -1, 7: 1}], {6: 1, 12: 1})


# ────────────────────────────────────────────────────────────────────
# §A 字母與 ranking-domain DFA（D2）
# ────────────────────────────────────────────────────────────────────

LETTERS = (0, 1, None)             # some 0、some 1、none


def enc(a) -> int:
    return 2 if a is None else a


def dec(k: int):
    return None if k == 2 else k


def rdstep(s: str, a) -> str:
    """B0 `lstep` 加一態 `one`（恰讀過 `[1]`）：`one` 讀哨兵入 dead ⟹ 拒絕 `[1]`（x = 1），
    其餘與 `lstep` 同。接受語言 = {extInM x : x 奇 ∧ x > 1}（B0 `RankingDomain` 的 DFA 形；
    Lean 端 `rdDFA` 為 B3c）。"""
    if s == 'start':
        return 'one' if a == 1 else 'dead'
    if s == 'one':
        return 'acc' if a == 1 else ('mid' if a == 0 else 'dead')
    return B.lstep(s, a)


# ────────────────────────────────────────────────────────────────────
# §B 構造器（D1）
# ────────────────────────────────────────────────────────────────────

def evec(i: int, sign: int = 1) -> tuple[int, ...]:
    v = [0] * 18
    v[i] = sign
    return tuple(v)


def vadd(u, v) -> tuple[int, ...]:
    return tuple(a + b for a, b in zip(u, v))


def vneg(v) -> tuple[int, ...]:
    return tuple(-a for a in v)


INIT = (B.INIT2, None, 'start')


def diff_step(q, a):
    """D 的一步：q = (輸入側態, 輸出側態|None, rdDFA 態)，回傳 (q′, 邊權向量)。
    輸入側讀 b = unmark a、發射 d = outBit；輸出側 idle 時遇 d = 1（K→S 邊界）啟動——
    自 (1,K,0) 讀 1 並計費；已啟動則讀 d 並計費。"""
    s_in, s_out, ell = q
    b = B.unmark(a)
    d = B.out_bit(s_in[0], b)
    v = evec(B.feat_idx(s_in, b), -1)
    s_in2 = B.step2(s_in, b)
    if s_out is None:
        if s_in[1] == 'K' and d == 1:
            v = vadd(v, evec(B.feat_idx(B.INIT2, 1)))
            s_out2 = B.step2(B.INIT2, 1)
        else:
            s_out2 = None
    else:
        v = vadd(v, evec(B.feat_idx(s_out, d)))
        s_out2 = B.step2(s_out, d)
    return (s_in2, s_out2, rdstep(ell, a)), v


def beta_vec(q) -> tuple[int, ...]:
    """尾聲（D1）：接受態 (in = (0,S,p), out, tail2) 的輸出側再讀 1+p 個零，逐步計費。"""
    s_in, s_out, ell = q
    if ell != 'tail2':
        return tuple([0] * 18)
    u, s = tuple([0] * 18), s_out
    for _ in range(1 + s_in[2]):
        u = vadd(u, evec(B.feat_idx(s, 0)))
        s = B.step2(s, 0)
    return u


@dataclass(frozen=True)
class DiffAutomaton:
    """D 的 θ 無關骨架：狀態 0..n−1（0 = 初態）、字母 {0, 1, 2}、邊權向量、β 向量、接受集。"""
    order: tuple
    idx: dict
    step: tuple
    vec: tuple
    beta: tuple
    accept: frozenset

    @property
    def n(self) -> int:
        return len(self.order)

    def instantiate(self, theta, alpha=Fraction(0)) -> E.CostAutomatonPy:
        """θ ∈ ℚ¹⁸ ↦ b2 格式（權重 θ·v、β = θ·u）。"""
        th = [Fraction(t) for t in theta]
        w = [{a: sum((th[i] * self.vec[q][a][i] for i in range(18)), Fraction(0))
              for a in (0, 1, 2)} for q in range(self.n)]
        bt = [sum((th[i] * self.beta[q][i] for i in range(18)), Fraction(0)) for q in range(self.n)]
        return E.mk_automaton(self.n, (0, 1, 2), self.step, w, 0, self.accept, alpha, bt)

    def vec_cost(self, word) -> tuple[tuple[int, ...], int]:
        """向量成本（Σ 邊權向量 + β(終態)）與終態。"""
        q, tot = 0, tuple([0] * 18)
        for a in word:
            tot = vadd(tot, self.vec[q][a])
            q = self.step[q][a]
        return vadd(tot, self.beta[q]), q

    def run_states(self, word) -> list[int]:
        q, st = 0, [0]
        for a in word:
            q = self.step[q][a]
            st.append(q)
        return st


def build_diff_automaton() -> DiffAutomaton:
    """BFS 可達態（字母序 0, 1, 2；決定性編號）。"""
    idx, order, dq, trans = {INIT: 0}, [INIT], deque([INIT]), {}
    while dq:
        q = dq.popleft()
        for a in LETTERS:
            q2, v = diff_step(q, a)
            if q2 not in idx:
                idx[q2] = len(order)
                order.append(q2)
                dq.append(q2)
            trans[(idx[q], enc(a))] = (idx[q2], v)
    n = len(order)
    step = tuple({a: trans[(i, a)][0] for a in (0, 1, 2)} for i in range(n))
    vec = tuple({a: trans[(i, a)][1] for a in (0, 1, 2)} for i in range(n))
    beta = tuple(beta_vec(q) for q in order)
    accept = frozenset(i for i, q in enumerate(order) if q[2] == 'tail2')
    return DiffAutomaton(tuple(order), idx, step, vec, beta, accept)


def word_of(x: int) -> tuple[int, ...]:
    """extInM x 的引擎編碼。"""
    return tuple(enc(a) for a in B.ext_in_m(x))


def dF(x: int) -> tuple[int, ...]:
    """ΔF_B(x) = F_B(Todd x) − F_B(x)（b3_attest 通道：F_B 與 todd_via_U）。"""
    Fy, Fx = B.F_B(B.todd_via_U(x)), B.F_B(x)
    return tuple(Fy[i] - Fx[i] for i in range(18))


def decode_witness(word) -> int | None:
    """Q6：引擎見證（0/1/2 平坦字）→ x = ofDigits（去兩個哨兵）；須恰為 extInM x，否則 None。"""
    word = tuple(word)
    if len(word) < 3 or word[-2:] != (2, 2) or any(k == 2 for k in word[:-2]):
        return None
    x = sum(b << i for i, b in enumerate(word[:-2]))
    return x if word_of(x) == word else None


# ────────────────────────────────────────────────────────────────────
# §C trim 圖、simple cycles、elementary 接受路徑、走行切環分解
# ────────────────────────────────────────────────────────────────────

def trimmed_graph(D: DiffAutomaton):
    """useful = 可達∧可出（b2 `trim`，與權重無關）；adj 只含 useful 態內的邊。"""
    R, C = E.trim(D.instantiate([1] * 18))
    useful = sorted(R & C)
    Dset = set(useful)
    adj = {q: [(a, D.step[q][a]) for a in (0, 1, 2) if D.step[q][a] in Dset] for q in useful}
    return useful, adj


def simple_cycles(useful, adj) -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    """每個 simple cycle 恰列一次，錨在其最小頂點（只走 > 起點的頂點再回到起點）。
    回傳 (狀態序列, 字母序列)，狀態序列以最小頂點開頭、長度 = 字母數。"""
    out = []
    for v in useful:
        stack = [(v, [v], [])]
        while stack:
            u, path, word = stack.pop()
            for a, t in adj[u]:
                if t == v:
                    out.append((tuple(path), tuple(word + [a])))
                elif t > v and t not in path:
                    stack.append((t, path + [t], word + [a]))
    return out


def elementary_paths(D: DiffAutomaton, useful, adj):
    """初態到接受態的 simple paths（接受態無 useful 出邊，路徑止於首次接受）。
    回傳 (狀態序列含終態, 字母序列)。"""
    out = []
    stack = [(0, [0], [])]
    while stack:
        u, path, word = stack.pop()
        if u in D.accept:
            out.append((tuple(path), tuple(word)))
            continue
        for a, t in adj[u]:
            if t not in path:
                stack.append((t, path + [t], word + [a]))
    return out


def edges_vec(D: DiffAutomaton, states, letters) -> tuple[int, ...]:
    v = tuple([0] * 18)
    for q, a in zip(states, letters):
        v = vadd(v, D.vec[q][a])
    return v


def cycle_vec(D: DiffAutomaton, states, letters) -> tuple[int, ...]:
    return edges_vec(D, states, letters)


def path_vec(D: DiffAutomaton, states, letters) -> tuple[int, ...]:
    """w(p) = Σ 邊權 + β(終態)。"""
    return vadd(edges_vec(D, states, letters), D.beta[states[-1]])


def canon_cycle(states, letters):
    """旋轉到最小頂點開頭（與 `simple_cycles` 的錨定一致）。"""
    k = states.index(min(states))
    return tuple(states[k:] + states[:k]), tuple(letters[k:] + letters[:k])


def decompose_run(D: DiffAutomaton, word):
    """走行 = elementary 路徑 + simple cycles（掃到重複態即切環）。
    回傳 (路徑狀態序列含終態, 路徑字母, [(循環狀態, 循環字母), …])。"""
    states = D.run_states(word)
    st_stack, ed_stack, cycles = [states[0]], [], []
    for a, q2 in zip(word, states[1:]):
        ed_stack.append(a)
        if q2 in st_stack:
            i = st_stack.index(q2)
            cycles.append(canon_cycle(st_stack[i:], ed_stack[i:]))
            st_stack, ed_stack = st_stack[:i + 1], ed_stack[:i]
        else:
            st_stack.append(q2)
    return tuple(st_stack), tuple(ed_stack), cycles


# ────────────────────────────────────────────────────────────────────
# §D 精確兩階段單純形（D3；純標準庫 Fraction、Bland 規則；輸出不受信任、呼叫端驗證）
# ────────────────────────────────────────────────────────────────────

def _pivot(T, r, c):
    pr = T[r]
    pv = pr[c]
    if pv != 1:
        inv = 1 / pv
        T[r] = pr = [v * inv for v in pr]
    for i in range(len(T)):
        if i != r:
            f = T[i][c]
            if f != 0:
                T[i] = [a - f * b for a, b in zip(T[i], pr)]


def feasible_point_or_farkas(A, b):
    """判定 {x ≥ 0 : A x ≤ b}：回傳 ("feasible", x) 或 ("infeasible", y)，
    y ≥ 0 為 Farkas 乘子（yᵀA ≥ 0 逐欄、yᵀb < 0）。第一階段：b_i < 0 的列乘 −1 加人工變數，
    最小化人工變數和；最優值 0 ⟹ 可行；否則最終目標列在鬆弛欄的 reduced cost 即 y
    （rc(s_i) = −π_i·sgn_i = y_i ≥ 0；x 欄 rc_j = Σ_i y_i A_ij ≥ 0；z* = −y·b > 0）。"""
    m, n = len(A), len(A[0])
    bb = [Fraction(v) for v in b]
    neg = [i for i in range(m) if bb[i] < 0]
    art_col = {i: n + m + j for j, i in enumerate(neg)}
    width = n + m + len(neg) + 1
    T, basis = [], []
    for i in range(m):
        sgn = -1 if bb[i] < 0 else 1
        row = [Fraction(0)] * width
        for j in range(n):
            row[j] = sgn * Fraction(A[i][j])
        row[n + i] = Fraction(sgn)
        if i in art_col:
            row[art_col[i]] = Fraction(1)
            basis.append(art_col[i])
        else:
            basis.append(n + i)
        row[-1] = sgn * bb[i]
        T.append(row)
    obj = [Fraction(0)] * width
    for i in neg:
        obj[art_col[i]] = Fraction(1)
    for i in neg:
        obj = [a - c for a, c in zip(obj, T[i])]
    while True:
        enter = next((j for j in range(width - 1) if obj[j] < 0), None)
        if enter is None:
            break
        leave, best = None, None
        for i in range(m):
            if T[i][enter] > 0:
                ratio = T[i][-1] / T[i][enter]
                if best is None or ratio < best or (ratio == best and basis[i] < basis[leave]):
                    leave, best = i, ratio
        if leave is None:
            raise RuntimeError("第一階段無界——不可能（目標 ≥ 0）")
        _pivot(T, leave, enter)
        f = obj[enter]
        obj = [a - f * c for a, c in zip(obj, T[leave])]
        basis[leave] = enter
    if -obj[-1] == 0:
        x = [Fraction(0)] * n
        for i in range(m):
            if basis[i] < n:
                x[basis[i]] = T[i][-1]
        return "feasible", x
    return "infeasible", [obj[n + i] for i in range(m)]


def verify_point(A, b, x) -> bool:
    """純有理：x ≥ 0 且 A x ≤ b。"""
    return all(Fraction(v) >= 0 for v in x) and all(
        sum((Fraction(A[i][j]) * x[j] for j in range(len(x))), Fraction(0)) <= b[i]
        for i in range(len(A)))


def verify_farkas(A, b, y) -> bool:
    """純有理：y ≥ 0、yᵀA ≥ 0 逐欄、yᵀb < 0。"""
    m, n = len(A), len(A[0])
    if len(y) != m or any(v < 0 for v in y):
        return False
    if any(sum((Fraction(y[i]) * A[i][j] for i in range(m)), Fraction(0)) < 0 for j in range(n)):
        return False
    return sum((Fraction(y[i]) * b[i] for i in range(m)), Fraction(0)) < 0


# ────────────────────────────────────────────────────────────────────
# §E θ-LP、圖憑證驗證、對立對、B3a 提升
# ────────────────────────────────────────────────────────────────────

class LPError(AssertionError):
    """單純形輸出未通過呼叫端驗證（求解器不受信任，bug 當場現形）。"""


def _integerize(y):
    L = 1
    for v in y:
        L = lcm(L, Fraction(v).denominator)
    return [int(Fraction(v) * L) for v in y], L


def theta_lp(cycle_vecs, path_vecs):
    """θ-LP {θ ≥ 0, θ·v(C) ≤ 0, θ·w(p) ≤ −1} 經其 Farkas 對偶
    {y ≥ 0, −Σ_j y_j row_j ≤ 0（18 列）, Σ_路徑 y = 1} 判定。
    回傳 ("infeasible", (mu, nu))——整數係數、以向量為鍵、已通過純整數驗證；
    或 ("feasible", θ)——已通過對全部列的驗證（保險絲）。"""
    rows = [tuple(v) for v in cycle_vecs] + [tuple(v) for v in path_vecs]
    nC, nP = len(cycle_vecs), len(path_vecs)
    A_dual = [[-rows[j][i] for j in range(nC + nP)] for i in range(18)]
    A_dual.append([0] * nC + [1] * nP)
    A_dual.append([0] * nC + [-1] * nP)
    b_dual = [0] * 18 + [1, -1]
    kind, w = feasible_point_or_farkas(A_dual, b_dual)
    if kind == "feasible":
        if not verify_point(A_dual, b_dual, w):
            raise LPError("對偶可行點未過驗證")
        yi, _ = _integerize(w)
        mu = {rows[j]: yi[j] for j in range(nC) if yi[j]}
        nu = {rows[j]: yi[j] for j in range(nC, nC + nP) if yi[j]}
        ok, _agg, why = verify_graph_certificate(set(rows[:nC]), set(rows[nC:]), mu, nu)
        if not ok:
            raise LPError(f"對偶頂點整數化後憑證驗證紅：{why}")
        return "infeasible", (mu, nu)
    # 對偶不可行：Farkas 乘子 z = (t₀…t₁₇, s⁺, s⁻)，zᵀA_dual ≥ 0 逐欄 ⟹ 對每列 j：
    # −t·row_j + (s⁺ − s⁻)[j 是路徑] ≥ 0；zᵀb = s⁺ − s⁻ < 0 ⟹ θ := t/(s⁻ − s⁺) 滿足原 LP。
    if not verify_farkas(A_dual, b_dual, w):
        raise LPError("對偶 Farkas 乘子未過驗證")
    s = w[18] - w[19]
    theta = [Fraction(w[i]) / (-s) for i in range(18)]
    if not verify_theta(theta, cycle_vecs, path_vecs):
        raise LPError("由對偶 Farkas 乘子推出的 θ 未過原 LP 驗證")
    return "feasible", theta


def verify_theta(theta, cycle_vecs, path_vecs) -> bool:
    """純有理：θ ≥ 0、θ·v(C) ≤ 0、θ·w(p) ≤ −1。"""
    th = [Fraction(t) for t in theta]
    dot = lambda v: sum((th[i] * v[i] for i in range(18)), Fraction(0))
    return (all(t >= 0 for t in th) and all(dot(v) <= 0 for v in cycle_vecs)
            and all(dot(v) <= -1 for v in path_vecs))


def verify_graph_certificate(cycle_set, path_set, mu: dict, nu: dict):
    """純整數 Farkas（圖形）：係數為正整數、生成元屬枚舉集、聚合 Σμ v(C) + Σν w(p) 逐座標 ≥ 0、
    Σν > 0（θ ≥ 0 錐上：θ·聚合 ≥ 0 而右端 ≤ −Σν < 0）。回傳 (ok, 聚合, 說明)。
    聚合恆零 ⟹ 論證不用 θ ≥ 0——對任意符號 θ 成立（D5）。"""
    for v, c in list(mu.items()) + list(nu.items()):
        if not (isinstance(c, int) and c > 0):
            return False, None, f"係數非正整數：{c}"
    if any(v not in cycle_set for v in mu):
        return False, None, "循環生成元不在枚舉集"
    if any(v not in path_set for v in nu):
        return False, None, "路徑生成元不在枚舉集"
    agg = [0] * 18
    for v, c in list(mu.items()) + list(nu.items()):
        for i in range(18):
            agg[i] += c * v[i]
    if any(a < 0 for a in agg):
        return False, agg, f"聚合有負座標：{agg}"
    if sum(nu.values()) <= 0:
        return False, agg, "Σν = 0（無路徑列，無法得出矛盾）"
    return True, agg, ("聚合恆零（任意符號 θ 皆矛盾）" if not any(agg) else "聚合 ≥ 0 非零")


def opposite_pairs(vec_to_xs: dict):
    """向量類口徑：{v, −v} 皆有實現者的無序對。代表元 = 各類最小 x；依 (max, min) 排序。
    回傳 [(x_小, x_大, v_of_x_小), …]。"""
    out = []
    for v, xs in vec_to_xs.items():
        nv = vneg(v)
        if nv in vec_to_xs and v < nv:
            a, c = xs[0], vec_to_xs[nv][0]
            lo, hi = (a, c) if a <= c else (c, a)
            out.append((hi, lo, (v if a <= c else nv)))
    out.sort()
    return [(lo, hi, v) for hi, lo, v in out]


def lift_b3a(D: DiffAutomaton, W, lam):
    """B3a 見證憑證的圖形提升（Q4）：每條走行切環分解，λ 加到其路徑與循環生成元上。
    回傳 (mu_by_vec, nu_by_vec, 明細, 生成元計數 (路徑, 循環))。"""
    nu_key, mu_key, detail = {}, {}, {}
    for x, l in zip(W, lam):
        ps, pl, cycs = decompose_run(D, word_of(x))
        nu_key[(ps, pl)] = nu_key.get((ps, pl), 0) + l
        for c in cycs:
            mu_key[c] = mu_key.get(c, 0) + l
        detail[x] = {"path_len": len(pl), "cycles": [len(c[1]) for c in cycs]}
    nu, mu = {}, {}
    for (ps, pl), c in nu_key.items():
        v = path_vec(D, ps, pl)
        nu[v] = nu.get(v, 0) + c
    for (cs, cl), c in mu_key.items():
        v = cycle_vec(D, cs, cl)
        mu[v] = mu.get(v, 0) + c
    return mu, nu, detail, (len(nu_key), len(mu_key))


def cycles_only_theta(cycle_vecs, live):
    """負向測試 (ii)：只留循環列、加 Σθ_活 = 1（否則 θ = 0 平凡）——期望可行；回傳 θ 或 None。"""
    rows = [list(v) for v in cycle_vecs]
    rows.append([1 if i in live else 0 for i in range(18)])
    rows.append([-1 if i in live else 0 for i in range(18)])
    rhs = [0] * len(cycle_vecs) + [1, -1]
    kind, w = feasible_point_or_farkas(rows, rhs)
    if kind != "feasible" or not verify_point(rows, rhs, w):
        return None
    return w


# ────────────────────────────────────────────────────────────────────
# §F 引擎 harness
# ────────────────────────────────────────────────────────────────────

HARNESS_SEED = 20260904


def harness_thetas(live, n_random: int = 6, seed: int = HARNESS_SEED):
    rng = random.Random(seed)
    ths = [("θ≡1", [1] * 18), ("θ≡0", [0] * 18)]
    ths += [(f"e{k}", [1 if i == k else 0 for i in range(18)]) for k in live]
    ths += [(f"rand{t}", [Fraction(rng.randint(0, 12), rng.randint(1, 4)) for _ in range(18)])
            for t in range(n_random)]
    ths.append(("K=1/S=2", [1 if (i % 6) < 2 else 2 for i in range(18)]))
    return ths


def run_harness(D: DiffAutomaton, thetas):
    """每組 θ：引擎判定、見證解碼、x 奇且 > 1、D_θ(x) = θ·ΔF_B(x) ≥ 0 且 = 引擎成本。
    回傳 [(名, 判定, 模式, x, 值, 通過)]。"""
    out = []
    for name, th in thetas:
        M = D.instantiate(th)
        v = E.decide_all_negative(M)
        if v.kind != "fail":
            out.append((name, v.kind, v.info.get("mode"), None, None, False))
            continue
        x = decode_witness(v.witness.word)
        thf = [Fraction(t) for t in th]
        if x is None:
            out.append((name, "fail", v.info.get("mode"), None, None, False))
            continue
        d = dF(x)
        val = sum((thf[i] * d[i] for i in range(18)), Fraction(0))
        ok = x % 2 == 1 and x > 1 and val >= 0 and val == E._cost(M, v.witness.word)
        out.append((name, "fail", v.info.get("mode"), x, val, ok))
    return out


# ────────────────────────────────────────────────────────────────────
# §G CI 段（由 b3_attest §G 呼叫；check 由呼叫端注入）
# ────────────────────────────────────────────────────────────────────

def _nz(v) -> dict:
    return {i: c for i, c in enumerate(v) if c}


def _live(cycle_vecs, path_vecs) -> list[int]:
    return [i for i in range(18) if any(v[i] for v in cycle_vecs) or any(v[i] for v in path_vecs)]


def run_checks(check=check) -> dict:
    t0 = time.time()
    # ── G1 構造與手算 ──
    print("\n--- G1 構造器（D1／D2）---")
    D = build_diff_automaton()
    acc_states = sorted((D.order[i][0], D.order[i][1]) for i in D.accept)
    check(D.n == EXPECT_REACH and len(D.accept) == EXPECT_ACCEPT and acc_states == EXPECT_ACCEPT_STATES,
          f"可達 {D.n} 態、接受態 {len(D.accept)}：{acc_states}（輸入分量 = A 的終末態對）")
    S8 = [(1, 'K', 0), (2, 'K', 0), (0, 'S', 0), (0, 'S', 1), (1, 'S', 0), (1, 'S', 1), (2, 'S', 0), (2, 'S', 1)]
    check(sorted({q[0] for q in D.order}) == sorted(S8)
          and all((q[1] is None) == (q[0][1] == 'K') for q in D.order),
          "輸入分量恰為 Core S8 八態；不變量 idle ⟺ 輸入側在 K（全體可達態）")
    for x, expect in ((3, EXPECT_HAND_3), (5, EXPECT_HAND_5)):
        st = D.run_states(word_of(x))
        steps = [_nz(D.vec[q][a]) for q, a in zip(st, word_of(x))]
        check(steps == expect[0] and _nz(D.beta[st[-1]]) == expect[1] and st[-1] in D.accept
              and D.vec_cost(word_of(x))[0] == dF(x),
              f"手算 x = {x}：逐步邊權 {steps}、β {_nz(D.beta[st[-1]])}、總帳 = ΔF_B({x})")
    fam = {x: (D.order[D.run_states(word_of(x))[-1]][0], D.order[D.run_states(word_of(x))[-1]][1])
           for x in EXPECT_TERMINAL_FAMILY}
    check(len(set(fam.values())) == 1 and D.run_states(word_of(1))[-1] not in D.accept
          and all(D.run_states(word_of(x))[-1] in D.accept for x in EXPECT_TERMINAL_FAMILY[1:]),
          f"D2 實況：x ∈ {EXPECT_TERMINAL_FAMILY} 機器終態全同 {fam[1]}；rdDFA 拒 x = 1、收其餘")

    # ── G2 成本橋 ──
    print("\n--- G2 成本橋（Q3 通道分離）---")
    bad = [x for x in range(0, 8192)
           if ((x % 2 == 1 and x > 1) != (D.vec_cost(word_of(x))[1] in D.accept))
           or (x % 2 == 1 and x > 1 and D.vec_cost(word_of(x))[0] != dF(x))]
    check(not bad, f"向量形：x < 8192 全體——接受 ⟺ 奇 ∧ > 1，且向量成本 = ΔF_B（壞例 {bad[:3]}）")
    rng = random.Random(1)
    nbad = 0
    for _ in range(4):
        th = [Fraction(rng.randint(-9, 9), rng.randint(1, 5)) for _ in range(18)]
        M = D.instantiate(th)
        for x in range(3, 2048, 2):
            d = dF(x)
            if E._cost(M, word_of(x)) != sum((th[i] * d[i] for i in range(18)), Fraction(0)):
                nbad += 1
    check(nbad == 0, "引擎通道：4 組隨機有理 θ（含負值）× 奇 x < 2048——b2_engine 成本 = θ·ΔF_B（b3_attest 通道）")

    # ── G3 trim 與枚舉 ──
    print("\n--- G3 trim 圖與枚舉規模 ---")
    useful, adj = trimmed_graph(D)
    edges = [(q, a, t) for q in useful for a, t in adj[q]]
    by_letter = {a: sum(1 for e in edges if e[1] == a) for a in (0, 1, 2)}
    check(len(useful) == EXPECT_USEFUL and len(edges) == EXPECT_EDGES and by_letter == EXPECT_EDGES_BY_LETTER,
          f"trim：useful {len(useful)} 態、邊 {len(edges)}（some0/some1/none = {by_letter}）")
    cycles = simple_cycles(useful, adj)
    paths = elementary_paths(D, useful, adj)
    cyc_vecs = sorted({cycle_vec(D, s, w) for s, w in cycles})
    path_vec_xs: dict = {}
    for s, w in paths:
        path_vec_xs.setdefault(path_vec(D, s, w), []).append(decode_witness(w))
    for v in path_vec_xs:
        path_vec_xs[v].sort()
    pth_vecs = sorted(path_vec_xs)
    clen = (min(len(w) for _, w in cycles), max(len(w) for _, w in cycles))
    plen = (min(len(w) for _, w in paths), max(len(w) for _, w in paths))
    check(len(cycles) == EXPECT_CYCLES and len(cyc_vecs) == EXPECT_CYCLE_VECS and clen == EXPECT_CYCLE_LEN,
          f"simple cycles {len(cycles)}（長 {clen[0]}–{clen[1]}）、相異權向量 {len(cyc_vecs)}")
    check(len(paths) == EXPECT_PATHS and len(pth_vecs) == EXPECT_PATH_VECS and plen == EXPECT_PATH_LEN
          and all(x is not None for xs in path_vec_xs.values() for x in xs),
          f"elementary 接受路徑 {len(paths)}（長 {plen[0]}–{plen[1]}）、相異向量 {len(pth_vecs)}；每條解碼為某 extInM x")
    live = _live(cyc_vecs, pth_vecs)
    check(live == list(range(2, 18)), f"活座標 {live}（0、1 死座標）")

    # ── G4 θ-LP ──
    print("\n--- G4 θ-LP（枚舉形 Farkas 對偶、自建精確單純形、輸出自驗）---")
    t1 = time.time()
    kind, res = theta_lp(cyc_vecs, pth_vecs)
    cset, pset = set(cyc_vecs), set(pth_vecs)
    if kind == "feasible":
        check(False, f"保險絲：θ-LP 可行！θ = {res}（已驗證滿足全部列）——停下回報")
        lp_cert = None
    else:
        mu, nu = res
        ok, agg, why = verify_graph_certificate(cset, pset, mu, nu)
        check(ok, f"θ-LP 不可行（{time.time() - t1:.2f} s）；LP 導出憑證：循環 {len(mu)}、路徑 {len(nu)}、"
                  f"Σν = {sum(nu.values())}、{why}")
        print(f"        LP 憑證（只印不錨）：循環係數 {sorted(mu.values())}、"
              f"路徑 x = {[path_vec_xs[v][0] for v in nu]}、聚合 {agg}")
        lp_cert = (mu, nu)

    # ── G5 對立對（D5 三件套）與 B3a 提升 ──
    print("\n--- G5 憑證：對立對（D5）與 B3a 提升（Q4）---")
    pairs = opposite_pairs(path_vec_xs)
    lo, hi = EXPECT_PAIR
    v_lo = pairs[0][2] if pairs else None
    check(len(pairs) == EXPECT_OPP_PAIRS_ELEM and pairs[0][:2] == EXPECT_PAIR,
          f"相異 elementary 路徑向量的對立對 {len(pairs)} 組；典範極小 = {pairs[0][:2] if pairs else None}")
    ps_lo, _, cyc_lo = decompose_run(D, word_of(lo))
    ps_hi, _, cyc_hi = decompose_run(D, word_of(hi))
    three = (vadd(dF(lo), dF(hi)) == tuple([0] * 18)
             and not cyc_lo and not cyc_hi and ps_lo[-1] in D.accept and ps_hi[-1] in D.accept
             and lo % 2 == 1 and hi % 2 == 1 and lo > 1 and hi > 1)
    check(three, f"三件套：ΔF_B({lo}) + ΔF_B({hi}) = 0（F_B 通道）∧ 兩走行皆 elementary ∧ 皆在域內")
    pair_cert = ({}, {dF(lo): 1, dF(hi): 1})
    ok, agg, why = verify_graph_certificate(cset, pset, *pair_cert)
    check(ok and not any(agg) and sum(pair_cert[1].values()) == 2,
          f"對立對作圖憑證：ν = (1, 1)、零循環、聚合 = 0、Σν = 2 ⟹ 任意符號 θ 皆矛盾（{why}）")
    mu3, nu3, detail, (n_p, n_c) = lift_b3a(D, B.LEAN_B3_W, B.LEAN_B3_LAM)
    ok, agg, why = verify_graph_certificate(cset, pset, mu3, nu3)
    e17 = [0] * 18
    e17[EXPECT_LIFT["agg_coord"]] = 1
    check(ok and agg == e17 and (n_p, n_c) == (EXPECT_LIFT["paths"], EXPECT_LIFT["cycles"])
          and sum(nu3.values()) == EXPECT_LIFT["sum_nu"] and sum(mu3.values()) == EXPECT_LIFT["sum_mu"],
          f"B3a 提升：路徑生成元 {n_p}（Σν {sum(nu3.values())}）、循環生成元 {n_c}（Σμ {sum(mu3.values())}）、"
          f"聚合 = e{EXPECT_LIFT['agg_coord']}（= Lean agg_eq_e17）")
    elem = [x for x in B.LEAN_B3_W if not detail[x]["cycles"]]
    cyc_prof = {x: detail[x]["cycles"] for x in B.LEAN_B3_W if detail[x]["cycles"]}
    check(elem == EXPECT_LIFT_ELEMENTARY and cyc_prof == EXPECT_LIFT_CYCLES,
          f"W₁₀ 切環分解：本身 elementary {elem}；其餘循環長 {cyc_prof}")

    # ── G6 負向測試 ──
    print("\n--- G6 負向測試 ---")
    tam = dict(pair_cert[1])
    tam.pop(dF(lo))
    check(not verify_graph_certificate(cset, pset, {}, tam)[0], "刪對立對一列（ν₂₅ → 0）⟹ 憑證紅")
    tam = {dF(3): 1, dF(hi): 1}
    check(not verify_graph_certificate(cset, pset, {}, tam)[0], "換一列（p₂₅ → p₃）⟹ 憑證紅")
    negc = next(v for v in mu3 if any(c < 0 for c in v))
    tam_mu = dict(mu3)
    tam_mu[negc] += 1
    check(not verify_graph_certificate(cset, pset, tam_mu, nu3)[0], "B3a 提升憑證一個循環係數 +1 ⟹ 聚合出現負座標、紅")
    th_c = cycles_only_theta(cyc_vecs, live)
    b6 = all(v[6] == 0 and v[13] == 0 for v in cyc_vecs)
    check(th_c is not None and all(sum((th_c[i] * v[i] for i in range(18)), Fraction(0)) <= 0 for v in cyc_vecs)
          and b6,
          f"去掉路徑列（＋Σθ_活 = 1）⟹ LP 可行：θ = {_nz(th_c) if th_c else None}；邊界座標 6/13 在所有循環向量為 0")
    ok, agg, why = verify_graph_certificate(set(), pset, {}, pair_cert[1])
    check(ok, "去掉循環列 ⟹ 仍不可行（對立對只用路徑列）——障礙完全住在邊界（路徑）結構")

    # ── G7 harness ──
    print("\n--- G7 B2 引擎 harness（θ ≥ 0 樣本全數 fail、見證解碼、直接求值）---")
    rec = run_harness(D, harness_thetas(live))
    allfail = all(k == "fail" and ok for _, k, _, _, _, ok in rec)
    minw = min(x for _, _, _, x, _, _ in rec if x is not None)
    bnd = {n for n, _, m, _, _, _ in rec if m == "boundary"}
    check(allfail and len(rec) == 25, f"{len(rec)} 組 θ ≥ 0 全數 fail；每個見證解碼為奇數 x > 1、D_θ(x) ≥ 0 且 = 引擎成本")
    check(minw == EXPECT_MIN_WITNESS and bnd == EXPECT_BOUNDARY_THETAS,
          f"最小見證 x = {minw}；boundary 模式恰 {sorted(bnd)}，其餘 {len(rec) - len(bnd)} 組 cycle 模式")
    big = max(x for _, _, _, x, _, _ in rec if x is not None)
    print(f"        最大見證 x = {big}（{big.bit_length()} 位 pump 字）；G 段耗時 {time.time() - t0:.2f} s")
    return {"D": D, "useful": useful, "adj": adj, "cyc_vecs": cyc_vecs, "pth_vecs": pth_vecs,
            "path_vec_xs": path_vec_xs, "live": live, "pairs": pairs, "lp_cert": lp_cert, "time": time.time() - t0}


# ────────────────────────────────────────────────────────────────────
# §H --deep（本機重掃；不進 CI）
# ────────────────────────────────────────────────────────────────────

MODE_IDX_B = 13    # B 座標 (2,K,0,1) = A 的 MODE_IDX_L2 = 5 經 σ（b3_attest §D）


def two_mode_delta(x: int, affine: bool = False) -> tuple[int, ...]:
    """A 側 `two_mode_delta` 的 B 座標形：區塊 m(y) 加 F_B(y)、區塊 m(x) 減 F_B(x)，m = F_B[13]。
    affine=True 另附 (e_{m(y)} − e_{m(x)}) 兩座標（每模式截距 β_m 的差分）。"""
    y = B.todd_via_U(x)
    Fx, Fy = B.F_B(x), B.F_B(y)
    mx, my = int(Fx[MODE_IDX_B] == 1), int(Fy[MODE_IDX_B] == 1)
    d = [0] * 36
    for i in range(18):
        d[my * 18 + i] += Fy[i]
        d[mx * 18 + i] -= Fx[i]
    if affine:
        e = [0, 0]
        e[my] += 1
        e[mx] -= 1
        d += e
    return tuple(d)


def _census(vec_fn, N: int, label: str):
    tbl: dict = {}
    for x in range(3, N, 2):
        tbl.setdefault(vec_fn(x), []).append(x)
    pairs = opposite_pairs(tbl)
    print(f"        {label}：x < {N} 相異向量 {len(tbl)}、對立對（向量類口徑）{len(pairs)}"
          f"；最小 {[p[:2] for p in pairs[:3]]}")
    return tbl, pairs


def run_deep(ctx: dict) -> None:
    D, cyc_vecs, pth_vecs, live = ctx["D"], ctx["cyc_vecs"], ctx["pth_vecs"], ctx["live"]
    N = 1 << 16
    print(f"\n=== --deep（本機）===")
    t0 = time.time()
    bad = [x for x in range(3, N, 2) if D.vec_cost(word_of(x))[0] != dF(x)]
    check(not bad, f"向量橋 x < 2^16 全體奇數（{time.time() - t0:.1f} s）")
    t0 = time.time()
    tbl1, pairs1 = _census(dF, N, "單模式 ΔF_B（18 維）")
    check(pairs1[0][:2] == EXPECT_PAIR and len(pairs1) >= EXPECT_OPP_PAIRS_ELEM,
          f"單模式普查：典範極小對立對 = {pairs1[0][:2]}（{time.time() - t0:.1f} s）")
    t0 = time.time()
    tbl2, pairs2 = _census(two_mode_delta, N, "雙模式差分（36 維、m = F_B[13]）")
    tbl3, pairs3 = _census(lambda x: two_mode_delta(x, affine=True), N, "雙模式仿射差分（38 維）")
    print(f"        觀察層（不入錨）：雙模式對立對 {'存在' if pairs2 else '不存在'}"
          f"（x < 2^16）；仿射 {'存在' if pairs3 else '不存在'}；{time.time() - t0:.1f} s")
    if pairs2:
        lo, hi, _ = pairs2[0]
        print(f"        雙模式最小對立對 ({lo}, {hi})：模式 m = {B.F_B(lo)[MODE_IDX_B]}/{B.F_B(hi)[MODE_IDX_B]}"
              f" → {B.F_B(B.todd_via_U(lo))[MODE_IDX_B]}/{B.F_B(B.todd_via_U(hi))[MODE_IDX_B]}")
        import certificates as A      # A 側複核（觀察層；σ 無關：兩向量之和為零）
        sA = A.two_mode_delta(lo, A.F2, A.MODE_IDX_L2, 18) + A.two_mode_delta(hi, A.F2, A.MODE_IDX_L2, 18)
        check(int(abs(sA).sum()) == 0 and two_mode_delta(lo, True) == vneg(two_mode_delta(hi, True)),
              f"雙模式對立對 ({lo}, {hi})：A 側 two_mode_delta 之和亦為零；仿射 38 維亦對立（截距差對消）")
    t0 = time.time()
    rng = random.Random(HARNESS_SEED + 1)
    ths = [(f"sweep{t}", [Fraction(rng.randint(0, 20), rng.randint(1, 6)) for _ in range(18)]) for t in range(200)]
    rec = run_harness(D, ths)
    xs = sorted(x for _, _, _, x, _, _ in rec if x is not None)
    modes = {m: sum(1 for _, _, mm, _, _, _ in rec if mm == m) for m in ("boundary", "cycle")}
    check(all(k == "fail" and ok for _, k, _, _, _, ok in rec),
          f"θ sweep ×200 全數 fail（{time.time() - t0:.1f} s）；見證 x 中位數 {xs[len(xs) // 2]}、最大 {xs[-1]}、模式 {modes}")
    t0 = time.time()
    kind, res = theta_lp([], pth_vecs)
    check(kind == "infeasible", f"只留路徑列的對偶 LP：{kind}（{time.time() - t0:.1f} s）；"
                                f"憑證路徑 {len(res[1]) if kind == 'infeasible' else '-'} 條")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--deep", action="store_true", help="本機重掃：向量橋 x < 2^16、對立對普查（含雙模式觀察）、θ sweep、只留路徑列 LP")
    args = ap.parse_args()
    t0 = time.time()
    print("=== B3b 差分自動機 D(θ)：CI 段（與 b3_attest §G 相同）===")
    ctx = run_checks(check)
    if args.deep:
        run_deep(ctx)
    print(f"\n耗時 {time.time() - t0:.2f} 秒。")
    if _failures:
        print(f"失敗 {len(_failures)} 項：")
        for f in _failures:
            print("   -", f)
        return 1
    print("全部通過。差分自動機成本橋、θ-LP 不可行憑證（三種）、負向測試、引擎 harness 一致。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
