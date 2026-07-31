"""從 l3_recon.py 的錨資料生成 Collatz_FST_L3_DimUpper.lean（上界 ≤ 31）
與 Collatz_FST_L3_DimLower.lean（下界 ≥ 31 + 維度定理 = 31）。

用法：python3 tools/gen_l3dim.py   （路徑相對 __file__，任何 checkout 可跑；
輸出應與 repo 中的兩個 Lean 檔逐位一致——這是審查時的再生性測試）

## 踩過的坑（改生成器前先讀）

1. **裸 `LinearMap.proj j` 不能用**：索引型別會被推成 ℕ，typeclass 卡死
   （`(i : ℕ) → Module ?m (?m i)`）。解法：完全定型的
   `private abbrev pr (j : Fin 96) : (Fin 96 → ℚ) →ₗ[ℚ] ℚ := LinearMap.proj j`。
2. **`Matrix.cons_val'` 在本版 Mathlib 不存在**；且對 65/96 深的 `![...]`
   字面值做 simp 索引化簡效能極差。解法：完全不用 simp——
   membership 65 個目標用 `show`-defeq 落到 dF96 原子層（vecCons 在字面索引上
   是 rfl 級化約，LinearMap 的 +/− application 也是）。
3. **單射證明要走「全數字原子」模式**（Level 2 DimUpper 的教訓）：
   先把 hR/hz 轉成數字索引的 have（`have c9 : v 9 = 0 := …` 由 defeq 接受），
   linarith 只見一致的數字原子；最後 `fin_cases j` 96 個 `exact`。
   混用 `⟨j,⋯⟩` 與數字形式會讓 linarith 把同一座標當不同原子。
4. **heartbeats**：單射那條要 `set_option maxHeartbeats 3200000`
   （成本在深索引 defeq 的 whnf/isDefEq，不在 linarith 搜尋；單檔 ~19s）。
5. 每個 linarith 的提示集要含全部 24 條流關係 + 相關座標零事實
   （rel_coords ∩ known 的交集裁剪）。
6. **ℚ 上的 `decide` 要加 `+kernel`**（下界見證值引理的教訓，探針實測）：
   elaborator 端的化約會卡在 Mathlib 的 ℚ 實例鏈（`Rat.sub` 的結構投影
   打不開，`instDecidableEqRat` 停在 match），`decide` 直接報 stuck；
   kernel 端不吃 `irreducible` 且 `Nat.gcd` 有內建加速，
   `simp only [展開 + Todd 改寫] ; decide +kernel` 一條 1 秒內過。
   `Todd`（`padicValNat`）不可 kernel 求值，**必須先用 `Todd_w` 引理換掉**。
7. 下界的純量讀出（`v_t_i`）靠 defeq 從 row 引理取：`freeIdx96 t`、
   `![...] t` 在字面索引上都是 whnf 級化約，宣告時直接
   `private lemma v_t_i : dFQ96 w (J : Fin 96) = a := row_w t` 即可。
   之後 `rw [v_t_0, …, v_t_30] at h_t` 全是字面原子，`linear_combination`
   直接吃，不經過任何深向量 simp（坑 2 的迴避在下界同樣適用）。

## 下界的資料與證明結構（本檔第二段生成）

- 資料全在 l3_recon.py：`LEAN_L3_WITNESSES`（31 見證）、`LEAN_L3_WITNESS_INV`
  （么模逆 B，max|B|=3）、`LEAN_L3_FREE_IDX`。生成前以純整數再驗一次
  `Mw·B = B·Mw = I` 與 `3w+1 = 2^v·y`（不靠 sympy 的獨立對帳）。
- 生成物：31 條 `Todd_w`（padicValNat 模式，同 L3_2Mode_NoGo）；
  `wit31`／`dFW96 i := dFQ96 (wit31 i)`；31 條 row 引理（坑 6）；
  961 條純量讀出（坑 7）；`sum_fin_31`（仿 Level 2 sum_fin_ten，
  `Fin.sum_univ_succ` 會留 `Fin.succ` 原子，故包成私有引理 `simp ; ring`）；
  線性獨立經 `Fintype.linearIndependent_iff`，31 條方程 h_t 取自由座標
  evaluation，**每個 `g i = 0` 用 `linear_combination Σₜ B[t][i]·hₜ`
  （orientation：gᵀMw = 0 ⇒ gᵀ = (gᵀMw)·B），不要 linarith**
  （31 元 31 式會撞牆）；收尾 `finrank_span_eq_card` +
  `Submodule.finrank_mono` + `le_antisymm`，照抄 Level 2 DimLower 的骨架。
"""
import importlib.util
from pathlib import Path
_HERE = Path(__file__).resolve().parent          # tools/
spec = importlib.util.spec_from_file_location("l3", str(_HERE / "l3_recon.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
R = m.reachable(); TERM = m.LEAN_L3_TERMINALS
FREE = m.LEAN_L3_FREE_IDX; RECON = m.LEAN_L3_RECONSTRUCTION
KEYS3 = m.KEYS3; INIT = (1,'K',0,0)

def lkey(k):
    (c,P,h2,h1),b = k
    return f"((({c} : ℕ), Phase.{P}, ({h2} : ℕ), ({h1} : ℕ)), {b})"
def lstate(g):
    c,P,h2,h1 = g
    return f"(({c} : ℕ), Phase.{P}, ({h2} : ℕ), ({h1} : ℕ))"
def dterm(j):
    return f"dF96 x {j//48} {lkey(KEYS3[j%48])}"

# 65 條關係（順序同 l3_recon rels65）：fam0⊕0 (31) + 0⊕fam0 (31) + e33 + e64 + fstart
dead_idx = [i for i,k in enumerate(KEYS3) if k[0] not in R]          # 20
clean_states = [g for g in R if tuple(g) not in [tuple(t) for t in TERM] and g != INIT]  # 11
def flow_coords(g):
    ins = [i for i,k in enumerate(KEYS3) if k[0] in [tuple(r) for r in R] and m.step3(k[0],k[1])==g]
    outs = [KEYS3.index((g,0)), KEYS3.index((g,1))]
    return ins, outs

rels = []   # (kind, data)
for j in dead_idx: rels.append(("proj", j))
for g in clean_states: rels.append(("flow", (0, g)))
for j in dead_idx: rels.append(("proj", j+48))
for g in clean_states: rels.append(("flow", (1, g)))
rels.append(("proj", 33)); rels.append(("proj", 48+16))
rels.append(("fstart", None))
assert len(rels)==65

def phi_entry(kind, data):
    P = "pr"
    if kind=="proj":
        return f"{P} {data}"
    if kind=="flow":
        b,g = data; ins,outs = flow_coords(g)
        s = " + ".join(f"{P} {i+48*b}" for i in ins)
        return f"({s} - {P} {outs[0]+48*b} - {P} {outs[1]+48*b})"
    # fstart：in(32) − out16 − out17，兩區塊相加
    ins,outs = flow_coords(INIT)
    parts = [f"{P} {i+48*b}" for b in (0,1) for i in ins]
    negs  = [f"{P} {o+48*b}" for b in (0,1) for o in outs]
    return f"({' + '.join(parts)} - " + " - ".join(negs) + ")"

phi_lines = ",\n    ".join(phi_entry(k,d) for k,d in rels)

# dFQ96_mem_Sol 的 65 個 tactic block
blocks = []
for k,d in rels:
    if k=="proj":
        j=d; b=j//48; key=KEYS3[j%48]
        if key[0] not in R:
            blocks.append(f"· show {dterm(j)} = 0\n    exact dF96_dead x {b} (by decide) {key[1]}")
        elif j==33:
            blocks.append(f"· show {dterm(j)} = 0\n    exact dF96_block0_mode x")
        else:
            blocks.append(f"· show {dterm(j)} = 0\n    exact dF96_block1_exit x")
    elif k=="flow":
        b,g = d; ins,outs = flow_coords(g)
        insL = "[" + ", ".join(lkey(KEYS3[i]) for i in ins) + "]"
        expr = " + ".join(dterm(i+48*b) for i in ins) + f" - {dterm(outs[0]+48*b)} - {dterm(outs[1]+48*b)}"
        blocks.append(
f"""· have h := dF96_flow_clean x {b} {lstate(g)} (by decide) (by decide) (by decide)
    simp only [show inEdges3 {lstate(g)} = {insL} from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show {expr} = 0
    linarith [h]""")
    else:
        ins,outs = flow_coords(INIT)
        expr = " + ".join(dterm(ins[0]+48*b) for b in (0,1))
        expr += " - " + " - ".join(dterm(o+48*b) for b in (0,1) for o in outs)
        blocks.append(
f"""· show {expr} = 0
    linarith [dF96_fstart x]""")
mem_blocks = "\n  ".join(blocks)

# 單射證明：全數字原子。r{t} = 流關係、c{j} = 座標零，最後 fin_cases 全 exact
free_lookup = {j: i for i, j in enumerate(FREE)}
flow_rel_idx = [i for i,(k,_) in enumerate(rels) if k in ("flow","fstart")]
rhaves = []
for t in flow_rel_idx:
    k,d = rels[t]
    if k == "flow":
        b,g = d; ins,outs = flow_coords(g)
        expr = " + ".join(f"v {i+48*b}" for i in ins) + f" - v {outs[0]+48*b} - v {outs[1]+48*b}"
    else:
        ins,outs = flow_coords(INIT)
        expr = " + ".join(f"v {ins[0]+48*b}" for b in (0,1))
        expr += " - " + " - ".join(f"v {o+48*b}" for b in (0,1) for o in outs)
    rhaves.append(f"  have r{t} : {expr} = 0 := hR {t}")
chaves = []
for j in range(96):
    if j in free_lookup:
        chaves.append(f"  have c{j} : v {j} = 0 := hz {free_lookup[j]}")
    else:
        pk = next((idx for idx,(k,d) in enumerate(rels) if k=="proj" and d==j), None)
        if pk is not None:
            chaves.append(f"  have c{j} : v {j} = 0 := hR {pk}")
rel_coords = {}
for t in flow_rel_idx:
    k,d = rels[t]
    if k == "flow":
        b,g = d; ins,outs = flow_coords(g)
        rel_coords[t] = {i+48*b for i in ins} | {o+48*b for o in outs}
    else:
        ins,outs = flow_coords(INIT)
        rel_coords[t] = {i+48*b for b in (0,1) for i in ins} | {o+48*b for b in (0,1) for o in outs}
known = set(free_lookup) | {d for k,d in rels if k=="proj"}
for j in sorted(RECON):
    touching = [t for t in flow_rel_idx]   # 全部關係（линarith 自選組合）
    coords = set().union(*(rel_coords[t] for t in touching)) & known
    hints = ", ".join([f"r{t}" for t in touching] + [f"c{i}" for i in sorted(coords)])
    chaves.append(f"  have c{j} : v {j} = 0 := by linarith [{hints}]")
fin96 = "\n  ".join(f"· exact c{j}" for j in range(96))
inj_body = "\n".join(rhaves) + "\n" + "\n".join(chaves)
print(f"linarith 目標數 = {len(RECON)}")
FREE_L = ", ".join(str(j) for j in FREE)
lean = f"""/-
# Level 3 上界：`dim span(dF96) ≤ 31`（ROADMAP A-3 Level 3 收官上半）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_L3_Delta.lean`（§73–78）。
本檔由 §73–78 的 65 條泛函打包出解空間並讀出上界，與 Level 2 `DimUpper` 同構。
資料面（自由座標、關係列表）與 `tools/l3_recon.py` ⑦ 的錨常數一致（CI 對帳）。

本檔為**機械生成**（`tools/` 錨資料 → Lean 字面值），維護時改生成器不改手寫。
關係的 65 個泛函用 `LinearMap.proj` 的加減組合——線性**免證**（LinearMap 代數）。

## 不在本檔範圍

下界（31 見證 + 么模逆 B 的 `linear_combination`）與 `dim = 31` 收官——下一步。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_Delta
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace CollatzFST.L3

open CollatzFST

/-! ## §79 96 維打包與 65 條關係 -/

/-- `dF96` 的 `Fin 96` 打包：座標 `j` = 區塊 `j/48`、key `KEYS3[j % 48]`。 -/
def dFQ96 (x : ℕ) : Fin 96 → ℚ := fun j =>
  dF96 x (j.val / 48) (KEYS3.getD (j.val % 48) (((0 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0))

/-- 座標投影（完全定型，避免 `proj` 的索引型別被推成 ℕ）。 -/
private abbrev pr (j : Fin 96) : (Fin 96 → ℚ) →ₗ[ℚ] ℚ := LinearMap.proj j

/-- 65 條泛函（`pr` 的加減組合，線性免證）。順序同 `tools/l3_recon.py` 的
`rels65`：31 條區塊 0 提升（20 死 + 11 乾淨流）、31 條區塊 1 提升、
`θ₀[33]`、`θ₁[16]`、`f_start` 跨區塊。 -/
def phi65 : Fin 65 → ((Fin 96 → ℚ) →ₗ[ℚ] ℚ) :=
  ![{phi_lines}]

/-- 解空間：65 條關係切出的核。 -/
def Sol96 : Submodule ℚ (Fin 96 → ℚ) := LinearMap.ker (LinearMap.pi phi65)

lemma mem_Sol96_iff (v : Fin 96 → ℚ) : v ∈ Sol96 ↔ ∀ k, phi65 k v = 0 := by
  rw [Sol96, LinearMap.mem_ker]
  constructor
  · intro h k; exact congrFun h k
  · intro h; funext k; exact h k

/-! ## §80 每個 dFQ96 都落在解空間 -/

theorem dFQ96_mem_Sol (x : ℕ) : dFQ96 x ∈ Sol96 := by
  rw [mem_Sol96_iff]
  intro k
  fin_cases k
  {mem_blocks}

/-! ## §81 上界 -/

/-- 31 個自由座標（`tools/l3_recon.py` 的 `LEAN_L3_FREE_IDX`）。 -/
def freeIdx96 : Fin 31 → Fin 96 := ![{FREE_L}]

def pick96 : (Fin 96 → ℚ) →ₗ[ℚ] (Fin 31 → ℚ) := LinearMap.funLeft ℚ ℚ freeIdx96

set_option maxHeartbeats 3200000 in
theorem pick96_injective_on_Sol : Function.Injective (pick96.domRestrict Sol96) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨v, hv⟩ hker
  have hR := (mem_Sol96_iff v).mp hv
  have hz : ∀ i : Fin 31, v (freeIdx96 i) = 0 := fun i => congrFun hker i
{inj_body}
  apply Subtype.ext
  funext j
  fin_cases j
  {fin96}

theorem finrank_Sol96_le : Module.finrank ℚ Sol96 ≤ 31 := by
  have h := LinearMap.finrank_le_finrank_of_injective pick96_injective_on_Sol
  simpa using h

/-- **上界定理**：Level 3 雙模式差分生成空間至多 **31 維**（96 維中）。 -/
theorem finrank_span_dFQ96_le :
    Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ96)) ≤ 31 :=
  le_trans
    (Submodule.finrank_mono
      (Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact dFQ96_mem_Sol x)))
    finrank_Sol96_le

end CollatzFST.L3
"""
out = _HERE.parent / "Lean4RealConstruction" / "ProjectA" / "Collatz_FST_L3_DimUpper.lean"
out.write_text(lean, encoding="utf-8")
print("生成", out, f"（{lean.count(chr(10))} 行）")

# ════════════════════════════════════════════════════════════════════
# 第二段：下界 Collatz_FST_L3_DimLower.lean（§82–88）
# ════════════════════════════════════════════════════════════════════
W = m.LEAN_L3_WITNESSES
B = m.LEAN_L3_WITNESS_INV
Mw = [[m.two_mode(w)[j] for j in FREE] for w in W]     # 31×31 自由座標投影


def _vp(n):
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


pairs = [(w, m.todd(w), _vp(3 * w + 1)) for w in W]

# 純整數對帳（不靠 sympy 的獨立檢查；l3_recon ⑦ 用 sympy 又驗一次）
_I = [[int(i == k) for k in range(31)] for i in range(31)]
assert [[sum(Mw[i][t] * B[t][k] for t in range(31)) for k in range(31)]
        for i in range(31)] == _I, "Mw·B ≠ I"
assert [[sum(B[i][t] * Mw[t][k] for t in range(31)) for k in range(31)]
        for i in range(31)] == _I, "B·Mw ≠ I"
assert all(3 * w + 1 == 2 ** v * y and y % 2 == 1 for w, y, v in pairs), "Todd 分解錯"


def _wrap(items, indent, sep=", ", width=96):
    """以 sep 接起 items，行寬超過 width 就換行（續行縮排 indent）。"""
    lines, cur = [], None
    for it in items:
        cand = it if cur is None else cur + sep + it
        if cur is not None and len(indent) + len(cand) > width:
            lines.append(cur + sep.rstrip())
            cur = it
        else:
            cur = cand
    lines.append(cur or "")
    return ("\n" + indent).join(lines)


# §82 Todd 求值（同 L3_2Mode_NoGo 的模式）
todd_lemmas = "\n".join(
    f"""private lemma Todd_{w} : Todd {w} = {y} := by
  have hv : padicValNat 2 (3 * {w} + 1) = {v} := by
    rw [show (3 * {w} + 1 : ℕ) = 2 ^ {v} * {y} by norm_num]
    exact padicValNat_two_pow_mul (by norm_num) (by decide)
  unfold Todd
  rw [hv]
  norm_num""" for w, y, v in pairs)

# §84 row 引理：每個見證在 31 個自由座標上的值，一條 decide +kernel
row_lemmas = "\n".join(
    f"""private lemma row_{w} : ∀ t : Fin 31, dFQ96 {w} (freeIdx96 t) =
    ({_wrap(['![' + str(Mw[i][0])] + [str(c) for c in Mw[i][1:-1]]
             + [str(Mw[i][-1]) + ']'], indent='      ')} : Fin 31 → ℚ) t := by
  simp only [dFQ96, dF96, E3, mode3, Todd_{w}]
  decide +kernel""" for i, (w, y, v) in enumerate(pairs))

# §85 純量讀出（defeq 取值；坑 7）
scalar_lemmas = []
for t, J in enumerate(FREE):
    scalar_lemmas.append(f"-- 自由座標 {t}（96 維索引 {J}）")
    for i, (w, _, _) in enumerate(pairs):
        scalar_lemmas.append(
            f"private lemma v_{t}_{i} : dFQ96 {w} ({J} : Fin 96) = {Mw[i][t]} := row_{w} {t}")
scalar_block = "\n".join(scalar_lemmas)

# §87 線性獨立
e_body = _wrap([f"g {i} * dFQ96 {w} j" for i, (w, _, _) in enumerate(pairs)],
               indent="        ", sep=" + ")
h_insts = "\n".join(f"  have h{t} := e ({J} : Fin 96)" for t, J in enumerate(FREE))
rw_blocks = "\n".join(
    "  rw [" + _wrap([f"v_{t}_{i}" for i in range(31)], indent="    ") + f"] at h{t}"
    for t in range(31))
g_blocks = []
for i in range(31):
    parts = []
    for t in range(31):
        c = B[t][i]
        if c == 0:
            continue
        mag = f"h{t}" if abs(c) == 1 else f"{abs(c)} * h{t}"
        parts.append(("-" if c < 0 else "") + mag if not parts
                     else ("- " if c < 0 else "+ ") + mag)
    g_blocks.append(f"  have g{i} : g {i} = 0 := by\n    linear_combination "
                    + _wrap(parts, indent="      ", sep=" "))
g_block = "\n".join(g_blocks)

lean_lower = f"""/-
# Level 3 下界與維度定理：`dim span(dF96) = 31`（ROADMAP A-3 Level 3 收官）

Mathlib rev c66c0c58（Lean v4.28.0-rc1）。承接 `Collatz_FST_L3_DimUpper.lean`（§79–81）。

上界 `≤ 31` 已由 65 條差分層泛函給出（`finrank_span_dFQ96_le`）。本檔補下界：
31 個具體見證（`tools/l3_recon.py` 的 `LEAN_L3_WITNESSES`，貪心取最小奇數）
投影到 §81 那 31 個自由座標（`freeIdx96`）構成 31×31 可逆矩陣——
行列式 = **1**（么模；比 Level 2 的 31 更乾淨），其整數逆矩陣 `B`
（max |B| = 3）錨在 `LEAN_L3_WITNESS_INV`。

與 Level 2 `DimLower` 的差異：31 元 31 式不餵 `linarith`（搜尋成本對變數數
敏感），每個 `g i = 0` 直接給方程的顯式整數組合 `g i = Σₜ B[t][i]·hₜ`，
一行 `linear_combination`——由 `Mw·B = I`（CI 對帳）保證恰好回到 `g i`。

見證值引理走 `simp only [展開 + Todd 改寫] ; decide +kernel`：
elaborator 端的化約會卡在 Mathlib 的 ℚ 實例鏈（`Rat.sub` 的結構投影），
kernel 端不吃 `irreducible` 且 `Nat.gcd` 有內建加速。
`Todd`（`padicValNat`）不可 kernel 求值，必須先用 `Todd_w` 引理換掉。

本檔為**機械生成**（`tools/gen_l3dim.py`，錨資料同 `l3_recon.py` ⑦，
CI 重生成並 diff），維護時改生成器不改手寫。

## 主定理

`finrank_span_dFQ96_eq_31 : Module.finrank ℚ (span ℚ (Set.range dFQ96)) = 31`

即 HandOver「Level 3 雙模式有效差分生成空間 = 31 維（不是 96）」的形式化。
-/
import Lean4RealConstruction.ProjectA.Collatz_FST_L3_DimUpper
import Mathlib.Tactic.LinearCombination

namespace CollatzFST.L3

open CollatzFST

/-! ## §82 31 個見證的 Todd 求值 -/

{todd_lemmas}

/-! ## §83 見證族 -/

/-- 31 個下界見證（`tools/l3_recon.py` 的 `LEAN_L3_WITNESSES`，貪心取最小奇數；
投影到自由座標的行列式 = 1）。 -/
def wit31 : Fin 31 → ℕ := ![{", ".join(str(w) for w in W)}]

/-- 見證的 96 維雙模式差分向量族。 -/
def dFW96 : Fin 31 → (Fin 96 → ℚ) := fun i => dFQ96 (wit31 i)

/-! ## §84 見證值：自由座標上的 31×31 矩陣（每見證一條 `decide +kernel`） -/

{row_lemmas}

/-! ## §85 純量讀出（`rw` 用的字面形式；由 row 引理 defeq 取出） -/

{scalar_block}

/-! ## §86 Fin 31 求和展開 -/

/-- `Fin 31` 上的和展開成 31 項、索引為字面數字。
（直接用 `Fin.sum_univ_succ` 會留下 `Fin.succ` 形式，
`linear_combination` 的 ring 正規化會把它們當成不同原子。） -/
private lemma sum_fin_31 (f : Fin 31 → ℚ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 +
      f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 +
      f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 := by
  simp [Fin.sum_univ_succ]
  ring

/-! ## §87 線性獨立 -/

set_option maxHeartbeats 1600000 in
/-- **31 條 dFW96 線性獨立**。判準：投影到 §81 那 31 個自由座標的 31×31 矩陣
可逆（行列式 = 1，么模）。每個係數 `g i` 由錨定的整數逆矩陣 `B` 給出顯式組合
`g i = Σₜ B[t][i]·hₜ`（一行 `linear_combination`，不經 `linarith` 搜尋）。 -/
theorem dFW96_linearIndependent : LinearIndependent ℚ dFW96 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e : ∀ j : Fin 96,
      {e_body} = 0 := by
    intro j
    have h := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [sum_fin_31] at h
    exact h
{h_insts}
{rw_blocks}
{g_block}
  intro i
  fin_cases i <;> assumption

/-! ## §88 下界與維度定理 -/

/-- 每條見證向量都在 `dFQ96` 的值域裡（定義即然）。 -/
theorem dFW96_mem_range (i : Fin 31) : dFW96 i ∈ Set.range dFQ96 := ⟨wit31 i, rfl⟩

/-- **下界**：`31 ≤ dim span(dFQ96)`。 -/
theorem thirtyone_le_finrank_span_dFQ96 :
    31 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ96)) := by
  have hcard : Module.finrank ℚ (Submodule.span ℚ (Set.range dFW96)) = 31 := by
    simpa using finrank_span_eq_card dFW96_linearIndependent
  have hle : Submodule.span ℚ (Set.range dFW96) ≤ Submodule.span ℚ (Set.range dFQ96) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact dFW96_mem_range i)
  calc (31 : ℕ) = Module.finrank ℚ (Submodule.span ℚ (Set.range dFW96)) := hcard.symm
    _ ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ96)) := Submodule.finrank_mono hle

/-- **維度定理**：Level 3 雙模式有效差分生成空間恰為 **31 維**（96 維中）。

這是 HandOver「維度精確化 (Dimensionality)」第二條主張的形式化：
上界來自 65 條差分層泛函（`finrank_span_dFQ96_le`，§79–81），
下界來自 31 條具體見證的線性獨立（`thirtyone_le_finrank_span_dFQ96`）。
與 Level 2 的 `Flow.finrank_span_dFQ_eq_ten` 對應；A-3 至此收官。 -/
theorem finrank_span_dFQ96_eq_31 :
    Module.finrank ℚ (Submodule.span ℚ (Set.range dFQ96)) = 31 :=
  le_antisymm finrank_span_dFQ96_le thirtyone_le_finrank_span_dFQ96

end CollatzFST.L3
"""
out_lower = _HERE.parent / "Lean4RealConstruction" / "ProjectA" / "Collatz_FST_L3_DimLower.lean"
out_lower.write_text(lean_lower, encoding="utf-8")
print("生成", out_lower, f"（{lean_lower.count(chr(10))} 行）")
