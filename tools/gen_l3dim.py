"""從 l3_recon.py 的錨資料生成 Collatz_FST_L3_DimUpper.lean（上界 ≤ 31）。

用法：python3 tools/gen_l3dim.py   （路徑相對 __file__，任何 checkout 可跑；
輸出應與 repo 中的 Lean 檔逐位一致——這是審查時的再生性測試）

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

## 下界擴充點（收官下半，還沒寫）

- 資料全在 l3_recon.py：`LEAN_L3_WITNESSES`（31 見證）、`LEAN_L3_WITNESS_INV`
  （么模逆 B，max|B|=3）、`LEAN_L3_FREE_IDX`。
- 生成物：`dFW96 i := dFQ96 (witness i)`；31 條見證值引理（`occ3` 具體求值，
  仿 LP.ΔF_231，**先探針一條** decide vs norm_num）；`sum_fin_31`
  （仿 Level 2 sum_fin_ten，Fin.sum_univ_succ 會留 Fin.succ 原子）；
  線性獨立經 `Fintype.linearIndependent_iff`，31 條方程 hⱼ 取自由座標
  evaluation，**每個 `g i = 0` 用 `linear_combination Σⱼ B[j][i]·hⱼ`
  （orientation：g·Mw = 0 ⇒ g = (g·Mw)·B），不要 linarith**；
  收尾 `finrank_span_eq_card` + `Submodule.finrank_mono` + `le_antisymm`，
  照抄 Level 2 DimLower 的骨架。
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
