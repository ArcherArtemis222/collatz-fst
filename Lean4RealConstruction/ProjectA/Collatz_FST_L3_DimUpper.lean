/-
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
  ![pr 0,
    pr 1,
    pr 2,
    pr 3,
    pr 4,
    pr 5,
    pr 6,
    pr 7,
    pr 18,
    pr 19,
    pr 20,
    pr 21,
    pr 22,
    pr 23,
    pr 34,
    pr 35,
    pr 36,
    pr 37,
    pr 38,
    pr 39,
    (pr 8 + pr 12 - pr 8 - pr 9),
    (pr 26 + pr 30 - pr 14 - pr 15),
    (pr 40 + pr 44 - pr 24 - pr 25),
    (pr 9 + pr 13 - pr 26 - pr 27),
    (pr 42 + pr 46 - pr 28 - pr 29),
    (pr 11 + pr 15 - pr 30 - pr 31),
    (pr 17 - pr 32 - pr 33),
    (pr 25 + pr 29 - pr 40 - pr 41),
    (pr 33 + pr 41 + pr 45 - pr 42 - pr 43),
    (pr 27 + pr 31 - pr 44 - pr 45),
    (pr 43 + pr 47 - pr 46 - pr 47),
    pr 48,
    pr 49,
    pr 50,
    pr 51,
    pr 52,
    pr 53,
    pr 54,
    pr 55,
    pr 66,
    pr 67,
    pr 68,
    pr 69,
    pr 70,
    pr 71,
    pr 82,
    pr 83,
    pr 84,
    pr 85,
    pr 86,
    pr 87,
    (pr 56 + pr 60 - pr 56 - pr 57),
    (pr 74 + pr 78 - pr 62 - pr 63),
    (pr 88 + pr 92 - pr 72 - pr 73),
    (pr 57 + pr 61 - pr 74 - pr 75),
    (pr 90 + pr 94 - pr 76 - pr 77),
    (pr 59 + pr 63 - pr 78 - pr 79),
    (pr 65 - pr 80 - pr 81),
    (pr 73 + pr 77 - pr 88 - pr 89),
    (pr 81 + pr 89 + pr 93 - pr 90 - pr 91),
    (pr 75 + pr 79 - pr 92 - pr 93),
    (pr 91 + pr 95 - pr 94 - pr 95),
    pr 33,
    pr 64,
    (pr 32 + pr 80 - pr 16 - pr 17 - pr 64 - pr 65)]

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
  · show dF96 x 0 (((0 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) = 0
    exact dF96_dead x 0 (by decide) 0
  · show dF96 x 0 (((0 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 0
    exact dF96_dead x 0 (by decide) 1
  · show dF96 x 0 (((0 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 0 (by decide) 0
  · show dF96 x 0 (((0 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 0 (by decide) 1
  · show dF96 x 0 (((0 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 0) = 0
    exact dF96_dead x 0 (by decide) 0
  · show dF96 x 0 (((0 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 1) = 0
    exact dF96_dead x 0 (by decide) 1
  · show dF96 x 0 (((0 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 0 (by decide) 0
  · show dF96 x 0 (((0 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 0 (by decide) 1
  · show dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 0 (by decide) 0
  · show dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 0 (by decide) 1
  · show dF96 x 0 (((1 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 0) = 0
    exact dF96_dead x 0 (by decide) 0
  · show dF96 x 0 (((1 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 1) = 0
    exact dF96_dead x 0 (by decide) 1
  · show dF96 x 0 (((1 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 0 (by decide) 0
  · show dF96 x 0 (((1 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 0 (by decide) 1
  · show dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 0 (by decide) 0
  · show dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 0 (by decide) 1
  · show dF96 x 0 (((2 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 0) = 0
    exact dF96_dead x 0 (by decide) 0
  · show dF96 x 0 (((2 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 1) = 0
    exact dF96_dead x 0 (by decide) 1
  · show dF96 x 0 (((2 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 0 (by decide) 0
  · show dF96 x 0 (((2 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 0 (by decide) 1
  · have h := dF96_flow_clean x 0 ((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) = [(((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0), (((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0) + dF96 x 0 (((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0) - dF96 x 0 (((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 0 (((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 0 ((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) = [(((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0), (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0) + dF96 x 0 (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0) - dF96 x 0 (((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0) - dF96 x 0 (((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 0 ((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) = [(((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0), (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0) + dF96 x 0 (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0) - dF96 x 0 (((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 0 (((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 0 ((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)) = [(((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1), (((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) + dF96 x 0 (((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1) - dF96 x 0 (((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0) - dF96 x 0 (((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 0 ((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) = [(((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0), (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0) + dF96 x 0 (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0) - dF96 x 0 (((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0) - dF96 x 0 (((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 0 ((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) = [(((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1), (((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1) + dF96 x 0 (((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) - dF96 x 0 (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0) - dF96 x 0 (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 0 ((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)) = [(((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) - dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 0 ((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) = [(((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1), (((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) + dF96 x 0 (((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1) - dF96 x 0 (((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 0 (((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 0 ((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)) = [(((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1), (((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1), (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) + dF96 x 0 (((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) + dF96 x 0 (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1) - dF96 x 0 (((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0) - dF96 x 0 (((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 0 ((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) = [(((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1), (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1) + dF96 x 0 (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) - dF96 x 0 (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0) - dF96 x 0 (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 0 ((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) = [(((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1), (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 0 (((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1) + dF96 x 0 (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) - dF96 x 0 (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0) - dF96 x 0 (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) = 0
    linarith [h]
  · show dF96 x 1 (((0 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) = 0
    exact dF96_dead x 1 (by decide) 0
  · show dF96 x 1 (((0 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 0
    exact dF96_dead x 1 (by decide) 1
  · show dF96 x 1 (((0 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 1 (by decide) 0
  · show dF96 x 1 (((0 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 1 (by decide) 1
  · show dF96 x 1 (((0 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 0) = 0
    exact dF96_dead x 1 (by decide) 0
  · show dF96 x 1 (((0 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 1) = 0
    exact dF96_dead x 1 (by decide) 1
  · show dF96 x 1 (((0 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 1 (by decide) 0
  · show dF96 x 1 (((0 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 1 (by decide) 1
  · show dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 1 (by decide) 0
  · show dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 1 (by decide) 1
  · show dF96 x 1 (((1 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 0) = 0
    exact dF96_dead x 1 (by decide) 0
  · show dF96 x 1 (((1 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 1) = 0
    exact dF96_dead x 1 (by decide) 1
  · show dF96 x 1 (((1 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 1 (by decide) 0
  · show dF96 x 1 (((1 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 1 (by decide) 1
  · show dF96 x 1 (((2 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 1 (by decide) 0
  · show dF96 x 1 (((2 : ℕ), Phase.K, (0 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 1 (by decide) 1
  · show dF96 x 1 (((2 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 0) = 0
    exact dF96_dead x 1 (by decide) 0
  · show dF96 x 1 (((2 : ℕ), Phase.K, (1 : ℕ), (0 : ℕ)), 1) = 0
    exact dF96_dead x 1 (by decide) 1
  · show dF96 x 1 (((2 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 0) = 0
    exact dF96_dead x 1 (by decide) 0
  · show dF96 x 1 (((2 : ℕ), Phase.K, (1 : ℕ), (1 : ℕ)), 1) = 0
    exact dF96_dead x 1 (by decide) 1
  · have h := dF96_flow_clean x 1 ((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) = [(((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0), (((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0) + dF96 x 1 (((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0) - dF96 x 1 (((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 1 (((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 1 ((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) = [(((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0), (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0) + dF96 x 1 (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0) - dF96 x 1 (((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0) - dF96 x 1 (((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 1 ((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) = [(((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0), (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0) + dF96 x 1 (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0) - dF96 x 1 (((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 1 (((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 1 ((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)) = [(((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1), (((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((0 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) + dF96 x 1 (((0 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1) - dF96 x 1 (((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0) - dF96 x 1 (((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 1 ((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) = [(((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0), (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0) + dF96 x 1 (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0) - dF96 x 1 (((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0) - dF96 x 1 (((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 1 ((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) = [(((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1), (((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((0 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1) + dF96 x 1 (((0 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) - dF96 x 1 (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0) - dF96 x 1 (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 1 ((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)) = [(((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) - dF96 x 1 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 1 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 1 ((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)) = [(((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1), (((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((1 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) + dF96 x 1 (((1 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1) - dF96 x 1 (((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 1 (((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 1 ((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)) = [(((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1), (((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1), (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) + dF96 x 1 (((2 : ℕ), Phase.S, (0 : ℕ), (0 : ℕ)), 1) + dF96 x 1 (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1) - dF96 x 1 (((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 0) - dF96 x 1 (((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 1 ((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)) = [(((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1), (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((1 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1) + dF96 x 1 (((1 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) - dF96 x 1 (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 0) - dF96 x 1 (((2 : ℕ), Phase.S, (1 : ℕ), (0 : ℕ)), 1) = 0
    linarith [h]
  · have h := dF96_flow_clean x 1 ((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) (by decide) (by decide) (by decide)
    simp only [show inEdges3 ((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)) = [(((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1), (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1)] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    show dF96 x 1 (((2 : ℕ), Phase.S, (0 : ℕ), (1 : ℕ)), 1) + dF96 x 1 (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) - dF96 x 1 (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 0) - dF96 x 1 (((2 : ℕ), Phase.S, (1 : ℕ), (1 : ℕ)), 1) = 0
    linarith [h]
  · show dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 0
    exact dF96_block0_mode x
  · show dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) = 0
    exact dF96_block1_exit x
  · show dF96 x 0 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) + dF96 x 1 (((2 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 0 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) - dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 0) - dF96 x 1 (((1 : ℕ), Phase.K, (0 : ℕ), (0 : ℕ)), 1) = 0
    linarith [dF96_fstart x]

/-! ## §81 上界 -/

/-- 31 個自由座標（`tools/l3_recon.py` 的 `LEAN_L3_FREE_IDX`）。 -/
def freeIdx96 : Fin 31 → Fin 96 := ![8, 10, 13, 15, 26, 29, 30, 31, 32, 40, 42, 44, 45, 46, 47, 56, 58, 61, 63, 74, 77, 78, 79, 80, 88, 89, 90, 92, 93, 94, 95]

def pick96 : (Fin 96 → ℚ) →ₗ[ℚ] (Fin 31 → ℚ) := LinearMap.funLeft ℚ ℚ freeIdx96

set_option maxHeartbeats 3200000 in
theorem pick96_injective_on_Sol : Function.Injective (pick96.domRestrict Sol96) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨v, hv⟩ hker
  have hR := (mem_Sol96_iff v).mp hv
  have hz : ∀ i : Fin 31, v (freeIdx96 i) = 0 := fun i => congrFun hker i
  have r20 : v 8 + v 12 - v 8 - v 9 = 0 := hR 20
  have r21 : v 26 + v 30 - v 14 - v 15 = 0 := hR 21
  have r22 : v 40 + v 44 - v 24 - v 25 = 0 := hR 22
  have r23 : v 9 + v 13 - v 26 - v 27 = 0 := hR 23
  have r24 : v 42 + v 46 - v 28 - v 29 = 0 := hR 24
  have r25 : v 11 + v 15 - v 30 - v 31 = 0 := hR 25
  have r26 : v 17 - v 32 - v 33 = 0 := hR 26
  have r27 : v 25 + v 29 - v 40 - v 41 = 0 := hR 27
  have r28 : v 33 + v 41 + v 45 - v 42 - v 43 = 0 := hR 28
  have r29 : v 27 + v 31 - v 44 - v 45 = 0 := hR 29
  have r30 : v 43 + v 47 - v 46 - v 47 = 0 := hR 30
  have r51 : v 56 + v 60 - v 56 - v 57 = 0 := hR 51
  have r52 : v 74 + v 78 - v 62 - v 63 = 0 := hR 52
  have r53 : v 88 + v 92 - v 72 - v 73 = 0 := hR 53
  have r54 : v 57 + v 61 - v 74 - v 75 = 0 := hR 54
  have r55 : v 90 + v 94 - v 76 - v 77 = 0 := hR 55
  have r56 : v 59 + v 63 - v 78 - v 79 = 0 := hR 56
  have r57 : v 65 - v 80 - v 81 = 0 := hR 57
  have r58 : v 73 + v 77 - v 88 - v 89 = 0 := hR 58
  have r59 : v 81 + v 89 + v 93 - v 90 - v 91 = 0 := hR 59
  have r60 : v 75 + v 79 - v 92 - v 93 = 0 := hR 60
  have r61 : v 91 + v 95 - v 94 - v 95 = 0 := hR 61
  have r64 : v 32 + v 80 - v 16 - v 17 - v 64 - v 65 = 0 := hR 64
  have c0 : v 0 = 0 := hR 0
  have c1 : v 1 = 0 := hR 1
  have c2 : v 2 = 0 := hR 2
  have c3 : v 3 = 0 := hR 3
  have c4 : v 4 = 0 := hR 4
  have c5 : v 5 = 0 := hR 5
  have c6 : v 6 = 0 := hR 6
  have c7 : v 7 = 0 := hR 7
  have c8 : v 8 = 0 := hz 0
  have c10 : v 10 = 0 := hz 1
  have c13 : v 13 = 0 := hz 2
  have c15 : v 15 = 0 := hz 3
  have c18 : v 18 = 0 := hR 8
  have c19 : v 19 = 0 := hR 9
  have c20 : v 20 = 0 := hR 10
  have c21 : v 21 = 0 := hR 11
  have c22 : v 22 = 0 := hR 12
  have c23 : v 23 = 0 := hR 13
  have c26 : v 26 = 0 := hz 4
  have c29 : v 29 = 0 := hz 5
  have c30 : v 30 = 0 := hz 6
  have c31 : v 31 = 0 := hz 7
  have c32 : v 32 = 0 := hz 8
  have c33 : v 33 = 0 := hR 62
  have c34 : v 34 = 0 := hR 14
  have c35 : v 35 = 0 := hR 15
  have c36 : v 36 = 0 := hR 16
  have c37 : v 37 = 0 := hR 17
  have c38 : v 38 = 0 := hR 18
  have c39 : v 39 = 0 := hR 19
  have c40 : v 40 = 0 := hz 9
  have c42 : v 42 = 0 := hz 10
  have c44 : v 44 = 0 := hz 11
  have c45 : v 45 = 0 := hz 12
  have c46 : v 46 = 0 := hz 13
  have c47 : v 47 = 0 := hz 14
  have c48 : v 48 = 0 := hR 31
  have c49 : v 49 = 0 := hR 32
  have c50 : v 50 = 0 := hR 33
  have c51 : v 51 = 0 := hR 34
  have c52 : v 52 = 0 := hR 35
  have c53 : v 53 = 0 := hR 36
  have c54 : v 54 = 0 := hR 37
  have c55 : v 55 = 0 := hR 38
  have c56 : v 56 = 0 := hz 15
  have c58 : v 58 = 0 := hz 16
  have c61 : v 61 = 0 := hz 17
  have c63 : v 63 = 0 := hz 18
  have c64 : v 64 = 0 := hR 63
  have c66 : v 66 = 0 := hR 39
  have c67 : v 67 = 0 := hR 40
  have c68 : v 68 = 0 := hR 41
  have c69 : v 69 = 0 := hR 42
  have c70 : v 70 = 0 := hR 43
  have c71 : v 71 = 0 := hR 44
  have c74 : v 74 = 0 := hz 19
  have c77 : v 77 = 0 := hz 20
  have c78 : v 78 = 0 := hz 21
  have c79 : v 79 = 0 := hz 22
  have c80 : v 80 = 0 := hz 23
  have c82 : v 82 = 0 := hR 45
  have c83 : v 83 = 0 := hR 46
  have c84 : v 84 = 0 := hR 47
  have c85 : v 85 = 0 := hR 48
  have c86 : v 86 = 0 := hR 49
  have c87 : v 87 = 0 := hR 50
  have c88 : v 88 = 0 := hz 24
  have c89 : v 89 = 0 := hz 25
  have c90 : v 90 = 0 := hz 26
  have c92 : v 92 = 0 := hz 27
  have c93 : v 93 = 0 := hz 28
  have c94 : v 94 = 0 := hz 29
  have c95 : v 95 = 0 := hz 30
  have c9 : v 9 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c11 : v 11 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c12 : v 12 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c14 : v 14 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c16 : v 16 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c17 : v 17 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c24 : v 24 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c25 : v 25 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c27 : v 27 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c28 : v 28 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c41 : v 41 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c43 : v 43 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c57 : v 57 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c59 : v 59 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c60 : v 60 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c62 : v 62 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c65 : v 65 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c72 : v 72 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c73 : v 73 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c75 : v 75 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c76 : v 76 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c81 : v 81 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  have c91 : v 91 = 0 := by linarith [r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r64, c8, c13, c15, c26, c29, c30, c31, c32, c33, c40, c42, c44, c45, c46, c47, c56, c61, c63, c64, c74, c77, c78, c79, c80, c88, c89, c90, c92, c93, c94, c95]
  apply Subtype.ext
  funext j
  fin_cases j
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6
  · exact c7
  · exact c8
  · exact c9
  · exact c10
  · exact c11
  · exact c12
  · exact c13
  · exact c14
  · exact c15
  · exact c16
  · exact c17
  · exact c18
  · exact c19
  · exact c20
  · exact c21
  · exact c22
  · exact c23
  · exact c24
  · exact c25
  · exact c26
  · exact c27
  · exact c28
  · exact c29
  · exact c30
  · exact c31
  · exact c32
  · exact c33
  · exact c34
  · exact c35
  · exact c36
  · exact c37
  · exact c38
  · exact c39
  · exact c40
  · exact c41
  · exact c42
  · exact c43
  · exact c44
  · exact c45
  · exact c46
  · exact c47
  · exact c48
  · exact c49
  · exact c50
  · exact c51
  · exact c52
  · exact c53
  · exact c54
  · exact c55
  · exact c56
  · exact c57
  · exact c58
  · exact c59
  · exact c60
  · exact c61
  · exact c62
  · exact c63
  · exact c64
  · exact c65
  · exact c66
  · exact c67
  · exact c68
  · exact c69
  · exact c70
  · exact c71
  · exact c72
  · exact c73
  · exact c74
  · exact c75
  · exact c76
  · exact c77
  · exact c78
  · exact c79
  · exact c80
  · exact c81
  · exact c82
  · exact c83
  · exact c84
  · exact c85
  · exact c86
  · exact c87
  · exact c88
  · exact c89
  · exact c90
  · exact c91
  · exact c92
  · exact c93
  · exact c94
  · exact c95

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
