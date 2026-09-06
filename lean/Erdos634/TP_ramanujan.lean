import Mathlib.Tactic
import Erdos634.Dissection
import Erdos634.Z15Real
import Erdos634.BaseBetaE1

/-!
# TP_ramanujan.lean — exact forms for the room `tileplace` (Erdős #634)

Two exact-arithmetic questions, answered.

## A.  The vertex-figure system, solved once and for all

The corpus reduces every vertex figure to the linear system over `ℕ`

    nα + 2·nγ = X,      nβ + nγ = Y                                    (★)

(`Dissection.vertex_multiplicities`, `AngleArithmetic`, `VertexFigureReal`), where `(X,Y)` is the
label of the ambient angle in the basis `α ↦ (1,0)`, `β ↦ (0,1)`, `γ = 2α+β ↦ (2,1)`,
`π = 3α+2β ↦ (3,2)`.  Every consumer in the corpus solves (★) at one *named* `(X,Y)` by `omega`.
This file solves it for **all** `(X,Y)` at once and reads off the consequence the room asked for.

* `figures X Y` — the solution set, exhibited as an explicit image of `Finset.range`.
* `mem_figures` — it *is* the solution set of (★).
* `card_figures` — **`|figures X Y| = min (X/2) Y + 1`.**  A closed form; every ad-hoc count in
  the corpus is an instance (`(3,2) ↦ 2`, `(6,4) ↦ 4`, `(0,1) ↦ 1`, `(3,0) ↦ 1`).
* `tile_count_eq` — the number of tiles at the point is `X + Y − 2·nγ`; so the possible counts form
  an arithmetic progression of step `2` from `X+Y` downwards, of length `min (X/2) Y + 1`.
* `tile_count_parity` — **the count's parity is `X+Y mod 2`, determined by the label alone.**
* `figure_unique_iff` / `count_determined_iff` — **the figure (equivalently, the tile count) is
  determined by exact angle arithmetic iff `X ≤ 1 ∨ Y = 0`.**
* `single_tile_iff` — "matched by *exactly one* tile" is an arithmetic consequence of the label iff
  `(X,Y) = (1,0)` or `(0,1)`.

Applied to a base-β target, whose four point-labels are `(0,1)` at a base corner, `(3,0)` at the
apex, `(3,2)` at a straight boundary point and `(6,4)` at an interior point, this gives a **sharp
negative** for G3: exact angle arithmetic decides "exactly one tile" at the base corners and
nowhere else — and it decides the count at the apex to be `3`, not `1`.  See
`basebeta_base_corner_one_tile`, `basebeta_apex_three_tiles`, `basebeta_apex_not_one_tile`,
`basebeta_boundary_count_undetermined`, `basebeta_interior_count_undetermined`.

## B.  A case-free sign test in `ℤ[√D]`, hence a closed-form containment certificate

Every certificate in the corpus (`Tiling44`, `Tiling99`, `Tiling28`, `CevianTiling63`,
`PgramTiling22/52`, `Z15Real`) decides `0 ≤ a + b√D` by the same **four-case** body:

    if 0 ≤ a then (if 0 ≤ b then true else D·b² ≤ a²) else (if b < 0 then false else a² ≤ D·b²)

The case analysis is unnecessary.  Because `t ↦ t·|t|` is a strictly monotone bijection of `ℝ`,

    `nonneg_zd_iff` :   0 ≤ a + b√D   ⟺   0 ≤ a·|a| + D·(b·|b|)                    (a b : ℤ, 0 ≤ D)

— **one integer inequality, no branches, uniform in `D`**, hence uniform in the base-β parameter
`(e,f)` since `D = 4f² − e²` there (companion §, `BaseBetaQuadCoord.Dq`).  `znonneg_iff_closedForm`
checks it against the corpus's own `Z15Real.znonneg`.  `insideCF` is the resulting containment
predicate — three such inequalities — and `insideCF_iff` proves it equal to the three real
half-plane conditions.  `witness_*` instantiate it on the real `N = 44` certificate's target.

Zero `sorry`; no new axioms.  Every theorem below is either unconditional arithmetic or carries an
exhibited satisfiability witness (`witness_figures_of_angle_sum`, `witness_inside_44`,
`witness_outside_44`, `witness_nn_nontrivial_*`).
-/

namespace Erdos634.TPRamanujan

/-! ## A. The vertex-figure system, solved -/

/-- The solution set of `nα + 2nγ = X`, `nβ + nγ = Y` over `ℕ`, parametrised by `nγ`. -/
def figures (X Y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (min (X / 2) Y + 1)).image (fun t => (X - 2 * t, Y - t, t))

/-- **`figures` is the solution set.** -/
theorem mem_figures {X Y na nb ng : ℕ} :
    (na, nb, ng) ∈ figures X Y ↔ na + 2 * ng = X ∧ nb + ng = Y := by
  classical
  simp only [figures, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, h1, h2, h3⟩
    subst h3
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨ng, by omega, by omega, by omega, rfl⟩

/-- **The closed form for the number of vertex figures at a label `(X,Y)`.** -/
theorem card_figures (X Y : ℕ) : (figures X Y).card = min (X / 2) Y + 1 := by
  classical
  rw [figures, Finset.card_image_of_injective _ (fun t t' h => by
    simpa using congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) h), Finset.card_range]

theorem figures_nonempty (X Y : ℕ) : (figures X Y).Nonempty := by
  refine Finset.card_pos.mp ?_
  rw [card_figures]
  omega

/-- **The tile count at a point of label `(X,Y)` is `X + Y − 2·nγ`** (written without truncated
subtraction).  Hence the achievable counts are an arithmetic progression of step `2`. -/
theorem tile_count_eq {X Y na nb ng : ℕ} (h1 : na + 2 * ng = X) (h2 : nb + ng = Y) :
    (na + nb + ng) + 2 * ng = X + Y := by omega

/-- **The parity of the tile count is fixed by the label alone.**  In particular a boundary
non-corner point (`X+Y = 5`) always carries an odd number of tiles and an interior point
(`X+Y = 10`) an even number. -/
theorem tile_count_parity {X Y na nb ng : ℕ} (h1 : na + 2 * ng = X) (h2 : nb + ng = Y) :
    (na + nb + ng) % 2 = (X + Y) % 2 := by omega

/-- **The exact criterion for the vertex figure to be pinned by arithmetic.** -/
theorem figure_unique_iff (X Y : ℕ) : (figures X Y).card = 1 ↔ X ≤ 1 ∨ Y = 0 := by
  rw [card_figures]; omega

/-- The same criterion in `∀`-form, over honest solutions of the system. -/
theorem figure_unique_iff' (X Y : ℕ) :
    (∀ na nb ng na' nb' ng' : ℕ, na + 2 * ng = X → nb + ng = Y →
        na' + 2 * ng' = X → nb' + ng' = Y → ng = ng') ↔ (X ≤ 1 ∨ Y = 0) := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨hX, hY⟩ := hc
    have := h X Y 0 (X - 2) (Y - 1) 1 (by omega) (by omega) (by omega) (by omega)
    omega
  · rintro (hX | hY) <;> intro na nb ng na' nb' ng' h1 h2 h3 h4 <;> omega

/-- **The tile count is determined by the label exactly when the figure is.**  Counts differ by
`2(nγ' − nγ)`, so no cancellation can make the count determined where the figure is not. -/
theorem count_determined_iff (X Y : ℕ) :
    (∀ na nb ng na' nb' ng' : ℕ, na + 2 * ng = X → nb + ng = Y →
        na' + 2 * ng' = X → nb' + ng' = Y → na + nb + ng = na' + nb' + ng') ↔ (X ≤ 1 ∨ Y = 0) := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨hX, hY⟩ := hc
    have := h X Y 0 (X - 2) (Y - 1) 1 (by omega) (by omega) (by omega) (by omega)
    omega
  · rintro (hX | hY) <;> intro na nb ng na' nb' ng' h1 h2 h3 h4 <;> omega

/-- **"Matched by exactly one tile" is an arithmetic consequence of the label at two labels
only**: `α` alone, and `β` alone.  On a base-β target only the second occurs. -/
theorem single_tile_iff (X Y : ℕ) :
    (∀ na nb ng : ℕ, na + 2 * ng = X → nb + ng = Y → na + nb + ng = 1) ↔
      ((X = 1 ∧ Y = 0) ∨ (X = 0 ∧ Y = 1)) := by
  constructor
  · intro h
    have h0 := h X Y 0 (by omega) (by omega)
    omega
  · rintro (⟨hX, hY⟩ | ⟨hX, hY⟩) <;> intro na nb ng h1 h2 <;> omega

/-- **Straight-angle and covering contributors only shift the label.**  A tile meeting the point in
the interior of one of its edges spends `π = (3,2)`; one covering the point spends `2π = (6,4)`.
So the corner multiplicities still solve (★), at the reduced label. -/
theorem figures_shift {X Y na nb ng s u : ℕ}
    (h1 : na + 2 * ng + 3 * s + 6 * u = X) (h2 : nb + ng + 2 * s + 4 * u = Y) :
    (na, nb, ng) ∈ figures (X - 3 * s - 6 * u) (Y - 2 * s - 4 * u) := by
  rw [mem_figures]; omega

/-! ### A′. The bridge to a real dissection

`Dissection.vertex_multiplicities` turns an angle identity at a real point into (★).  Composing,
any multiset of tile corner angles realising the label `(X,Y)` lies in `figures X Y`. -/

/-- **Any real vertex figure of label `(X,Y)` is a member of `figures X Y`.** -/
theorem figures_of_angle_sum {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (na nb ng X Y : ℕ)
    (hsum : (na : ℝ) * α + (nb : ℝ) * β + (ng : ℝ) * (2 * α + β)
      = (X : ℝ) * α + (Y : ℝ) * β) :
    (na, nb, ng) ∈ figures X Y := by
  have h : (na : ℝ) * α + (nb : ℝ) * β + (ng : ℝ) * (2 * α + β)
      = ((X : ℤ) : ℝ) * α + ((Y : ℤ) : ℝ) * β := by push_cast; linarith
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr na nb ng (X : ℤ) (Y : ℤ) h
  rw [mem_figures]; omega

/-- **Satisfiability witness for `figures_of_angle_sum`.**  The `(e,f) = (1,2)` base-β tile:
`α = 2·arcsin(1/4)` has `sin(α/2) = 1/4 = e/(2f)`, so `BaseBetaE1.tile_alpha_irrational` applies,
and `β = (π − 3α)/2` gives the relation.  The straight-angle figure `{3α, 2β}` is then a genuine
member of `figures 3 2`, so the theorem above is not vacuous. -/
theorem witness_figures_of_angle_sum :
    ∃ α β : ℝ, 3 * α + 2 * β = Real.pi ∧ (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧
      ((3, 2, 0) ∈ figures 3 2) := by
  refine ⟨2 * Real.arcsin (1 / 4), (Real.pi - 3 * (2 * Real.arcsin (1 / 4))) / 2, by ring, ?_, ?_⟩
  · have hsin : Real.sin ((2 * Real.arcsin (1 / 4)) / 2) = ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ)) := by
      have : (2 * Real.arcsin (1 / 4)) / 2 = Real.arcsin (1 / 4) := by ring
      rw [this, Real.sin_arcsin (by norm_num) (by norm_num)]
      norm_num
    exact Erdos634.BaseBetaE1.tile_alpha_irrational 1 2 (by norm_num) (by norm_num) _ hsin
  · rw [mem_figures]; omega

/-! ### A″. The base-β consequences, as exact arithmetic

A base-β target presents exactly four labels: `(0,1)` at a base corner, `(3,0)` at the apex,
`(3,2)` at a straight boundary point, `(6,4)` at an interior point. -/

/-- Base corner, label `β = (0,1)`: **exactly one tile**, presenting `β`. -/
theorem basebeta_base_corner_one_tile :
    ∀ na nb ng : ℕ, na + 2 * ng = 0 → nb + ng = 1 → na + nb + ng = 1 := by
  intro na nb ng h1 h2; omega

theorem basebeta_base_corner_unique : (figures 0 1).card = 1 := by
  rw [card_figures]; norm_num

/-- Apex, label `3α = (3,0)`: **exactly three tiles**, each presenting `α`. -/
theorem basebeta_apex_three_tiles :
    ∀ na nb ng : ℕ, na + 2 * ng = 3 → nb + ng = 0 → na + nb + ng = 3 := by
  intro na nb ng h1 h2; omega

theorem basebeta_apex_unique : (figures 3 0).card = 1 := by
  rw [card_figures]; norm_num

/-- **The base-corner trick does not extend to the apex.**  The apex figure is pinned by
arithmetic, but to *three* tiles, so "matched by exactly one tile" is false there. -/
theorem basebeta_apex_not_one_tile :
    ¬ (∀ na nb ng : ℕ, na + 2 * ng = 3 → nb + ng = 0 → na + nb + ng = 1) := by
  intro h; have := h 3 0 0 (by norm_num) (by norm_num); omega

/-- Straight boundary point, label `π = (3,2)`: **two** figures. -/
theorem basebeta_boundary_two_figures : (figures 3 2).card = 2 := by
  rw [card_figures]; norm_num

/-- Interior point, label `2π = (6,4)`: **four** figures. -/
theorem basebeta_interior_four_figures : (figures 6 4).card = 4 := by
  rw [card_figures]; norm_num

/-- **The tile count at a straight boundary point is not decided by arithmetic**: `{3α,2β}` has
five tiles, `{α,β,γ}` has three. -/
theorem basebeta_boundary_count_undetermined :
    ¬ (∀ na nb ng na' nb' ng' : ℕ, na + 2 * ng = 3 → nb + ng = 2 →
        na' + 2 * ng' = 3 → nb' + ng' = 2 → na + nb + ng = na' + nb' + ng') := by
  intro h
  have := h 3 2 0 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  omega

/-- **Nor at an interior point**: `{6α,4β}` has ten tiles, `{β,3γ}` has four. -/
theorem basebeta_interior_count_undetermined :
    ¬ (∀ na nb ng na' nb' ng' : ℕ, na + 2 * ng = 6 → nb + ng = 4 →
        na' + 2 * ng' = 6 → nb' + ng' = 4 → na + nb + ng = na' + nb' + ng') := by
  intro h
  have := h 6 4 0 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  omega

/-- **The sharp form of the negative.**  Among the four base-β labels, arithmetic pins the tile
count exactly at the two target-vertex labels, and "exactly one tile" exactly at the base corner. -/
theorem basebeta_label_summary :
    ((figures 0 1).card = 1 ∧ (figures 3 0).card = 1 ∧
      (figures 3 2).card = 2 ∧ (figures 6 4).card = 4) ∧
    (((0 : ℕ) = 1 ∧ (1 : ℕ) = 0) ∨ ((0 : ℕ) = 0 ∧ (1 : ℕ) = 1)) ∧
    ¬ (((3 : ℕ) = 1 ∧ (0 : ℕ) = 0) ∨ ((3 : ℕ) = 0 ∧ (0 : ℕ) = 1)) := by
  refine ⟨⟨basebeta_base_corner_unique, basebeta_apex_unique,
    basebeta_boundary_two_figures, basebeta_interior_four_figures⟩, Or.inr ⟨rfl, rfl⟩, ?_⟩
  rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega

/-! ## B. A case-free sign test in `ℤ[√D]` -/

/-- `t ↦ t·|t|` is strictly monotone on `ℝ`. -/
theorem sgnSq_strictMono {x y : ℝ} (h : x < y) : x * |x| < y * |y| := by
  by_cases hx : (0 : ℝ) ≤ x
  · have hy : (0 : ℝ) ≤ y := le_trans hx h.le
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    nlinarith
  · push_neg at hx
    by_cases hy : (0 : ℝ) ≤ y
    · rw [abs_of_neg hx, abs_of_nonneg hy]
      nlinarith
    · push_neg at hy
      rw [abs_of_neg hx, abs_of_neg hy]
      nlinarith

/-- Hence `t ↦ t·|t|` reflects and preserves `≤`. -/
theorem sgnSq_le_iff (x y : ℝ) : x * |x| ≤ y * |y| ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact absurd h (not_le.mpr (sgnSq_strictMono hc))
  · intro h
    rcases eq_or_lt_of_le h with rfl | h'
    · exact le_rfl
    · exact (sgnSq_strictMono h').le

/-- **The closed form.**  For integers `a b` and `0 ≤ D`,
`0 ≤ a + b√D` iff `0 ≤ a·|a| + D·(b·|b|)` — one integer inequality, no case analysis, uniform
in `D`.  (The corpus's `znonneg` is a four-branch decision procedure computing the same Boolean.) -/
theorem nonneg_zd_iff (D : ℤ) (hD : 0 ≤ D) (a b : ℤ) :
    0 ≤ (a : ℝ) + (b : ℝ) * Real.sqrt (D : ℝ) ↔ 0 ≤ a * |a| + D * (b * |b|) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (D : ℝ) ^ 2 = (D : ℝ) := Real.sq_sqrt (by exact_mod_cast hD)
  have hstep : 0 ≤ (a : ℝ) + (b : ℝ) * Real.sqrt (D : ℝ)
      ↔ -((b : ℝ) * Real.sqrt (D : ℝ)) ≤ (a : ℝ) := by
    constructor <;> intro h <;> linarith
  have hkey : (-((b : ℝ) * Real.sqrt (D : ℝ))) * |(-((b : ℝ) * Real.sqrt (D : ℝ)))|
      = -((D : ℝ) * ((b : ℝ) * |(b : ℝ)|)) := by
    rw [abs_neg, abs_mul, abs_of_nonneg hs,
      show (-((b : ℝ) * Real.sqrt (D : ℝ))) * (|(b : ℝ)| * Real.sqrt (D : ℝ))
        = -(Real.sqrt (D : ℝ) ^ 2 * ((b : ℝ) * |(b : ℝ)|)) from by ring, hs2]
  have hcast : (0 ≤ a * |a| + D * (b * |b|))
      ↔ (0 : ℝ) ≤ (a : ℝ) * |(a : ℝ)| + (D : ℝ) * ((b : ℝ) * |(b : ℝ)|) := by
    constructor
    · intro h
      have h' : ((0 : ℤ) : ℝ) ≤ ((a * |a| + D * (b * |b|) : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
    · intro h
      have h' : ((0 : ℤ) : ℝ) ≤ ((a * |a| + D * (b * |b|) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h'
  rw [hstep, ← sgnSq_le_iff, hkey, hcast]
  constructor <;> intro h <;> linarith

/-- **Agreement with the corpus's four-branch `znonneg`, at `D = 15`.** -/
theorem znonneg_iff_closedForm (z : Erdos634.Z15Real.Z15) :
    Erdos634.Z15Real.znonneg z = true ↔ 0 ≤ z.1 * |z.1| + 15 * (z.2 * |z.2|) := by
  rw [Erdos634.Z15Real.toR_nonneg_iff]
  have h := nonneg_zd_iff 15 (by norm_num) z.1 z.2
  simpa [Erdos634.Z15Real.toR] using h

/-! ### B′. The closed-form containment certificate -/

/-- An element of `ℤ[√D]`. -/
abbrev ZD := ℤ × ℤ
/-- A point of the plane over `ℤ[√D]`, as `(x, y)`. -/
abbrev PtD := ZD × ZD

def zaddD (u v : ZD) : ZD := (u.1 + v.1, u.2 + v.2)
def zsubD (u v : ZD) : ZD := (u.1 - v.1, u.2 - v.2)
def zmulD (D : ℤ) (u v : ZD) : ZD := (u.1 * v.1 + D * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- The `z`-component of `(a − o) × (b − o)`, in `ℤ[√D]`. -/
def crossD (D : ℤ) (o a b : PtD) : ZD :=
  zsubD (zmulD D (zsubD a.1 o.1) (zsubD b.2 o.2)) (zmulD D (zsubD a.2 o.2) (zsubD b.1 o.1))

/-- **The case-free sign functional**: `nn D z ≥ 0` iff `z ≥ 0` in `ℤ[√D]`. -/
def nn (D : ℤ) (z : ZD) : ℤ := z.1 * |z.1| + D * (z.2 * |z.2|)

noncomputable def toRD (D : ℤ) (z : ZD) : ℝ := (z.1 : ℝ) + (z.2 : ℝ) * Real.sqrt (D : ℝ)

theorem toRD_nonneg_iff (D : ℤ) (hD : 0 ≤ D) (z : ZD) : 0 ≤ toRD D z ↔ 0 ≤ nn D z :=
  nonneg_zd_iff D hD z.1 z.2

theorem toRD_sub (D : ℤ) (u v : ZD) : toRD D (zsubD u v) = toRD D u - toRD D v := by
  simp only [toRD, zsubD]; push_cast; ring

theorem toRD_mul (D : ℤ) (hD : 0 ≤ D) (u v : ZD) :
    toRD D (zmulD D u v) = toRD D u * toRD D v := by
  have hs2 : Real.sqrt (D : ℝ) ^ 2 = (D : ℝ) := Real.sq_sqrt (by exact_mod_cast hD)
  simp only [toRD, zmulD]
  push_cast
  linear_combination (-((u.2 : ℝ) * (v.2 : ℝ))) * hs2

/-- The real cross product of the `ℤ[√D]` points. -/
noncomputable def realCross (D : ℤ) (o a b : PtD) : ℝ :=
  (toRD D a.1 - toRD D o.1) * (toRD D b.2 - toRD D o.2)
    - (toRD D a.2 - toRD D o.2) * (toRD D b.1 - toRD D o.1)

theorem toRD_crossD (D : ℤ) (hD : 0 ≤ D) (o a b : PtD) :
    toRD D (crossD D o a b) = realCross D o a b := by
  simp only [crossD, realCross, toRD_sub, toRD_mul D hD]

/-- **The closed-form containment predicate**: three integer inequalities, decidable, no branches,
uniform in `D`. -/
def insideCF (D : ℤ) (P0 P1 P2 p : PtD) : Prop :=
  0 ≤ nn D (crossD D P0 P1 p) ∧ 0 ≤ nn D (crossD D P1 P2 p) ∧ 0 ≤ nn D (crossD D P2 P0 p)

instance (D : ℤ) (P0 P1 P2 p : PtD) : Decidable (insideCF D P0 P1 P2 p) := by
  unfold insideCF; infer_instance

/-- **The closed form is exactly the three half-plane conditions.**  For a positively oriented
triangle `P0P1P2` this is membership in the closed triangle. -/
theorem insideCF_iff (D : ℤ) (hD : 0 ≤ D) (P0 P1 P2 p : PtD) :
    insideCF D P0 P1 P2 p ↔
      (0 ≤ realCross D P0 P1 p ∧ 0 ≤ realCross D P1 P2 p ∧ 0 ≤ realCross D P2 P0 p) := by
  simp only [insideCF, ← toRD_crossD D hD, toRD_nonneg_iff D hD]

/-! ### B″. Witnesses on the certified `N = 44` target

`Tiling44`'s target, scaled by `8` into `ℤ[√15]`, is `(0,0)`, `(176,0)`, `(88, 24√15)`. -/

def q0 : PtD := ((0, 0), (0, 0))
def q1 : PtD := ((176, 0), (0, 0))
def q2 : PtD := ((88, 0), (0, 24))

/-- An interior point of the `N = 44` target: `(88, 8√15)`. -/
theorem witness_inside_44 : insideCF 15 q0 q1 q2 ((88, 0), (0, 8)) := by
  unfold insideCF nn crossD zsubD zmulD q0 q1 q2
  norm_num

/-- A point below the base is rejected: `(88, −√15)`.  Two-sided, so the predicate is not
trivially true. -/
theorem witness_outside_44 : ¬ insideCF 15 q0 q1 q2 ((88, 0), (0, -1)) := by
  unfold insideCF nn crossD zsubD zmulD q0 q1 q2
  norm_num

/-- The closed form does real work: `−1 + √15 ≥ 0` although `a < 0`. -/
theorem witness_nn_nontrivial_pos : 0 ≤ nn 15 (-1, 1) := by unfold nn; decide

/-- And `3 − √15 < 0` although `a > 0`. -/
theorem witness_nn_nontrivial_neg : ¬ (0 ≤ nn 15 (3, -1)) := by unfold nn; decide

/-- The two witnesses above, read back through `nonneg_zd_iff`, as statements about `ℝ`. -/
theorem witness_real_pos : (0 : ℝ) ≤ -1 + Real.sqrt 15 := by
  have h := (nonneg_zd_iff 15 (by norm_num) (-1) 1).mpr (by decide)
  push_cast at h
  linarith

theorem witness_real_neg : ¬ ((0 : ℝ) ≤ 3 - Real.sqrt 15) := by
  intro h
  have h' : (0 : ℝ) ≤ ((3 : ℤ) : ℝ) + ((-1 : ℤ) : ℝ) * Real.sqrt ((15 : ℤ) : ℝ) := by
    push_cast; linarith
  have hz := (nonneg_zd_iff 15 (by norm_num) 3 (-1)).mp h'
  exact absurd hz (by decide)

end Erdos634.TPRamanujan
