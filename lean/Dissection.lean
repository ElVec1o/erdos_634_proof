import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic
import Erdos634.SupportFace
import Erdos634.SegmentDense

open scoped ENNReal

/-!
# The geometric layer: dissections of a triangle

Every other Lean file in this development is arithmetic or combinatorial: it takes the geometry as
*hypotheses* (`gamma_injection`, `cancellation_core`, `vertex_pi`, …).  This file begins the layer
that is supposed to **supply** those hypotheses — i.e. the step "a tiling exists ⟹ these equations
hold", which until now rested entirely on the written proofs in the paper.

Mathlib has no theory of dissections (no `IsTiling`, no planar subdivision, no Jordan curve theorem,
no Euler formula, no polytopes — verified by source survey), so everything here is built from the
convexity and measure-theory primitives that *do* exist.

## What is defined

* `Tri` — a nondegenerate closed triangle in the plane, carried by its three vertices together with
  affine independence.  Its point set is `Tri.carrier = convexHull ℝ (range pts)`.
* `Dissection N` — **G1**: a target triangle, `N` tiles, the covering equation, and pairwise
  disjointness of tile *interiors*.  This is the faithful minimal definition: "disjoint interiors
  covering `T`" is stated combinatorially (`Disjoint (interior _) (interior _)` and a set equation),
  *not* measure-theoretically, so that it is provable-with; the measure-theoretic consequence is
  derived below rather than assumed.

## What is proved (no `sorry`, no new axioms)

* `Tri.volume_pos`, `Tri.volume_ne_top` — a nondegenerate tile has positive finite area.  The route
  is affine independence ⟹ `affineSpan = ⊤` ⟹ nonempty interior ⟹ positive Haar measure.
* `Dissection.aedisjoint` — **the bridge from "disjoint interiors" to "a.e. disjoint"**.  This is
  where `Convex.addHaar_frontier` (a convex set has null frontier) does the real work: it is the
  reason a tiling may be non-edge-to-edge and the area count still holds.
* `Dissection.volume_target` — **the area identity** `|T| = Σ |tᵢ|`.
* `Dissection.volume_target_of_congruent` — for equal-area tiles, `|T| = N · |t|`, i.e. `N` is
  determined by the target and the tile.
* `Dissection.pos` — a dissection has at least one tile.
* `cornerAngle_sum` — the three interior angles of a tile sum to `π` (from Mathlib's
  `angle_add_angle_add_angle_eq_pi`).
* `angle_indep`, `vertex_multiplicities`, and the three corollaries
  `vertex_pi_multiplicities`, `vertex_beta_corner_multiplicities`, `vertex_apex_multiplicities` —
  **the arithmetic half of G5**, which converts a *real* angle equation at a vertex into the
  *integer* multiplicity equations that `BaseBetaE1.vertex_pi`, `vertex_beta_corner` and
  `vertex_apex` currently take as hypotheses.  These corollaries produce those hypotheses in exactly
  the form those theorems consume, so that half of the vertex-figure classification is no longer
  assumed.

## What is NOT proved, and is taken as an explicit hypothesis

Following the discipline of `BaseBetaWalks.gamma_injection` and `InvariantCore.cancellation_core`,
the facts this file cannot yet derive are isolated as named `Prop`-valued predicates in the final
section (`HasAngleSums`, `HasEdgeChains`, `InteriorBalanced`), each with a docstring saying exactly
what it asserts and why it is not available.  They are *definitions*, not axioms: nothing in this
file assumes them, and any downstream theorem that needs one must take it as a hypothesis.

The single sharpest gap is `HasAngleSums`.  Its difficulty is narrower than first recorded here:
Mathlib *does* have oriented angles at a point in an oriented plane (`EuclideanGeometry.oangle`,
valued in `ℝ/2πℤ`) together with additivity, so the statement "the angles around an interior point
sum to `2π`" is free MODULO `2π` — the oriented angles telescope around the cycle.  What is missing
is the lift: that the tiles at the point occupy pairwise disjoint sectors in cyclic order covering
all directions, which turns a sum that is `0` in `ℝ/2πℤ` into unsigned angles summing to exactly
`2π`.  See `lean/AngleSumScope.lean`, where the free half is compiled and the remaining half is
stated.

## Compile status

**Compiles clean** (verified 2026-07-29, Lean 4.30.0 / Mathlib v4.30.0 — the pinned revision).
`Tri.volume_pos`, `Dissection.aedisjoint`, `Dissection.volume_target`, `Dissection.pos`,
`cornerAngle_sum` and `angle_indep` all elaborate, on `propext`, `Classical.choice`, `Quot.sound`
and nothing else; no `sorry`.

This project holds no Mathlib build of its own. To check the file, run from any project that has a
v4.30.0 build:

    lake env lean /path/to/ERDOS/634/lean/Dissection.lean

(An earlier version of this header said the file had never been compiled and flagged four tactic
steps as guesses. That is obsolete: the file compiles as written, and the four steps go through.)
-/

namespace Erdos634.Geometry

open MeasureTheory Set

/-- The ambient plane.  `EuclideanSpace ℝ (Fin 2)` rather than `ℝ × ℝ`: the `IsAddHaarMeasure`
instance for `volume` is direct here (`measureSpaceOfInnerProductSpace`), whereas on `ℝ × ℝ` it is
supplied by a defeq-fragile anonymous instance declared in an unrelated file. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-! ## Triangles -/

/-- A **nondegenerate closed triangle**: three vertices, affinely independent.

Nondegeneracy is carried in the structure rather than derived, because every geometric statement
downstream needs it and because it is exactly what makes the area positive.  Mathlib's
`Affine.Triangle ℝ Plane` (`= Affine.Simplex ℝ Plane 2`) is the same data; we use a bare structure
so that `carrier` is definitionally a `convexHull`, which is where the usable API lives.  The bridge
is `Affine.Simplex.convexHull_eq_closedInterior`, a `@[simp]` lemma, if the `Simplex` face/centroid
API is ever wanted. -/
structure Tri where
  /-- The three vertices. -/
  pts : Fin 3 → Plane
  /-- Nondegeneracy. -/
  indep : AffineIndependent ℝ pts

namespace Tri

/-- The filled triangle: the convex hull of the three vertices. -/
def carrier (T : Tri) : Set Plane := convexHull ℝ (Set.range T.pts)

theorem convex (T : Tri) : Convex ℝ T.carrier := convex_convexHull ℝ _

theorem isCompact (T : Tri) : IsCompact T.carrier :=
  (Set.finite_range _).isCompact_convexHull ℝ

theorem measurableSet (T : Tri) : MeasurableSet T.carrier := T.isCompact.measurableSet

theorem nullMeasurableSet (T : Tri) : NullMeasurableSet T.carrier volume :=
  T.measurableSet.nullMeasurableSet

/-- **The null-frontier fact.**  A convex set has Haar-null frontier.  This is the keystone that
lets a *non-edge-to-edge* dissection still be additive for area: tiles may meet along partial
edges, and those overlaps are null. -/
theorem volume_frontier (T : Tri) : volume (frontier T.carrier) = 0 :=
  T.convex.addHaar_frontier volume

/-- A triangle agrees with its interior up to a null set. -/
theorem interior_ae_eq (T : Tri) : interior T.carrier =ᵐ[volume] T.carrier :=
  interior_ae_eq_of_null_frontier T.volume_frontier

/-- Affine independence of three points in the plane spans it. -/
theorem affineSpan_eq_top (T : Tri) : affineSpan ℝ T.carrier = ⊤ := by
  -- `T.carrier` is *definitionally* `convexHull ℝ (range T.pts)`, so this term typechecks as stated
  -- without unfolding `carrier` by hand.
  have h : affineSpan ℝ T.carrier = affineSpan ℝ (Set.range T.pts) :=
    affineSpan_convexHull _
  rw [h]
  -- `Fintype.card (Fin 3) = finrank ℝ Plane + 1`, i.e. `3 = 2 + 1`;
  -- `Fintype.card_fin` and `finrank_euclideanSpace` are both `@[simp]`.
  exact T.indep.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)

theorem interior_nonempty (T : Tri) : (interior T.carrier).Nonempty :=
  T.convex.interior_nonempty_iff_affineSpan_eq_top.mpr T.affineSpan_eq_top

/-- **A nondegenerate tile has positive area.**  (Nonempty interior + `volume` is an open-positive
measure.) -/
theorem volume_pos (T : Tri) : 0 < volume T.carrier :=
  (isOpen_interior.measure_pos volume T.interior_nonempty).trans_le
    (measure_mono interior_subset)

/-- A tile has finite area (it is compact and `volume` is finite on compacts). -/
theorem volume_ne_top (T : Tri) : volume T.carrier ≠ ⊤ := T.isCompact.measure_lt_top.ne

end Tri

/-! ## Dissections (G1) -/

/-- **G1 — a dissection of a triangle into `N` triangles.**

The two conditions are exactly the paper's: the tiles *cover* the target, and their *interiors* are
pairwise disjoint.  Both are stated as plain set-theoretic conditions, not measure-theoretic ones —
this is the faithful reading, and the measure-theoretic consequence (`aedisjoint`,
`volume_target`) is *derived*.  Nothing here presumes the incidence is edge-to-edge. -/
structure Dissection (N : ℕ) where
  /-- The triangle being dissected. -/
  target : Tri
  /-- The tiles. -/
  tile : Fin N → Tri
  /-- The tiles cover the target and nothing more. -/
  covers : (⋃ i, (tile i).carrier) = target.carrier
  /-- Distinct tiles have disjoint interiors. -/
  interiors_disjoint :
    Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)

namespace Dissection

variable {N : ℕ}

/-- **Disjoint interiors ⟹ a.e. disjoint.**  Two tiles meet only in their frontiers, which are null
because the tiles are convex (`Tri.volume_frontier`).  This is the step at which a non-edge-to-edge
incidence stops mattering. -/
theorem aedisjoint (D : Dissection N) {i j : Fin N} (hij : i ≠ j) :
    AEDisjoint volume (D.tile i).carrier (D.tile j).carrier := by
  -- a point in both tiles lies in the frontier of at least one of them
  have hsub : (D.tile i).carrier ∩ (D.tile j).carrier ⊆
      frontier (D.tile i).carrier ∪ frontier (D.tile j).carrier := by
    rintro x ⟨hxi, hxj⟩
    by_cases h1 : x ∈ interior (D.tile i).carrier
    · by_cases h2 : x ∈ interior (D.tile j).carrier
      · exfalso
        have hd : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
          D.interiors_disjoint hij
        exact Set.disjoint_left.mp hd h1 h2
      · exact Or.inr ⟨subset_closure hxj, h2⟩
    · exact Or.inl ⟨subset_closure hxi, h1⟩
  refine measure_mono_null hsub ?_
  exact measure_union_null (D.tile i).volume_frontier (D.tile j).volume_frontier

/-- **The area identity.**  `|T| = Σᵢ |tᵢ|`.

This is the first genuine geometric theorem of the development: it is *not* assumed anywhere, it is
derived from `Dissection`.  Everything the paper's area equation needs is here. -/
theorem volume_target (D : Dissection N) :
    volume D.target.carrier = ∑ i, volume (D.tile i).carrier := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N))) (f := fun i => (D.tile i).carrier)
    (fun _ _ _ _ hij => D.aedisjoint hij)
    (fun i _ => (D.tile i).nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), (D.tile i).carrier) = D.target.carrier := by
    rw [← D.covers]; simp
  rw [hU] at h
  exact h

/-- **`N` is determined by the target and the tile.**  If every tile has area `v`, then
`|T| = N · v`.  (The paper's "area equation" in its cleanest form; congruent tiles certainly have
equal area, so this covers the case actually used.) -/
theorem volume_target_of_congruent (D : Dissection N) (v : ℝ≥0∞)
    (hv : ∀ i, volume (D.tile i).carrier = v) :
    volume D.target.carrier = (N : ℝ≥0∞) * v := by
  rw [D.volume_target]
  simp [hv]

/-- **A dissection has at least one tile.**  (If `N = 0` the area identity would force the target to
have zero area, contradicting `Tri.volume_pos`.)  Small, but it is a real consequence of the
definition rather than a stipulation. -/
theorem pos (D : Dissection N) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    have hz := D.volume_target
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hz
    exact absurd hz D.target.volume_pos.ne'
  · exact h

end Dissection

/-! ## Tile angles

Only the *local* half of G2 is available from Mathlib: the angles of a single triangle sum to `π`.
The vertex-figure half (angles around a point of the dissection) is not — see `HasAngleSums`. -/

/-- The interior angle of the triangle `p q r` at the vertex `q`.  (`V := Plane` is supplied
explicitly: `EuclideanGeometry.angle` leaves the vector space implicit, and here the point space and
the vector space coincide.) -/
noncomputable def cornerAngle (p q r : Plane) : ℝ :=
  EuclideanGeometry.angle (V := Plane) p q r

/-- **The angles of a tile sum to `π`.**  Immediate from Mathlib's triangle angle sum, once
nondegeneracy supplies the distinctness hypothesis. -/
theorem cornerAngle_sum (T : Tri) :
    cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
      + cornerAngle (T.pts 2) (T.pts 1) (T.pts 0)
      + cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi := by
  have h10 : T.pts 1 ≠ T.pts 0 := by
    intro h
    have : (1 : Fin 3) = 0 := T.indep.injective h
    exact absurd this (by decide)
  have key := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (V := Plane) (p₁ := T.pts 0) (p₂ := T.pts 1) (T.pts 2) h10
  unfold cornerAngle
  rw [EuclideanGeometry.angle_comm (V := Plane) (T.pts 1) (T.pts 0) (T.pts 2),
      EuclideanGeometry.angle_comm (V := Plane) (T.pts 2) (T.pts 1) (T.pts 0),
      EuclideanGeometry.angle_comm (V := Plane) (T.pts 0) (T.pts 2) (T.pts 1)]
  linarith [key]

/-! ## The vertex-figure bridge (arithmetic half of G5)

`BaseBetaE1.vertex_pi`, `vertex_beta_corner` and `vertex_apex` are stated for *given integer
multiplicities* satisfying two linear equations.  The step from a *real* vertex figure to those
integers was, until now, entirely on paper.  It has two halves:

* the geometric half — a vertex figure of the dissection yields naturals `x, y, z` with
  `x·α + y·β + z·γ` equal to `2π`, `π`, or a corner angle.  **Not available** (see `HasAngleSums`).
* the arithmetic half — from such a real equation, together with `3α+2β = π` and `α ∉ ℚπ`, the two
  integer equations follow.  **That is what is proved here**, and it is unconditional.

The mechanism: `α` and `π` are linearly independent over `ℚ` (that is exactly the irrationality
hypothesis), so a relation `A·α + B·π = 0` with integer `A, B` forces `A = B = 0`. -/

/-- **ℚ-linear independence of `α` and `π`.**  If `α` is not a rational multiple of `π`, an integral
relation `A·α + B·π = 0` is trivial.  (Same mechanism as `BaseBetaE1.direction_free`.) -/
theorem angle_indep {α : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (A B : ℤ)
    (h : (A : ℝ) * α + (B : ℝ) * Real.pi = 0) : A = 0 ∧ B = 0 := by
  have hA : A = 0 := by
    by_contra hA0
    apply hirr
    have hAR : (A : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hA0
    refine ⟨((-B : ℤ) : ℚ) / ((A : ℤ) : ℚ), ?_⟩
    push_cast
    field_simp
    linarith
  refine ⟨hA, ?_⟩
  have h' : (B : ℝ) * Real.pi = 0 := by
    rw [hA] at h
    push_cast at h
    linarith
  rcases mul_eq_zero.mp h' with hb | hpi
  · exact_mod_cast hb
  · exact absurd hpi Real.pi_ne_zero

/-- **The vertex-figure bridge.**  Let the tile have angles `α`, `β`, `γ = 2α + β` with
`3α + 2β = π` and `α ∉ ℚπ` (both supplied by `BaseBetaE1.tile_alpha_irrational` for every tile of
the family).  If a vertex figure consists of `x` copies of `α`, `y` of `β` and `z` of `γ`, and the
total is `s·α + t·β`, then the multiplicities satisfy `x + 2z = s` and `y + z = t`.

Eliminating `β = (π − 3α)/2` turns the real equation into `A·α + B·π = 0` with
`A = 2(x+2z−s) − 3(y+z−t)` and `B = y+z−t`; `angle_indep` kills both. -/
theorem vertex_multiplicities {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ) (s t : ℤ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = (s : ℝ) * α + (t : ℝ) * β) :
    (x : ℤ) + 2 * z = s ∧ (y : ℤ) + z = t := by
  have hβ : β = (Real.pi - 3 * α) / 2 := by linarith
  have hkey : ((2 * ((x : ℤ) + 2 * z - s) - 3 * ((y : ℤ) + z - t) : ℤ) : ℝ) * α
      + (((y : ℤ) + z - t : ℤ) : ℝ) * Real.pi = 0 := by
    rw [hβ] at hsum
    push_cast
    linear_combination 2 * hsum
  obtain ⟨hA, hB⟩ := angle_indep hirr
    (2 * ((x : ℤ) + 2 * z - s) - 3 * ((y : ℤ) + z - t)) ((y : ℤ) + z - t) hkey
  omega

/-- **Supplies the hypotheses of `BaseBetaE1.vertex_pi`.**  A vertex figure summing to `π` — a point
interior to an edge — has multiplicities obeying `y + z = 2` and `2x + z = 3y`, which are precisely
the two hypotheses `h1`, `h2` that `vertex_pi` consumes. -/
theorem vertex_pi_multiplicities {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = Real.pi) :
    y + z = 2 ∧ 2 * x + z = 3 * y := by
  have h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β)
      = ((3 : ℤ) : ℝ) * α + ((2 : ℤ) : ℝ) * β := by
    push_cast
    linear_combination hsum - hrel
  obtain ⟨h1, h2⟩ := vertex_multiplicities hrel hirr x y z 3 2 h
  omega

/-- **Supplies the hypotheses of `BaseBetaE1.vertex_beta_corner`.**  A vertex figure at a corner of
angle `β` obeys `y + z = 1` and `2x + z + 3 = 3y`. -/
theorem vertex_beta_corner_multiplicities {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = β) :
    y + z = 1 ∧ 2 * x + z + 3 = 3 * y := by
  have h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β)
      = ((0 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * β := by
    push_cast
    linear_combination hsum
  obtain ⟨h1, h2⟩ := vertex_multiplicities hrel hirr x y z 0 1 h
  omega

/-- **Supplies the hypotheses of `BaseBetaE1.vertex_apex`.**  The apex angle is `π − 2β = 3α`; a
vertex figure there obeys `y + z = 0` and `2x + z = 3y + 6`. -/
theorem vertex_apex_multiplicities {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = 3 * α) :
    y + z = 0 ∧ 2 * x + z = 3 * y + 6 := by
  have h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β)
      = ((3 : ℤ) : ℝ) * α + ((0 : ℤ) : ℝ) * β := by
    push_cast
    linear_combination hsum
  obtain ⟨h1, h2⟩ := vertex_multiplicities hrel hirr x y z 3 0 h
  omega

/-! ## What is still assumed

The following are `Prop`-valued **definitions**, not axioms.  Nothing above uses them.  They name,
precisely, the geometric facts the paper still supplies by hand, so that a downstream theorem can
take one as an explicit hypothesis — the discipline of `BaseBetaWalks.gamma_injection` and
`InvariantCore.cancellation_core`. -/

/-- **G2 — the angle sums.**  `angleAt D v i` is intended to be the angle the `i`-th tile subtends
at the point `v` (zero if `v` is not on the tile).  `HasAngleSums` asserts the three classical
statements: the tile angles at a point interior to the target sum to `2π`; at a point interior to a
side of the target they sum to `π`; at a corner of the target they sum to that corner's angle.

**Status: research-level in Lean.**  Mathlib has the triangle angle sum
(`EuclideanGeometry.angle_add_angle_add_angle_eq_pi`) and the on-a-line splitting
(`angle_add_angle_eq_pi_of_angle_eq_pi`), and it has free *mod 2π* additivity for oriented angles
(`Orientation.oangle_add`).  It has **nothing** that lifts a mod-2π sum to a real-valued one beyond
two summands (`Real.Angle.toReal_add_eq_toReal_add_toReal`), and no sectors, no angular measure and
no winding number.  Distinguishing `2π` from `4π` for an `n`-fold fan must be built from scratch. -/
def HasAngleSums {N : ℕ} (D : Dissection N) (angleAt : Plane → Fin N → ℝ) : Prop :=
  (∀ v ∈ interior D.target.carrier, ∑ i, angleAt v i = 2 * Real.pi) ∧
  (∀ v ∈ frontier D.target.carrier, v ∉ Set.range D.target.pts →
    ∑ i, angleAt v i = Real.pi) ∧
  (∀ k : Fin 3, ∑ i, angleAt (D.target.pts k) i
    = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)))

/-- **G3 — the chain lemma.**  No vertex of the dissection lies in the relative interior of a tile
edge unless that edge is collinear with it; consequently each side of the target, and each maximal
interior segment, is partitioned into whole tile edges, and the far side of any segment is met by a
chain of whole edges.  Stated here as: the set of tile vertices meeting a segment `S` cuts `S` into
sub-segments each of which is a union of whole tile edges.

**Status: hard but not research-level** — it is a finite combinatorial statement about a finite
point configuration, but it needs a usable notion of "edge of a tile" and of "maximal segment",
neither of which Mathlib provides.  This is the input to `BaseBetaWalks`' walk equations
`P·a + Q·b + R·c = (side length)`. -/
def HasEdgeChains {N : ℕ} (D : Dissection N) (edgeOf : Fin N → Fin 3 → Set Plane) : Prop :=
  ∀ i : Fin 3, ∃ (part : Finset (Fin N × Fin 3)),
    (⋃ e ∈ part, edgeOf e.1 e.2) = segment ℝ (D.target.pts i) (D.target.pts (i + 1))

/-!
NOTE (2026-07-30). The previous form of `HasEdgeChains` quantified over *every* subset `S` of the
frontier, demanding each be a union of whole tile edges. That is unsatisfiable — a singleton subset
is not such a union — so any theorem assuming it would have been vacuously true. Nothing in the
development assumed it, so no result was affected, but the statement is corrected above to the one
its own docstring describes: each of the target's three sides is a finite union of whole tile edges.
That is exactly the input the walk equations `P·a + Q·b + R·c = (side length)` need.
-/

/-- The `i`-th edge of a triangle: the segment from vertex `i` to vertex `i+1`. This is the
`edgeOf` that `HasEdgeChains` quantifies over, made concrete. -/
def Tri.edge (T : Tri) (i : Fin 3) : Set Plane := segment ℝ (T.pts i) (T.pts (i + 1))

/-- **A tile meets a supporting line in a face.** If a linear functional `f` is bounded by `c` on a
triangle and the line `f = c` is a genuine line (`f ≠ 0`), the contact set is the convex hull of the
vertices on the line, and there are at most two of those: three would put the whole triangle on the
line, contradicting that a triangle has interior.

This is the step that makes a target side a union of WHOLE tile edges rather than partial ones,
which is the content of `HasEdgeChains`. It does not by itself discharge G3, which additionally
needs the ordering and exhaustion bookkeeping along the side. -/
theorem tile_contact_face (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hle : ∀ x ∈ T.carrier, f x ≤ c) :
    {x ∈ T.carrier | f x = c}
      = convexHull ℝ (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) :
          Set Plane) := by
  classical
  have hmem : ∀ v ∈ (Finset.univ.image T.pts), f v ≤ c := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hle _ (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hcar : T.carrier = convexHull ℝ ((Finset.univ.image T.pts : Finset Plane) : Set Plane) := by
    rw [Tri.carrier]; congr 1
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact ⟨i, rfl⟩
  rw [hcar]
  exact Erdos634.SupportFace.contact_eq_face f c _ hmem

/-- **At most two vertices of a tile lie on a supporting line.** Otherwise the whole triangle lies on
the line `f = c`, which has empty interior when `f ≠ 0`, contradicting `Tri.interior_nonempty`. -/
theorem two_vertices_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hall : ∀ i, f (T.pts i) = c) : False := by
  have hsub : T.carrier ⊆ {x | f x = c} := by
    rw [Tri.carrier]
    refine convexHull_min ?_ ?_
    · rintro x ⟨i, rfl⟩; exact hall i
    · intro a ha b hb ta tb hta htb htab
      simp only [Set.mem_setOf_eq] at *
      rw [map_add, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul]
      linear_combination c * htab
  obtain ⟨x, hx⟩ := T.interior_nonempty
  have hxc : f x = c := hsub (interior_subset hx)
  -- an interior point has a ball inside the carrier, hence inside the line: impossible for f ≠ 0
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext fun z => by simp [h z])
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  set t : ℝ := ε / (2 * ‖y‖) with ht
  have hynorm : 0 < ‖y‖ := by
    rcases eq_or_ne y 0 with rfl | hy0
    · simp at hy
    · exact norm_pos_iff.mpr hy0
  have htpos : 0 < t := by positivity
  have hdist : dist (x + t • y) x = t * ‖y‖ := by
    rw [dist_eq_norm]
    have hxy : x + t • y - x = t • y := by abel
    rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  have hmemball : x + t • y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, hdist]
    have hhalf : t * ‖y‖ = ε / 2 := by rw [ht]; field_simp
    rw [hhalf]; linarith
  have : f (x + t • y) = c := hsub (interior_subset (hball hmemball))
  rw [map_add, map_smul, hxc, smul_eq_mul] at this
  have : t * f y = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (ne_of_gt htpos)
  · exact hy h

/-- Each tile lies inside the target. -/
theorem tile_subset_target (D : Dissection N) (j : Fin N) :
    (D.tile j).carrier ⊆ D.target.carrier := by
  rw [← D.covers]; exact Set.subset_iUnion (fun i => (D.tile i).carrier) j

/-- **The tile contacts exhaust the side.** For a functional `f` bounded by `c` on the target, the
contact sets of the tiles with the line `f = c` cover exactly the target's own contact set. Combined
with `tile_contact_face`, applied both to each tile and to the target itself, this says: the side of
the target is the union of the faces the tiles present to it.

This is the exhaustion half of G3. What it leaves is that those faces are edges rather than isolated
vertices, which needs the finitely-many-vertices argument, not this one. -/
theorem contacts_cover_side (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (⋃ j, {x ∈ (D.tile j).carrier | f x = c}) = {x ∈ D.target.carrier | f x = c} := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    exact ⟨tile_subset_target D j hxj.1, hxj.2⟩
  · rintro ⟨hxt, hfx⟩
    rw [← D.covers] at hxt
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxt
    exact Set.mem_iUnion.mpr ⟨j, hxj, hfx⟩

/-- A tile edge is closed: it is the convex hull of a pair, hence compact. -/
theorem Tri.isClosed_edge (T : Tri) (k : Fin 3) : IsClosed (T.edge k) := by
  have hc : IsCompact (T.edge k) := by
    rw [Tri.edge, segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  exact hc.isClosed

/-- **Any two distinct vertices of a triangle span one of its edges.**  The three edges realise the
three unordered pairs, so the convex hull of two distinct vertices is an edge, up to the symmetry
`segment x y = segment y x`. This is what turns "the contact face has two vertices" into "the contact
face IS a tile edge". -/
theorem Tri.pair_eq_edge (T : Tri) {p q : Fin 3} (hpq : p ≠ q) :
    ∃ k, segment ℝ (T.pts p) (T.pts q) = T.edge k := by
  simp only [Tri.edge]
  fin_cases p <;> fin_cases q <;> simp_all <;>
    [ exact ⟨0, rfl⟩;
      exact ⟨2, segment_symm ℝ _ _⟩;
      exact ⟨0, segment_symm ℝ _ _⟩;
      exact ⟨1, rfl⟩;
      exact ⟨2, rfl⟩;
      exact ⟨1, segment_symm ℝ _ _⟩ ]

/-- The three vertices of a triangle form an affine basis of the plane. -/
noncomputable def Tri.basis (T : Tri) : AffineBasis (Fin 3) ℝ Plane :=
  AffineBasis.mk T.pts T.indep (by
    have := T.affineSpan_eq_top
    rwa [Tri.carrier, affineSpan_convexHull] at this)

/-- **G3a — every side of a triangle has a supporting functional.**  For the side from `pts i` to
`pts (i+1)`, the barycentric coordinate opposite that side vanishes on both its endpoints and equals
`1` at the third vertex. Its negated linear part, with the constant absorbed into `c`, is a linear
functional bounded by `c` on the triangle, attaining `c` exactly at the two endpoints and strictly
less at the third vertex.

Together with `tile_contact_face` this identifies `{x ∈ carrier | f x = c}` as the side itself, which
is what the chain lemma needs in order to be instantiated. -/
theorem exists_supporting (T : Tri) (i : Fin 3) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ x ∈ T.carrier, f x ≤ c) ∧
      f (T.pts i) = c ∧ f (T.pts (i + 1)) = c ∧ f (T.pts (i + 2)) < c := by
  classical
  set g : Plane →ᵃ[ℝ] ℝ := T.basis.coord (i + 2) with hg
  have hdecomp : ∀ x, g x = g.linear x + g 0 := by
    intro x; simpa using congrFun (AffineMap.decomp g) x
  have hb : ∀ j, g (T.pts j) = if i + 2 = j then 1 else 0 := by
    intro j; exact AffineBasis.coord_apply T.basis (i + 2) j
  have hne1 : i + 2 ≠ i := by fin_cases i <;> decide
  have hne2 : i + 2 ≠ i + 1 := by fin_cases i <;> decide
  have h0 : g (T.pts i) = 0 := by rw [hb]; simp [hne1]
  have h1 : g (T.pts (i + 1)) = 0 := by rw [hb]; simp [hne2]
  have h2 : g (T.pts (i + 2)) = 1 := by rw [hb]; simp
  have hnonneg : ∀ j, (0:ℝ) ≤ g (T.pts j) := by
    intro j; rw [hb]; split <;> norm_num
  refine ⟨-g.linear, g 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hlin0 : g.linear = 0 := by
      have := congrArg Neg.neg hzero; simpa using this
    have ha := hdecomp (T.pts i)
    have hc := hdecomp (T.pts (i + 2))
    rw [hlin0] at ha hc
    simp only [LinearMap.zero_apply, zero_add] at ha hc
    rw [h0] at ha; rw [h2] at hc
    linarith
  · intro x hx
    rw [Tri.carrier] at hx
    show x ∈ {y : Plane | (-g.linear) y ≤ g 0}
    refine convexHull_min ?_ ?_ hx
    · rintro y ⟨j, rfl⟩
      simp only [Set.mem_setOf_eq, LinearMap.neg_apply]
      linarith [hdecomp (T.pts j), hnonneg j]
    · intro a ha b hb ta tb hta htb htab
      simp only [Set.mem_setOf_eq, LinearMap.neg_apply] at ha hb ⊢
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have key : -(ta * g.linear a + tb * g.linear b)
               = ta * (-g.linear a) + tb * (-g.linear b) := by ring
      rw [key]
      calc ta * (-g.linear a) + tb * (-g.linear b)
          ≤ ta * g 0 + tb * g 0 :=
            add_le_add (mul_le_mul_of_nonneg_left ha hta) (mul_le_mul_of_nonneg_left hb htb)
        _ = g 0 := by rw [← add_mul, htab, one_mul]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts i), h0]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts (i + 1)), h1]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts (i + 2)), h2]

/-- **A tile's contact with a supporting line is an edge, once a non-vertex point lies on it.**
The contact is the hull of the tile's vertices on the line; if a point of the contact is not a
vertex, at least two vertices are involved, and `two_vertices_on_line` forbids all three, so exactly
two are, and `pair_eq_edge` names the edge. -/
theorem contact_is_edge (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ x ∈ T.carrier, f x ≤ c) {x : Plane} (hx : x ∈ T.carrier) (hfx : f x = c)
    (hxv : ∀ k, x ≠ T.pts k) :
    ∃ k, {y ∈ T.carrier | f y = c} = T.edge k := by
  classical
  set V : Finset (Fin 3) := Finset.univ.filter (fun k => f (T.pts k) = c) with hV
  have himg : (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) : Set Plane)
            = T.pts '' (V : Set (Fin 3)) := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hv
      obtain ⟨⟨k, _, hk⟩, hfv⟩ := hv
      refine ⟨k, ?_, hk⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter]
      exact ⟨Finset.mem_univ k, by rw [hk]; exact hfv⟩
    · rintro ⟨k, hkV, rfl⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter] at hkV
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨k, Finset.mem_univ k, rfl⟩, hkV.2⟩
  have hcontact : {y ∈ T.carrier | f y = c} = convexHull ℝ (T.pts '' (V : Set (Fin 3))) := by
    rw [tile_contact_face T f c hle, himg]
  have hxc : x ∈ convexHull ℝ (T.pts '' (V : Set (Fin 3))) := by
    rw [← hcontact]; exact ⟨hx, hfx⟩
  have hcard3 : V.card ≤ 3 := by
    have := Finset.card_le_card (Finset.subset_univ V)
    simpa using this
  interval_cases h : V.card
  · -- empty
    rw [Finset.card_eq_zero] at h
    rw [h] at hxc; simp at hxc
  · -- a single vertex
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
    rw [hk] at hxc
    simp only [Finset.coe_singleton, Set.image_singleton, convexHull_singleton,
      Set.mem_singleton_iff] at hxc
    exact absurd hxc (hxv k)
  · -- two vertices: the contact is an edge
    obtain ⟨p, q, hpq, hV2⟩ := Finset.card_eq_two.mp h
    obtain ⟨k, hk⟩ := T.pair_eq_edge hpq
    refine ⟨k, ?_⟩
    rw [hcontact, hV2]
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
    rw [convexHull_pair, hk]
  · -- all three: impossible
    exfalso
    have hall : ∀ k, f (T.pts k) = c := by
      intro k
      have hmem : k ∈ V := by
        have : V = Finset.univ := Finset.eq_univ_of_card V (by simpa using h)
        rw [this]; exact Finset.mem_univ k
      simpa [hV, Finset.mem_filter] using hmem
    exact two_vertices_on_line T f c hf hall

/-- The target's own contact with the supporting line of side `i` is that side. -/
theorem target_contact_side (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {i : Fin 3}
    (hle : ∀ x ∈ T.carrier, f x ≤ c) (hi : f (T.pts i) = c) (hi1 : f (T.pts (i + 1)) = c)
    (hi2 : f (T.pts (i + 2)) < c) :
    {x ∈ T.carrier | f x = c} = segment ℝ (T.pts i) (T.pts (i + 1)) := by
  classical
  set V : Finset (Fin 3) := Finset.univ.filter (fun k => f (T.pts k) = c) with hV
  have hexh : ∀ k : Fin 3, k = i ∨ k = i + 1 ∨ k = i + 2 := by
    intro k; fin_cases i <;> fin_cases k <;> decide
  have hVeq : V = {i, i + 1} := by
    apply Finset.Subset.antisymm
    · intro k hk
      rw [hV, Finset.mem_filter] at hk
      rcases hexh k with rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact absurd hk.2 (by linarith)
    · intro k hk
      rw [hV, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk'
      · exact hi
      · rw [Finset.mem_singleton.mp hk']; exact hi1
  have himg : (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) : Set Plane)
            = T.pts '' (V : Set (Fin 3)) := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hv
      obtain ⟨⟨k, _, hk⟩, hfv⟩ := hv
      refine ⟨k, ?_, hk⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter]
      exact ⟨Finset.mem_univ k, by rw [hk]; exact hfv⟩
    · rintro ⟨k, hkV, rfl⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter] at hkV
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨k, Finset.mem_univ k, rfl⟩, hkV.2⟩
  rw [tile_contact_face T f c hle, himg, hVeq]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  rw [convexHull_pair]

/-- **G3 — the chain lemma, proved.**  Each side of the target is exactly the union of the tile
edges lying on it. -/
theorem hasEdgeChains_edge (D : Dissection N) :
    HasEdgeChains D (fun j k => (D.tile j).edge k) := by
  classical
  intro i
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  set S : Set Plane := segment ℝ (D.target.pts i) (D.target.pts (i + 1)) with hSdef
  have hS : {x ∈ D.target.carrier | f x = c} = S :=
    target_contact_side D.target f c hle hi hi1 hi2
  set part : Finset (Fin N × Fin 3) :=
    Finset.univ.filter (fun e : Fin N × Fin 3 => (D.tile e.1).edge e.2 ⊆ S) with hpart
  refine ⟨part, ?_⟩
  apply Set.Subset.antisymm
  · -- every listed edge lies in the side
    intro x hx
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
    have : (D.tile e.1).edge e.2 ⊆ S := by
      rw [hpart, Finset.mem_filter] at he; exact he.2
    exact this hxe
  · -- and they cover it
    have hFfin : (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2).Finite :=
      Set.finite_range _
    have hUclosed : IsClosed (⋃ e ∈ part, (D.tile e.1).edge e.2) :=
      Set.Finite.isClosed_biUnion (Finset.finite_toSet part)
        (fun e _ => (D.tile e.1).isClosed_edge e.2)
    have hnd : D.target.pts i ≠ D.target.pts (i + 1) := by
      intro h
      have hij : i = i + 1 := D.target.indep.injective h
      fin_cases i <;> exact absurd hij (by decide)
    have hkey : S \ (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2)
              ⊆ ⋃ e ∈ part, (D.tile e.1).edge e.2 := by
      rintro x ⟨hxS, hxF⟩
      have hxt : x ∈ D.target.carrier ∧ f x = c := by rw [← hS] at hxS; exact hxS
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (by rw [D.covers]; exact hxt.1)
      have hlej : ∀ y ∈ (D.tile j).carrier, f y ≤ c :=
        fun y hy => hle y (tile_subset_target D j hy)
      have hxv : ∀ k, x ≠ (D.tile j).pts k := by
        intro k hk; exact hxF ⟨(j, k), hk.symm⟩
      obtain ⟨k, hk⟩ := contact_is_edge (D.tile j) f c hf hlej hxj hxt.2 hxv
      have hsub : (D.tile j).edge k ⊆ S := by
        rw [← hk, ← hS]
        rintro y ⟨hy1, hy2⟩
        exact ⟨tile_subset_target D j hy1, hy2⟩
      refine Set.mem_iUnion₂.mpr ⟨(j, k), ?_, ?_⟩
      · rw [hpart, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsub⟩
      · rw [← hk]; exact ⟨hxj, hxt.2⟩
    calc S ⊆ closure (S \ (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2)) :=
          Erdos634.SegmentDense.subset_closure_diff_finite hnd hFfin
      _ ⊆ closure (⋃ e ∈ part, (D.tile e.1).edge e.2) := closure_mono hkey
      _ = _ := hUclosed.closure_eq

/-- **G4 — the cancellation input.**  For a direction `d`, `Lint d` is the total directed length of
interior tile-edges in direction `d`.  `InteriorBalanced` asserts `Lint (d + π) = Lint d`, i.e. each
interior segment is covered exactly once from each side.

**Status: this is precisely the hypothesis `hLint` of `InvariantCore.cancellation_core`**, which is
already machine-checked to imply the Cancellation lemma.  Supplying it is the remaining geometric
content: it is where non-edge-to-edge incidences are absorbed (the two sides of a segment may
subdivide it differently, but each covers it once because the tiles cover the target with disjoint
interiors — the same fact `Dissection.aedisjoint` uses, but in a *length* rather than *area* form,
which is why it does not follow from the area work above). -/
def InteriorBalanced {Dir : Type*} (neg : Dir → Dir) (Lint : Dir → ℤ) : Prop :=
  ∀ d, Lint (neg d) = Lint d

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.volume_pos
#print axioms Erdos634.Geometry.Dissection.aedisjoint
#print axioms Erdos634.Geometry.Dissection.volume_target
#print axioms Erdos634.Geometry.Dissection.pos
#print axioms Erdos634.Geometry.cornerAngle_sum
#print axioms Erdos634.Geometry.angle_indep
#print axioms Erdos634.Geometry.vertex_multiplicities
#print axioms Erdos634.Geometry.vertex_pi_multiplicities
#print axioms Erdos634.Geometry.vertex_beta_corner_multiplicities
#print axioms Erdos634.Geometry.vertex_apex_multiplicities
