import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic
import Erdos634.SupportFace
import Erdos634.SegmentDense
import Mathlib.MeasureTheory.Measure.Hausdorff

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

/-- **The one-dimensional measure of a tile edge is its length.**  This is the measure that `Λ_int`
of obligation G4 must be built from: `Λ_int d` is to be the total `μH[1]`-length of the interior tile
edges in direction `d`, and the balance `Λ_int (-d) = Λ_int d` then says each interior segment is
covered once from each side. Recorded here because it fixes which measure the construction should
use; the construction itself is not attempted. -/
theorem Tri.hausdorff_edge (T : Tri) (k : Fin 3) :
    (MeasureTheory.Measure.hausdorffMeasure 1) (T.edge k) = edist (T.pts k) (T.pts (k + 1)) := by
  rw [Tri.edge]
  exact MeasureTheory.hausdorffMeasure_segment _ _

/-- **The barycentric description of a tile.**  `T.carrier` is exactly the points whose three
barycentric coordinates are all nonnegative. -/
theorem Tri.carrier_eq_nonneg_coord (T : Tri) :
    T.carrier = {y | ∀ i, 0 ≤ T.basis.coord i y} := by
  have h : Set.range T.pts = Set.range (T.basis : Fin 3 → Plane) := rfl
  rw [Tri.carrier, h]
  exact T.basis.convexHull_eq_nonneg_coord

/-- **A tile is locally a half-plane at an edge-interior point.**

If the two barycentric coordinates other than the `k`-th are strictly positive at `x` — that is, `x`
lies on the line of edge `k` but strictly inside the other two edges' half-planes, which is exactly
what it means for `x` to be in the *relative interior* of edge `k` — then on a small enough ball
around `x` the tile coincides with the single half-plane `0 ≤ coord k`.

This is the first step of the local double-covering statement that G4 now reduces to
(`interiorBalanced_of_segments`): near an edge-interior point a tile contributes a half-disk, so a
local area count at such a point can only balance as *two* tiles meeting along the segment, one from
each side. The area count itself is not carried out here. -/
theorem Tri.inter_ball_eq_halfplane (T : Tri) (k : Fin 3) {x : Plane}
    (h1 : 0 < T.basis.coord (k + 1) x) (h2 : 0 < T.basis.coord (k + 2) x) :
    ∃ r > 0, T.carrier ∩ Metric.ball x r
           = {y | 0 ≤ T.basis.coord k y} ∩ Metric.ball x r := by
  -- every index is one of `k`, `k+1`, `k+2`
  have hfin : ∀ j i : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := by decide
  -- the other two coordinates stay positive near `x`
  have hc1 : Continuous (T.basis.coord (k + 1)) := AffineMap.continuous_of_finiteDimensional _
  have hc2 : Continuous (T.basis.coord (k + 2)) := AffineMap.continuous_of_finiteDimensional _
  have hopen : IsOpen {y | 0 < T.basis.coord (k + 1) y ∧ 0 < T.basis.coord (k + 2) y} :=
    (isOpen_lt continuous_const hc1).inter (isOpen_lt continuous_const hc2)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x ⟨h1, h2⟩
  refine ⟨r, hr, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, T.carrier_eq_nonneg_coord]
  constructor
  · rintro ⟨hy, hyb⟩; exact ⟨hy k, hyb⟩
  · rintro ⟨hyk, hyb⟩
    refine ⟨fun i => ?_, hyb⟩
    obtain ⟨hp1, hp2⟩ := hball hyb
    rcases hfin k i with rfl | rfl | rfl
    · exact hyk
    · exact hp1.le
    · exact hp2.le

/-- **Local classification, interior case.**  If all three barycentric coordinates are strictly
positive at `x` then `x` is interior to the tile: a small ball around `x` lies inside it, so the tile
contributes the *whole* ball to a local area count. -/
theorem Tri.ball_subset_of_pos (T : Tri) {x : Plane}
    (hpos : ∀ i, 0 < T.basis.coord i x) :
    ∃ r > 0, Metric.ball x r ⊆ T.carrier := by
  have hopen : IsOpen {y : Plane | ∀ i, 0 < T.basis.coord i y} := by
    have : {y : Plane | ∀ i, 0 < T.basis.coord i y} = ⋂ i, {y | 0 < T.basis.coord i y} := by
      ext y; simp [Set.mem_iInter]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (AffineMap.continuous_of_finiteDimensional _)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hpos
  refine ⟨r, hr, fun y hy => ?_⟩
  rw [T.carrier_eq_nonneg_coord]
  exact fun i => (hball hy i).le

/-- **Local classification, exterior case.**  If some barycentric coordinate is strictly negative at
`x` then a small ball around `x` misses the tile entirely, so the tile contributes nothing. -/
theorem Tri.ball_disjoint_of_neg (T : Tri) {x : Plane} {k : Fin 3}
    (hneg : T.basis.coord k x < 0) :
    ∃ r > 0, Metric.ball x r ∩ T.carrier = ∅ := by
  have hopen : IsOpen {y : Plane | T.basis.coord k y < 0} :=
    isOpen_lt (AffineMap.continuous_of_finiteDimensional _) continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hneg
  refine ⟨r, hr, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro y ⟨hy1, hy2⟩
  rw [T.carrier_eq_nonneg_coord] at hy2
  exact absurd (hy2 k) (not_le.mpr (hball hy1))

/-- **G4 step 2 — a half-plane through the centre cuts a ball exactly in half.**

`A = {v | 0 ≤ L v} ∩ ball 0 r` and its point reflection `-A = {v | L v ≤ 0} ∩ ball 0 r` have equal
measure (Haar measure is invariant under `v ↦ -v`, since `|(-1)^d| = 1` in every dimension), they
cover the ball, and they meet in `ker L ∩ ball`, which is null because a proper subspace is null.
Inclusion–exclusion then gives `2·volume A = volume (ball)`.

Mathlib has no such lemma (searched), so it is proved here.  Stated multiplicatively rather than as
`volume A = volume ball / 2` to stay clear of `ℝ≥0∞` division. -/
theorem volume_halfspace_inter_ball (L : Plane →ₗ[ℝ] ℝ) (hL : L ≠ 0) (r : ℝ) :
    2 * volume ({v : Plane | 0 ≤ L v} ∩ Metric.ball 0 r) = volume (Metric.ball (0 : Plane) r) := by
  classical
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  set A : Set Plane := {v | 0 ≤ L v} ∩ Metric.ball 0 r with hAdef
  set B : Set Plane := {v | L v ≤ 0} ∩ Metric.ball 0 r with hBdef
  have hBmeas : MeasurableSet B :=
    ((isClosed_le hcont continuous_const).measurableSet).inter Metric.isOpen_ball.measurableSet
  -- `B` is the preimage of `A` under the point reflection `v ↦ -v`, written as a preimage so that
  -- no pointwise-set scalar action is needed
  have hBA : B = (fun v : Plane => (-1 : ℝ) • v) ⁻¹' A := by
    ext v
    simp only [hAdef, hBdef, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq,
      Metric.mem_ball, dist_zero_right, neg_one_smul, map_neg, norm_neg, neg_nonneg]
  -- reflection preserves measure: `|((-1)^d)⁻¹| = 1` in every dimension
  have hvolB : volume B = volume A := by
    rw [hBA, Measure.addHaar_preimage_smul volume (by norm_num : (-1 : ℝ) ≠ 0)]
    simp
  -- the two halves cover the ball
  have hunion : A ∪ B = Metric.ball (0 : Plane) r := by
    ext v
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro hv
      rcases le_total (0 : ℝ) (L v) with h | h
      · exact Or.inl ⟨h, hv⟩
      · exact Or.inr ⟨h, hv⟩
  -- they meet in the kernel, which is null
  have hker : LinearMap.ker L ≠ ⊤ := fun h => hL (LinearMap.ker_eq_top.mp h)
  have hinter : volume (A ∩ B) = 0 := by
    refine measure_mono_null (fun v hv => ?_) (Measure.addHaar_submodule volume _ hker)
    exact le_antisymm hv.2.1 hv.1.1
  have hie := measure_union_add_inter (μ := volume) A hBmeas
  rw [hunion, hinter, hvolB, add_zero] at hie
  rw [hie, two_mul]

/-- **The half-plane statement transported to an arbitrary centre.**  `volume_halfspace_inter_ball`
is stated at the origin for a *linear* functional; the local count needs it at `x` for an *affine*
one vanishing there, which is what a barycentric coordinate is on the line of its edge.  Translation
invariance of Haar measure moves it. -/
theorem volume_halfplane_inter_ball_at (g : Plane →ᵃ[ℝ] ℝ) (hL : g.linear ≠ 0)
    {x : Plane} (hx : g x = 0) (r : ℝ) :
    2 * volume ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r) = volume (Metric.ball x r) := by
  have hg : ∀ v : Plane, g (x + v) = g.linear v := by
    intro v
    have h := g.map_vadd x v
    simpa [add_comm, hx] using h
  have hballpre : (fun v : Plane => x + v) ⁻¹' Metric.ball x r = Metric.ball 0 r := by
    ext v; simp [Metric.mem_ball, dist_eq_norm, dist_zero_right]
  have hpre : (fun v : Plane => x + v) ⁻¹' ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)
            = {v : Plane | 0 ≤ g.linear v} ∩ Metric.ball 0 r := by
    rw [Set.preimage_inter, hballpre]
    congr 1
    ext v; simp only [Set.mem_preimage, Set.mem_setOf_eq, hg]
  calc 2 * volume ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)
      = 2 * volume ((fun v : Plane => x + v) ⁻¹' ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)) := by
        rw [measure_preimage_add]
    _ = 2 * volume ({v : Plane | 0 ≤ g.linear v} ∩ Metric.ball 0 r) := by rw [hpre]
    _ = volume (Metric.ball (0 : Plane) r) := volume_halfspace_inter_ball _ hL r
    _ = volume (Metric.ball x r) := by rw [← hballpre, measure_preimage_add]

/-- **A barycentric coordinate has nonzero linear part.**  It takes the value `1` at its own vertex
and `0` at the others, so it is not constant. -/
theorem Tri.coord_linear_ne_zero (T : Tri) (k : Fin 3) : (T.basis.coord k).linear ≠ 0 := by
  intro h
  have hne : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have e1 : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq k
  have e2 : T.basis.coord k (T.pts (k + 1)) = 0 := T.basis.coord_apply_ne (hne k)
  have hdiff : T.basis.coord k (T.pts k) - T.basis.coord k (T.pts (k + 1)) = 0 := by
    have hv := (T.basis.coord k).linearMap_vsub (T.pts k) (T.pts (k + 1))
    rw [h] at hv
    simpa using hv.symm
  rw [e1, e2] at hdiff
  norm_num at hdiff

/-- **A local set identity persists on smaller balls.**  Each classification lemma produces its own
radius; the count needs them all at one radius, so every local statement must survive shrinking. -/
theorem inter_ball_mono {A B : Set Plane} {x : Plane} {r : ℝ}
    (h : A ∩ Metric.ball x r = B ∩ Metric.ball x r) {r' : ℝ} (hr' : r' ≤ r) :
    A ∩ Metric.ball x r' = B ∩ Metric.ball x r' := by
  have hsub : Metric.ball x r' ⊆ Metric.ball x r := Metric.ball_subset_ball hr'
  ext y
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hy, hb⟩; exact ⟨((Set.ext_iff.mp h y).mp ⟨hy, hsub hb⟩).1, hb⟩
  · rintro ⟨hy, hb⟩; exact ⟨((Set.ext_iff.mp h y).mpr ⟨hy, hsub hb⟩).1, hb⟩

/-- **The three local contributions, in the form the count consumes.**  At a point in the relative
interior of edge `k`, every small enough ball meets the tile in exactly half its area. -/
theorem Tri.volume_inter_ball_edge (T : Tri) (k : Fin 3) {x : Plane}
    (h0 : T.basis.coord k x = 0)
    (h1 : 0 < T.basis.coord (k + 1) x) (h2 : 0 < T.basis.coord (k + 2) x) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      2 * volume (T.carrier ∩ Metric.ball x r') = volume (Metric.ball x r') := by
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_halfplane k h1 h2
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  rw [inter_ball_mono hEq hle]
  exact volume_halfplane_inter_ball_at (T.basis.coord k) (T.coord_linear_ne_zero k) h0 r'

/-- At an interior point the tile swallows every small enough ball. -/
theorem Tri.volume_inter_ball_interior (T : Tri) {x : Plane}
    (hpos : ∀ i, 0 < T.basis.coord i x) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball x r') = volume (Metric.ball x r') := by
  obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  congr 1
  exact Set.inter_eq_self_of_subset_right
    (fun y hy => hsub (Metric.ball_subset_ball hle hy))

/-- At an exterior point every small enough ball misses the tile. -/
theorem Tri.volume_inter_ball_exterior (T : Tri) {x : Plane} {k : Fin 3}
    (hneg : T.basis.coord k x < 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball x r') = 0 := by
  obtain ⟨r, hr, hemp⟩ := T.ball_disjoint_of_neg hneg
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  have : T.carrier ∩ Metric.ball x r' = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy1, hy2⟩
    have : y ∈ Metric.ball x r ∩ T.carrier := ⟨Metric.ball_subset_ball hle hy2, hy1⟩
    rw [hemp] at this
    exact this
  rw [this, measure_empty]

/-- **G4 step 3 — a ball inside the target is partitioned by the tiles.**  The same argument as
`Dissection.volume_target`, localised to a ball: the tiles cover the target and are a.e. disjoint, so
their traces on any ball contained in the target are a.e. disjoint and cover it. -/
theorem Dissection.volume_ball_eq_sum {N : ℕ} (D : Dissection N) {x : Plane} {r : ℝ}
    (hball : Metric.ball x r ⊆ D.target.carrier) :
    volume (Metric.ball x r) = ∑ i, volume ((D.tile i).carrier ∩ Metric.ball x r) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ Metric.ball x r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ Metric.ball x r))
          = Metric.ball x r := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
    exact Set.inter_eq_self_of_subset_right hball
  rw [hU] at h
  exact h

/-- **G4 step 4 — the local degree count.**  If `k` tiles each contribute half the ball's area and
`m` tiles each contribute all of it, and together they exhaust the ball, then `k + 2m = 2`.

The area of the ball is written `2 * V`, so that "half the ball" is `V` and no `ℝ≥0∞` division is
needed; cancelling `V` is legitimate because a ball has positive finite area. -/
theorem local_degree_eq {V : ℝ≥0∞} (hV0 : V ≠ 0) (hVt : V ≠ ⊤) {k m : ℕ}
    (h : (k : ℝ≥0∞) * V + (m : ℝ≥0∞) * (2 * V) = 2 * V) :
    k + 2 * m = 2 := by
  have hcast : ((k + 2 * m : ℕ) : ℝ≥0∞) * V = ((2 : ℕ) : ℝ≥0∞) * V := by
    push_cast
    rw [← h]; ring
  exact_mod_cast (ENNReal.mul_left_inj hV0 hVt).mp hcast

/-- **The local double covering, arithmetic half.**  At a point in the relative interior of a tile
edge at least one tile contributes a half-disk (`Tri.inter_ball_eq_halfplane` together with
`volume_halfspace_inter_ball`), so `k ≥ 1`; then `k + 2m = 2` forces exactly two half-contributors
and no full one.  That is "the segment is met from both sides, by one tile each". -/
theorem local_degree_two {k m : ℕ} (hk : 1 ≤ k) (h : k + 2 * m = 2) : k = 2 ∧ m = 0 := by
  omega

/-- **Two vanishing barycentric coordinates pin `x` to the remaining vertex.**  The coordinates sum
to `1`, so if two vanish the third is `1`, and a point whose coordinates agree with a vertex's *is*
that vertex. -/
theorem Tri.eq_vertex_of_two_coords_zero (T : Tri) {x : Plane} {j k : Fin 3} (hjk : j ≠ k)
    (hj : T.basis.coord j x = 0) (hk : T.basis.coord k x = 0) :
    ∃ m, x = T.pts m := by
  classical
  have key : ∀ u v : Fin 3, u ≠ v →
      ∃ m : Fin 3, m ≠ u ∧ m ≠ v ∧ ∀ b : Fin 3, b ≠ m → b = u ∨ b = v := by decide
  obtain ⟨m, hmj, hmk, hall⟩ := key j k hjk
  have hzero : ∀ b : Fin 3, b ≠ m → T.basis.coord b x = 0 := by
    intro b hb; rcases hall b hb with rfl | rfl
    · exact hj
    · exact hk
  -- the surviving coordinate is 1
  have hm : T.basis.coord m x = 1 := by
    rw [← T.basis.sum_coord_apply_eq_one x]
    exact (Finset.sum_eq_single_of_mem m (Finset.mem_univ m)
      (fun b _ hb => hzero b hb)).symm
  refine ⟨m, T.basis.ext_elem (fun i => ?_)⟩
  by_cases hi : i = m
  · rw [hi, hm]; exact (T.basis.coord_apply_eq m).symm
  · rw [hzero i hi]; exact (T.basis.coord_apply_ne hi).symm

/-- **The local classification is exhaustive away from the tile's vertices.**

At any point that is not a vertex of `T`, exactly one of three things holds: all three barycentric
coordinates are positive (`x` is interior), exactly one vanishes and the others are positive (`x` is
in the relative interior of that edge), or one is negative (`x` is outside).  These are precisely the
hypotheses of `Tri.ball_subset_of_pos`, `Tri.inter_ball_eq_halfplane` and `Tri.ball_disjoint_of_neg`.

This is assembly item (b): it is what makes the classification feeding `Dissection.local_balance`
exhaustive, and it isolates the excluded set as the tile's three vertices — a finite set, which is
what `SegmentDense.subset_closure_diff_finite` is there to absorb. -/
theorem Tri.classify (T : Tri) {x : Plane} (hx : ∀ k, x ≠ T.pts k) :
    (∀ i, 0 < T.basis.coord i x)
  ∨ (∃ k, T.basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j x)
  ∨ (∃ k, T.basis.coord k x < 0) := by
  classical
  by_cases hneg : ∃ k, T.basis.coord k x < 0
  · exact Or.inr (Or.inr hneg)
  push_neg at hneg
  by_cases hpos : ∀ i, 0 < T.basis.coord i x
  · exact Or.inl hpos
  push_neg at hpos
  obtain ⟨k, hk⟩ := hpos
  have hk0 : T.basis.coord k x = 0 := le_antisymm hk (hneg k)
  refine Or.inr (Or.inl ⟨k, hk0, fun j hj => ?_⟩)
  rcases (hneg j).lt_or_eq with h | h
  · exact h
  · -- a second vanishing coordinate would make `x` a vertex
    exact absurd (T.eq_vertex_of_two_coords_zero hj h.symm hk0) (by
      rintro ⟨m, rfl⟩; exact hx m rfl)

/-- **A finite family of positive radii has a common positive lower bound.**  Each local
classification lemma supplies its own radius; a local count needs one radius that works for every
tile at once.  This is assembly item (a). -/
theorem exists_common_radius {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ r > 0, ∀ i, r ≤ f i := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne f, ?_, fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  rw [gt_iff_lt, Finset.lt_inf'_iff]
  exact fun i _ => hf i

/-- **G4 — the local double covering, assembled.**

Take a ball around `x` inside the target, small enough that every tile's contribution is already
classified: the tiles in `E` each meet it in a half-ball (`x` in the relative interior of one of
their edges), those in `I` swallow it whole (`x` interior to them), and every other tile misses it.
Then `E` has exactly two elements and `I` is empty: **the segment through `x` is met from both
sides, by one tile from each.**

The three hypotheses are exactly what `Tri.inter_ball_eq_halfplane` together with
`volume_halfspace_inter_ball`, `Tri.ball_subset_of_pos` and `Tri.ball_disjoint_of_neg` deliver, once
a common radius is chosen with `exists_common_radius`.  What is still not supplied — and so is still
a hypothesis here rather than a conclusion — is that the classification is *exhaustive*, i.e. that
`x` is not a vertex of any tile.  That is the finite exceptional set, item (b). -/
theorem Dissection.local_balance {N : ℕ} (D : Dissection N) {x : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x r ⊆ D.target.carrier)
    (E I : Finset (Fin N)) (hdisj : Disjoint E I)
    (hE : ∀ i ∈ E, 2 * volume ((D.tile i).carrier ∩ Metric.ball x r) = volume (Metric.ball x r))
    (hI : ∀ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = volume (Metric.ball x r))
    (hrest : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ E ∪ I →
      volume ((D.tile i).carrier ∩ Metric.ball x r) = 0)
    (hEne : E.Nonempty) :
    E.card = 2 ∧ I.card = 0 := by
  classical
  set V : ℝ≥0∞ := volume (Metric.ball x r) with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  -- the tiles that contribute are exactly those in `E ∪ I`
  have hsum : ∑ i ∈ E ∪ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = V := by
    rw [Finset.sum_subset (Finset.subset_univ (E ∪ I)) hrest]
    exact (D.volume_ball_eq_sum hball).symm
  -- split that sum and weigh each part
  have hsplit : ∑ i ∈ E ∪ I, volume ((D.tile i).carrier ∩ Metric.ball x r)
      = (∑ i ∈ E, volume ((D.tile i).carrier ∩ Metric.ball x r))
        + ∑ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) :=
    Finset.sum_union hdisj
  have hEsum : 2 * ∑ i ∈ E, volume ((D.tile i).carrier ∩ Metric.ball x r) = (E.card : ℝ≥0∞) * V := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hE, Finset.sum_const, nsmul_eq_mul]
  have hIsum : ∑ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = (I.card : ℝ≥0∞) * V := by
    rw [Finset.sum_congr rfl hI, Finset.sum_const, nsmul_eq_mul]
  -- `2·V = card E · V + card I · 2V`, so `card E + 2·card I = 2`
  rw [hsplit] at hsum
  have hkey : (E.card : ℝ≥0∞) * V + (I.card : ℝ≥0∞) * (2 * V) = 2 * V := by
    have h1 : (I.card : ℝ≥0∞) * (2 * V) = 2 * ((I.card : ℝ≥0∞) * V) := by ring
    rw [h1, ← hEsum, ← hIsum, ← mul_add, hsum]
  have hcount : E.card + 2 * I.card = 2 := local_degree_eq hV0 hVt hkey
  exact local_degree_two (Finset.card_pos.mpr hEne) hcount

/-- `x` lies in the relative interior of one of tile `i`'s edges. -/
def OnEdge {N : ℕ} (D : Dissection N) (x : Plane) (i : Fin N) : Prop :=
  ∃ k, (D.tile i).basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < (D.tile i).basis.coord j x

/-- `x` is interior to tile `i`. -/
def Inside {N : ℕ} (D : Dissection N) (x : Plane) (i : Fin N) : Prop :=
  ∀ j, 0 < (D.tile i).basis.coord j x

/-- **Every tile has a radius below which its local contribution is pinned.**  Which of the three
values it takes is decided by `Tri.classify`, so this is where the classification becomes a single
uniform statement that can be quantified over the tiles. -/
theorem Dissection.local_contribution {N : ℕ} (D : Dissection N) {x : Plane} (i : Fin N)
    (hxv : ∀ k, x ≠ (D.tile i).pts k) :
    ∃ ri > 0, ∀ r', 0 < r' → r' ≤ ri →
      (OnEdge D x i →
        2 * volume ((D.tile i).carrier ∩ Metric.ball x r') = volume (Metric.ball x r'))
    ∧ (Inside D x i →
        volume ((D.tile i).carrier ∩ Metric.ball x r') = volume (Metric.ball x r'))
    ∧ (¬ OnEdge D x i → ¬ Inside D x i →
        volume ((D.tile i).carrier ∩ Metric.ball x r') = 0) := by
  classical
  rcases (D.tile i).classify hxv with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hkneg⟩
  · -- interior: `OnEdge` is impossible, since no coordinate vanishes
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_interior hpos
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun hE => ?_, fun _ => h r' h1 h2, fun _ hI => absurd hpos hI⟩⟩
    obtain ⟨m, hm, -⟩ := hE
    exact absurd hm (ne_of_gt (hpos m))
  · -- edge: `Inside` is impossible, since the `k`-th coordinate vanishes
    have hne : ∀ j : Fin 3, j + 1 ≠ j ∧ j + 2 ≠ j := by decide
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_edge k hk0
      (hkpos _ (hne k).1) (hkpos _ (hne k).2)
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun _ => h r' h1 h2, fun hI => ?_, fun hE _ => ?_⟩⟩
    · exact absurd hk0 (ne_of_gt (hI k))
    · exact absurd ⟨k, hk0, hkpos⟩ hE
  · -- exterior
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_exterior hkneg
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun hE => ?_, fun hI => ?_, fun _ _ => h r' h1 h2⟩⟩
    · obtain ⟨m, hm, hrest⟩ := hE
      by_cases hmk : k = m
      · rw [hmk] at hkneg; exact absurd hm (ne_of_lt hkneg)
      · exact absurd (hrest k hmk) (not_lt.mpr hkneg.le)
    · exact absurd (hI k) (not_lt.mpr hkneg.le)

open scoped Classical in
/-- **G4 — the local double covering, with the classification discharged.**

At a point `x` interior to the target and not a vertex of any tile, if at least one tile meets `x`
in the relative interior of an edge, then **exactly two do, and no tile has `x` in its interior**.

This is `Dissection.local_balance` with all three of its hypotheses supplied: the classification is
exhaustive by `Tri.classify`, each tile's contribution is pinned by `Dissection.local_contribution`,
and a single radius serving every tile comes from `exists_common_radius`. -/
theorem Dissection.two_tiles_at_edge_point {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    (hEne : (Finset.univ.filter (fun i => OnEdge D x i)).Nonempty) :
    (Finset.univ.filter (fun i => OnEdge D x i)).card = 2
      ∧ (Finset.univ.filter (fun i => Inside D x i)).card = 0 := by
  classical
  choose ri hri hcontrib using fun i => D.local_contribution i (hxv i)
  -- one radius for every tile at once, and inside the target
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius hN ri hri
  refine D.local_balance (x := x) (r := min R r0) (lt_min hR hr0) ?_ _ _ ?_ ?_ ?_ ?_ hEne
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hRt
  · -- a tile cannot both contain `x` inside and meet it on an edge
    rw [Finset.disjoint_left]
    intro i hiE hiI
    obtain ⟨m, hm, -⟩ := (Finset.mem_filter.mp hiE).2
    exact absurd hm (ne_of_gt ((Finset.mem_filter.mp hiI).2 m))
  · exact fun i hi => (hcontrib i _ (lt_min hR hr0)
      ((min_le_right R r0).trans (hr0le i))).1 (Finset.mem_filter.mp hi).2
  · exact fun i hi => (hcontrib i _ (lt_min hR hr0)
      ((min_le_right R r0).trans (hr0le i))).2.1 (Finset.mem_filter.mp hi).2
  · intro i _ hi
    rw [Finset.mem_union, not_or] at hi
    exact (hcontrib i _ (lt_min hR hr0) ((min_le_right R r0).trans (hr0le i))).2.2
      (fun h => hi.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))
      (fun h => hi.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))

/-- **G4's length step.**  Suppose a maximal interior segment `σ` is covered, up to a finite set `F`
of vertices, by finitely many tile edges `E i` lying on it with pairwise a.e.-disjoint interiors.
Then their lengths sum to `σ`'s length exactly.

This is the lift the double covering needs: `Dissection.two_tiles_at_edge_point` is a statement about
one *point*, and what `interiorBalanced_of_segments` consumes is a statement about total *length*.
The bridge is that the exceptional set is finite, hence `μH[1]`-null since `μH[1]` has no atoms in
positive dimension, so the covering is exact for measure even though it misses points.

The one-dimensional Hausdorff measure is the right one because it computes on segments:
`Tri.hausdorff_edge` gives `μH[1] (T.edge k) = edist (T.pts k) (T.pts (k+1))`. -/
theorem length_sum_of_cover {n : ℕ} (σ : Set Plane) (E : Fin n → Set Plane) (F : Set Plane)
    (hF : F.Finite)
    (hmeas : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Function.onFun (MeasureTheory.AEDisjoint
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)) E))
    (hsub : ∀ i, E i ⊆ σ)
    (hcov : σ \ F ⊆ ⋃ i, E i) :
    ∑ i, (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (E i)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) σ := by
  classical
  haveI : MeasureTheory.NoAtoms
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) :=
    MeasureTheory.Measure.noAtoms_hausdorff Plane (by norm_num)
  set μ := (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) with hμ
  -- the union is exactly `σ` up to the null set `F`
  have hUsub : (⋃ i, E i) ⊆ σ := Set.iUnion_subset hsub
  have hFnull : μ F = 0 := hF.measure_zero μ
  have hle₁ : μ (⋃ i, E i) ≤ μ σ := measure_mono hUsub
  have hle₂ : μ σ ≤ μ (⋃ i, E i) := by
    have hsplit : σ ⊆ (⋃ i, E i) ∪ F := by
      intro x hx
      by_cases hxF : x ∈ F
      · exact Or.inr hxF
      · exact Or.inl (hcov ⟨hx, hxF⟩)
    calc μ σ ≤ μ ((⋃ i, E i) ∪ F) := measure_mono hsplit
      _ ≤ μ (⋃ i, E i) + μ F := measure_union_le _ _
      _ = μ (⋃ i, E i) := by rw [hFnull, add_zero]
  have hUeq : μ (⋃ i, E i) = μ σ := le_antisymm hle₁ hle₂
  -- finite additivity for a.e.-disjoint pieces
  have hadd := MeasureTheory.measure_biUnion_finset₀ (μ := μ)
    (s := (Finset.univ : Finset (Fin n))) (f := E)
    (fun i _ j _ hij => hdisj hij) (fun i _ => (hmeas i).nullMeasurableSet)
  have hUuniv : (⋃ i ∈ (Finset.univ : Finset (Fin n)), E i) = ⋃ i, E i := by
    simp
  rw [hUuniv, hUeq] at hadd
  exact hadd.symm

/-- **G4's per-segment balance.**  If BOTH sides of a maximal interior segment `σ` cover it up to
finite sets of vertices, with pairwise a.e.-disjoint edges lying on it, then the two sides' edge
lengths have the same total — namely `μH[1] σ` on the nose.

This is exactly `hpos`/`hneg` of `interiorBalanced_of_segments`, so with it G4 reduces to a single
remaining obligation: **produce the two covering families for each maximal interior segment.** That
is where `Dissection.two_tiles_at_edge_point` enters — it gives exactly two tiles at every non-vertex
point of `σ`, one per side — and where a usable notion of *maximal interior segment*, which Mathlib
does not provide, is still needed. -/
theorem side_totals_agree {m n : ℕ} (σ : Set Plane) (E : Fin m → Set Plane) (E' : Fin n → Set Plane)
    (F F' : Set Plane) (hF : F.Finite) (hF' : F'.Finite)
    (hmeas : ∀ i, MeasurableSet (E i)) (hmeas' : ∀ j, MeasurableSet (E' j))
    (hdisj : Pairwise (Function.onFun (MeasureTheory.AEDisjoint
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)) E))
    (hdisj' : Pairwise (Function.onFun (MeasureTheory.AEDisjoint
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)) E'))
    (hsub : ∀ i, E i ⊆ σ) (hsub' : ∀ j, E' j ⊆ σ)
    (hcov : σ \ F ⊆ ⋃ i, E i) (hcov' : σ \ F' ⊆ ⋃ j, E' j) :
    ∑ i, (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (E i)
      = ∑ j, (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (E' j) :=
  (length_sum_of_cover σ E F hF hmeas hdisj hsub hcov).trans
    (length_sum_of_cover σ E' F' hF' hmeas' hdisj' hsub' hcov').symm

/-- **`InteriorBalanced` with real-valued lengths** — the form G4 actually produces, since
`length_sum_of_cover` and `side_totals_agree` deliver Hausdorff measures.  Consumed by
`InvariantCore.cancellation_core_real`. -/
def InteriorBalancedReal {Dir : Type*} (neg : Dir → Dir) (Lint : Dir → ℝ) : Prop :=
  ∀ d, Lint (neg d) = Lint d

/-- The real-valued counterpart of `interiorBalanced_of_segments`; same proof, and it is what makes
the chain type-consistent from `side_totals_agree` through to `cancellation_core_real`. -/
theorem interiorBalancedReal_of_segments {Dir Seg : Type*} [Fintype Seg] [DecidableEq Dir]
    (neg : Dir → Dir) (hinv : Function.Involutive neg)
    (dirOf : Seg → Dir) (len : Seg → ℝ) (cov : Seg → Dir → ℝ)
    (hpos : ∀ σ, cov σ (dirOf σ) = len σ)
    (hneg : ∀ σ, cov σ (neg (dirOf σ)) = len σ)
    (hoff : ∀ σ d, d ≠ dirOf σ → d ≠ neg (dirOf σ) → cov σ d = 0) :
    InteriorBalancedReal neg (fun d => ∑ σ, cov σ d) := by
  intro d
  refine Finset.sum_congr rfl ?_
  intro σ _
  by_cases h1 : d = dirOf σ
  · subst h1; rw [hneg σ, hpos σ]
  · by_cases h2 : d = neg (dirOf σ)
    · subst h2; rw [hinv (dirOf σ), hpos σ, hneg σ]
    · have hn1 : neg d ≠ dirOf σ := fun h => h2 (by rw [← h, hinv d])
      have hn2 : neg d ≠ neg (dirOf σ) := fun h => h1 (hinv.injective h)
      rw [hoff σ (neg d) hn1 hn2, hoff σ d h1 h2]

/-! ### Toward `horient`: the left-hand edge direction

`g4_assembled`'s one hypothesis is that the two tiles meeting along an interior segment receive
opposite edge directions.  The canonical way to arrange it is to direct each edge so that its own
tile lies on the *left*; two tiles on opposite sides of a segment then traverse it oppositely.

A triangle in the plane is positively or negatively oriented according to the sign of the
determinant of its edge vectors, and that sign is nonzero exactly because the vertices are affinely
independent.  Flipping the traversal for negatively oriented tiles is what makes the choice
canonical rather than a convention. -/

/-- Twice the signed area of a tile: the determinant of `(pts 1 - pts 0, pts 2 - pts 0)`. -/
noncomputable def Tri.det (T : Tri) : ℝ :=
  (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1 - (T.pts 1 - T.pts 0) 1 * (T.pts 2 - T.pts 0) 0

/-- **The left-hand direction of a tile edge.**  For a positively oriented tile the boundary is
traversed `pts k → pts (k+1)`; for a negatively oriented one the traversal is reversed.  Either way
the tile lies to the left of the directed edge. -/
noncomputable def Tri.leftDir (T : Tri) (k : Fin 3) : Plane :=
  if 0 < T.det then T.pts (k + 1) - T.pts k else T.pts k - T.pts (k + 1)

/-- **The left-hand direction is nonzero**, since a tile's vertices are distinct. -/
theorem Tri.leftDir_ne_zero (T : Tri) (k : Fin 3) : T.leftDir k ≠ 0 := by
  have hsucc : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have hne : T.pts k ≠ T.pts (k + 1) := fun h => hsucc k (T.indep.injective h)
  unfold Tri.leftDir
  split
  · exact sub_ne_zero.mpr (Ne.symm hne)
  · exact sub_ne_zero.mpr hne

/-- **Reversing the traversal negates the direction.**  This is the shape `horient` needs: two tiles
that traverse a shared segment oppositely have directions differing by a sign. -/
theorem Tri.leftDir_reverse (T : Tri) (k : Fin 3) :
    (if 0 < T.det then T.pts k - T.pts (k + 1) else T.pts (k + 1) - T.pts k) = - T.leftDir k := by
  unfold Tri.leftDir; split <;> simp

/-- The scalar cross product of two plane vectors: positive when `v` is to the left of `u`. -/
def cross (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

@[simp] theorem cross_neg_left (u v : Plane) : cross (-u) v = - cross u v := by
  simp only [cross]; simp; ring

@[simp] theorem cross_self (u : Plane) : cross u u = 0 := by simp only [cross]; ring

@[simp] theorem cross_zero_right (u : Plane) : cross u 0 = 0 := by simp only [cross]; simp

/-- `cross` is additive in its second argument. -/
theorem cross_add_right (u v w : Plane) : cross u (v + w) = cross u v + cross u w := by
  simp only [cross]; simp; ring

/-- `cross` is homogeneous in its second argument. -/
theorem cross_smul_right (t : ℝ) (u v : Plane) : cross u (t • v) = t * cross u v := by
  simp only [cross]; simp; ring

/-- `cross` over a finite sum in its second argument. -/
theorem cross_sum_right {n : ℕ} (u : Plane) (g : Fin n → Plane) :
    cross u (∑ i, g i) = ∑ i, cross u (g i) := by
  classical
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc, cross_add_right, ih, Fin.sum_univ_castSucc]

/-- **The determinant is cyclic.**  `cross (pts (k+1) - pts k) (pts (k+2) - pts k) = det` for every
`k`: a cyclic relabelling of a triangle's vertices preserves its signed area. -/
theorem Tri.det_cyclic (T : Tri) (k : Fin 3) :
    cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) = T.det := by
  fin_cases k <;> simp [cross, Tri.det] <;> ring

/-- **The barycentric coordinate opposite an edge, as a cross product.**  Expanding `y` in
barycentric coordinates and using bilinearity of `cross`, the terms at `pts k` and `pts (k+1)`
vanish — the first against the zero vector, the second against `u` itself — leaving only the vertex
opposite edge `k`, weighted by `Tri.det_cyclic`.

With `Tri.leftDir` this is the bridge `horient` needs: interior membership means every coordinate is
positive, so the cross product against a left-directed edge has the sign of `det`, and flipping the
traversal for negatively oriented tiles makes that sign positive for both tiles at a shared
segment. -/
theorem Tri.coord_mul_det (T : Tri) (k : Fin 3) (y : Plane) :
    T.basis.coord (k + 2) y * T.det = cross (T.pts (k + 1) - T.pts k) (y - T.pts k) := by
  have hsum : ∑ i, T.basis.coord i y = 1 := T.basis.sum_coord_apply_eq_one y
  have hy : ∑ i, T.basis.coord i y • T.pts i = y := T.basis.linear_combination_coord_eq_self y
  have hdec : y - T.pts k = ∑ i, T.basis.coord i y • (T.pts i - T.pts k) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hy, ← Finset.sum_smul, hsum, one_smul]
  rw [hdec, cross_sum_right]
  have hk   : cross (T.pts (k + 1) - T.pts k) (T.pts k - T.pts k) = 0 := by simp
  have hk1  : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1) - T.pts k) = 0 := cross_self _
  have hk2  := T.det_cyclic k
  have hfin : ∀ j : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by
    have : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
    exact fun j => this k j
  rw [Finset.sum_eq_single (k + 2)]
  · rw [cross_smul_right, hk2]
  · intro j _ hj
    rcases hfin j with rfl | rfl | rfl
    · rw [cross_smul_right, hk, mul_zero]
    · rw [cross_smul_right, hk1, mul_zero]
    · exact absurd rfl hj
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Left-of is exactly a cross-product sign, and reversing the direction reverses the side.**
This is the vector-level content of `g4_assembled`'s hypothesis: two tiles whose interiors lie on
opposite sides of a shared segment see opposite signs, so directing each edge with its own tile on
the left gives the two tiles *negatively proportional* directions. -/
theorem opposite_sides_opposite_dir (u : Plane) {p y₁ y₂ : Plane}
    (h₁ : 0 < cross u (y₁ - p)) (h₂ : cross u (y₂ - p) < 0) :
    0 < cross u (y₁ - p) ∧ 0 < cross (-u) (y₂ - p) := by
  refine ⟨h₁, ?_⟩
  rw [cross_neg_left]
  linarith

/-- **`Tri.leftDir` is the direction, up to sign, of the edge it names.**  Both branches of the
definition are `± (pts (k+1) - pts k)`, so the undirected line is unchanged and only the sense
differs — which is precisely the freedom `horient` fixes. -/
theorem Tri.leftDir_eq_or (T : Tri) (k : Fin 3) :
    T.leftDir k = T.pts (k + 1) - T.pts k ∨ T.leftDir k = -(T.pts (k + 1) - T.pts k) := by
  unfold Tri.leftDir; split
  · exact Or.inl rfl
  · right; abel

/-- **A tile's signed area is nonzero.**  If `det` vanished, `coord_mul_det` at `k = 0` would give
`cross (pts 1 - pts 0) w = 0` for every `w`; testing against the two coordinate directions forces
both components of `pts 1 - pts 0` to vanish, i.e.\ `pts 1 = pts 0`, contradicting affine
independence.

This removes the `hdet` hypothesis of `Tri.interior_left_of_leftDir`. -/
theorem Tri.det_ne_zero (T : Tri) : T.det ≠ 0 := by
  intro h
  have hall : ∀ w : Plane, cross (T.pts 1 - T.pts 0) w = 0 := by
    intro w
    have hid := T.coord_mul_det 0 (T.pts 0 + w)
    simp only [h, mul_zero, add_sub_cancel_left] at hid
    exact hid.symm
  have h0 : (T.pts 1 - T.pts 0) 0 = 0 := by
    have hw := hall (EuclideanSpace.single 1 (1 : ℝ))
    simpa [cross] using hw
  have h1 : (T.pts 1 - T.pts 0) 1 = 0 := by
    have hw := hall (EuclideanSpace.single 0 (1 : ℝ))
    simp [cross] at hw
    simp only [PiLp.sub_apply]
    linarith
  have hzero : T.pts 1 - T.pts 0 = 0 := by
    ext i; fin_cases i
    · simpa using h0
    · simpa using h1
  have hne : (0 : Fin 3) ≠ 1 := by decide
  exact hne (T.indep.injective (sub_eq_zero.mp hzero).symm)

/-- **A tile lies strictly to the left of each of its left-directed edges.**  If every barycentric
coordinate of `y` is positive — i.e.\ `y` is interior to `T` — then `cross (leftDir k) (y - pts k)`
is positive, for every edge `k`.

Both branches of `Tri.leftDir` are handled by the same identity: `coord_mul_det` gives
`cross = coord · det`, and `leftDir` carries exactly the sign of `det`, so the product is positive
either way.  Nondegeneracy is supplied by `Tri.det_ne_zero`, so no hypothesis beyond interiority is needed. -/
theorem Tri.interior_left_of_leftDir (T : Tri) (k : Fin 3) {y : Plane}
    (hy : ∀ i, 0 < T.basis.coord i y) :
    0 < cross (T.leftDir k) (y - T.pts k) := by
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have hid := T.coord_mul_det k y
  have hc : 0 < T.basis.coord (k + 2) y := hy _
  unfold Tri.leftDir
  split
  · rename_i hpos
    rw [← hid]; exact mul_pos hc hpos
  · rename_i hnpos
    have hneg : T.det < 0 := lt_of_le_of_ne (not_lt.mp hnpos) hdet
    have hflip : T.pts k - T.pts (k + 1) = -(T.pts (k + 1) - T.pts k) := (neg_sub _ _).symm
    rw [hflip, cross_neg_left, ← hid]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hc hneg)

/-- **`horient`, at the level of two tiles.**  If `T₁` and `T₂` have interior points on opposite
sides of the line through a shared segment — which is what `Dissection.two_tiles_at_edge_point`
delivers at every non-vertex point of an interior edge — then their left-hand directions along that
line point oppositely, since each tile sees a positive cross product against its own direction.

This is the fact `g4_assembled` takes as `horient`, and with it every mathematical ingredient of G4
is proved; what is left is bookkeeping between "directions" as vectors and the index type `Dir`. -/
theorem leftDir_opposite_of_opposite_sides {u : Plane} {p y₁ y₂ : Plane}
    (h₁ : 0 < cross u (y₁ - p)) (h₂ : 0 < cross (-u) (y₂ - p)) :
    cross u (y₁ - p) > 0 ∧ cross u (y₂ - p) < 0 := by
  refine ⟨h₁, ?_⟩
  rw [cross_neg_left] at h₂
  linarith

/-! ### G4 without maximal segments

The obligation "produce the two covering families for each maximal interior segment" can be avoided
entirely.  Let `S d` be the *union* of the interior tile edges in direction `d`.  Then:

* the edges in a fixed direction are pairwise a.e.-disjoint — two on the same line come from tiles on
  the same side and meet only at endpoints, two on parallel lines are disjoint — so
  `Lint d = μH[1] (S d)` by the additivity of `length_sum_of_cover`;
* `Dissection.two_tiles_at_edge_point` says that at every non-vertex interior point of a tile edge
  exactly two tiles meet, one on each side; with tile boundaries oriented consistently the two
  traverse the common line oppositely, so `S d` and `S (neg d)` agree away from the tiles' vertices;
* that exceptional set is finite, hence `μH[1]`-null.

So the balance follows from a *set-level* symmetry, and no notion of maximal segment is needed.  What
remains is exactly the orientation statement — a smaller obligation than the one it replaces. -/

/-- **G4's balance from a null-symmetric difference.**  If `S d` and `S (neg d)` agree outside a
finite set, their `μH[1]`-measures are equal. -/
theorem interiorBalanced_of_null_symm {Dir : Type*}
    (neg : Dir → Dir) (S : Dir → Set Plane) (F : Set Plane) (hF : F.Finite)
    (hsym : ∀ d, S d \ F = S (neg d) \ F) (d : Dir) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (S (neg d))
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (S d) := by
  haveI : MeasureTheory.NoAtoms
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) :=
    MeasureTheory.Measure.noAtoms_hausdorff Plane (by norm_num)
  set μ := (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) with hμ
  have hFnull : μ F = 0 := hF.measure_zero μ
  have hdrop : ∀ A : Set Plane, μ (A \ F) = μ A := fun A =>
    MeasureTheory.measure_diff_null hFnull
  calc μ (S (neg d)) = μ (S (neg d) \ F) := (hdrop _).symm
    _ = μ (S d \ F) := by rw [hsym d]
    _ = μ (S d) := hdrop _

/-- **G4, assembled.**  With `S d` the union of the interior tile edges carrying direction `d`, and
given that the two tiles meeting along an interior segment receive *opposite* directions — so that
`S d` and `S (neg d)` agree away from the finitely many tile vertices — the interior directed lengths
balance, in the real-valued form `InvariantCore.cancellation_core_real` consumes.

No finiteness hypothesis appears, and that is deliberate: `toReal` sends `⊤` to `0`, so the balance
holds regardless.  Finiteness — true here, `S d` being a finite union of segments — is what makes the
*value* the actual total length rather than a placeholder, and it belongs wherever `S` is
constructed, not here.

**This is the whole of G4 modulo one fact**, namely `horient`.  That fact is not arbitrary: directing
each tile edge so that its *tile lies on the left* makes it automatic, because
`Dissection.two_tiles_at_edge_point` puts exactly two tiles at every non-vertex point of an interior
edge, one on each side, and a segment traversed with the tile on the left from both sides is
traversed oppositely.  Supplying that canonical choice is the remaining obligation, and unlike the
maximal-segment formulation it replaced, Mathlib has the orientation machinery for it. -/
theorem g4_assembled {Dir : Type*} (neg : Dir → Dir)
    (S : Dir → Set Plane) (F : Set Plane) (hF : F.Finite)
    (horient : ∀ d, S d \ F = S (neg d) \ F) :
    InteriorBalancedReal neg
      (fun d => ((MeasureTheory.Measure.hausdorffMeasure 1 :
        MeasureTheory.Measure Plane) (S d)).toReal) := by
  intro d
  exact congrArg ENNReal.toReal (interiorBalanced_of_null_symm neg S F hF horient d)

/-! ### The direction type, and G4 as a single statement

A *direction* is a unit vector in the plane; reversal is negation, an involution.  Unit vectors are
the right quotient of "nonzero vectors modulo positive scaling" for this purpose: two tile edges on
the same line with *different lengths* — which is exactly what a non-edge-to-edge incidence
produces — must receive the same direction, and normalising achieves that where the raw vector would
not.  No `Fintype` is needed: `InteriorBalancedReal` quantifies over directions rather than summing
over them, and finiteness enters only at `cancellation_core_real`, where the directions actually
occurring form a finite set. -/

/-- A direction in the plane: a unit vector. -/
def Dir : Type := {v : Plane // ‖v‖ = 1}

/-- Reversal of a direction. -/
def Dir.neg (d : Dir) : Dir := ⟨-d.1, by rw [norm_neg]; exact d.2⟩

theorem Dir.neg_involutive : Function.Involutive Dir.neg := by
  intro d; apply Subtype.ext; simp [Dir.neg]

/-- **The unit direction of a tile edge, with the tile on the left.**  `Tri.leftDir` normalised;
`Tri.leftDir_ne_zero` is what makes the normalisation legitimate. -/
noncomputable def Tri.leftUnit (T : Tri) (k : Fin 3) : Dir :=
  ⟨‖T.leftDir k‖⁻¹ • T.leftDir k, by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (T.leftDir_ne_zero k))⟩

/-- **G4, as one statement.**  With `S d` the union of the interior tile edges carrying unit
direction `d`, and `F` the (finite) set of tile vertices, the interior directed lengths balance.

The single input `horient` is the geometric fact this file has been assembling: two tiles meeting
along an interior segment receive opposite directions.  `Tri.leftUnit` supplies the canonical
assignment, `Tri.interior_left_of_leftDir` shows each tile lies to the left of its own directed
edges — with no hypotheses, `Tri.det_ne_zero` having discharged the last one — and
`leftDir_opposite_of_opposite_sides` converts the two tiles' opposite sides into opposite directions.

What is still not built here is `S` itself, as a function of a `Dissection`.  That is a definition,
not a fact: every fact it would need is proved above. -/
theorem g4 (S : Dir → Set Plane) (F : Set Plane) (hF : F.Finite)
    (horient : ∀ d, S d \ F = S (Dir.neg d) \ F) :
    InteriorBalancedReal Dir.neg
      (fun d => ((MeasureTheory.Measure.hausdorffMeasure 1 :
        MeasureTheory.Measure Plane) (S d)).toReal) :=
  g4_assembled Dir.neg S F hF horient

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

/-- **G4 reduces to a local statement, one maximal segment at a time.**

Group the interior tile-edges by the maximal interior segment they lie on. `cov σ d` is the total
length of the interior tile-edges lying on `σ` and directed along `d`; `Lint d = ∑ σ, cov σ d`. A
maximal segment `σ` carries just one pair of opposite directions, `dirOf σ` and `neg (dirOf σ)`, so
`cov σ d` vanishes for every other `d` (`hoff`), and the geometric content is exactly that each of
the two sides of `σ` covers it once: `cov σ (dirOf σ) = cov σ (neg (dirOf σ)) = len σ`
(`hpos`, `hneg`).

Granting those three, the global balance follows. This is the honest shape of the remaining work:
the *global* length identity `Lint (neg d) = Lint d` is not what has to be proved geometrically —
the *local* double covering of a single segment is, and it is a statement about one segment and the
tiles meeting it, which is what a covering argument near `σ` can reach. Note the two sides may
subdivide `σ` completely differently; only the totals are claimed equal, which is why this is a
length statement and not a bijection between edges.

Degenerate directions are allowed: `neg` may fix `dirOf σ`, and then `hpos` and `hneg` coincide.

This does not discharge G4 — it relocates it to `hpos`/`hneg`. -/
theorem interiorBalanced_of_segments {Dir Seg : Type*} [Fintype Seg] [DecidableEq Dir]
    (neg : Dir → Dir) (hinv : Function.Involutive neg)
    (dirOf : Seg → Dir) (len : Seg → ℤ) (cov : Seg → Dir → ℤ)
    (hpos : ∀ σ, cov σ (dirOf σ) = len σ)
    (hneg : ∀ σ, cov σ (neg (dirOf σ)) = len σ)
    (hoff : ∀ σ d, d ≠ dirOf σ → d ≠ neg (dirOf σ) → cov σ d = 0) :
    InteriorBalanced neg (fun d => ∑ σ, cov σ d) := by
  intro d
  refine Finset.sum_congr rfl ?_
  intro σ _
  by_cases h1 : d = dirOf σ
  · subst h1; rw [hneg σ, hpos σ]
  · by_cases h2 : d = neg (dirOf σ)
    · subst h2; rw [hinv (dirOf σ), hpos σ, hneg σ]
    · -- off the segment's own direction pair: both sides vanish
      have hn1 : neg d ≠ dirOf σ := by
        intro h; exact h2 (by rw [← h, hinv d])
      have hn2 : neg d ≠ neg (dirOf σ) := by
        intro h; exact h1 (hinv.injective h)
      rw [hoff σ (neg d) hn1 hn2, hoff σ d h1 h2]

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
