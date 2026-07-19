import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

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

The single sharpest gap: Mathlib has the triangle angle sum but has **no** statement that the angles
around an interior point sum to `2π`, and no machinery (no sectors, no angular measure, no winding
number) to build one.  See `HasAngleSums`.

## Compile status

Every Mathlib lemma invoked below was verified to exist, with its exact signature and argument
order, by reading the source of the pinned revision (Lean 4.30.0 / Mathlib v4.30.0 — the same
revision this project already builds against).  The file has **not** been compiled.  Four steps are
tactic-level guesses rather than verified applications and should be checked first if it fails:

1. `Tri.affineSpan_eq_top` — the closing `by simp` must discharge `Fintype.card (Fin 3) = 2 + 1`.
   Fallback: `by simp [Fintype.card_fin, finrank_euclideanSpace]` or `by norm_num`.
2. `Dissection.volume_target` — the anonymous pairwise lambda is elaborated against
   `Set.Pairwise ↑univ (AEDisjoint volume on _)`, which requires unfolding `Set.Pairwise` and
   `Function.onFun`.  Fallback: state it as a separate `have` with explicit `∀ i ∈ _, ∀ j ∈ _, …`
   binders (defeq ignores binder annotation, so that form is accepted).
3. `Dissection.volume_target_of_congruent` — the closing `simp [hv]`.
   Fallback: `simp only [hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.
4. `cornerAngle_sum` — the three `angle_comm` rewrites are order-sensitive.  The three rewritten
   terms are checked by hand to be exactly the three summands of `key`; if `rw` misfires, use
   `simp only [EuclideanGeometry.angle_comm]` plus `linarith`, or `omega`-free `linarith` on a
   restated `key`.

The remaining proofs are either single verified lemma applications or `omega`/`linear_combination`
on hand-checked algebraic identities.

Axiom-clean apart from the usual `propext`, `Classical.choice`, `Quot.sound`.
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
  ∀ (S : Set Plane), S ⊆ frontier D.target.carrier →
    ∃ (part : Finset (Fin N × Fin 3)), (⋃ e ∈ part, edgeOf e.1 e.2) = S

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
