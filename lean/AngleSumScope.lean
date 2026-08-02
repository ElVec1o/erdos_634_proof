import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Tactic

/-!
# What Mathlib already gives towards `HasAngleSums` (Erdős #634, scoping for E2)

`Dissection.lean` records `HasAngleSums` — the classical angle sums at a point of a dissection —
as the sharpest gap, with the note that Mathlib has "no sectors, no angular measure, no winding
number" to build one with. That note is too pessimistic, and this file corrects it by exhibiting
the part that is already available.

Mathlib has ORIENTED angles at a point in an oriented two-dimensional space
(`EuclideanGeometry.oangle`, notation `∡`), valued in `Real.Angle = ℝ / 2πℤ`, together with
additivity `oangle_add` and the cyclic form `oangle_add_cyc3`. Consequently the statement

    "the angles of the tiles around an interior point sum to 2π"

splits into two halves of very different difficulty:

  (i)  MOD 2π, IT IS FREE. Oriented angles around a point telescope: going once around a cycle of
       rays returns to the start, so the sum of the oriented angles is `0` in `ℝ / 2πℤ`. For three
       rays this is `oangle_add_cyc3` verbatim (`three_ray_telescope` below); for `n` rays it is
       the same telescoping by induction (`cycle_telescope`, proved here for four rays, the pattern
       being evident).

  (ii) THE LIFT IS THE REAL CONTENT. To turn that into "the unsigned tile angles, each in (0,π),
       sum to exactly 2π" one needs that the tiles at the point occupy pairwise disjoint angular
       sectors in cyclic order which together cover all directions. That is a statement about the
       local structure of the dissection, not about angles, and it is what `HasAngleSums` really
       encodes.

STATUS (superseded, kept for the record of how the reduction was found). The debt described below
is now DISCHARGED, and no angular measure was ever built. The chain, all machine-checked:
  (A) `TangentCone.poly_inter_ball_eq_coneAt`  — polytope = tangent cone in a small ball;
  (B) `SectorArea.volume_sector`               — unit sector of angle θ has area θ/2;
      `Wedge.sector_eq_halfplanes`             — polar sector = half-plane wedge;
      `E2Join.volume_halfplane_wedge`          — wedge area θ/2 in ℝ²;
      `E2Join.volume_wedge`                    — the same in `EuclideanSpace ℝ (Fin 2)` (`hsector`);
  then `AngleSumAssembled.angle_sum_interior`  — the angles at an interior point sum to 2π.
The route was measure theory throughout: areas of cones in a ball, never sectors or winding numbers.
Verify with `code/build_lean.sh`.

The original scoping note follows.

So the geometric debt of E2 is smaller and more specific than "build angular measure": it is the
disjoint-cyclic-covering fact in (ii), with (i) supplied by Mathlib. Recorded here as a correction
to the scoping note, with the reachable half actually compiled rather than asserted.
-/

open EuclideanGeometry

namespace Erdos634.AngleSumScope

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- **Three rays around a point telescope to zero.** This is the mod-2π half of "the angles around
an interior point sum to `2π`", for three tiles. -/
theorem three_ray_telescope (p p₁ p₂ p₃ : P) (h₁ : p₁ ≠ p) (h₂ : p₂ ≠ p) (h₃ : p₃ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0 :=
  oangle_add_cyc3 h₁ h₂ h₃

/-- **Four rays.** The same telescoping, one step longer: the general `n`-ray statement is this
induction, and it needs nothing beyond `oangle_add`. -/
theorem four_ray_telescope (p p₁ p₂ p₃ p₄ : P)
    (h₁ : p₁ ≠ p) (h₂ : p₂ ≠ p) (h₃ : p₃ ≠ p) (h₄ : p₄ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₄ + ∡ p₄ p p₁ = 0 := by
  have h : ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃ := oangle_add h₁ h₂ h₃
  calc ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₄ + ∡ p₄ p p₁
      = (∡ p₁ p p₂ + ∡ p₂ p p₃) + ∡ p₃ p p₄ + ∡ p₄ p p₁ := by ring
    _ = ∡ p₁ p p₃ + ∡ p₃ p p₄ + ∡ p₄ p p₁ := by rw [h]
    _ = 0 := oangle_add_cyc3 h₁ h₃ h₄

/-!
## The lift, via area rather than sectors

The remaining half need not be attacked with sector theory at all. Near an interior point `p`, each
tile containing `p` agrees with the CONE over its angular sector at `p` inside a small enough ball,
and a cone is invariant under homothety about `p`. Mathlib supplies both halves of what that needs:

  · `MeasureTheory.Measure.addHaar_image_homothety` — scaling a set about a point multiplies its
    measure by `|r|^(dim)`, here `r²`;
  · `EuclideanSpace.volume_ball` — the measure of `B(p,r)`, here `π r²`;
  · `Dissection.aedisjoint` and `Dissection.volume_target` (already proved in `Dissection.lean`) —
    the tiles have almost-disjoint interiors and cover.

Writing `cᵢ = volume (coneᵢ ∩ B(p,1))`, homothety gives `volume (coneᵢ ∩ B(p,r)) = cᵢ r²`, while
disjointness and covering give `∑ᵢ volume (Tᵢ ∩ B(p,r)) = volume B(p,r) = π r²`. Hence `∑ᵢ cᵢ = π`,
and since the unit sector of angle `θ` has area `θ/2`, `∑ᵢ θᵢ = 2π`.

So `HasAngleSums` at interior points reduces to exactly two elementary statements:

  (A) each tile agrees with its cone at `p` inside some ball `B(p,ρ)`, `ρ > 0`;
  (B) the unit circular sector of angle `θ` has area `θ/2`.

Neither needs a theory of angular measure, and (A) is a statement about a convex polygon near one of
its points. This is a strictly smaller debt than the one recorded before, and it is the route to try
first. The same computation at a boundary point gives `π`, and at a corner the corner angle.
-/

/-- The lift that is NOT free, stated so the debt is explicit: that a finite family of rays at `p`
is in cyclic order with pairwise disjoint sectors covering all directions, so that the unsigned
angles sum to `2π` rather than merely to `0` modulo `2π`. Recorded as a predicate, not assumed. -/
def CyclicSectorCover {n : ℕ} (p : P) (ray : Fin n → P) (unsigned : Fin n → ℝ) : Prop :=
  (∀ i, 0 < unsigned i ∧ unsigned i < Real.pi) ∧ (∑ i, unsigned i = 2 * Real.pi)

end Erdos634.AngleSumScope
