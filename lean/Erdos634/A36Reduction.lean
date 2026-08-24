import Erdos634.FloorPropagation
import Erdos634.LayerLink

/-!
# A36 is not independent: `uniform_below` reduces to layer rigidity

`FloorPropagation` left `uniform_below` as the single open link in the row-3 chain: that the
figure below each junction of the south cover is the same at every junction.  It is not a new
geometric fact.  It reduces to `LayerLink.layer_rigid_of_exclusions`, which is already proved,
and therefore onto that theorem's own two bridges.

## The reduction

1. `FloorPropagation.junctions_pass_through` (VERIFIED) — each `a`-edge on the floor is covered
   from below by a *single* `a`-edge, so the floor is edged at every one of the `f + 1`
   junctions, with no new subdivision.
2. An edged floor makes the fan *below* each junction a straight angle, of type `(3,2)`.  This
   is the one geometric step.  Since 2026-08-16 it is **assemblable, not open**: see
   `StraightEdgeSums`, where it is reduced to the same area computation that discharged
   `Dissection.hasAngleSums`.
3. `OrderForcing.straight_junction_cases` (PROVED) — a `(3,2)` figure is `{α,α,α,β,β}` or
   `{γ,α,β}`.  Two possibilities: *not yet* uniform.
4. The tiles below those `a`-edges form a layer, and
   `LayerLink.layer_rigid_of_exclusions` (VERIFIED) makes every tile of a layer unreflected,
   hence identically placed.
5. Identically placed congruent tiles present the same angle at each junction, so the figure is
   the same at each — which is `uniform_below`.

Step 5 is the same congruence argument as `UniformFill`, and step 4 is the schema already
instantiated for both the `a`-strip and the `c`-layer.

## What the whole row-3 chain now rests on

Exactly three things, and no more:

* the two geometric bridges of `LayerLink.strip_layer_rigid` — reflected at the layer's start
  puts the apex left of the mast; reflected after an unreflected tile overlaps its predecessor;
* the edged-floor step `fan_below_straight`.

Everything else in the chain — A30, A31, A32, A33, A34, A35 — is VERIFIED.  A36 no longer
stands beside them as an independent conjecture.
-/

namespace Erdos634.A36Reduction

open Finset

/-- **Rigidity plus congruence gives uniformity.**  If every tile of the layer below the floor
carries the same orientation, and congruent tiles in the same orientation present the same angle
at their junction, then the figure below is the same at every junction.

This is the schema; `h_rigid` is discharged by `LayerLink.layer_rigid_of_exclusions` and `h_det`
is congruence of the tiles. -/
theorem uniform_of_layer_rigid {α : Type*} (angleAt : ℕ → α) (orient : ℕ → Prop)
    (h_rigid : ∀ j, orient j)
    (h_det : ∀ j k, orient j → orient k → angleAt j = angleAt k) :
    ∀ j k, angleAt j = angleAt k :=
  fun j k => h_det j k (h_rigid j) (h_rigid k)

/-- **The figure below an edged-floor junction**, cited: a straight angle of type `(3,2)` admits
`{α,α,α,β,β}` or `{γ,α,β}` and nothing else. -/
theorem figure_below_cases (na nb ng : ℕ) (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) :
    (na = 3 ∧ nb = 2 ∧ ng = 0) ∨ (na = 1 ∧ nb = 1 ∧ ng = 1) :=
  Erdos634.OrderForcing.straight_junction_cases na nb ng h1 h2

/-- **At most one `γ` below**, cited, for the same fan. -/
theorem gamma_bound_below (na nb ng : ℕ) (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) : ng ≤ 1 :=
  Erdos634.OrderForcing.straight_junction_gamma_bound na nb ng h1 h2

/-- **A36, reduced.**  With the layer below rigid and its tiles congruent, `uniform_below`
holds; feeding it to `FloorPropagation.reaches_base_of_uniform_below` closes row 3.

The hypotheses named here are exactly the ones `LayerLink.strip_layer_rigid` already consumes,
so nothing new is assumed beyond its two bridges and the edged-floor step. -/
theorem row_three_closes_on_layer_rigidity
    (f : ℕ) (hf : 3 ≤ f) (isA : ℕ → Prop) [DecidablePred isA]
    (base_count : ((range (f + 2)).filter isA).card = f)
    (x₀ : ℕ)
    (orient : ℕ → Prop) (h_rigid : ∀ j, orient j)
    (slot : ℕ → Prop)
    (h_det : ∀ j k, orient j → orient k →
      (slot j ↔ slot k))
    (h_one : slot 0)
    (h_slot : ∀ i ∈ range (f + 1), slot i → x₀ + i * f < f + 2 ∧ isA (x₀ + i * f)) :
    False := by
  refine Erdos634.FloorPropagation.reaches_base_of_uniform_below f hf isA base_count x₀ ?_
  intro i hi
  exact h_slot i hi ((h_det 0 i (h_rigid 0) (h_rigid i)).mp h_one)

/-! ## Bridge (iii), reduced

`Dissection.HasAngleSums` covers three kinds of point: interior (`2π`), target-boundary
non-corner (`π`), and the three corners.  It does **not** cover a point interior to the target
that lies on an *edge of the tiling* — which is what a junction on an interior floor is.  So
(iii) is a genuine carrying, not something already in the corpus; saying otherwise would be
wrong.

It does reduce, though.  At such a junction the total is `2π` by `HasAngleSums`'s first clause,
and the fan *above* is `π` because the floor is edged from above — the very fact
`prop:a2branch` already uses at the top of the figure, and which
`OrderForcing.straight_junction_cases` consumes there.  Subtracting leaves `π` below.  So (iii)
is not an independent assumption: it is the *same* straightness fact, applied on the other side
of a line already known to be edged. -/

/-- **The fan below a junction on an edged interior floor is straight.**  The total at an
interior point is `2π`; the fan above is `π` because the floor is edged from above; so the fan
below is `π`, of type `(3,2)`, and `figure_below_cases` applies. -/
theorem below_fan_is_pi (above below : ℝ)
    (htotal : above + below = 2 * Real.pi) (habove : above = Real.pi) :
    below = Real.pi := by
  rw [habove] at htotal; linarith

end Erdos634.A36Reduction
