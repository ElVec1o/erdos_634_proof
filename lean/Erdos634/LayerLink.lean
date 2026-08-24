import Erdos634.Congruence
import Erdos634.StripRigid
import Erdos634.CLayerRigid

/-!
# Aiming the layer exclusions at the congruence predicate

`StripRigid` proves two pointwise arithmetic exclusions and supplies `layer_induction` as a
schema over an abstract `U : ℕ → Prop`, recording as its blocker that connecting the two
"needs a formalization of tilings that this project does not have".  `Congruence` supplied
that: `CongruentDissection.UnreflectedAt` is the predicate, and it is now stateable.  This
file makes the connection.

## One schema, both layers

`StripRigid` and `CLayerRigid` have the *same* shape.  `CLayerRigid`'s own summary says it:
"a reflected tile is impossible at position 1 (left gap) and impossible after an unreflected
one (mixed gap); induction from the mast makes every tile unreflected."  `StripRigid` is the
same with mast and overlap in those two roles.  So `layer_rigid_of_exclusions` takes exactly
those two exclusions and concludes that the whole layer is unreflected — no arithmetic in it
at all, and it serves both layers.

## The instantiation, and where the geometry sits

`strip_layer_rigid` instantiates it for the `a`-strip.  The two geometric bridges are named
hypotheses:

* `mast` — a reflected tile at the layer's start puts its apex left of the mast;
* `overlap` — a reflected tile after an unreflected one overlaps its predecessor;

each asserting that the configuration would force `e N₀ ≤ 2 a f`.  Both are then refuted by
a single already-proved inequality, `StripRigid.shift_gt_two_a`: `2 a f < e N₀`.  That is
exactly the economy its own docstring claims — "**This single inequality carries both
exclusions below**" — now discharged against the geometric predicate rather than against an
abstract placeholder.

**Status of the two bridges (updated 2026-08-24).**  They are taken as hypotheses *here*, but
they are no longer unproved: `ChordChart` derives both.  Placing the tile's `a`-edge on the floor
and subtracting the two distance equations puts the reflected apex at `(a²+b²-c²)/(2a)`, whose
numerator is `e²(e²-f²) < 0` for every member, so it lies left of the mast
(`ChordChart.reflected_apex_left_of_mast`); and the overlap follows because each corner cone
contains the straight-up direction, so both bodies contain a vertical segment of positive height
from the shared foot (`ChordChart.upward_in_cone`, `shared_segment_pos`).

The earlier text here read "The two bridges are *not* proved ... proving them needs the fan
machinery that `Dissection` lines 396–402 record as absent from Mathlib."  Both halves of that
are now wrong: the bridges are proved, and that `Dissection` note was itself superseded when
`HasAngleSums` was discharged on 2026-08-16.  What remains is assembly: feeding `ChordChart`'s
geometric conclusions into the inequality-shaped hypotheses below, via `Dissection.covers` and
`Dissection.interiors_disjoint`.
-/

namespace Erdos634.Geometry

open Erdos634.StripRigid

variable {N : ℕ}

/-- **Layer rigidity from the two exclusions.**  If the reflected placement is impossible at
the layer's start, and impossible immediately after an unreflected tile, then every tile of
the layer is unreflected.  Pure logic over the orientation dichotomy — no arithmetic — so it
serves the `a`-strip (`StripRigid`) and the `c`-layer (`CLayerRigid`) alike. -/
theorem layer_rigid_of_exclusions (D : CongruentDissection N) (idx : ℕ → Fin N)
    (base_excl : ¬ (D.tile (idx 0)).Reflected D.model)
    (step_excl : ∀ j, D.UnreflectedAt (idx j) → ¬ (D.tile (idx (j + 1))).Reflected D.model) :
    ∀ j, D.UnreflectedAt (idx j) := by
  intro j
  induction j with
  | zero =>
      rcases D.unreflected_or_reflected (idx 0) with h | h
      · exact h
      · exact absurd h base_excl
  | succ n ih =>
      rcases D.unreflected_or_reflected (idx (n + 1)) with h | h
      · exact h
      · exact absurd h (step_excl n ih)

/-- **The `a`-strip is rigid, against the real predicate.**  Given the two geometric bridges
— reflected at the start ⟹ apex left of the mast, reflected after an unreflected one ⟹
overlap with the predecessor, each forcing `e N₀ ≤ 2 a f` — every tile of the strip is
unreflected.  Both bridges die against `shift_gt_two_a`, the single inequality `StripRigid`
says carries both exclusions. -/
theorem strip_layer_rigid (D : CongruentDissection N) (idx : ℕ → Fin N) (e f : ℤ)
    (he : 0 < e) (hef : e < f)
    (mast : (D.tile (idx 0)).Reflected D.model →
      e * (3 * f ^ 2 - e ^ 2) ≤ 2 * (e * f) * f)
    (overlap : ∀ j, D.UnreflectedAt (idx j) → (D.tile (idx (j + 1))).Reflected D.model →
      e * (3 * f ^ 2 - e ^ 2) ≤ 2 * (e * f) * f) :
    ∀ j, D.UnreflectedAt (idx j) :=
  have hS : 2 * (e * f) * f < e * (3 * f ^ 2 - e ^ 2) := shift_gt_two_a e f he hef
  layer_rigid_of_exclusions D idx
    (fun h => absurd (mast h) (not_le.mpr hS))
    (fun j hj h => absurd (overlap j hj h) (not_le.mpr hS))

/-- **The `c`-layer is rigid, against the real predicate.**  `CLayerRigid` proves that three
gap areas are never nonnegative integer multiples of the tile area.  The two geometric bridges
say that a reflected tile at the layer's start leaves the left gap, and a reflected tile after
an unreflected one leaves the mixed gap; each gap would have to be tiled, i.e. its area would
have to be `n` tile areas with `n ≥ 0`.  Both are refuted directly.

Same schema as `strip_layer_rigid`, which is the point: `CLayerRigid`'s own summary already
describes this shape, and `layer_rigid_of_exclusions` is where the two meet. -/
theorem c_layer_rigid_link (D : CongruentDissection N) (idx : ℕ → Fin N) (e f : ℤ)
    (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (left_gap : (D.tile (idx 0)).Reflected D.model →
      ∃ n : ℤ, 0 ≤ n ∧ n * f ^ 4 = f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2))
    (mixed_gap : ∀ j, D.UnreflectedAt (idx j) → (D.tile (idx (j + 1))).Reflected D.model →
      ∃ n : ℤ, 0 ≤ n ∧ n * f ^ 4 = 2 * f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2)) :
    ∀ j, D.UnreflectedAt (idx j) :=
  layer_rigid_of_exclusions D idx
    (fun h => by
      obtain ⟨n, hn, hEq⟩ := left_gap h
      exact Erdos634.CLayerRigid.left_gap_not_tiles e f n he hef hcop hn hEq)
    (fun j hj h => by
      obtain ⟨n, hn, hEq⟩ := mixed_gap j hj h
      exact Erdos634.CLayerRigid.mixed_gap_not_tiles e f n he hef hcop hn hEq)

end Erdos634.Geometry
