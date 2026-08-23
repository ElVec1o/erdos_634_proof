import Erdos634.Congruence
import Erdos634.StripRigid

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

**What is still assumed.**  The two bridges are *not* proved.  They are the geometric step
from "this tile is the reflected placement" to "its apex/edge lands where the arithmetic
says", and proving them needs the fan machinery that `Dissection` lines 396–402 record as
absent from Mathlib.  They are isolated here as two named hypotheses and nothing else, which
is the point: the layer's rigidity now rests on exactly two geometric facts, not on an
unformalized notion of tiling.
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

end Erdos634.Geometry
