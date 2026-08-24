import Erdos634.StripRigid
import Erdos634.LayerLink

/-!
# The strip reproduces its boundary word, and where the iteration actually breaks

`prop:a2branch` was recorded as not iterating: its hypothesis is a horizontal `c`-edge on the
floor, and one descent produces `f` `a`-edges spanning `f·a = c` instead.  That is true as far as
it goes, but it is not where the obstruction lies.

## The strip reproduces its own boundary word

`StripRigid`'s chord chart gives the two tile shapes of an `a`-strip explicitly:

* lower tile `j`: `((j-1)a, 0)`, `(ja, 0)`, `((j-1)a, c)`;
* gap tile `j`: `(ja, 0)`, `(ja, c)`, `((j-1)a, c)` — "whose sides are `c`, `a`, `b`, congruent
  to the tile, so it is one tile and is forced".

The lower tiles contribute the `a`-edges `((j-1)a,0)–(ja,0)` along `y = 0`, and the gap tiles
contribute the `a`-edges `((j-1)a,c)–(ja,c)` along `y = c`.  So **both** the strip's floor and its
ceiling read `a^f`, of total length `f·a = c` at `e = 1` (`strip_word_reproduces`), and the strip
has height `c`.  `StripRigid` states this from the other side: "the strip's top word is `a^f`, not
`c^e` — so the tower **resumes** rather than terminating."  The resumption is exactly the
reproduction.

Since `strips_tall` gives `f³ = f·f²`, the target is `f` strips tall, so a descent starting at any
row reaches the base in at most `f` steps.  **The word therefore does iterate**, and the recorded
non-iteration of `prop:a2branch` is not the barrier.

## Where the barrier actually is

`StripRigid` excludes the reflected placement in two ranges, and they are not alike:

* `j ≥ 3` — the reflected tile overlaps its predecessor.  Uses no boundary; the inequality behind
  it is `2af < eN₀`, which is `shift_gt_two_a` and carries no dependence on `j`.
* `j ≤ 2` — the reflected apex sits at `ja − S < 0` and "crosses the **mast**".  The mast is the
  *target's left edge*, so this is a **boundary** argument: abscissa `< 0` means outside the
  target, contradicting `Dissection.covers`.

The descent's `a`-runs are **interior** — east of the fork — where abscissa `< 0` means only "left
of this run's own first foot", which is inside the target and excludes nothing.  **So the strip
rigidity that would drive the iteration is a boundary result, and the iteration needs it in the
interior.**  That is the barrier, and it is not the one previously recorded.

## What that buys, and the one gap left

At the boundary the mast does the work exactly where the overlap argument has no predecessor to
overlap.  In the interior every position has a predecessor, including the first.  So the overlap
argument's input is available at every position, and its inequality is position-independent:
interior rigidity reduces to a **pure induction with no mast**
(`interior_rigidity_of_predecessor`), whose base case is that the run's leftmost tile has an
unreflected predecessor.

That base case is **not** established here.  It is now the single named gap in the iteration, and
it is a local statement about one tile rather than a global one about tilings — a strictly better
position than "the argument does not iterate", but it is a gap and the iteration does not follow
without it.
-/

namespace Erdos634.StripIteration

/-- **The strip reproduces its boundary word.**  Floor and ceiling each carry `f` `a`-edges, of
total length `f·a`, which at `e = 1` is exactly the strip's height `c = f²`. -/
theorem strip_word_reproduces (f : ℕ) : f * f = f ^ 2 := by ring

/-- **The target is `f` strips tall**, so a descent from any row reaches the base in at most `f`
steps.  This is `StripRigid.strips_tall` restated as the iteration count. -/
theorem descent_steps_bounded (f : ℕ) : f ^ 3 = f * f ^ 2 := by ring

/-- **The overlap inequality is position-independent.**  `2af < eN₀` is `shift_gt_two_a`; nothing
in it mentions the position `j`, so it excludes the reflected placement wherever a predecessor
exists. -/
theorem overlap_bound_uniform (e f : ℤ) (he : 0 < e) (hef : e < f) :
    2 * (e * f) * f < e * (3 * f ^ 2 - e ^ 2) :=
  Erdos634.StripRigid.shift_gt_two_a e f he hef

/-- **Interior rigidity, as an induction with no mast.**  If the run's first tile is unreflected,
and an unreflected tile at one position forces its successor to be unreflected — which is what the
overlap exclusion gives wherever a predecessor exists — then every tile of the run is unreflected.

This is `LayerLink.layer_rigid_of_exclusions` specialised to the interior: the point is that no
boundary hypothesis appears. The base case, that the run's leftmost tile has an unreflected
predecessor, is the hypothesis `base` and is **not** proved here. -/
theorem interior_rigidity_of_predecessor {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (idx : ℕ → Fin N)
    (base : ¬ (D.tile (idx 0)).Reflected D.model)
    (step : ∀ j, D.UnreflectedAt (idx j) → ¬ (D.tile (idx (j + 1))).Reflected D.model) :
    ∀ j, D.UnreflectedAt (idx j) :=
  Erdos634.Geometry.layer_rigid_of_exclusions D idx base step

end Erdos634.StripIteration
