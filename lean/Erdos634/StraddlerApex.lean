import Mathlib.Tactic
import Erdos634.OrderForcing

/-!
# The straddler's residue is a gap, and the apex is where it can be caught

Erdős #634 — the crux of `conj:advance` at `e = 1`, and a direction the companion rules out
downward but not upward.

## The crux, as the companion states it

`rem:straddler`: at every strip junction of a row-`j` `A`-branch the wedge is exactly `α`, and its
filler is either the mirrored `L = -2` mate (rigid) or the direct `L = 0` **straddler**, which lays
`c` along the run tile's `b`-ray, covering that whole `b` and overshooting by exactly `c - b = 1`.
At row `2` the analogous fill dies because `2b - c = f² - 2` is a gap.  At rows `≥ 3` the poke is
interior and no local figure excludes it.  And:

> "The straddler does not cascade: it couples strips only upward, so no descent-to-the-base argument
> applies.  Killing this one shape at rows `≥ 3` is equivalent to the full chain reach, hence to
> Conjecture `conj:advance` at `e = 1`."

So the whole `e = 1` case reduces to one tile placement.

## What is proved here

Nothing arithmetic is new: `f² - 2 ∉ ⟨f, f²-1, f²⟩` is `OrderForcing.gap_2b_minus_c`, already in
the corpus, and `residue_is_gap` below is a one-line restatement of it.  What is new is the
*identification*: `residue_eq_two_b_minus_c` shows the residue left by the apex T-junction,
`b - 1`, is the same value `f² - 2` as the row-`2` residue `2b - c` that the companion already uses
to kill the straddler there.

## Why the apex is the place to look

The companion's own remark blocks descent: the coupling runs *upward*.  But upward terminates, and
`lem:apex` shows the terminus is rigid — the apex angle `3α` admits only three `α`-corners, so the
apex has **exactly two** configurations, "distinguished by the middle tile's chirality: its `b`
shares the `-1`-ray with the left tile's `b`, or its `c` covers that `b` with a T-junction at depth
`b`".  **The second is the straddler's shape.**

`ApexRay` identifies that ray: `L_f` leaves the apex at exactly `α`, so `L_f` *is* the `-1`-ray, and
`chord_jb` divides it into `f` segments of length `b` whose top segment is the left apex tile's
`b`-edge.  In the second apex configuration the middle tile's `c` covers that segment and overshoots
into the next by `c - b = 1`, leaving `b - 1 = f² - 2` to be covered — a gap by `residue_is_gap`.

So at the apex the straddler dies for the same arithmetic reason it dies at row `2`: both are rigid
corners.  What is not proved here is that the upward coupling transmits this downward to rows `≥ 3`;
that is the remaining step, and it is stated, not assumed.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.StraddlerApex

/-- **The straddler's residue is a gap** — this is `OrderForcing.gap_2b_minus_c`, already in the
corpus, restated here only to name the use.  `f² - 2` is not in `⟨f, f²-1, f²⟩` for `f ≥ 3`: it is
below `b`, so only `a`'s could cover it, and `f ∤ f² - 2`. -/
theorem residue_is_gap {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - 2) : False :=
  OrderForcing.gap_2b_minus_c hf h

/-- **It is the row-2 residue.**  `2b - c = 2(f²-1) - f² = f² - 2`. -/
theorem residue_eq_two_b_minus_c (f : ℤ) : 2 * (f ^ 2 - 1) - f ^ 2 = f ^ 2 - 2 := by ring

/-- **The overshoot is exactly `1`.**  `c - b = f² - (f²-1) = 1 = e²` at `e = 1`. -/
theorem overshoot_one (f : ℤ) : f ^ 2 - (f ^ 2 - 1) = 1 := by ring

/-- The apex dichotomy, as a two-valued choice: the middle tile shares the `-1`-ray's `b`, or its
`c` covers it with a T-junction — the straddler shape. -/
inductive ApexConfig | shared | tjunction

/-- In the T-junction case the residue on the next segment is `b - 1 = f² - 2`, a gap. -/
theorem tjunction_residue (f : ℤ) : (f ^ 2 - 1) - 1 = f ^ 2 - 2 := by ring

end Erdos634.StraddlerApex

#print axioms Erdos634.StraddlerApex.residue_is_gap
#print axioms Erdos634.StraddlerApex.residue_eq_two_b_minus_c
#print axioms Erdos634.StraddlerApex.overshoot_one
#print axioms Erdos634.StraddlerApex.tjunction_residue
