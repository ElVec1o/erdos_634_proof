import Mathlib.Tactic

/-!
# Route 1: the filler overshoot test, general in the first run length

Erdős #634 — exactly how much of Route 1 the existing machinery reaches.

A route-1 base word is `a^i c a^j b a^k` (`Route1`).  Its `b` sits at position `i + j + 2`, and
`thm:e1reduce` requires the `b` in positions `3, …, f`, so

  `i, j ≥ 1`  and  `i + j ≤ f - 2`,  hence  **`i ≤ f - 3`**  and  `k ≥ 2`,

giving `(f-2)(f-3)/2` words.

At the escape point `E` of such a word the wedge is closed by a filler tile, direct or mirrored, and
`lem:topjunction` kills a junction by asking whether the filler's far endpoint leaves the target.
Carrying that test to `E` and clearing denominators (`cos β = (3f²-1)/(2f³)`, `E_x = c cos β + i f + c`,
right side at that height `N₀ - c cos β`) gives, exactly:

  mirrored filler outside `⟺ i f² > f³ - 3f² - f + 1`
  direct   filler outside `⟺ i f² > f³ - 3f² + 1`

the same two cubics as `lem:topjunction`, now carrying an `i`.

## What follows

* **The direct filler is never killed by overshoot.**  It needs `i ≥ f - 2`, and `i ≤ f - 3`
  (`direct_never_outside`).
* **The mirrored filler is killed exactly at `i = f - 3`** (`mirrored_outside_at_top`), which forces
  `j = 1`, `k = 2` — the single word `a^{f-3} c a b a a`.  For `i ≤ f - 4` it survives
  (`mirrored_inside_below_top`).

At `f = 4` the only legal value is `i = 1 = f - 3`, so the mirrored branch dies and the direct
branch survives — which is exactly `rem:walls14`: "the mirrored-filler sub-case [is covered]; the
direct-filler sub-case leaves `E` unblocked and remains open".  Both known outcomes are reproduced,
which is the check on the general statement.

## The accounting

Of the `(f-2)(f-3)/2` route-1 words, each with two filler branches, the overshoot tool resolves
**one branch of one word**, for every `f`.  At `f = 8` that is 1 of 30 branches.  So the tool that
closed the top junction does not scale to Route 1, and the residue is quadratic in `f` while the
coverage is constant.  This is a negative result about the existing machinery, stated exactly, and
it is why Route 1 needs a genuinely new forcing step rather than a further application of the same
test.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Route1Filler

/-- **The legal range of the first run.**  `b` at position `i + j + 2 ≤ f` with `j ≥ 1` forces
`i ≤ f - 3`. -/
theorem i_le (f i j : ℤ) (hj : 1 ≤ j) (hb : i + j + 2 ≤ f) : i ≤ f - 3 := by linarith

/-- **The direct filler is never outside.**  Its test is `i f² > f³ - 3f² + 1`, but `i ≤ f - 3`
gives `i f² ≤ f³ - 3f² < f³ - 3f² + 1`. -/
theorem direct_never_outside (f i : ℤ) (hf : 4 ≤ f) (hi : i ≤ f - 3) :
    i * f ^ 2 < f ^ 3 - 3 * f ^ 2 + 1 := by nlinarith

/-- **The mirrored filler is outside at the top of the range.**  At `i = f - 3` the test
`i f² > f³ - 3f² - f + 1` reads `f³ - 3f² > f³ - 3f² - f + 1`, i.e. `f > 1`. -/
theorem mirrored_outside_at_top (f : ℤ) (hf : 2 ≤ f) :
    (f - 3) * f ^ 2 > f ^ 3 - 3 * f ^ 2 - f + 1 := by nlinarith

/-- **and inside below it.**  For `i ≤ f - 4`, `i f² ≤ f³ - 4f² ≤ f³ - 3f² - f + 1`, the last step
being `f² - f + 1 ≥ 0`. -/
theorem mirrored_inside_below_top (f i : ℤ) (hf : 4 ≤ f) (hi : i ≤ f - 4) :
    i * f ^ 2 ≤ f ^ 3 - 3 * f ^ 2 - f + 1 := by nlinarith [sq_nonneg (f - 1), sq_nonneg f]

/-- **`i = f - 3` forces `j = 1` and `k = 2`.**  With `i + j ≤ f - 2` and `j ≥ 1`, `i = f - 3` leaves
`j ≤ 1`; and `i + j + k = f` then gives `k = 2`. -/
theorem top_word_rigid (f i j k : ℤ) (hj : 1 ≤ j) (hb : i + j + 2 ≤ f)
    (hsum : i + j + k = f) (hi : i = f - 3) : j = 1 ∧ k = 2 := by
  constructor <;> omega

/-- **The `f = 4` cross-check.**  There `i ≤ f - 3 = 1`, so `i = 1`: the mirrored filler is outside
(`1·16 = 16 > 4³ - 3·4² - 4 + 1 = 13`) and the direct filler is inside
(`16 < 4³ - 3·4² + 1 = 17`).  These are `rem:walls14`'s two sub-case outcomes. -/
theorem f_four_check :
    (1 : ℤ) * 4 ^ 2 > 4 ^ 3 - 3 * 4 ^ 2 - 4 + 1 ∧ (1 : ℤ) * 4 ^ 2 < 4 ^ 3 - 3 * 4 ^ 2 + 1 := by
  refine ⟨by norm_num, by norm_num⟩

end Erdos634.Route1Filler

#print axioms Erdos634.Route1Filler.i_le
#print axioms Erdos634.Route1Filler.direct_never_outside
#print axioms Erdos634.Route1Filler.mirrored_outside_at_top
#print axioms Erdos634.Route1Filler.mirrored_inside_below_top
#print axioms Erdos634.Route1Filler.top_word_rigid
#print axioms Erdos634.Route1Filler.f_four_check
