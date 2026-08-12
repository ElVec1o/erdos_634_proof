import Mathlib.Tactic

/-!
# The second-edge quartic is the golden form in the tile's own sides

Erdős #634, base-`β` branch.  `WedgeBound.second_edge_quartic` reduces the second-base-edge
question to the sign of

    P(e,f) = e⁴ − e³f − 3e²f² + ef³ + f⁴.

That polynomial looks arbitrary.  It is not: with the tile `(a,b,c) = (ef, f²−e², f²)`,

    P(e,f) = b² + a·b − a²,

the golden quadratic form evaluated at `(b,a)`.  So the criterion `P < 0` is exactly
`a² − ab − b² > 0`, i.e. `a/b` exceeds the golden ratio.

This is a strictly better statement of the same criterion: it is invariant, it is checkable from the
tile alone without reference to `(e,f)`, and it explains the threshold `t₀ = 0.7376403…` as the
root of `φt² + t − φ` rather than as a numerical constant.

Everything here is a ring identity over `ℤ`.  Axiom-clean.
-/

namespace Erdos634.GoldenForm

/-- Tile sides of the base-`β` family. -/
def a (e f : ℤ) : ℤ := e * f
def b (e f : ℤ) : ℤ := f ^ 2 - e ^ 2

/-- **The quartic is the golden form.**  The second-edge polynomial of `WedgeBound` equals
`b² + ab − a²` on the nose. -/
theorem quartic_eq_golden (e f : ℤ) :
    e ^ 4 - e ^ 3 * f - 3 * e ^ 2 * f ^ 2 + e * f ^ 3 + f ^ 4
      = b e f ^ 2 + a e f * b e f - a e f ^ 2 := by
  unfold a b; ring

/-- **The criterion, in the tile's own sides.**  The quartic is negative exactly when
`a² − ab − b² > 0`, which for positive `a, b` is `a/b > φ`. -/
theorem quartic_neg_iff_golden (e f : ℤ) :
    e ^ 4 - e ^ 3 * f - 3 * e ^ 2 * f ^ 2 + e * f ^ 3 + f ^ 4 < 0
      ↔ 0 < a e f ^ 2 - a e f * b e f - b e f ^ 2 := by
  rw [quartic_eq_golden]; omega

/-- The golden form is the Fibonacci-recurrence discriminant: `a² − ab − b²` takes the value `±1`
exactly on consecutive Fibonacci pairs, which is why the threshold is `φ` and not some other
algebraic number.  Recorded as the defining identity `F(a,b) = −F(b, a−b)`. -/
theorem golden_form_step (a b : ℤ) :
    a ^ 2 - a * b - b ^ 2 = -(b ^ 2 - b * (a - b) - (a - b) ^ 2) := by ring

/-- `a > b` is *not* enough: the criterion needs the golden gap.  At `(e,f) = (3,7)` — the member of
`N = 138` — one has `a = 21 < 40 = b`, so the form is negative and the quartic is positive.  This is
the sharpness witness `WedgeBound.quartic_at_3_7` restated invariantly. -/
theorem golden_fails_at_3_7 : a 3 7 ^ 2 - a 3 7 * b 3 7 - b 3 7 ^ 2 < 0 := by
  unfold a b; decide

/-- At `(5,6)` — the member of `N = 83` — the form is positive: `a = 30`, `b = 11`, and
`900 − 330 − 121 = 449 > 0`. -/
theorem golden_holds_at_5_6 : 0 < a 5 6 ^ 2 - a 5 6 * b 5 6 - b 5 6 ^ 2 := by
  unfold a b; decide

/-- **Close pairs are golden except at `f = 3`.**  At `e = f − 1` the form is
`a² − ab − b² = f²(f−1)² − (f−1)f(2f−1) − (2f−1)²`, positive exactly for `f ≥ 4`. -/
theorem golden_on_close_pairs (f : ℤ) (hf : 4 ≤ f) :
    0 < a (f - 1) f ^ 2 - a (f - 1) f * b (f - 1) f - b (f - 1) f ^ 2 := by
  unfold a b; nlinarith [sq_nonneg (f - 4), sq_nonneg f, sq_nonneg (f - 1)]

/-- And it fails at `f = 3`, the single close-pair exception `(e,f) = (2,3)`, `N = 23`. -/
theorem golden_fails_at_2_3 : a 2 3 ^ 2 - a 2 3 * b 2 3 - b 2 3 ^ 2 < 0 := by
  unfold a b; decide

end Erdos634.GoldenForm

#print axioms Erdos634.GoldenForm.quartic_eq_golden
#print axioms Erdos634.GoldenForm.quartic_neg_iff_golden
#print axioms Erdos634.GoldenForm.golden_on_close_pairs
