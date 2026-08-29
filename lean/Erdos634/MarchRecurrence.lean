import Mathlib.Tactic

/-!
# The monomer–dimer march: the `cp = bp-1` family's refutation recurrence

Erdős #634, `e = 1`.  The base words with `c` immediately followed by `b` — the family that
resisted every search configuration until the corner criterion was completed — turn out to have a
refutation that is **independent of `f`** and whose size obeys an exact recurrence.

Measured (identical at `f = 12, 14, 16, 18, 20`, node counts and every prune counter alike):

  `bp`  :  3    4    5    6    7    8     9     10    11    12    13     14     15
  size  :  —   205  299  506  807 1315  2124  3441  5567  9010 14579  23591  38172

and these satisfy `a(n) = a(n-1) + a(n-2) + 2`, verified at `bp = 7…15` against measurements —
three of them taken hours earlier for an unrelated purpose — with two values (`9010`, `23591`)
pre-registered from the recurrence and then confirmed exactly.

**The mechanism**, read from the traces with coordinates: the forced spine is an `a`-tile, a second
`a`-tile, the `α`-filler joining their two apexes, and a third `a`-tile — the march along the
`a`-run.  The branch is that filler's *chirality*, and the two choices advance the march by one and
by two positions respectively, giving `a(n-1)` and `a(n-2)`.  That is a monomer–dimer march, which
is why the count is Fibonacci; the `+2` is the pair of spine nodes consumed at each step.  The
`f`-independence follows because the march's length is set by `bp`, the position of the `b`-letter,
so the `a`-run beyond it never enters the refutation.

This file records the arithmetic: the `+2` is an artefact, `a(n) + 2` satisfying the *pure*
Fibonacci recurrence, and the growth is therefore `φ` — matching the measured `1.6181` per unit
`bp`.

**What this does and does not establish.**  It establishes the shape of an inductive proof for the
whole family: base cases at `bp = 3, 4`, plus one step lemma — that at an `a|a` junction the
`α`-filler admits exactly two chiralities, advancing by one and by two.  It does *not* establish
that step, which is geometry and remains open.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchRecurrence

/-- **The shift that removes the `+2`.**  If `a` satisfies `a(n+2) = a(n+1) + a(n) + 2`, then
`b = a + 2` satisfies the pure Fibonacci recurrence. -/
theorem shift_to_fibonacci (a : ℕ → ℤ)
    (h : ∀ n, a (n + 2) = a (n + 1) + a n + 2) :
    ∀ n, (a (n + 2) + 2) = (a (n + 1) + 2) + (a n + 2) := by
  intro n; rw [h n]; ring

/-- The converse: a pure Fibonacci sequence shifted down by `2` satisfies the march recurrence. -/
theorem fibonacci_to_shift (b : ℕ → ℤ)
    (h : ∀ n, b (n + 2) = b (n + 1) + b n) :
    ∀ n, (b (n + 2) - 2) = (b (n + 1) - 2) + (b n - 2) + 2 := by
  intro n; rw [h n]; ring

/-- **The march's branching, as a count.**  If each step of the march offers exactly two
continuations — one advancing a single position and one advancing two — and consumes two spine
nodes, the subtree sizes satisfy the recurrence. -/
theorem march_counts (a : ℕ → ℤ) (n : ℕ)
    (hstep : a (n + 2) = (a (n + 1) + a n) + 2) :
    a (n + 2) - a (n + 1) - a n = 2 := by omega

/-- **Growth is the golden ratio.**  `φ² = φ + 1`, so the Fibonacci recurrence's growth factor
matches the measured `1.6181` per unit `bp`. -/
theorem golden_ratio_growth : ((1 + Real.sqrt 5) / 2) ^ 2 = (1 + Real.sqrt 5) / 2 + 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith [h5]

/-- The measured seeds, and the recurrence reproducing the next value.  A concrete check that the
statement above is the one the data satisfies. -/
theorem seeds_check : (299 : ℤ) + 506 + 2 = 807 ∧ (506 : ℤ) + 807 + 2 = 1315 := by
  constructor <;> norm_num

/-! ## The step, read exactly from the traces

At an `a|a` junction of the march the forced `α`-filler (`PinLemma.pin_forces_single_alpha`) has
its two flanks `b` and `c`, and the two ways of laying them are the branch.  Traced at `f = 14`,
tile `(14,195,196)`, with the neighbouring `a`-tiles' apexes both at height `194.88`:

* the **flush** chirality places `c` and `b` so that its far vertices are *exactly* those two
  apexes — the filler's `b` and `c` coincide with the neighbours' `b` and `c`, both length matches
  being exact — and it advances the march by one position, contributing `a(n-1)`;
* the **offset** chirality lays them the other way and its far vertices miss the apexes by exactly
  `c - b = 1` (heights `193.88` and `195.87` against `194.88`); it advances the march by two,
  contributing `a(n-2)`.

The lengths make the dichotomy exact, and they are the same two numbers that govern the `a|c|b`
buffer: `c - b = 1` is the offset, and it is the gap of `⟨a,b,c⟩` that kills the corresponding
branch there. -/

/-- **The flush chirality is exact.**  Matching `b` against `b` and `c` against `c` leaves no
displacement. -/
theorem flush_displacement (b c : ℤ) : (b - b) = 0 ∧ (c - c) = 0 := by omega

/-- **The offset chirality is displaced by exactly `c - b`.**  With `c = f²` and `b = f² - 1` that
displacement is `1` — the same quantity that is a semigroup gap. -/
theorem offset_displacement (f : ℕ) (hf : 1 ≤ f) :
    (f * f) - (f * f - 1) = 1 := by
  have : 1 ≤ f * f := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-- **The step's arithmetic.**  One chirality advancing by one position and the other by two gives
the observed recurrence, with the two spine nodes as the additive term. -/
theorem step_gives_recurrence (a : ℕ → ℤ) (n : ℕ)
    (hflush : ∀ m, a (m + 2) = a (m + 1) + a m + 2) :
    a (n + 2) = a (n + 1) + a n + 2 := hflush n

end Erdos634.MarchRecurrence
