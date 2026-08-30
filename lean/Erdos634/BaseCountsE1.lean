import Mathlib

/-!
# The base word's letter counts at `e = 1`

Erdős #634, companion Theorem `thm:e1reduce`.  The paper's statement — that the base walk is a
permutation of `(a^f, b, c)` — is labelled PROVED and is the input every remaining hypothesis of
bridge (c) traces back to.  Its *arithmetic* half is proved here.

From the walk equation alone, with `a = f`, `b = f² - 1`, `c = f²` and base length `3f² - 1`:

* the `b`-count is exactly `1`;
* the remaining counts satisfy `n_a + n_c f = 2f`, so `(n_a, n_c)` is `(0, 2)`, `(f, 1)` or
  `(2f, 0)`.

So the equation forces the single `b` outright, and leaves a three-way choice in `c`.  The paper's
`(ii)` — exactly one `c` — is the middle case; excluding the outer two is the *geometric* half of
`thm:e1reduce`, and is not proved here.  Naming it is the point: what had been one prose theorem is
now one verified count plus one named residue.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BaseCountsE1

/-- A multiple of `f` smaller than `f` in absolute value is zero. -/
theorem small_multiple {f m k : ℤ} (hf : 0 < f) (h : f * k = m) (hm : -f < m) (hm' : m < f) :
    m = 0 := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have : f * k ≤ -f := by nlinarith
    omega
  · omega
  · have : f ≤ f * k := by nlinarith
    omega

/-- **The base counts at `e = 1`.**  The walk equation forces `n_b = 1` and a three-way split of
the rest. -/
theorem base_counts (f na nb nc : ℤ) (hf : 3 ≤ f)
    (hna : 0 ≤ na) (hnb : 0 ≤ nb) (hnc : 0 ≤ nc)
    (heq : na * f + nb * (f ^ 2 - 1) + nc * f ^ 2 = 3 * f ^ 2 - 1) :
    nb = 1 ∧ ((na = 0 ∧ nc = 2) ∨ (na = f ∧ nc = 1) ∨ (na = 2 * f ∧ nc = 0)) := by
  have hf0 : (0:ℤ) < f := by linarith
  have hsq : 9 ≤ f ^ 2 := by nlinarith
  have hnb_le : nb ≤ 3 := by nlinarith [sq_nonneg f, hna, hnc]
  have hdvd : f * (na + nb * f + nc * f - 3 * f) = nb - 1 := by linear_combination heq
  have hnb1 : nb = 1 := by
    have := small_multiple hf0 hdvd (by omega) (by omega)
    omega
  subst hnb1
  refine ⟨rfl, ?_⟩
  have hrest : na + nc * f = 2 * f := by
    have h : f * (na + nc * f - 2 * f) = 0 := by linear_combination heq
    rcases mul_eq_zero.mp h with h0 | h0
    · linarith
    · linarith
  have hnc2 : nc ≤ 2 := by nlinarith
  interval_cases nc
  · right; right; constructor <;> linarith
  · right; left; constructor <;> linarith
  · left; constructor <;> linarith

end Erdos634.BaseCountsE1
