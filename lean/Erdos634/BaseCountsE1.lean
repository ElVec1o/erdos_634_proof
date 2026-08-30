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

/-! ## Excluding `n_c = 2`

With `n_c = 2` the base has `n_a = 0`, so it is three edges — a permutation of `(b, c, c)`.  The
corner condition (`prop:cornerpara`: the first two and the last two edges lie in `{a, c}`) then
forbids the `b` from every position, since with three edges those two pairs cover the word.  So
`n_c ≠ 2`, and only `(2f, 0)` and `(f, 1)` survive.

The remaining exclusion, `n_c ≠ 0`, is the paper's `prop:gammatrap` — every side carries at least
one `c`-edge — whose Lean counterpart `AngleArithmetic.gamma_trap` is the arithmetic ingredient
`ng ≤ 1`, not the statement itself.  It is therefore not available here, and `n_c = 0` stays open. -/

/-- **A three-letter base cannot hold the `b`.**  If the first two and the last two of three
positions avoid `b`, no position holds it. -/
theorem no_b_in_three (isB : Fin 3 → Prop) [DecidablePred isB]
    (hb : ∃ i, isB i) (h0 : ¬ isB 0) (h1 : ¬ isB 1) (h2 : ¬ isB 2) : False := by
  obtain ⟨i, hi⟩ := hb
  fin_cases i
  · exact h0 hi
  · exact h1 hi
  · exact h2 hi

/-- **The base counts, with `n_c = 2` excluded.**  Under the corner condition the base is either
all `a`s with no `c` — still open — or the intended `(a^f, b, c)`. -/
theorem base_counts_corner (f na nb nc : ℤ) (hf : 3 ≤ f)
    (hna : 0 ≤ na) (hnb : 0 ≤ nb) (hnc : 0 ≤ nc)
    (heq : na * f + nb * (f ^ 2 - 1) + nc * f ^ 2 = 3 * f ^ 2 - 1)
    (hcorner : nc = 2 → False) :
    nb = 1 ∧ ((na = f ∧ nc = 1) ∨ (na = 2 * f ∧ nc = 0)) := by
  obtain ⟨hb, hcases⟩ := base_counts f na nb nc hf hna hnb hnc heq
  refine ⟨hb, ?_⟩
  rcases hcases with ⟨_, h2⟩ | h | h
  · exact absurd h2 (fun h => hcorner h)
  · exact Or.inl h
  · exact Or.inr h

end Erdos634.BaseCountsE1
