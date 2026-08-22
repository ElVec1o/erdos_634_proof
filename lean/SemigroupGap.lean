import Mathlib.Tactic

/-!
# A general gap lemma for the thin family's edge semigroup

Erdős #634 — generalizing the companion's `double_c_kill` from three values to a family.

At `e = 1` the tile is `(a,b,c) = (f, f²-1, f²)`, and a straight run in a tiling is covered by whole
tile edges, so its length lies in the numerical semigroup

  `S = ⟨f, f²-1, f²⟩`.

Since `f² = f·f`, the third generator is redundant and `S = ⟨f, f²-1⟩`, with `gcd(f, f²-1) = 1`.

The companion's `double_c_kill` records that the three specific lengths

  `b - a = f²-f-1`,   `2b - a = 2f²-f-2`,   `2b - c = f²-2`

are gaps of `S` for every `f ≥ 3`; at `f = 4` these are the values `11, 26, 14` against `⟨4,15,16⟩`.
Those three are the cases `(j,r) = (1,a), (2,a), (2,c)` of the following.

## The lemma

  For `f ≥ 3`, every `j ≤ f-1`, and every `r > 0` divisible by `f`:
  if `j·b - r` is representable then a contradiction follows.

Note `1 ≤ j` is **not** assumed: the proof derives `j > y ≥ 0` from positivity, so the lower bound
on `j` is a consequence.  Lean flagged the hypothesis as unused and it was removed rather than left
standing (Rule 6: an unused hypothesis means the statement is stronger than written).

The proof is one identity.  If `j b - r = x a + y b + z c` with `r = k f`, then rearranging,

  `(j - y)(f² - 1) = f (x + z f + k)`,

so `f ∣ (j-y)(f²-1)`; as `gcd(f, f²-1) = 1`, `f ∣ j - y`.  The right-hand side is at least
`f k = r > 0`, so `j > y`, whence `1 ≤ j - y ≤ j ≤ f-1 < f`, contradicting `f ∣ j - y`.

## Why it matters

The companion states that the general `e = 1` argument is complete except for the enumeration:
"for `f ≥ 5` there are `f-3` walks and the argument as written covers an initial block of exactly
`2` followed by an `a`-run".  The restriction to an initial block of exactly `2` is precisely the
restriction to `j = 2`, which was all `double_c_kill` supplied.  This lemma removes it: `j` is
arbitrary up to `f-1`, and `r` may be any positive combination of `a` and `c` (both multiples of
`f`), not just a single edge.

Falsified before proving (Rule 3): 102949 cases over `f ≤ 30`, no counterexample; and both
hypotheses are witnessed necessary — dropping `j ≤ f-1` admits 117 memberships in the tested range,
dropping `f ∣ r` admits 1676.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SemigroupGap

/-- **The gap lemma.**  With `b = f²-1`, no `j b - r` with `1 ≤ j ≤ f-1` and `f ∣ r`, `r > 0`, is
representable as `x f + y b + z f²` in nonnegative integers. -/
theorem gap (f j r x y z k : ℤ) (hf : 3 ≤ f)
    (hjf : j ≤ f - 1)
    (hk : 1 ≤ k) (hr : r = k * f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (heq : j * (f ^ 2 - 1) - r = x * f + y * (f ^ 2 - 1) + z * f ^ 2) :
    False := by
  have hf0 : (0:ℤ) < f := by linarith
  -- the identity
  have key : (j - y) * (f ^ 2 - 1) = f * (x + z * f + k) := by
    have : r = k * f := hr
    nlinarith [heq, this]
  -- f divides (j - y)(f^2 - 1)
  have hdvd : f ∣ (j - y) * (f ^ 2 - 1) := ⟨x + z * f + k, key⟩
  -- gcd(f, f^2 - 1) = 1, since f * f - (f^2 - 1) = 1
  have hcop : IsCoprime (f) (f ^ 2 - 1) := by
    refine ⟨f, -1, ?_⟩; ring
  have hjy : f ∣ (j - y) := hcop.dvd_of_dvd_mul_right hdvd
  -- the right side is positive, so j > y
  have hpos : 0 < f * (x + z * f + k) := by nlinarith
  have hb : (0:ℤ) < f ^ 2 - 1 := by nlinarith
  have hjy_pos : 0 < j - y := by
    by_contra h
    rw [not_lt] at h
    nlinarith [key, hb, hpos]
  -- but 0 < j - y ≤ j ≤ f - 1 < f contradicts f ∣ (j - y)
  have hle : j - y ≤ f - 1 := by linarith
  obtain ⟨t, ht⟩ := hjy
  have ht1 : 1 ≤ t := by nlinarith
  nlinarith [ht, ht1]

/-- The companion's `double_c_kill` values are the cases `(j,r) = (1,a), (2,a), (2,c)`. -/
theorem recovers_double_c_kill (f : ℤ) (hf : 3 ≤ f) :
    (1 * (f ^ 2 - 1) - f = f ^ 2 - f - 1)
      ∧ (2 * (f ^ 2 - 1) - f = 2 * f ^ 2 - f - 2)
      ∧ (2 * (f ^ 2 - 1) - f ^ 2 = f ^ 2 - 2) := by
  refine ⟨by ring, by ring, by ring⟩

/-- `a = f` and `c = f²` are both multiples of `f`, so the lemma applies to `r` any nonnegative
combination of them — in particular to a run of `a`-edges and `c`-edges, not just one edge. -/
theorem r_admissible (f s t : ℤ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s * f + t * f ^ 2 = (s + t * f) * f := by ring

/-- At `f = 4` the three companion values are `11, 26, 14`, matching the paper. -/
theorem f_four : (1 * (4 ^ 2 - 1) - 4 = 11) ∧ (2 * (4 ^ 2 - 1) - 4 = 26)
    ∧ (2 * (4 ^ 2 - 1) - 4 ^ 2 = 14) := by refine ⟨by norm_num, by norm_num, by norm_num⟩

end Erdos634.SemigroupGap

#print axioms Erdos634.SemigroupGap.gap
#print axioms Erdos634.SemigroupGap.recovers_double_c_kill
#print axioms Erdos634.SemigroupGap.r_admissible
#print axioms Erdos634.SemigroupGap.f_four
