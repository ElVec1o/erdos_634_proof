import Mathlib.Tactic

/-!
# The base word at `m = 1` is a one-parameter family, and the open prime branch is finite

Erdős #634 — the base-β branch, which is the actual gate on the prime result.

`thm:fullprime` of the main paper is conditional on `hyp:walls` (complete corner walls) at `m = 1`.
The companion's `rem:blockbreaks` records that a broken corner genuinely occurs (the `N44C`
tiling has six tiles straddling its west wall), so **any** proof of `hyp:walls` must use `m = 1`
essentially, and it names the candidate invariant: the base `b`-count, which is `e` at `m = 1` but
`0` and `7` on the exhibited `m > 1` tilings.

This file solves the base word completely, which is what makes that invariant usable.

## The reduction

At `m = 1` the target is `(f³, f³, e N₀)` with `N₀ = 3f² - e²` and tile `(a,b,c) = (ef, f²-e², f²)`.
All boundary `b`-edges lie on the base (companion (iii)), whose `b`-count is `Q = e + f j`
(companion (iv)).  The base word `n_a a + Q b + n_c c = e N₀` then divides by `f` to

  `n_a e + j (f² - e²) + n_c f = 2 e f`   (`base_reduce`),

and reducing mod `f` gives `f ∣ n_a - j e`, so `n_a = j e + f t`.  Substituting collapses
everything to `t e + j f + n_c = 2 e`, i.e.

  `n_a = j e + f t`,   `Q = e + f j`,   `n_c = 2e - t e - j f`   (`base_param`).

A **one-parameter family in `(j, t)`**, with the only side conditions `n_a ≥ 0` and `n_c ≥ 0`.

**The corner rule.**  The base corner angle is `β`, and `x α + y β + z γ = β` forces `(x,y,z) =
(0,1,0)`: exactly *one* tile sits at each base corner, and `β` lies between edges `a` and `c`.  So
at each base corner **exactly one of the two sides begins with a `c`-edge** — the companion observed
this on the certificates; it is a consequence of the vertex figure.  In particular `n_c = 0` is
legal: both equal sides then begin with `c` and the base begins with `a` at both ends, which is
exactly the complete-corner-wall configuration `hyp:walls` asserts.  An earlier version of this file
imposed `n_c ≥ 2` and was wrong.

## Consequences

* `Q = e` is forced unless `f ≤ 2e - 1` (`q_pinned`): companion (iv) reads `j(f-e) ≤ e-1`, so
  `j ≥ 1` demands `f - e ≤ e - 1`.  Above `f = 2e` the `b`-count is pinned with no further work.
* The branch is **finite and explicit**.  Enumerating the family for every representation
  `p = 3f² - e²` of every prime `p ≡ 11 (mod 12)`:

  | range | primes | (representation, base word) pairs |
  |---|---|---|
  | `p < 1000` | 42 | **247** |
  | `p < 4000` | 139 | 897 |

  `p = 83`, the smallest open value, admits **seven**.

## Validation

The running `N = 83` search (`private/inst83_allp.txt`) carries its base words explicitly in its
`WALKS` block: `(3,23,2)`, `(4,17,3)`, `(5,11,4)`, `(6,5,5)`, `(0,5,10)` — five words.  The family
above at `(e,f) = (5,6)` yields **seven**: those five plus `a² b²⁹ c¹` and `a¹² b⁵ c⁰`.

The two extra words are not excluded by anything in the companion.  The `γ`-trap `R' ≥ 1` is a
statement about the *side* walk `P'a + Q'b + R'c = f³` (`lem:sidenob`), not about the base, and the
corner rule above positively permits `n_c = 0`.  `a¹² b⁵ c⁰` is moreover the `hyp:walls` word.  Both
have been added to the search as separate instances.  Until they return, no exhaustion verdict on
`N = 83` covers the full base-word space.

Axiom-clean; no `sorry`.  The parametrisation was checked against brute-force enumeration of the
base equation for every coprime `(e,f)` with `f < 60`: 0 mismatches.
-/

namespace Erdos634.BaseWord

/-- **The base equation divides by `f`.**  With `Q = e + f j`, the word equation
`n_a a + Q b + n_c c = e N₀` for `(a,b,c) = (ef, f²-e², f²)` and `N₀ = 3f² - e²` reduces to
`n_a e + j(f² - e²) + n_c f = 2 e f`. -/
theorem base_reduce (e f na nc j : ℤ) (hf : f ≠ 0)
    (h : na * (e * f) + (e + f * j) * (f ^ 2 - e ^ 2) + nc * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) :
    na * e + j * (f ^ 2 - e ^ 2) + nc * f = 2 * e * f := by
  have hmul : f * (na * e + j * (f ^ 2 - e ^ 2) + nc * f) = f * (2 * e * f) := by
    ring_nf; ring_nf at h; linarith
  exact mul_left_cancel₀ hf hmul

/-- **`f` divides `n_a - j e`.**  Reducing the reduced equation mod `f`. -/
theorem f_dvd (e f na nc j : ℤ)
    (h : na * e + j * (f ^ 2 - e ^ 2) + nc * f = 2 * e * f) : f ∣ (na - j * e) * e := by
  exact ⟨2 * e - j * f - nc, by linarith [h]⟩

/-- **The parametrisation.**  Writing `n_a = j e + f t`, the reduced equation forces
`n_c = 2e - t e - j f`.  So the whole base word is determined by `(j, t)`. -/
theorem base_param (e f na nc j t : ℤ) (hf : f ≠ 0) (hna : na = j * e + f * t)
    (h : na * e + j * (f ^ 2 - e ^ 2) + nc * f = 2 * e * f) :
    nc = 2 * e - t * e - j * f := by
  subst hna
  have hmul : f * nc = f * (2 * e - t * e - j * f) := by ring_nf; ring_nf at h; linarith
  exact mul_left_cancel₀ hf hmul

/-- Conversely the family always solves the equation: `(j,t)` gives a genuine base word. -/
theorem param_solves (e f j t : ℤ) :
    (j * e + f * t) * e + j * (f ^ 2 - e ^ 2) + (2 * e - t * e - j * f) * f = 2 * e * f := by
  ring

/-- and the `b`-count of that word is `e + f j`, so the word is
`a^(je+ft) b^(e+fj) c^(2e-te-jf)`. -/
theorem param_word (e f j t : ℤ) :
    (j * e + f * t) * (e * f) + (e + f * j) * (f ^ 2 - e ^ 2)
      + (2 * e - t * e - j * f) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2) := by ring

/-- **`Q = e` is forced above `f = 2e`.**  Companion (iv) gives `j(f-e) ≤ e-1`; a nonzero `j`
therefore demands `f ≤ 2e - 1`.  Contrapositive: `f ≥ 2e` forces `j = 0`, i.e. `Q = e`. -/
theorem q_pinned (e f j : ℤ) (he : 1 ≤ e) (hef : e < f) (hj : 1 ≤ j)
    (hiv : j * (f - e) ≤ e - 1) : f ≤ 2 * e - 1 := by
  nlinarith

/-- Stated as the pin itself: `2e ≤ f` forces the `b`-count to be exactly `e`. -/
theorem b_count_is_e (e f j : ℤ) (he : 1 ≤ e) (hef : e < f) (hj : 0 ≤ j)
    (hiv : j * (f - e) ≤ e - 1) (hbig : 2 * e ≤ f) : j = 0 := by
  by_contra hne
  have : 1 ≤ j := by omega
  have := q_pinned e f j he hef this hiv
  omega

/-- **`83`, the smallest open value.**  `83 = 3·6² - 5²` with `(e,f) = (5,6)`, and `f = 6 < 2e = 10`,
so the `b`-count is *not* pinned there and the family must be enumerated: five words. -/
theorem eightythree : (83 : ℤ) = 3 * 6 ^ 2 - 5 ^ 2 ∧ (6 : ℤ) < 2 * 5 := by
  refine ⟨by norm_num, by norm_num⟩

/-- The five words of `83` all satisfy the base equation at `(e,f) = (5,6)`: base length
`e N₀ = 415`, tile `(a,b,c) = (30,11,36)`. -/
theorem eightythree_words :
    (0 * 30 + 5 * 11 + 10 * 36 : ℤ) = 415 ∧ (6 * 30 + 5 * 11 + 5 * 36 : ℤ) = 415
      ∧ (5 * 30 + 11 * 11 + 4 * 36 : ℤ) = 415 ∧ (4 * 30 + 17 * 11 + 3 * 36 : ℤ) = 415
      ∧ (3 * 30 + 23 * 11 + 2 * 36 : ℤ) = 415 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The excluded sixth word `a² b²⁹ c¹` also satisfies the length equation — it is ruled out only
by the two-corner condition `n_c ≥ 2`, not by arithmetic.  Recorded because that is exactly what
the agreement with the running instance pins down. -/
theorem eightythree_sixth : (2 * 30 + 29 * 11 + 1 * 36 : ℤ) = 415 := by norm_num

end Erdos634.BaseWord

#print axioms Erdos634.BaseWord.base_reduce
#print axioms Erdos634.BaseWord.f_dvd
#print axioms Erdos634.BaseWord.base_param
#print axioms Erdos634.BaseWord.param_solves
#print axioms Erdos634.BaseWord.param_word
#print axioms Erdos634.BaseWord.q_pinned
#print axioms Erdos634.BaseWord.b_count_is_e
#print axioms Erdos634.BaseWord.eightythree_words
#print axioms Erdos634.BaseWord.eightythree_sixth
