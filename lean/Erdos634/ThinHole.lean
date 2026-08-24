import Mathlib.Tactic

/-!
# The `e = 1` hole in the conditional prime theorem

Erdős #634 — which primes the conditional theorem cannot reach, and why.

`thm:fullprime` excludes every prime `N ≡ 3 (mod 4)`, `N > 3`, *assuming* Hypothesis (walls).  The
assumption is a genuine hypothesis when `e ≥ 2`.  At `e = 1` it is not: the companion's
`rem:sidenoa` shows that there Hypothesis (walls) is *equivalent* to the conclusion — "at `e = 1` it
**is** the case" — because the complete-block base word `a^f b c` ends in a `c` while
`thm:e1reduce` forces `a`-edges at both ends.  So at `e = 1` the hypothesis can never be discharged
without proving the case directly, and a prime all of whose representations `p = 3f² - e²` have
`e = 1` gets no content from the theorem at all.

This file records the arithmetic of that hole.

## `f` is even

If `f` is odd then `3f²` is odd and `N = 3f² - 1` is even, so `N` is not an odd prime
(`even_of_odd`, `f_even_of_prime`).  Every prime in the hole therefore has `f` even — checked
against the census below.  The consequence for proof strategy is sharp: **any argument that bites
only on odd `f` is irrelevant to the primes**, which is why a `b`-edge pairing/parity count gives
nothing here (it would force `f` even, which already holds).

## The census

Enumerating primes `p = 3f² - e²` with `gcd(e,f) = 1`, `1 ≤ e < f`, below `200000`: 4000 primes,
of which 3949 admit some representation with `e ≥ 2` and **51** admit only `e = 1`.  Three of those
(`11, 47, 107`) are already excluded unconditionally by certified exhaustion, leaving **48**.  The
smallest unsettled is `191 = 3·8² - 1`, with the single representation `(e,f) = (1,8)`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ThinHole

/-- **`3f² - 1` is even when `f` is odd.**  Then `f = 2m+1`, and `3f² - 1 = 2(6m² + 6m + 1)`. -/
theorem even_of_odd (m : ℕ) : 3 * (2 * m + 1) ^ 2 - 1 = 2 * (6 * m ^ 2 + 6 * m + 1) := by
  have h : 3 * (2 * m + 1) ^ 2 = 2 * (6 * m ^ 2 + 6 * m + 1) + 1 := by ring
  omega

/-- **So a prime of the thin form has `f` even.**  If `N = 3f² - 1` is prime and `N > 2` then `f` is
even: an odd `f` makes `N` even and greater than `2`, hence composite. -/
theorem f_even_of_prime (f : ℕ) (hf : 2 ≤ f) (hp : Nat.Prime (3 * f ^ 2 - 1)) : Even f := by
  by_contra hodd
  obtain ⟨m, rfl⟩ : ∃ m, f = 2 * m + 1 := by
    rcases Nat.even_or_odd f with h | h
    · exact absurd h hodd
    · exact h
  have hval : 3 * (2 * m + 1) ^ 2 - 1 = 2 * (6 * m ^ 2 + 6 * m + 1) := even_of_odd m
  rw [hval] at hp
  have h2 : (2 : ℕ) ∣ 2 * (6 * m ^ 2 + 6 * m + 1) := ⟨_, rfl⟩
  have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2)
  have hm : 1 ≤ m := by omega
  rcases this with h | h <;> nlinarith [hm]

/-- The smallest member of the hole: `191 = 3·8² - 1`, and `8` is even as the previous theorem
requires. -/
theorem one_ninety_one : 3 * 8 ^ 2 - 1 = 191 ∧ Even 8 := ⟨by norm_num, by decide⟩

/-- `11`, `47`, `107`, `191` are the first four thin primes, all with `f` even. -/
theorem first_four :
    (3 * 2 ^ 2 - 1 = 11) ∧ (3 * 4 ^ 2 - 1 = 47) ∧ (3 * 6 ^ 2 - 1 = 107)
      ∧ (3 * 8 ^ 2 - 1 = 191) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **A representation with `e ≥ 2` is what makes Hypothesis (walls) a genuine hypothesis.**  The
hole consists of the primes admitting none.  Decidable membership test for a given `p`: search
`e, f` in the finite box `e < f ≤ p`. -/
def hasBigE (p : ℕ) : Prop :=
  ∃ e f : ℕ, 2 ≤ e ∧ e < f ∧ f ≤ p ∧ Nat.Coprime e f ∧ 3 * f ^ 2 - e ^ 2 = p

/-- `23 = 3·3² - 2²` has a representation with `e = 2`, so it is outside the hole — consistent with
its being one of the values already excluded unconditionally. -/
theorem twentythree_outside : hasBigE 23 :=
  ⟨2, 3, by norm_num, by norm_num, by norm_num, by decide, by norm_num⟩

/-- `191` has no representation with `e ≥ 2` and `f ≤ 9`; the only one is `(1,8)`.  (The full search
box is `f ≤ 191`, verified by enumeration outside Lean; this records the small-`f` part.) -/
theorem oneninetyone_small_box :
    ∀ e f : ℕ, 2 ≤ e → e < f → f ≤ 9 → 3 * f ^ 2 - e ^ 2 ≠ 191 := by
  intro e f he hef hf9
  interval_cases f <;> interval_cases e <;> norm_num

/-! ## The hole, characterised

The census counts the hole; it does not say what it *is*.  It is exactly the primes of the form
`3f² − 1`:

  a prime `p` has all its representations `p = 3f² − e²` with `e = 1`
    **iff** `p = 3f² − 1` for some `f`.

Verified by direct enumeration: below `200 000` both sets have `51` members and below `600 000`
both have `82`, with no discrepancy either way
(`code/analysis/hole_characterisation.py`).

### Why

Subtracting the two representations,

  `3g² − e² = 3f² − 1`  ⟺  `3(g−f)(g+f) = (e−1)(e+1)`   (`rep_identity`)

so `e = 1` forces `g = f`, and `e ≥ 2` forces `g > f`.  That the larger `g` never occurs is the
unit structure of `ℤ[√3]`: `e² − 3g² = −p` says `Norm(e + g√3) = −p`, the fundamental unit is
`ε = 2 + √3` of norm `1`, and it acts by `(e,g) ↦ (2e+3g, e+2g)`.  The ratio `t = e/g` has fixed
point `√3`, and `e < g` means `t < 1`; one step of `ε` carries `t = 1/f` to about `3/2 > 1`, and
`ε⁻¹` does the same in magnitude, so **both** neighbours of `(1,f)` have `e > g`.  The orbit
therefore contributes exactly one admissible representation, the one with `e = 1`.

### What it means for the project

The `e ≥ 2` half of `thm:fullprime` is unconditional, so a natural hope is that some hole prime
also admits an `e ≥ 2` representation and is closed that way.  The characterisation says this hope
is **empty by construction**: the hole is precisely the primes for which no such representation
exists.  Recorded so the route is not attempted again. -/

/-- **The representation identity.**  Two base-`β` representations of the same number differ by
`3(g−f)(g+f) = (e−1)(e+1)`; so `e = 1` forces `g = f`, and `e ≥ 2` forces `g > f`. -/
theorem rep_identity (e f g : ℤ) (h : 3 * g ^ 2 - e ^ 2 = 3 * f ^ 2 - 1) :
    3 * ((g - f) * (g + f)) = (e - 1) * (e + 1) := by linarith [h, sq_nonneg e]

/-- **`e = 1` forces `g = f`** (given `f, g > 0`). -/
theorem rep_e_one (f g : ℤ) (hf : 0 < f) (hg : 0 < g)
    (h : 3 * g ^ 2 - 1 ^ 2 = 3 * f ^ 2 - 1) : g = f := by nlinarith [h]

/-- **`e ≥ 2` forces `g > f`.**  The identity's right-hand side is then positive. -/
theorem rep_e_ge_two (e f g : ℤ) (he : 2 ≤ e) (hf : 0 < f) (hg : 0 < g)
    (h : 3 * g ^ 2 - e ^ 2 = 3 * f ^ 2 - 1) : f < g := by nlinarith [h]

/-- **The unit action of `ℤ[√3]`.**  `ε = 2 + √3` has norm `1` and sends `(e,g)` to
`(2e+3g, e+2g)`, preserving `e² − 3g²`. -/
theorem unit_preserves_norm (e g : ℤ) :
    (2 * e + 3 * g) ^ 2 - 3 * (e + 2 * g) ^ 2 = e ^ 2 - 3 * g ^ 2 := by ring

/-- **One step of `ε` leaves the admissible range.**  From `(1,f)` with `f ≥ 2` the image is
`(2+3f, 1+2f)`, and `2+3f > 1+2f`, so the new pair has `e > g`. -/
theorem unit_step_exits (f : ℤ) (hf : 2 ≤ f) : 1 + 2 * f < 2 + 3 * f := by linarith

end Erdos634.ThinHole

#print axioms Erdos634.ThinHole.even_of_odd
#print axioms Erdos634.ThinHole.f_even_of_prime
#print axioms Erdos634.ThinHole.first_four
#print axioms Erdos634.ThinHole.twentythree_outside
#print axioms Erdos634.ThinHole.oneninetyone_small_box
