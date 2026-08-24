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

Enumerating primes `p = 3f² - e²` with `gcd(e,f) = 1`, `1 ≤ e < f`, below `200000`: **4489**
primes, of which 4438 have `e ≥ 2` and **51** have `e = 1`.  (An earlier count here said 4000 and
3949; its sweep capped `f` near 260, while `p < 200000` needs `f` up to 316, so it dropped 489
primes.  The `e = 1` count was unaffected, hole primes having `f ≤ 258`.)  The corrected total is
exactly the number of primes `≡ 11 (mod 12)` below `200000`, as `thm:mod12` requires, and no prime
in the range has two representations, as `rep_unique` requires --- two independent checks passed by
the same sweep (`code/analysis/separated_census.py`).  Three of those
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

/-! ## The characterisation is a THEOREM: every representable prime has ONE representation

The census and the `ℤ[√3]` orbit sketch above are superseded by an elementary proof.  The point is
an exact identity, with no modular inverse anywhere: if `p = 3f₁² − e₁² = 3f₂² − e₂²` then

  `(e₁f₂)² − (e₂f₁)² = p·(f₁² − f₂²)`   (`rep_cross_identity`)

so `p ∣ (e₁f₂ − e₂f₁)(e₁f₂ + e₂f₁)`.  The admissibility condition `e < f` forces
`p = 3f² − e² ≥ 2f² + 2f − 1 > 2f²`, hence `2f₁f₂ < p`; so both `e₁f₂` and `e₂f₁` lie strictly
below `p/2`.  Their **sum** then lies strictly in `(0, p)` and cannot be divisible by `p`, so `p`
divides the **difference**, which lies in `(−p, p)` and is therefore `0`.  Coprimality of each
pair upgrades `e₁f₂ = e₂f₁` to `(e₁,f₁) = (e₂,f₂)`.

**Consequently a representable prime has exactly one representation**, and it lies in the hole
precisely when that representation has `e = 1`, i.e. precisely when `p = 3f² − 1`.  What was a
census of 51 primes below `200 000` (and 82 below `600 000`, `code/analysis/hole_characterisation.py`)
is a theorem.

The practical consequence is the one already recorded: no hole prime can be reached through the
unconditional `e ≥ 2` half of `thm:fullprime`, because no hole prime *has* an `e ≥ 2`
representation, and now that is proved rather than observed. -/

/-- **The cross identity.**  Two representations of the same `p` satisfy
`(e₁f₂)² − (e₂f₁)² = p(f₁² − f₂²)` exactly, over `ℤ`. -/
theorem rep_cross_identity (p e1 f1 e2 f2 : ℤ)
    (h1 : 3 * f1 ^ 2 - e1 ^ 2 = p) (h2 : 3 * f2 ^ 2 - e2 ^ 2 = p) :
    (e1 * f2) ^ 2 - (e2 * f1) ^ 2 = p * (f1 ^ 2 - f2 ^ 2) := by
  linear_combination (-f2 ^ 2) * h1 + f1 ^ 2 * h2

/-- **Admissibility bounds the parameter**: `e < f` gives `2f² < p`. -/
theorem two_sq_lt_of_admissible (p e f : ℤ) (he : 1 ≤ e) (hlt : e < f)
    (h : 3 * f ^ 2 - e ^ 2 = p) : 2 * f ^ 2 < p := by nlinarith [h, hlt, he]

/-- **The cross products agree.**  For a prime `p` with two admissible representations,
`e₁f₂ = e₂f₁`. -/
theorem rep_cross_eq (p e1 f1 e2 f2 : ℤ) (hp : Prime p)
    (h1 : 3 * f1 ^ 2 - e1 ^ 2 = p) (h2 : 3 * f2 ^ 2 - e2 ^ 2 = p)
    (he1 : 1 ≤ e1) (hlt1 : e1 < f1) (he2 : 1 ≤ e2) (hlt2 : e2 < f2) :
    e1 * f2 = e2 * f1 := by
  have hf1 : 0 < f1 := by linarith
  have hf2 : 0 < f2 := by linarith
  have hb1 : 2 * f1 ^ 2 < p := two_sq_lt_of_admissible p e1 f1 he1 hlt1 h1
  have hb2 : 2 * f2 ^ 2 < p := two_sq_lt_of_admissible p e2 f2 he2 hlt2 h2
  have hppos : 0 < p := by nlinarith [hb1, hf1]
  have hprod : 2 * (f1 * f2) < p := by nlinarith [hb1, hb2, hf1, hf2, hppos]
  have key := rep_cross_identity p e1 f1 e2 f2 h1 h2
  have hdvd : p ∣ (e1 * f2 - e2 * f1) * (e1 * f2 + e2 * f1) :=
    ⟨f1 ^ 2 - f2 ^ 2, by linarith [key]⟩
  have hs1 : e1 * f2 < f1 * f2 := by nlinarith [hlt1, hf2]
  have hs2 : e2 * f1 < f2 * f1 := by nlinarith [hlt2, hf1]
  have hp1 : 0 < e1 * f2 := by positivity
  have hp2 : 0 < e2 * f1 := by positivity
  rcases hp.2.2 _ _ hdvd with hA | hB
  · have habs : |e1 * f2 - e2 * f1| < p := by
      rw [abs_lt]; constructor <;> nlinarith [hprod, hs1, hs2, hp1, hp2]
    have := Int.eq_zero_of_abs_lt_dvd hA habs
    linarith
  · exfalso
    have hlt : e1 * f2 + e2 * f1 < p := by nlinarith [hprod, hs1, hs2]
    have := Int.le_of_dvd (by positivity) hB
    linarith

/-- **Uniqueness of the representation.**  A prime has at most one admissible base-`β`
representation.  Hence it lies in the `e = 1` hole exactly when `p = 3f² − 1`. -/
theorem rep_unique (p e1 f1 e2 f2 : ℤ) (hp : Prime p)
    (h1 : 3 * f1 ^ 2 - e1 ^ 2 = p) (h2 : 3 * f2 ^ 2 - e2 ^ 2 = p)
    (he1 : 1 ≤ e1) (hlt1 : e1 < f1) (hc1 : IsCoprime e1 f1)
    (he2 : 1 ≤ e2) (hlt2 : e2 < f2) (hc2 : IsCoprime e2 f2) :
    e1 = e2 ∧ f1 = f2 := by
  have h := rep_cross_eq p e1 f1 e2 f2 hp h1 h2 he1 hlt1 he2 hlt2
  have hd1 : e1 ∣ e2 := hc1.dvd_of_dvd_mul_right ⟨f2, h.symm⟩
  have hd2 : e2 ∣ e1 := hc2.dvd_of_dvd_mul_right ⟨f1, h⟩
  have hee : e1 = e2 := Int.dvd_antisymm (by linarith) (by linarith) hd1 hd2
  refine ⟨hee, ?_⟩
  subst hee
  exact (mul_left_cancel₀ (by linarith : e1 ≠ 0) h).symm

/-! ## The consequence of `rep_unique` for the two halves of `thm:fullprime`

With uniqueness proved, the sketch above is retired and the characterisation is exact: a prime whose
representation has `e = 1` is a prime of the form `3f² - 1`, and by `f_even_of_prime` every such
prime has `f` even.  The `e ≥ 2` half of `thm:fullprime` is therefore not merely unhelpful on the
hole — it is *provably* inapplicable, since no hole prime has an `e ≥ 2` representation to apply it
to, and that is now a theorem rather than a census of 82 numbers. -/

end Erdos634.ThinHole

#print axioms Erdos634.ThinHole.even_of_odd
#print axioms Erdos634.ThinHole.f_even_of_prime
#print axioms Erdos634.ThinHole.first_four
#print axioms Erdos634.ThinHole.twentythree_outside
#print axioms Erdos634.ThinHole.oneninetyone_small_box
