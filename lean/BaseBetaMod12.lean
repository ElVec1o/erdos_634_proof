import Mathlib.Tactic

/-!
# The base-`β` exceptional set is a congruence class

Erdős #634. The main theorem excludes primes `N ≡ 3 (mod 4)`, `N > 3`, **except** the base-`β`
candidates `N = 3f² − e²` (`gcd(e,f) = 1`, `1 ≤ e < f`). Stated that way the exception is a
Diophantine condition and it is not obvious which primes it catches.

It is a single congruence class. Every count formula in this problem is a value of a binary quadratic
form — `x²+y²` (disc `−4`) for the commensurable branch, `x²+xy+y²` (disc `−3`) for the `2π/3` tiles,
and `3x²−y²` (disc `12`) for the base-`β` branch — and for the indefinite form `3x²−y²` the
represented primes form one class modulo the discriminant:

* `basebeta_prime_mod_twelve` (proved here): if `p` is a prime `> 3` with `p + e² = 3f²` and
  `gcd(e,f) = 1`, then `p ≡ 11 (mod 12)`.
* The converse also holds — every prime `≡ 11 (mod 12)` is `3f² − e²` — by the classical theory of
  discriminant `12`: for `p ≡ 3 (mod 4)` and `p ≡ 2 (mod 3)`, quadratic reciprocity gives `(3/p) = 1`,
  so `p` splits in `ℚ(√3)`; the narrow class group has order `2`, the two classes being `x²−3y²`
  (which forces `p ≡ 1 mod 3`) and `3y²−x²` (which forces `p ≡ 2 mod 3`), so `p` lies in the second.
  That direction is not needed for the main theorem and is not formalized here. Verified
  computationally for all `109` primes `≡ 11 (mod 12)` below `3000`, with no exception in either
  direction.

**Consequence.** A prime `p > 3` with `p ≡ 3 (mod 4)` satisfies `p ≡ 7` or `p ≡ 11 (mod 12)` (the
class `3 mod 12` forces `3 ∣ p`). The exception is exactly the class `11`, so the main theorem is
*unconditional* on the class `7 (mod 12)` — half of all primes `≡ 3 (mod 4)` by Dirichlet — and the
whole open problem is the class `11 (mod 12)`. In particular `19 ≡ 7 (mod 12)`, which is why the
headline value is unaffected by the exception.

Axiom-clean.
-/

namespace Erdos634.BaseBetaMod12

/-- Squares of numbers prime to `3` are `≡ 1 (mod 3)`. -/
theorem sq_mod_three (a : ℕ) (h : a % 3 ≠ 0) : (a * a) % 3 = 1 := by
  have h1 : a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases h1 with h1 | h1 <;> rw [Nat.mul_mod, h1]

/-- Odd squares are `≡ 1 (mod 4)`. -/
theorem sq_mod_four_odd (a : ℕ) (h : a % 2 = 1) : (a * a) % 4 = 1 := by
  have h1 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  rcases h1 with h1 | h1 <;> rw [Nat.mul_mod, h1]

/-- Even squares are `≡ 0 (mod 4)`. -/
theorem sq_mod_four_even (a : ℕ) (h : a % 2 = 0) : (a * a) % 4 = 0 := by
  have h1 : a % 4 = 0 ∨ a % 4 = 2 := by omega
  rcases h1 with h1 | h1 <;> rw [Nat.mul_mod, h1]

/-- **The base-`β` prime candidates lie in one class mod 12.**  If `p` is a prime `> 3` with
`p + e² = 3f²` and `gcd(e,f) = 1`, then `p ≡ 11 (mod 12)`.

Two separate congruences, then CRT.  *Mod 3*: `3 ∤ e` (else `3 ∣ p`), so `e² ≡ 1` and `p ≡ −1 ≡ 2`.
*Mod 4*: `e` and `f` are not both even (coprimality) and not both odd (else `p ≡ 3−1 = 2 (mod 4)`,
making the prime `p > 3` even); in either remaining case `p ≡ 3 (mod 4)`. -/
theorem basebeta_prime_mod_twelve (p e f : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (hcop : Nat.Coprime e f) (heq : p + e ^ 2 = 3 * f ^ 2) :
    p % 12 = 11 := by
  have hee : p + e * e = 3 * (f * f) := by rw [pow_two, pow_two] at heq; exact heq
  -- `p` is odd
  have hodd : p % 2 = 1 := by
    rcases Nat.even_or_odd p with hev | hod
    · exfalso
      rcases (hp.eq_one_or_self_of_dvd 2 hev.two_dvd) with h | h <;> omega
    · exact Nat.odd_iff.mp hod
  -- `3 ∤ e`, else `3 ∣ p`
  have he3 : e % 3 ≠ 0 := by
    intro h
    have h3e : 3 ∣ e := Nat.dvd_of_mod_eq_zero h
    have h3p : 3 ∣ p := by
      have hd : (3 : ℕ) ∣ p + e * e := hee ▸ ⟨f * f, rfl⟩
      have he2 : (3 : ℕ) ∣ e * e := h3e.mul_right e
      exact (Nat.dvd_add_right he2).mp (by rwa [Nat.add_comm] at hd)
    rcases (hp.eq_one_or_self_of_dvd 3 h3p) with h | h <;> omega
  -- (i) `p ≡ 2 (mod 3)`
  have hm3 : p % 3 = 2 := by
    have h0 : (p + e * e) % 3 = 0 := by rw [hee]; simp [Nat.mul_mod_right]
    have h1 : (e * e) % 3 = 1 := sq_mod_three e he3
    omega
  -- (ii) `p ≡ 3 (mod 4)`
  have hm4 : p % 4 = 3 := by
    have hnotboth : ¬ (e % 2 = 0 ∧ f % 2 = 0) := by
      rintro ⟨h1, h2⟩
      have : (2 : ℕ) ∣ Nat.gcd e f := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1)
        (Nat.dvd_of_mod_eq_zero h2)
      rw [hcop] at this
      omega
    have heq4 : (p + e * e) % 4 = (3 * (f * f)) % 4 := by rw [hee]
    rcases Nat.even_or_odd e with hE | hE <;> rcases Nat.even_or_odd f with hF | hF
    · exact absurd ⟨Nat.even_iff.mp hE, Nat.even_iff.mp hF⟩ hnotboth
    · -- `e` even, `f` odd : `p ≡ 3·1 − 0 = 3`
      have h1 : (e * e) % 4 = 0 := sq_mod_four_even e (Nat.even_iff.mp hE)
      have h2 : (f * f) % 4 = 1 := sq_mod_four_odd f (Nat.odd_iff.mp hF)
      omega
    · -- `e` odd, `f` even : `p ≡ 0 − 1 = 3`
      have h1 : (e * e) % 4 = 1 := sq_mod_four_odd e (Nat.odd_iff.mp hE)
      have h2 : (f * f) % 4 = 0 := sq_mod_four_even f (Nat.even_iff.mp hF)
      omega
    · -- both odd : `p ≡ 2 (mod 4)`, contradicting `p` odd
      exfalso
      have h1 : (e * e) % 4 = 1 := sq_mod_four_odd e (Nat.odd_iff.mp hE)
      have h2 : (f * f) % 4 = 1 := sq_mod_four_odd f (Nat.odd_iff.mp hF)
      omega
  -- CRT
  omega

/-- **Restatement.**  A prime `p > 3` that is not `≡ 11 (mod 12)` is not a base-`β` candidate.  This
is the form in which the main theorem's exception is discharged: the exception is a single congruence
class, not a Diophantine condition. -/
theorem not_basebeta_of_mod_twelve_ne (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hne : p % 12 ≠ 11) :
    ¬ ∃ e f : ℕ, Nat.Coprime e f ∧ p + e ^ 2 = 3 * f ^ 2 := by
  rintro ⟨e, f, hcop, heq⟩
  exact hne (basebeta_prime_mod_twelve p e f hp hp3 hcop heq)

end Erdos634.BaseBetaMod12

#print axioms Erdos634.BaseBetaMod12.sq_mod_three
#print axioms Erdos634.BaseBetaMod12.sq_mod_four_odd
#print axioms Erdos634.BaseBetaMod12.sq_mod_four_even
#print axioms Erdos634.BaseBetaMod12.basebeta_prime_mod_twelve
#print axioms Erdos634.BaseBetaMod12.not_basebeta_of_mod_twelve_ne
