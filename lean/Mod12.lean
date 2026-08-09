-- Mod12.lean — the base-beta candidate primes are exactly the primes congruent to 11 mod 12.
-- This file formalises the forward direction of Theorem (the exceptional set is a congruence class):
-- a prime p > 3 of the form 3f^2 - e^2 with gcd(e,f) = 1 satisfies p = 11 (mod 12).
--
-- That direction is the load-bearing one: it is what makes the class 7 (mod 12) unconditional,
-- since a prime in that class is not a base-beta candidate at all.
--
-- The converse (every prime 11 mod 12 is of that form) uses quadratic reciprocity and the class
-- group of discriminant 12; it is not formalised here and the paper carries it at PROVED.

import Mathlib.Tactic

namespace Erdos634.Mod12

/-- If `e` is odd then `e² ≡ 1 (mod 4)`. -/
theorem sq_odd_mod_four {e : ℕ} (he : e % 2 = 1) : e * e % 4 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, e = 2 * m + 1 := ⟨e / 2, by omega⟩
  have : (2 * m + 1) * (2 * m + 1) = 4 * (m * m + m) + 1 := by ring
  omega

/-- If `e` is even then `4 ∣ e²`. -/
theorem sq_even_mod_four {e : ℕ} (he : e % 2 = 0) : e * e % 4 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, e = 2 * m := ⟨e / 2, by omega⟩
  have : 2 * m * (2 * m) = 4 * (m * m) := by ring
  omega

/-- If `3 ∤ e` then `e² ≡ 1 (mod 3)`. -/
theorem sq_mod_three {e : ℕ} (he : e % 3 ≠ 0) : e * e % 3 = 1 := by
  have h : e % 3 = 1 ∨ e % 3 = 2 := by omega
  obtain ⟨m, hm⟩ : ∃ m, e = 3 * m + e % 3 := ⟨e / 3, by omega⟩
  rcases h with h | h <;> rw [h] at hm <;> subst hm
  · have : (3 * m + 1) * (3 * m + 1) = 3 * (3 * (m * m) + 2 * m) + 1 := by ring
    omega
  · have : (3 * m + 2) * (3 * m + 2) = 3 * (3 * (m * m) + 4 * m + 1) + 1 := by ring
    omega

/-- **The base-`β` candidate primes lie in the class `11 (mod 12)`.**
Let `p > 3` be prime with `p + e² = 3f²` (that is, `p = 3f² − e²`) and `gcd(e,f) = 1`.
Then `p ≡ 11 (mod 12)`.

Proof. Modulo 3: if `3 ∣ e` then `3 ∣ p`, impossible for a prime `p > 3`; so `e² ≡ 1` and
`p ≡ −1 ≡ 2 (mod 3)`. Modulo 4: `e` and `f` are not both even by coprimality, and not both odd,
since then `p ≡ 3 − 1 = 2 (mod 4)` would make `p` an even prime exceeding 3. In either remaining
case `p ≡ 3 (mod 4)`. Combining gives `p ≡ 11 (mod 12)`. -/
theorem base_beta_prime_mod12 {p e f : ℕ} (hp : Nat.Prime p) (hp3 : 3 < p)
    (hco : Nat.Coprime e f) (h : p + e * e = 3 * (f * f)) :
    p % 12 = 11 := by
  -- (1) three does not divide e
  have h3e : e % 3 ≠ 0 := by
    intro h0
    obtain ⟨k, rfl⟩ : ∃ k, e = 3 * k := ⟨e / 3, by omega⟩
    have hdvd : (3 : ℕ) ∣ p := by
      have hexp : 3 * k * (3 * k) = 9 * (k * k) := by ring
      omega
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd)
    omega
  -- (2) p ≡ 2 (mod 3)
  have hp3mod : p % 3 = 2 := by
    have he3 := sq_mod_three h3e
    omega
  -- (3) e and f are not both even
  have hnot2 : ¬ (e % 2 = 0 ∧ f % 2 = 0) := by
    rintro ⟨he, hf⟩
    have h2e : (2 : ℕ) ∣ e := by omega
    have h2f : (2 : ℕ) ∣ f := by omega
    have : (2 : ℕ) ∣ Nat.gcd e f := Nat.dvd_gcd h2e h2f
    rw [hco] at this
    omega
  -- (4) e and f are not both odd
  have hnotodd : ¬ (e % 2 = 1 ∧ f % 2 = 1) := by
    rintro ⟨he, hf⟩
    have h1 := sq_odd_mod_four he
    have h2 := sq_odd_mod_four hf
    -- p ≡ 3·1 − 1 = 2 (mod 4), so p is even
    have hpe : p % 2 = 0 := by omega
    have h2p : (2 : ℕ) ∣ p := by omega
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2p)
    omega
  -- (5) p ≡ 3 (mod 4) in either remaining case
  have hp4mod : p % 4 = 3 := by
    rcases Nat.even_or_odd e with he | he
    · have he0 : e % 2 = 0 := Nat.even_iff.mp he
      have hf1 : f % 2 = 1 := by
        rcases Nat.even_or_odd f with hf | hf
        · exact absurd ⟨he0, Nat.even_iff.mp hf⟩ hnot2
        · exact Nat.odd_iff.mp hf
      have h1 := sq_even_mod_four he0
      have h2 := sq_odd_mod_four hf1
      omega
    · have he1 : e % 2 = 1 := Nat.odd_iff.mp he
      have hf0 : f % 2 = 0 := by
        rcases Nat.even_or_odd f with hf | hf
        · exact Nat.even_iff.mp hf
        · exact absurd ⟨he1, Nat.odd_iff.mp hf⟩ hnotodd
      have h1 := sq_odd_mod_four he1
      have h2 := sq_even_mod_four hf0
      omega
  -- (6) combine
  omega

end Erdos634.Mod12
