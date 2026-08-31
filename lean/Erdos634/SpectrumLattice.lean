import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# The spectrum lattice: which scales are admissible

`thm:admissible` leaves the admissible counts of the base-`α` isosceles target described by two
arithmetic conditions on the scale parameter `w`, with `r = c - a - b` and `N = d·w²·(a+2b)`:

  `e ∣ w·r`   and   `w·r/e ≡ N (mod 2)`.

`thm:lattice` asserts the `w` satisfying both are exactly the multiples of `E`, where
`g = gcd(e,r)`, `e₁ = e/g`, `T = r/g + d·e₁²·(a+2b) (mod 2)`, and `E = e₁` for `T` even, `2e₁` for
`T` odd.  PAPER_MAP recorded the blocker as "the general statement needs the `d`, `e₁`, `r`
normalisation formalized and the parity case split, which is arithmetic and simply not done".

Both steps are here.  The normalisation is taken as hypotheses — `e = g·e₁`, `r = g·r₁` with
`e₁, r₁` coprime — which is what `g = gcd(e,r)` provides and avoids truncated division; and the
quotient `w·r/e` is likewise given by the equation `e·q = w·r` rather than by `/`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SpectrumLattice

/-- **Step 1: the divisibility clause is exactly `e₁ ∣ w`.** -/
theorem dvd_iff_e1_dvd (g e1 r1 w : ℕ) (hg : 0 < g) (hcop : Nat.Coprime e1 r1) :
    (g * e1) ∣ w * (g * r1) ↔ e1 ∣ w := by
  constructor
  · intro h
    have h2 : e1 ∣ w * r1 := by
      rcases h with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have : g * (w * r1) = g * (e1 * k) := by rw [← Nat.mul_left_cancel_iff hg] at hk ⊢ <;> linarith [hk, hk.symm] 
      exact Nat.eq_of_mul_eq_mul_left hg this
    exact hcop.dvd_of_dvd_mul_right h2
  · rintro ⟨k, rfl⟩; exact ⟨k * r1, by ring⟩

/-- In `ZMod 2` every element is its own square. -/
theorem sq_self (x : ZMod 2) : x ^ 2 = x := by revert x; decide +kernel

/-- **Step 2: the parity clause is exactly `u·T ≡ 0 (mod 2)`,** with `T = r₁ + d·e₁²·(a+2b)`.
Writing `w = e₁·u`, the quotient `w·r/e` is `u·r₁`, and `u² ≡ u` collapses `N` to `u·d·e₁²·(a+2b)`. -/
theorem parity_iff (d e1 a2b u r1 : ZMod 2) :
    u * r1 = d * (e1 * u) ^ 2 * a2b ↔ u * (r1 + d * e1 ^ 2 * a2b) = 0 := by
  revert d e1 a2b u r1; decide +kernel

/-- **`thm:lattice`'s arithmetic content.**  For `w = e₁·u` with the normalisation `e = g·e₁`,
`r = g·r₁`, `gcd(e₁,r₁) = 1`, the two admissibility conditions hold exactly when `u·T ≡ 0 (mod 2)`.
Hence every `u` works when `T` is even, and only even `u` when `T` is odd — that is, `w` ranges over
the multiples of `e₁` in the first case and of `2e₁` in the second. -/
theorem admissible_iff (d g e1 r1 a2b u : ℕ) (hg : 0 < g) (hcop : Nat.Coprime e1 r1) :
    ((g * e1) ∣ (e1 * u) * (g * r1))
      ∧ ((u * r1 : ZMod 2) = (d : ZMod 2) * ((e1 : ZMod 2) * (u : ZMod 2)) ^ 2 * (a2b : ZMod 2))
    ↔ (u : ZMod 2) * ((r1 : ZMod 2) + (d : ZMod 2) * (e1 : ZMod 2) ^ 2 * (a2b : ZMod 2)) = 0 := by
  constructor
  · rintro ⟨-, h2⟩; exact (parity_iff _ _ _ _ _).mp h2
  · intro h
    exact ⟨(dvd_iff_e1_dvd g e1 r1 (e1 * u) hg hcop).mpr ⟨u, rfl⟩,
      (parity_iff _ _ _ _ _).mpr h⟩

/-- **The case split.**  `u·T = 0` in `ZMod 2` says `T = 0`, or `u` is even. -/
theorem case_split (u T : ZMod 2) : u * T = 0 ↔ (T = 0 ∨ u = 0) := by
  revert u T; decide +kernel

end Erdos634.SpectrumLattice
