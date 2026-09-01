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

/-! ## Assembling the set equality (gap (i) named in `PAPER_MAP`'s `thm:lattice` row)

`admissible_iff` and `case_split` give the two admissibility conditions on `w` in terms of the
single parity `u·T` for `w = e₁·u`.  What was still missing — pure bookkeeping, not new arithmetic
content — is packaging that into the actual set equality: the set of admissible `w` (as naturals,
via the two named conditions) equals the multiples of `E`, with `E` read off `T`'s parity. -/

/-- **`w·r/e` as a natural, when `e₁ ∣ w`, equals `u·r₁`.**  Needed to relate the *value* of the
quotient (not just its class mod 2) to `u`, since `admissible_iff` above works entirely in
`ZMod 2`. -/
theorem quot_eq (g e1 r1 u : ℕ) (hg : 0 < g) (he1 : 0 < e1) :
    (e1 * u) * (g * r1) / (g * e1) = u * r1 := by
  have hpos : 0 < e1 * g := Nat.mul_pos he1 hg
  have hnum : (e1 * u) * (g * r1) = (u * r1) * (e1 * g) := by ring
  rw [hnum, show g * e1 = e1 * g by ring, Nat.mul_div_cancel _ hpos]

/-- **The admissible-scale set, as an explicit set equality.**  With `e = g·e₁`, `r = g·r₁`,
`gcd(e₁,r₁) = 1`, and `T = r₁ + d·e₁²·(a+2b) (mod 2)`, the set of positive `w` satisfying both
admissibility clauses is exactly the positive multiples of `E`, where `E = e₁` if `T = 0` and
`E = 2·e₁` if `T ≠ 0`.  This closes gap (i) of `thm:lattice`'s `PAPER_MAP` row: the assembly of
`prop:latticeparam`'s reduction and the parity case split into the actual admissible set. Gap (ii)
— the word "admissible", which quantifies over tilings via `thm:admissible` — is untouched: this
theorem is about the two arithmetic clauses, not about a real tiling. -/
theorem admissible_set_eq (e r d a2b g e1 r1 : ℕ) (hg : 0 < g) (he1pos : 0 < e1)
    (he : e = g * e1) (hr : r = g * r1) (hcop : Nat.Coprime e1 r1) :
    {w : ℕ | 0 < w ∧ e ∣ w * r ∧
      ((w * r / e : ℕ) : ZMod 2) = (d : ZMod 2) * (w : ZMod 2) ^ 2 * (a2b : ZMod 2)}
    = {w : ℕ | ∃ u : ℕ, 0 < u ∧
        w = (if (r1 : ZMod 2) + (d : ZMod 2) * (e1 : ZMod 2) ^ 2 * (a2b : ZMod 2) = 0
             then e1 else 2 * e1) * u} := by
  ext w
  simp only [Set.mem_setOf_eq]
  subst he hr
  constructor
  · rintro ⟨hwpos, hdvd, hpar⟩
    have he1dvd : e1 ∣ w := (dvd_iff_e1_dvd g e1 r1 w hg hcop).mp hdvd
    obtain ⟨u, rfl⟩ := he1dvd
    have hqeq : (e1 * u) * (g * r1) / (g * e1) = u * r1 := quot_eq g e1 r1 u hg he1pos
    rw [hqeq] at hpar
    have hcast : ((u * r1 : ℕ) : ZMod 2) = (u : ZMod 2) * (r1 : ZMod 2) := by push_cast; ring
    rw [hcast] at hpar
    have hcastw : ((e1 * u : ℕ) : ZMod 2) = (e1 : ZMod 2) * (u : ZMod 2) := by push_cast; ring
    rw [hcastw] at hpar
    have hT : (u : ZMod 2) * ((r1 : ZMod 2) + (d : ZMod 2) * (e1 : ZMod 2) ^ 2 * (a2b : ZMod 2))
        = 0 := (parity_iff d e1 a2b u r1).mp hpar
    have hu0 : 0 < u := by
      rcases Nat.eq_zero_or_pos u with rfl | h
      · simp at hwpos
      · exact h
    rcases (case_split (u : ZMod 2)
        ((r1 : ZMod 2) + (d : ZMod 2) * (e1 : ZMod 2) ^ 2 * (a2b : ZMod 2))).mp hT with hT0 | hu2
    · rw [if_pos hT0]; exact ⟨u, hu0, rfl⟩
    · -- `u ≡ 0 (mod 2)` in `ZMod 2` means `u` is even as a natural
      have hueven : 2 ∣ u := (ZMod.natCast_eq_zero_iff u 2).mp hu2
      obtain ⟨u', rfl⟩ := hueven
      -- either value of the `if` is satisfied by `w = e1 * (2 * u')`, since `2u'` is itself
      -- a positive multiple regardless of which branch `E` takes
      by_cases hT0' : (r1 : ZMod 2) + (d : ZMod 2) * (e1 : ZMod 2) ^ 2 * (a2b : ZMod 2) = 0
      · rw [if_pos hT0']; exact ⟨2 * u', by omega, rfl⟩
      · rw [if_neg hT0']; exact ⟨u', by omega, by ring⟩
  · rintro ⟨u, hu0, rfl⟩
    split_ifs with hT0
    · refine ⟨by positivity, (dvd_iff_e1_dvd g e1 r1 (e1 * u) hg hcop).mpr ⟨u, rfl⟩, ?_⟩
      rw [quot_eq g e1 r1 u hg he1pos]
      have hcast : ((u * r1 : ℕ) : ZMod 2) = (u : ZMod 2) * (r1 : ZMod 2) := by push_cast; ring
      have hcastw : ((e1 * u : ℕ) : ZMod 2) = (e1 : ZMod 2) * (u : ZMod 2) := by push_cast; ring
      rw [hcast, hcastw]
      exact (parity_iff d e1 a2b u r1).mpr (by rw [hT0, mul_zero])
    · refine ⟨by positivity,
        (dvd_iff_e1_dvd g e1 r1 (2 * e1 * u) hg hcop).mpr ⟨2 * u, by ring⟩, ?_⟩
      rw [show 2 * e1 * u = e1 * (2 * u) by ring, quot_eq g e1 r1 (2 * u) hg he1pos]
      have h2z : ((2 * u : ℕ) : ZMod 2) = 0 := by
        push_cast
        rw [show (2 : ZMod 2) = 0 from by decide]
        ring
      have hkey := (parity_iff d e1 a2b (2 * u : ℕ) r1).mpr (by rw [h2z, zero_mul])
      push_cast at hkey ⊢
      linear_combination hkey

end Erdos634.SpectrumLattice
