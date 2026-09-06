import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Erdos634.FourCompCongruence

/-!
# `FourCompCongruence` steps (1)–(3): the coprime factorization

Erdős #634, Beeson III Theorem 12's `(2α,α,2β)` branch, continued from
`Erdos634.FourCompCongruence`.  That file formalized steps (4) and (5) — the two congruence
obstructions — and left the passage to the two branches as a hypothesis `hsplit`.  This file
discharges that hypothesis from the equation `A · B = N · w²`.

Throughout, for integers `e, f`,

    A = 2f² − e²,   B = 3f² − e².

## Contents

* `gcd_A_B` — **step (1)**: `IsCoprime A B` whenever `IsCoprime e f`.  Elementary:
  `B − A = f²` and `3A − 2B = −e²`, so any common divisor divides `gcd(e², f²) = 1`.
  Also given in `Int.gcd` form (`gcd_A_B_nat`, `gcd_A_B_int_gcd`).
* `A_pos`, `B_pos` — positivity on the geometric range `0 < e < f`, which is what resolves the
  sign ambiguity in `Int.sq_of_coprime`.
* `coprime_sq_split` — a general helper: a coprime factorization of a square into two positive
  factors is a product of squares.
* `split_of_prime` — **steps (2)–(3), the second half**: from `A · B = N · w²` with `N` prime,
  exactly the disjunction `fourcomp_no_odd_prime` takes as its hypothesis.
* `fourcomp_AB_prime_eq_two` — the chain: `A · B = N · w²`, `N` prime, `0 < e < f` coprime
  ⟹ `N = 2`.  Theorem 11 is nowhere in it.
* `AB_never_square` — a by-product: `A · B` is never a perfect square on the coprime range.

## What is still NOT formalized

The *first* half of step (2): the passage from the raw tiling equation `N · R² = M² · A · B`
(with `R = (f−e)(2f+e)` and **no** divisibility hypothesis on `M`) to `A · B = N · w²`, which is
the `v_N`-parity argument, together with `M ∣ R`.  That remains a paper-level step.  Everything
downstream of `A · B = N · w²` is now Lean.
-/

namespace Erdos634.FCStep1

open Erdos634.FourCompCongruence

/-! ### Step (1): `gcd(A, B) = 1` -/

/-- **Step (1).**  For coprime `e, f`, the two quadratic forms `A = 2f² − e²` and
`B = 3f² − e²` are coprime.

The Bézout certificate is explicit: if `a·e² + b·f² = 1` then, since `e² = 3A − 2B` and
`f² = B − A`, we get `(−3a − b)·A + (2a + b)·B = 1`. -/
theorem gcd_A_B {e f : ℤ} (hc : IsCoprime e f) :
    IsCoprime (2 * f ^ 2 - e ^ 2) (3 * f ^ 2 - e ^ 2) := by
  obtain ⟨a, b, hab⟩ := hc.pow (m := 2) (n := 2)
  exact ⟨-3 * a - b, 2 * a + b, by linear_combination hab⟩

/-- The same statement with the hypothesis phrased as `Int.gcd e f = 1`. -/
theorem gcd_A_B_int_gcd {e f : ℤ} (hc : Int.gcd e f = 1) :
    Int.gcd (2 * f ^ 2 - e ^ 2) (3 * f ^ 2 - e ^ 2) = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp (gcd_A_B (Int.isCoprime_iff_gcd_eq_one.mpr hc))

/-- The same statement for natural-number parameters, as they occur in the base-β family. -/
theorem gcd_A_B_nat {e f : ℕ} (hc : Nat.Coprime e f) :
    Int.gcd (2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2) (3 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2) = 1 :=
  gcd_A_B_int_gcd (by simpa [Int.gcd_natCast_natCast] using hc)

/-! ### Positivity on the geometric range -/

theorem A_pos {e f : ℤ} (he : 0 < e) (hef : e < f) : 0 < 2 * f ^ 2 - e ^ 2 := by nlinarith

theorem B_pos {e f : ℤ} (he : 0 < e) (hef : e < f) : 0 < 3 * f ^ 2 - e ^ 2 := by nlinarith

/-! ### A general coprime-factorization helper -/

/-- If two coprime **positive** integers multiply to a square, each is a square.
This is `Int.sq_of_coprime` with the sign ambiguity resolved by positivity. -/
theorem coprime_sq_split {x y c : ℤ} (h : IsCoprime x y) (hx : 0 < x) (hy : 0 < y)
    (heq : x * y = c ^ 2) : ∃ u v : ℤ, x = u ^ 2 ∧ y = v ^ 2 := by
  obtain ⟨u, hu⟩ := Int.sq_of_isCoprime h heq
  obtain ⟨v, hv⟩ := Int.sq_of_isCoprime h.symm (by rw [mul_comm]; exact heq)
  refine ⟨u, v, ?_, ?_⟩
  · rcases hu with hu | hu
    · exact hu
    · exfalso; linarith [sq_nonneg u]
  · rcases hv with hv | hv
    · exact hv
    · exfalso; linarith [sq_nonneg v]

/-! ### Steps (2)–(3): the split -/

/-- **Steps (2)–(3).**  If `A · B = N · w²` with `N` prime and `0 < e < f` coprime, then the
prime lands wholly in one factor and the other factor is a perfect square.  This is precisely the
disjunction that `FourCompCongruence.fourcomp_no_odd_prime` assumes. -/
theorem split_of_prime {e f w : ℤ} {N : ℕ} (hc : IsCoprime e f) (he : 0 < e) (hef : e < f)
    (hN : Nat.Prime N)
    (heq : (2 * f ^ 2 - e ^ 2) * (3 * f ^ 2 - e ^ 2) = (N : ℤ) * w ^ 2) :
    (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = (N : ℤ) * u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = v ^ 2) ∨
    (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = (N : ℤ) * v ^ 2) := by
  set A : ℤ := 2 * f ^ 2 - e ^ 2 with hAdef
  set B : ℤ := 3 * f ^ 2 - e ^ 2 with hBdef
  have hA : 0 < A := A_pos he hef
  have hB : 0 < B := B_pos he hef
  have hcop : IsCoprime A B := gcd_A_B hc
  have hNprime : Prime (N : ℤ) := Nat.prime_iff_prime_int.mp hN
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN.pos
  have hNne : (N : ℤ) ≠ 0 := ne_of_gt hNpos
  have hdvd : (N : ℤ) ∣ A * B := ⟨w ^ 2, heq⟩
  rcases hNprime.dvd_mul.mp hdvd with hdA | hdB
  · -- `N ∣ A`
    obtain ⟨A', hA'⟩ := hdA
    have hA'pos : 0 < A' := by nlinarith
    have hprod : A' * B = w ^ 2 := by
      have : (N : ℤ) * (A' * B) = (N : ℤ) * w ^ 2 := by rw [← heq, hA']; ring
      exact mul_left_cancel₀ hNne this
    have hcop' : IsCoprime A' B :=
      IsCoprime.of_isCoprime_of_dvd_left hcop ⟨(N : ℤ), by rw [hA']; ring⟩
    obtain ⟨u, v, hu, hv⟩ := coprime_sq_split hcop' hA'pos hB hprod
    exact Or.inl ⟨u, v, by rw [hA', hu], hv⟩
  · -- `N ∣ B`
    obtain ⟨B', hB'⟩ := hdB
    have hB'pos : 0 < B' := by nlinarith
    have hprod : A * B' = w ^ 2 := by
      have : (N : ℤ) * (A * B') = (N : ℤ) * w ^ 2 := by rw [← heq, hB']; ring
      exact mul_left_cancel₀ hNne this
    have hcop' : IsCoprime A B' :=
      IsCoprime.of_isCoprime_of_dvd_right hcop ⟨(N : ℤ), by rw [hB']; ring⟩
    obtain ⟨u, v, hu, hv⟩ := coprime_sq_split hcop' hA hB'pos hprod
    exact Or.inr ⟨u, v, hu, by rw [hB', hv]⟩

/-! ### The chain, and a by-product -/

/-- **The chain.**  `A · B = N · w²` with `N` prime and `0 < e < f` coprime forces `N = 2`.
Beeson III Theorem 11 is used nowhere. -/
theorem fourcomp_AB_prime_eq_two {e f w : ℤ} {N : ℕ} (hc : IsCoprime e f) (he : 0 < e)
    (hef : e < f) (hN : Nat.Prime N)
    (heq : (2 * f ^ 2 - e ^ 2) * (3 * f ^ 2 - e ^ 2) = (N : ℤ) * w ^ 2) : N = 2 :=
  fourcomp_no_odd_prime hc hN (split_of_prime hc he hef hN heq)

/-- By-product of step (1) plus `B_never_square`: the product `A · B` is never a perfect
square on the coprime range `0 < e < f`. -/
theorem AB_never_square {e f c : ℤ} (hc : IsCoprime e f) (he : 0 < e) (hef : e < f) :
    (2 * f ^ 2 - e ^ 2) * (3 * f ^ 2 - e ^ 2) ≠ c ^ 2 := by
  intro heq
  obtain ⟨u, v, _, hv⟩ :=
    coprime_sq_split (gcd_A_B hc) (A_pos he hef) (B_pos he hef) heq
  exact B_never_square hc hv

/-! ### Non-vacuity witnesses

Every hypothesis above is satisfiable, and the conclusions are non-trivial statements. -/

/-- `e = 1, f = 2`: `A = 7`, `B = 11`, and `gcd_A_B` really does assert `IsCoprime 7 11`. -/
example : IsCoprime (7 : ℤ) 11 := by
  have h := gcd_A_B (e := 1) (f := 2) isCoprime_one_left
  have e1 : 2 * (2 : ℤ) ^ 2 - 1 ^ 2 = 7 := by norm_num
  have e2 : 3 * (2 : ℤ) ^ 2 - 1 ^ 2 = 11 := by norm_num
  rwa [e1, e2] at h

/-- The `Int.gcd` form at `e = 1, f = 2`. -/
example : Int.gcd (7 : ℤ) 11 = 1 := by
  have h := gcd_A_B_int_gcd (e := 1) (f := 2) (by norm_num)
  have e1 : 2 * (2 : ℤ) ^ 2 - 1 ^ 2 = 7 := by norm_num
  have e2 : 3 * (2 : ℤ) ^ 2 - 1 ^ 2 = 11 := by norm_num
  rwa [e1, e2] at h

/-- `e = 3, f = 5`: `A = 41`, `B = 66`, coprime. -/
example : IsCoprime (41 : ℤ) 66 := by
  have hco : IsCoprime (3 : ℤ) 5 := Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)
  have h := gcd_A_B hco
  have e1 : 2 * (5 : ℤ) ^ 2 - 3 ^ 2 = 41 := by norm_num
  have e2 : 3 * (5 : ℤ) ^ 2 - 3 ^ 2 = 66 := by norm_num
  rw [e1, e2] at h
  exact h

/-- `split_of_prime` is non-vacuous: at `e = 647, f = 2993` one has
`A = 4183²` and `B = 2 · 3637²`, so `A · B = 2 · (4183 · 3637)²` with `N = 2` prime, and the
theorem's right branch is realized.  (This is the unique prime hit found by the Rust sweep over
all 2 735 387 coprime pairs with `0 < e < f < 3000`.) -/
example : (2 * (2993 : ℤ) ^ 2 - 647 ^ 2) * (3 * (2993 : ℤ) ^ 2 - 647 ^ 2)
    = (2 : ℤ) * (4183 * 3637) ^ 2 := by norm_num

/-- …and the same witness satisfies the coprimality and range hypotheses, so
`fourcomp_AB_prime_eq_two` is applicable there and returns `N = 2`. -/
example : (2 : ℕ) = 2 :=
  fourcomp_AB_prime_eq_two (e := 647) (f := 2993) (w := 4183 * 3637) (N := 2)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)) (by norm_num) (by norm_num)
    Nat.prime_two (by norm_num)

end Erdos634.FCStep1

#print axioms Erdos634.FCStep1.gcd_A_B
#print axioms Erdos634.FCStep1.gcd_A_B_int_gcd
#print axioms Erdos634.FCStep1.gcd_A_B_nat
#print axioms Erdos634.FCStep1.coprime_sq_split
#print axioms Erdos634.FCStep1.split_of_prime
#print axioms Erdos634.FCStep1.fourcomp_AB_prime_eq_two
#print axioms Erdos634.FCStep1.AB_never_square
