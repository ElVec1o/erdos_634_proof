import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# The `(2α,α,2β)` scalene target: an unconditional congruence proof

Erdős #634, Beeson III Theorem 12's arithmetic core.  Room `advance`, Ramanujan seat, 2026-09-06;
verified and formalized here.

## What was already there, and why this is different

`Beeson3NotPrime.fourcomp_not_prime` proves `N = (2f²−e²)(3f²−e²)k²` is never prime.  That is a
**triviality given its hypothesis**: the hypothesis already hands you the factorization.  It is
reached only through Beeson III Theorem 11, whose statement says `ℓ = lcm(a,c)` while its proof uses
`lcm(a,b,c)` — and only `lcm(a,c)` reproduces Beeson's own Figures 12/13/14.  So the existing route
to that shape passes through a garbled recap sentence in Theorem 11's proof.

**Corrected 2026-09-06 by the room's adversarial audit.**  An earlier version of this header said
the existing route "rests on a misprinted theorem".  That inference is **wrong** and is withdrawn.
The misprints are real — `b1206.txt:3514` writes `M = ℓ(s − s² − 2)` with `ℓ = lcm(a,b,c)`, against
the statement's `M = ℓ(2 − s² − s)` with `ℓ = lcm(a,c)` at `:3500`, so that one sentence carries
*two* errors, the `lcm` and a sign flip.  But Theorem 10 (`:3324`, `:3333`) says `lcm(a,c)` in both
its statement and its proof, Theorem 11's *statement* says `lcm(a,c)`, and Theorem 12 uses
`ℓ = lcm(a,c) = ac/g` at `:3586`.  The route Thm 10 → Thm 11 statement → Thm 12 is therefore
internally consistent; the defect is confined to a recap sentence.  The `lcm(a,c)` reading is the
correct one and reproduces Beeson's own Figures 12/13/14 (`N = 77, 442, 1288`, checked).

**The real defect in Theorem 12 is elsewhere, and this file repairs it.**  At `b1206.txt:3563-3572`
the step giving `M ∣ (c−a)(2c+a)` argues "`p ∤ N` since `N` is prime" — a non sequitur: `p` prime and
`N` prime do not give `p ≠ N`.  `FCStep2.mul_eq_prime_mul_sq_of_raw` reaches the same conclusion by
a `gcd(M,R)` extraction that never needs `p ≠ N`.

The tiling equation *before* Theorem 11 is applied is

    N · R² = M² · A · B,     A = 2f² − e²,  B = 3f² − e²,  R = (f−e)(2f+e),

with **no divisibility hypothesis on `M`**.  Standard coprime-factorization (`gcd(A,B) = 1`, and
`v_N` parity for `N` prime) splits this into `(A,B) = (N u², v²)` or `(A,B) = (u², N v²)`.  This
file proves the two congruence obstructions that kill both branches, and they are what make the
argument unconditional:

* `B_never_square`  — `3f² − e² = v²` is impossible for coprime `e, f`  (mod 3).  Kills branch one.
* `A_square_forces` — if `2f² − e² = u²` then `3f² − e² ≡ 2 (mod 4)`.  (It is `≡ 2 (mod 8)` in
  truth; that sharper form is discharged in `FCAudit.A_square_forces_mod8`, not asserted here.)
* `fourcomp_prime_eq_two` — combining, branch two forces `N = 2`.

So no **odd** prime survives, with Theorem 11 nowhere in the chain.

## Scope, stated honestly

Formalized here: steps (4) and (5) of the seat's chain, and their combination — the new content.
**Not formalized here**: steps (1)–(3), the passage from `N·R² = M²·A·B` to the two branches
(`gcd(A,B) = 1` plus `v_N`-parity coprime factorization).  Those are standard but real, and until
they are in Lean this file is the *core* of the argument, not the whole of it.  It is stated below
as `fourcomp_prime_eq_two` with the branch supplied as a hypothesis, so nothing is over-claimed.
-/

namespace Erdos634.FourCompCongruence

private theorem three_zero : (3 : ZMod 3) = 0 := rfl

/-- Coprime integers are not both even. -/
theorem not_both_even {e f : ℤ} (hc : IsCoprime e f) : ¬ ((2 : ℤ) ∣ e ∧ (2 : ℤ) ∣ f) := by
  rintro ⟨he, hf⟩
  obtain ⟨u, v, huv⟩ := hc
  have h2 : (2 : ℤ) ∣ 1 := by
    rw [← huv]; exact dvd_add (Dvd.dvd.mul_left he u) (Dvd.dvd.mul_left hf v)
  omega

/-- `2 ∣ e` is visible in `ZMod 4` as `e ↦ 0` or `e ↦ 2`. -/
theorem even_iff_zmod4 (e : ℤ) : (2 : ℤ) ∣ e ↔ (((e : ZMod 4)) = 0 ∨ ((e : ZMod 4)) = 2) := by
  constructor
  · rintro ⟨k, rfl⟩
    have key : ∀ K : ZMod 4, 2 * K = 0 ∨ 2 * K = 2 := by decide
    have h := key ((k : ZMod 4))
    push_cast
    exact h
  · intro h
    rcases h with h | h
    · have h4 : (4 : ℤ) ∣ e := (ZMod.intCast_zmod_eq_zero_iff_dvd e 4).mp h
      obtain ⟨c, hc⟩ := h4; exact ⟨2 * c, by linarith⟩
    · have h0 : ((e - 2 : ℤ) : ZMod 4) = 0 := by push_cast; rw [h]; ring
      have h4 : (4 : ℤ) ∣ (e - 2) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h0
      obtain ⟨c, hc⟩ := h4; exact ⟨2 * c + 1, by linarith⟩

/-- **Step (4).**  `B = 3f² − e²` is never a perfect square when `gcd(e,f) = 1`.
Mod 3: `v² + e² ≡ 0` forces `3 ∣ v` and `3 ∣ e`, whence `3 ∣ f` — contradicting coprimality. -/
theorem B_never_square {e f v : ℤ} (hc : IsCoprime e f) : 3 * f ^ 2 - e ^ 2 ≠ v ^ 2 := by
  intro h
  have hcast : 3 * ((f : ZMod 3)) ^ 2 - ((e : ZMod 3)) ^ 2 = ((v : ZMod 3)) ^ 2 := by
    have := congrArg (fun z : ℤ => (z : ZMod 3)) h; push_cast at this; exact this
  have h3 : ((v : ZMod 3)) ^ 2 + ((e : ZMod 3)) ^ 2 = 0 := by
    linear_combination -hcast + ((f : ZMod 3)) ^ 2 * three_zero
  have key : ∀ V E : ZMod 3, V ^ 2 + E ^ 2 = 0 → V = 0 ∧ E = 0 := by decide
  obtain ⟨hv0, he0⟩ := key _ _ h3
  have hve : (3 : ℤ) ∣ v := (ZMod.intCast_zmod_eq_zero_iff_dvd v 3).mp hv0
  have hee : (3 : ℤ) ∣ e := (ZMod.intCast_zmod_eq_zero_iff_dvd e 3).mp he0
  obtain ⟨a, ha⟩ := hee
  obtain ⟨b, hb⟩ := hve
  have hf2 : f ^ 2 = 3 * (a ^ 2 + b ^ 2) := by
    rw [ha, hb] at h; nlinarith [h]
  have hff : ((f : ZMod 3)) ^ 2 = 0 := by
    have hc2 : ((f : ZMod 3)) ^ 2 = 3 * (((a : ZMod 3)) ^ 2 + ((b : ZMod 3)) ^ 2) := by
      have := congrArg (fun z : ℤ => (z : ZMod 3)) hf2; push_cast at this; exact this
    rw [hc2, three_zero, zero_mul]
  have keyf : ∀ F : ZMod 3, F ^ 2 = 0 → F = 0 := by decide
  have hfd : (3 : ℤ) ∣ f := (ZMod.intCast_zmod_eq_zero_iff_dvd f 3).mp (keyf _ hff)
  obtain ⟨u, w, huv⟩ := hc
  have hone : (3 : ℤ) ∣ 1 := by
    rw [← huv]
    exact dvd_add (Dvd.dvd.mul_left ⟨a, ha⟩ u) (Dvd.dvd.mul_left hfd w)
  omega

/-- **Step (5).**  If `A = 2f² − e²` is a perfect square and `gcd(e,f) = 1`, then
`B = 3f² − e² ≡ 2 (mod 4)`.  The mixed-parity cases are *vacuous*: they force `u²` to be
`3` or `2` mod `4`. -/
theorem A_square_forces {e f u : ℤ} (hc : IsCoprime e f) (h : 2 * f ^ 2 - e ^ 2 = u ^ 2) :
    (((3 * f ^ 2 - e ^ 2 : ℤ)) : ZMod 4) = 2 := by
  have hne := not_both_even hc
  have hE : ¬ (((e : ZMod 4)) = 0 ∨ ((e : ZMod 4)) = 2) ∨
            ¬ (((f : ZMod 4)) = 0 ∨ ((f : ZMod 4)) = 2) := by
    by_contra hcon
    push_neg at hcon
    exact hne ⟨(even_iff_zmod4 e).mpr hcon.1, (even_iff_zmod4 f).mpr hcon.2⟩
  have h4 : 2 * ((f : ZMod 4)) ^ 2 - ((e : ZMod 4)) ^ 2 = ((u : ZMod 4)) ^ 2 := by
    have := congrArg (fun z : ℤ => (z : ZMod 4)) h; push_cast at this; exact this
  have key : ∀ E F U : ZMod 4,
      2 * F ^ 2 - E ^ 2 = U ^ 2 →
      (¬ (E = 0 ∨ E = 2) ∨ ¬ (F = 0 ∨ F = 2)) →
      3 * F ^ 2 - E ^ 2 = 2 := by decide
  have hres := key _ _ _ h4 hE
  push_cast
  exact hres

/-- **The combination.**  In the surviving branch `B = 3f² − e² = N v²` with `A = 2f² − e²` a
square, `N` prime forces `N = 2`.  Mod `4`: `N v² ≡ 2` has a solution only for `N ≡ 2`. -/
theorem fourcomp_prime_eq_two {e f u v : ℤ} {N : ℕ} (hc : IsCoprime e f) (hN : Nat.Prime N)
    (hA : 2 * f ^ 2 - e ^ 2 = u ^ 2) (hB : 3 * f ^ 2 - e ^ 2 = (N : ℤ) * v ^ 2) : N = 2 := by
  have h2 := A_square_forces hc hA
  rw [hB] at h2
  push_cast at h2
  have key : ∀ Nz Vz : ZMod 4, Nz * Vz ^ 2 = 2 → Nz = 2 := by decide
  have hNz : ((N : ZMod 4)) = 2 := key _ _ h2
  have h0 : (((N : ℤ) - 2 : ℤ) : ZMod 4) = 0 := by push_cast; rw [hNz]; ring
  have hd4 : (4 : ℤ) ∣ ((N : ℤ) - 2) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h0
  obtain ⟨c, hcc⟩ := hd4
  have hd2 : (2 : ℤ) ∣ (N : ℤ) := ⟨2 * c + 1, by linarith⟩
  have hd2n : (2 : ℕ) ∣ N := by exact_mod_cast hd2
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hN).mp hd2n).symm

/-- **No odd prime**, in the form the branch analysis delivers it.  Note the disjunction is
formal only: `FCAudit.hsplit_left_branch_is_empty` proves the LEFT branch is unsatisfiable for every
coprime `e, f` — killing it *is* step (4).  So this is a one-branch theorem wearing a disjunction,
and no witness for the left branch should be sought.  Whichever of the two coprime
splittings holds, `N` prime forces `N = 2`.  Theorem 11 is not used. -/
theorem fourcomp_no_odd_prime {e f : ℤ} {N : ℕ} (hc : IsCoprime e f) (hN : Nat.Prime N)
    (hsplit : (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = (N : ℤ) * u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = v ^ 2) ∨
              (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = (N : ℤ) * v ^ 2)) :
    N = 2 := by
  rcases hsplit with ⟨u, v, _, hv⟩ | ⟨u, v, hu, hv⟩
  · exact absurd hv (B_never_square hc)
  · exact fourcomp_prime_eq_two hc hN hu hv

end Erdos634.FourCompCongruence

#print axioms Erdos634.FourCompCongruence.B_never_square
#print axioms Erdos634.FourCompCongruence.A_square_forces
#print axioms Erdos634.FourCompCongruence.fourcomp_no_odd_prime
