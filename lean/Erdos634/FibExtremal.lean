import Mathlib

/-!
# Fibonacci families are the extremal ones

Erdős #634, main paper `thm:fib`.  With `M = f + e` and `N₀ = 3f² - e²`:

* `M² - N₀ = -2(f² - ef - e²)` — an identity;
* `f² - ef - e² ≠ 0` when `gcd(e,f) = 1` and `1 ≤ e < f`, so `|M² - N₀| ≥ 2`;
* equality iff `f² - ef - e² = ±1`;
* consecutive Fibonacci numbers satisfy that, by the Cassini-style identity proved here;
* and then `N₀ = M² - 2(-1)^…`, the counts being a Fibonacci square displaced by `2`.

What is *not* here is the converse of the fourth item — that `|f² - ef - e²| = 1` forces `(e,f)`
consecutive Fibonacci.  It needs the descent `(e, f) ↦ (f - e, e)`, which is a separate induction.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.FibExtremal

/-- **The identity.** -/
theorem sq_sub (e f : ℤ) : (f + e) ^ 2 - (3 * f ^ 2 - e ^ 2) = -2 * (f ^ 2 - e * f - e ^ 2) := by
  ring

/-- **The form is nonzero** for coprime `1 ≤ e < f`: `e² = f(f - e)` would make `f` a unit. -/
theorem form_ne_zero (e f : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f) :
    f ^ 2 - e * f - e ^ 2 ≠ 0 := by
  intro h
  have hdvd : f ∣ e ^ 2 := ⟨f - e, by linarith [h]⟩
  have hu : IsUnit f := (hcop.symm.pow_right (n := 2)).isUnit_of_dvd' dvd_rfl hdvd
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega

/-- **The gap is at least `2`.** -/
theorem two_le_gap (e f : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f) :
    2 ≤ |(f + e) ^ 2 - (3 * f ^ 2 - e ^ 2)| := by
  have hne := form_ne_zero e f he hef hcop
  have h1 : 1 ≤ |f ^ 2 - e * f - e ^ 2| := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  rw [sq_sub, abs_mul]
  simp only [abs_neg, abs_two]
  linarith

/-- **Equality holds exactly at `±1`.** -/
theorem gap_eq_two_iff (e f : ℤ) :
    |(f + e) ^ 2 - (3 * f ^ 2 - e ^ 2)| = 2 ↔ |f ^ 2 - e * f - e ^ 2| = 1 := by
  rw [sq_sub, abs_mul]
  simp only [abs_neg, abs_two]
  constructor <;> intro h <;> omega

/-- **Cassini, in the form the theorem needs.**  For consecutive Fibonacci numbers,
`F(n+1)² - F(n)F(n+1) - F(n)² = (-1)ⁿ`. -/
theorem fib_form (n : ℕ) :
    ((Nat.fib (n + 1) : ℤ)) ^ 2 - (Nat.fib n : ℤ) * (Nat.fib (n + 1) : ℤ)
      - (Nat.fib n : ℤ) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hf : (Nat.fib (m + 2) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
      rw [Nat.fib_add_two]; push_cast; ring
    have hpow : ((-1 : ℤ)) ^ (m + 1) = -((-1 : ℤ)) ^ m := by ring
    rw [hf, hpow]
    linarith [ih]

/-- **Consecutive Fibonacci numbers are extremal.** -/
theorem fib_gap (n : ℕ) :
    |((Nat.fib (n + 1) : ℤ) + (Nat.fib n : ℤ)) ^ 2
      - (3 * (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) ^ 2)| = 2 := by
  rw [gap_eq_two_iff, fib_form n]
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow]; norm_num
  · rw [h.neg_one_pow]; norm_num

/-- **The count is a Fibonacci square displaced by `2`.**  `M = F(n+2)` and
`N₀ = M² + 2(-1)ⁿ`. -/
theorem fib_count (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) + (Nat.fib n : ℤ) = (Nat.fib (n + 2) : ℤ) ∧
      3 * (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) ^ 2
        = (Nat.fib (n + 2) : ℤ) ^ 2 + 2 * (-1) ^ n := by
  have hf : (Nat.fib (n + 2) : ℤ) = (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
    rw [Nat.fib_add_two]; push_cast; ring
  refine ⟨by rw [hf]; ring, ?_⟩
  rw [hf]
  linarith [fib_form n]

/-! ## The descent: extremal pairs are consecutive Fibonacci

The converse.  If `f ≥ 2e` the form is at least `e²`, so `e = 1` and then `f = 2`.  Otherwise
`(e, f) ↦ (f - e, e)` lowers the larger entry while negating the form, and the induction closes. -/

/-- The form negates under the descent `(e, f) ↦ (f - e, e)`. -/
theorem form_descent (e f : ℤ) :
    e ^ 2 - (f - e) * e - (f - e) ^ 2 = -(f ^ 2 - e * f - e ^ 2) := by ring

/-- **Extremal pairs are consecutive Fibonacci numbers.** -/
theorem fib_of_gap : ∀ f : ℕ, ∀ e : ℕ, 1 ≤ e → e < f → Nat.Coprime e f →
    |(f : ℤ) ^ 2 - (e : ℤ) * (f : ℤ) - (e : ℤ) ^ 2| = 1 →
    ∃ n, e = Nat.fib (n + 1) ∧ f = Nat.fib (n + 2) := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro e he hef hcop habs
    rcases Nat.lt_or_ge f (2 * e) with hlt | hge
    · -- `f < 2e`: descend to `(f - e, e)`
      have hfe1 : 1 ≤ f - e := by omega
      have hlt' : f - e < e := by omega
      have hcop' : Nat.Coprime (f - e) e := by
        unfold Nat.Coprime
        rw [Nat.gcd_sub_self_left (le_of_lt hef)]
        exact Nat.Coprime.gcd_eq_one (hcop.symm)
      have hcast : ((f - e : ℕ) : ℤ) = (f : ℤ) - (e : ℤ) :=
        Nat.cast_sub (le_of_lt hef)
      have habs' : |(e : ℤ) ^ 2 - ((f - e : ℕ) : ℤ) * (e : ℤ) - ((f - e : ℕ) : ℤ) ^ 2| = 1 := by
        rw [hcast, form_descent, abs_neg]
        exact habs
      obtain ⟨n, hn1, hn2⟩ := ih e hef (f - e) hfe1 hlt' hcop' habs'
      refine ⟨n + 1, hn2, ?_⟩
      have hsplit : f = (f - e) + e := by omega
      rw [hsplit, hn1, hn2]
      exact (Nat.fib_add_two (n := n + 1)).symm

    · -- `f ≥ 2e`: the form is at least `e²`, forcing `e = 1` and then `f = 2`
      have hE : (1:ℤ) ≤ (e:ℤ) := by exact_mod_cast he
      have hF : (2:ℤ) * (e:ℤ) ≤ (f:ℤ) := by exact_mod_cast hge
      have hform : (e:ℤ) ^ 2 ≤ (f : ℤ) ^ 2 - (e : ℤ) * (f : ℤ) - (e : ℤ) ^ 2 := by nlinarith
      have hpos : 0 < (f : ℤ) ^ 2 - (e : ℤ) * (f : ℤ) - (e : ℤ) ^ 2 := by nlinarith
      rw [abs_of_pos hpos] at habs
      have he1 : (e : ℤ) = 1 := by nlinarith
      have hfe : (f : ℤ) = 2 := by
        rw [he1] at habs
        have h2 : ((f:ℤ) - 2) * ((f:ℤ) + 1) = 0 := by linarith [habs]
        rcases mul_eq_zero.mp h2 with h | h
        · linarith
        · have : (0:ℤ) ≤ (f:ℤ) := by positivity
          linarith
      refine ⟨1, ?_, ?_⟩
      · have : e = 1 := by exact_mod_cast he1
        simpa [Nat.fib] using this
      · have : f = 2 := by exact_mod_cast hfe
        simpa [Nat.fib] using this
/-- **`thm:fib`, complete.**  The gap is `2` exactly at consecutive Fibonacci pairs. -/
theorem gap_two_iff_fib (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) :
    |((f : ℤ) + (e : ℤ)) ^ 2 - (3 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2)| = 2 ↔
      ∃ n, e = Nat.fib (n + 1) ∧ f = Nat.fib (n + 2) := by
  constructor
  · intro h
    exact fib_of_gap f e he hef hcop ((gap_eq_two_iff (e : ℤ) (f : ℤ)).mp h)
  · rintro ⟨n, rfl, rfl⟩
    have h := fib_gap (n + 1)
    have hf : (Nat.fib (n + 2) : ℤ) = (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [show n + 1 + 1 = n + 2 from rfl] at h
    linarith [h, hf, abs_nonneg ((Nat.fib (n+2) : ℤ) + (Nat.fib (n+1) : ℤ))]

end Erdos634.FibExtremal
