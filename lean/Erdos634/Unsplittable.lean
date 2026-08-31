import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Unsplittability of the tile's edges

Erdős #634, main paper `prop:unsplit`.  For the base-`β` tile `(a,b,c) = (ef, f²-e², f²)` with
`gcd(e,f) = 1` and `1 ≤ e < f`:

* `a` is not a sum of two or more tile edges — its only representation is itself;
* `b` likewise;
* `c` is such a sum exactly when `e = 1`, and then uniquely as `f` copies of `a`.

All three are one argument: reduce modulo `f`, use `gcd(e,f) = 1` to force `f ∣ y`, and observe
that a single `b` already exceeds the target unless `y = 0`; then reduce the two-term equation.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Unsplittable

variable {e f x y z : ℤ}

/-- The `b`-coefficient vanishes in any representation of something below `f·b`. -/
theorem y_zero (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f) (hy : 0 ≤ y)
    (hbound : y * (f ^ 2 - e ^ 2) ≤ f ^ 2) (hdvd : f ∣ y) : y = 0 := by
  obtain ⟨k, rfl⟩ := hdvd
  rcases eq_or_lt_of_le (by nlinarith : (0:ℤ) ≤ k) with h | h
  · simp [← h]
  · exfalso
    have hf2 : 2 ≤ f := by omega
    have h1 : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
    nlinarith [hbound]

/-- **`a` is unsplittable.** -/
theorem a_unsplittable (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (heq : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = e * f) :
    x = 1 ∧ y = 0 ∧ z = 0 := by
  have hf2 : 2 ≤ f := by omega
  have hz0 : z = 0 := by
    by_contra hzz
    have h1 : 1 ≤ z := by omega
    have : f ^ 2 ≤ z * f ^ 2 := by nlinarith
    nlinarith [mul_nonneg hx (by nlinarith : (0:ℤ) ≤ e * f),
      mul_nonneg hy (by nlinarith : (0:ℤ) ≤ f ^ 2 - e ^ 2)]
  subst hz0
  have hfy : f ∣ y * e ^ 2 := ⟨x * e + y * f - e, by linarith [heq]⟩
  have hfy' : f ∣ y := by
    have hce : IsCoprime f (e ^ 2) := (hcop.symm.pow_right)
    exact hce.dvd_of_dvd_mul_right hfy
  have hy0 : y = 0 := by
    refine y_zero he hef hcop hy ?_ hfy'
    nlinarith [mul_nonneg hx (by nlinarith : (0:ℤ) ≤ e * f), heq]
  subst hy0
  refine ⟨?_, rfl, rfl⟩
  have hef0 : (0:ℤ) < e * f := by nlinarith
  have : x * (e * f) = 1 * (e * f) := by linarith [heq]
  exact mul_right_cancel₀ (ne_of_gt hef0) this

/-- **`c` splits only at `e = 1`, and then uniquely as `f` copies of `a`.** -/
theorem c_split (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (heq : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = f ^ 2) :
    (x = 0 ∧ y = 0 ∧ z = 1) ∨ (e = 1 ∧ x = f ∧ y = 0 ∧ z = 0) := by
  have hf2 : 2 ≤ f := by omega
  have hxa : 0 ≤ x * (e * f) := mul_nonneg hx (by nlinarith)
  have hyb : 0 ≤ y * (f ^ 2 - e ^ 2) := mul_nonneg hy (by nlinarith)
  rcases eq_or_lt_of_le hz with h | h
  · -- `z = 0`
    have hz0 : z = 0 := h.symm
    subst hz0
    have hfy : f ∣ y * e ^ 2 := ⟨x * e + y * f - f, by linarith [heq]⟩
    have hfy' : f ∣ y := (hcop.symm.pow_right).dvd_of_dvd_mul_right hfy
    have hy0 : y = 0 := y_zero he hef hcop hy (by linarith [heq]) hfy'
    subst hy0
    -- `x·e·f = f²`, so `x·e = f`, so `e ∣ f`, so `e = 1`
    have hxe : x * e = f := by
      have hf0 : (0:ℤ) < f := by omega
      have : (x * e) * f = f * f := by linarith [heq]
      exact mul_right_cancel₀ (ne_of_gt hf0) (by linarith [this, sq f])
    have hdvd : e ∣ f := ⟨x, by linarith [hxe]⟩
    have hu : IsUnit e := hcop.isUnit_of_dvd' dvd_rfl hdvd
    have he1 : e = 1 := by
      rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega
    subst he1
    exact Or.inr ⟨rfl, by linarith [hxe], rfl, rfl⟩
  · -- `z ≥ 1` forces `z = 1` and the rest zero
    have hz1 : z = 1 := by
      by_contra hzz
      have h2 : 2 ≤ z := by omega
      have : 2 * f ^ 2 ≤ z * f ^ 2 := by nlinarith
      nlinarith [heq, hxa, hyb]
    subst hz1
    have hsum : x * (e * f) + y * (f ^ 2 - e ^ 2) = 0 := by linarith [heq]
    have hx0 : x = 0 := by
      by_contra hxx
      have h1 : 1 ≤ x := by omega
      have : e * f ≤ x * (e * f) := by nlinarith
      nlinarith [hsum, hyb]
    have hy0 : y = 0 := by
      by_contra hyy
      have h1 : 1 ≤ y := by omega
      have : f ^ 2 - e ^ 2 ≤ y * (f ^ 2 - e ^ 2) := by nlinarith
      nlinarith [hsum, hxa]
    exact Or.inl ⟨hx0, hy0, rfl⟩

end Erdos634.Unsplittable
