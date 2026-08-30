import Mathlib

/-!
# The second stub is a gap

Erdős #634, companion `lem:stubgap`.  For the base-`β` tile `(a,b,c) = (ef, f²-e², f²)` the
difference `|a - b|` is a gap of the numerical semigroup `⟨a, b, c⟩`.

The proof is the paper's, with the final step taken directly rather than through `min`/`max`: both
generators exceed `1` and are coprime, so `a ≠ b`; the difference is below `c`, killing the
`c`-coefficient; it is below whichever of `a`, `b` is larger, killing that one; and the surviving
equation makes the smaller generator divide the larger, which coprimality forbids.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.StubGap

/-- `ef` and `f² - e²` are coprime when `e` and `f` are. -/
theorem coprime_a_b (e f : ℤ) (hcop : IsCoprime e f) : IsCoprime (e * f) (f ^ 2 - e ^ 2) := by
  have he : IsCoprime e (f ^ 2 - e ^ 2) := by
    have h1 : IsCoprime e (f ^ 2) := (hcop.pow_right)
    have := h1.add_mul_left_right (-e)
    simpa [sub_eq_add_neg, pow_two, mul_comm] using this
  have hf : IsCoprime f (f ^ 2 - e ^ 2) := by
    have h1 : IsCoprime f (-(e ^ 2)) := ((hcop.symm.pow_right).neg_right)
    have := h1.add_mul_left_right f
    have h2 : -(e ^ 2) + f * f = f ^ 2 - e ^ 2 := by ring
    rwa [h2] at this
  exact he.mul_left hf

/-- **The stub is a gap.**  `|a - b|` has no representation `xa + yb + zc` in nonnegative
coefficients. -/
theorem stub_gap (e f x y z : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 ≠ |e * f - (f ^ 2 - e ^ 2)| := by
  intro hrep
  have hab := coprime_a_b e f hcop
  have hf1 : 2 ≤ f := by omega
  have ha2 : 2 ≤ e * f := by nlinarith
  have hb3 : 3 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have hane : (0:ℤ) ≤ e * f := by linarith
  have hbne : (0:ℤ) ≤ f ^ 2 - e ^ 2 := by linarith
  have hxa : 0 ≤ x * (e * f) := mul_nonneg hx hane
  have hyb : 0 ≤ y * (f ^ 2 - e ^ 2) := mul_nonneg hy hbne
  have hzc : 0 ≤ z * f ^ 2 := mul_nonneg hz (by positivity)
  -- `a ≠ b`
  have hne : e * f ≠ f ^ 2 - e ^ 2 := by
    intro h
    rw [h] at hab
    have hu : IsUnit (f ^ 2 - e ^ 2) := hab.isUnit_of_dvd' dvd_rfl dvd_rfl
    rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega
  have hpos : 0 < |e * f - (f ^ 2 - e ^ 2)| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlt : |e * f - (f ^ 2 - e ^ 2)| < f ^ 2 := by
    rcases abs_cases (e * f - (f ^ 2 - e ^ 2)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> nlinarith
  -- the `c`-coefficient vanishes
  have hz0 : z = 0 := by
    by_contra hzz
    have : 1 ≤ z := by omega
    have : f ^ 2 ≤ z * f ^ 2 := by nlinarith
    linarith [hrep, hlt]
  subst hz0
  rcases lt_trichotomy (e * f) (f ^ 2 - e ^ 2) with hlt' | heq | hgt
  · have habs : |e * f - (f ^ 2 - e ^ 2)| = (f ^ 2 - e ^ 2) - e * f := by
      rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    rw [habs] at hrep
    have hy0 : y = 0 := by
      by_contra hyy
      have h1 : 1 ≤ y := by omega
      have : (f ^ 2 - e ^ 2) ≤ y * (f ^ 2 - e ^ 2) := by nlinarith
      linarith [hrep]
    subst hy0
    have hdvd : (e * f) ∣ (f ^ 2 - e ^ 2) := ⟨x + 1, by linarith [hrep]⟩
    have hu : IsUnit (e * f) := hab.isUnit_of_dvd' dvd_rfl hdvd
    rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega
  · exact hne heq
  · have habs : |e * f - (f ^ 2 - e ^ 2)| = e * f - (f ^ 2 - e ^ 2) := abs_of_pos (by linarith)
    rw [habs] at hrep
    have hx0 : x = 0 := by
      by_contra hxx
      have h1 : 1 ≤ x := by omega
      have : (e * f) ≤ x * (e * f) := by nlinarith
      linarith [hrep]
    subst hx0
    have hdvd : (f ^ 2 - e ^ 2) ∣ (e * f) := ⟨y + 1, by linarith [hrep]⟩
    have hu : IsUnit (f ^ 2 - e ^ 2) := hab.symm.isUnit_of_dvd' dvd_rfl hdvd
    rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega

end Erdos634.StubGap
