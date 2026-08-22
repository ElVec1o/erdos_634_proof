import Mathlib.Tactic

/-!
# Why the Γc-emptiness route cannot close the base-β branch

Beeson's `Γc` argument — the engine of his equilateral no-prime theorem — runs by showing the
directed graph `Γc` is empty: if no relation `j·c = u·a + v·b` is witnessed with `j` below the tile
count, then a `Γc` link must emanate from the boundary, which is impossible because links have
in- and out-degree `1` and cannot terminate on `∂ABC`.

For the base-`β` tile `(a,b,c) = (ef, f²−e², f²)` that hypothesis is false — and not by accident.
This file machine-checks the two facts behind that:

* `gammac_classification` : the COMPLETE solution set of `j·c = u·a + v·b` in nonnegative integers
  is `v = f·w`, `u = w·e + f·s`, `j = s·e + w·f`;
* `gammac_witness` : the generator with `(w,s) = (0,1)` is `e·c = f·a`, which is the identity
  `e·f² = f·(e·f)` — so a relation with `j = e` exists for EVERY `(e,f)`;
* `gammac_j_lt_N` : and `e < 3f² − e² = N`, so that relation is far below the tile count.

Hence the `Γc`-emptiness contradiction never triggers on this branch, uniformly in `(e,f)`.
Closing it would require controlling a *non-empty* `Γc`, which is exactly the step left open in
Beeson's isosceles paper.

The equation is carried in the subtraction-free form obtained by multiplying `b + e² = f²` by `v`:

    j·f² + v·e²  =  u·(e·f) + v·f² .

`#print axioms` is checked after each theorem.
-/

namespace Erdos634.GammaC

/-- The relation `e·c = f·a` for the base-`β` tile `(a,b,c) = (ef, f²−e², f²)`: it is an identity,
so it holds for every `(e,f)` with no hypotheses at all.  This is the relation that blocks the
`Γc`-emptiness argument, with `j = e`. -/
theorem gammac_witness (e f : ℕ) : e * f ^ 2 = f * (e * f) := by ring

/-- The witness has `j = e`, and `e` is far below the tile count `N = 3f² − e²`. -/
theorem gammac_j_lt_N (e f : ℕ) (he : 1 ≤ e) (hef : e < f) : e + e ^ 2 < 3 * f ^ 2 := by
  nlinarith [he, hef, sq_nonneg (f - e), sq_nonneg e]

/-- **Complete classification of the `Γc` relations.**  Every solution of `j·c = u·a + v·b` in
nonnegative integers, for the base-`β` tile, has the displayed form.  Reducing modulo `f` twice
(using `gcd(e,f) = 1`) forces first `f ∣ v` and then `f ∣ u − w·e`. -/
theorem gammac_classification (e f j u v : ℤ) (hf : 0 < f) (hcop : IsCoprime e f)
    (h : j * f ^ 2 + v * e ^ 2 = u * (e * f) + v * f ^ 2) :
    ∃ w s : ℤ, v = f * w ∧ u = w * e + f * s ∧ j = s * e + w * f := by
  have hfne : f ≠ 0 := hf.ne'
  -- (1) reduce mod f: f ∣ v * e^2, and gcd(e,f)=1, so f ∣ v
  have h1 : f ∣ v * e ^ 2 := ⟨u * e + v * f - j * f, by linarith⟩
  have hcop2 : IsCoprime f (e ^ 2) := (hcop.symm).pow_right
  obtain ⟨w, hw⟩ : f ∣ v := hcop2.dvd_of_dvd_mul_right h1
  -- (2) substitute and cancel one factor f
  have h2 : j * f + w * e ^ 2 = u * e + w * f ^ 2 := by
    apply mul_right_cancel₀ hfne
    rw [hw] at h; nlinarith [h]
  -- (3) reduce mod f again: f ∣ (w*e - u)*e, so f ∣ w*e - u
  have h3 : f ∣ (w * e - u) * e := ⟨w * f - j, by linarith⟩
  obtain ⟨t, ht⟩ : f ∣ (w * e - u) := (hcop.symm).dvd_of_dvd_mul_right h3
  refine ⟨w, -t, hw, by linarith, ?_⟩
  -- (4) j*f = (s*e + w*f)*f, cancel f
  apply mul_right_cancel₀ hfne
  have hu : u = w * e - f * t := by linarith
  rw [hu] at h2; nlinarith [h2]

#print axioms gammac_witness
#print axioms gammac_j_lt_N
#print axioms gammac_classification

end Erdos634.GammaC
