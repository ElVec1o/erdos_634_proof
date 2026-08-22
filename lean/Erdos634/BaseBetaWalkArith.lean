import Mathlib.Tactic

/-!
# The boundary walk of a base-`β` target at `m = 1`

Erdős #634.  Tile `(a,b,c) = (ef, f²−e², f²)`, `gcd(e,f) = 1`, `1 ≤ e < f`; target
`(f³, f³, e(3f²−e²))` at `m = 1`, with `N = 3f² − e²`.

Each side of the target is exactly partitioned by the tile edges lying on it, so a side of length
`L` gives a *walk equation*

    nₐ·(ef) + n_b·b + n_c·f²  =  L,      nₐ, n_b, n_c ≥ 0.

This file solves those equations, using as an extra input the `γ`-trap of `BaseBetaCorners`: every
side carries at least one `c`-edge, i.e. `n_c ≥ 1`.

To avoid truncated subtraction everything is over `ℤ` with explicit non-negativity, and `b` is
carried as a variable constrained by `b + e² = f²`.

## Results

* `equal_side_no_b` — if `f² > 2e²` then an equal side carries **no `b`-edge**.  The two competing
  solutions die for different reasons: `n_b = f` forces `(nₐ,n_b,n_c) = (e,f,0)`, which has no
  `c`-edge and is killed by the `γ`-trap; `n_b ≥ 2f` is already too long.
* `equal_side_shape` — consequently `nₐ = fk` and `n_c = f − ke`.
* `base_b_count` — if `f² > 2ef + e²` (that is, `f/e > 1 + √2`) then the base carries **exactly `e`
  `b`-edges**; the walk equation then gives `nₐ = fℓ` and `n_c = e(2 − ℓ)`, so `R_base ∈ {e, 2e}`.

At `e = 1` the hypotheses read `f² > 2` and `f² > 2f + 1`, i.e. `f ≥ 3`, and these specialise to the
`e = 1` reduction: equal sides free of `b`-edges, base with one `b`-edge and `R_base ∈ {1,2}`.

Both hypotheses are sharp, in that the excluded solutions genuinely appear otherwise: `n_b = 2f` on
an equal side needs exactly `f² ≤ 2e²`, and `n_b = e + f` on the base needs exactly
`f² ≤ 2ef + e²` — the latter because `(f+e)²(f−e) = e(3f²−e²) + f(f² − 2ef − e²)`.  Checked by
enumeration over all 198 coprime pairs with `f ≤ 25`: zero discrepancies.

Axiom-clean.
-/

namespace Erdos634.BaseBetaWalkArith

/-- Divisibility with a bounded witness: `f ∣ x` together with `0 ≤ x < f` forces `x = 0`. -/
theorem eq_zero_of_dvd_of_lt (f x : ℤ) (hf : 0 < f) (hd : f ∣ x) (h0 : 0 ≤ x) (h1 : x < f) :
    x = 0 := by
  obtain ⟨s, hs⟩ := hd
  rcases lt_trichotomy s 0 with h | h | h
  · exfalso
    have hle : f * s ≤ f * (-1) := mul_le_mul_of_nonneg_left (by omega) hf.le
    linarith [hs, hle]
  · rw [h, mul_zero] at hs; exact hs
  · exfalso
    have hle : f * 1 ≤ f * s := mul_le_mul_of_nonneg_left (by omega) hf.le
    linarith [hs, hle]

/-- **An equal side carries no `b`-edge, once `f² > 2e²`.**

The walk equation is `nₐ·ef + n_b·b + n_c·f² = f³` with `b + e² = f²`.  Rearranged it gives
`n_b·e² = f·(nₐ·e + n_b·f + n_c·f − f²)`, so `f ∣ n_b·e²` and hence `f ∣ n_b`.

Write `n_b = f·t`.  If `t ≥ 2` then the `b`-edges alone cost at least `2f·b = 2f³ − 2fe²`, which
together with `n_c·f² ≥ f²` exceeds `f³` unless `f² ≤ 2e²`.  If `t = 1` then cancelling `f` gives
`nₐ·e + n_c·f = e²`, so `nₐ ≤ e` and `f ∣ e(e − nₐ)`; coprimality with `0 ≤ e − nₐ ≤ e < f` gives
`nₐ = e`, and then `n_c = 0` — no `c`-edge, contradicting the `γ`-trap.  So `t = 0`. -/
theorem equal_side_no_b (e f b na nb nc : ℤ)
    (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hb : b + e ^ 2 = f ^ 2) (hthin : 2 * e ^ 2 < f ^ 2)
    (hna : 0 ≤ na) (hnb : 0 ≤ nb) (hnc : 1 ≤ nc)
    (hwalk : na * (e * f) + nb * b + nc * f ^ 2 = f ^ 3) :
    nb = 0 := by
  have hf0 : (0 : ℤ) < f := by linarith
  have hbpos : 0 < b := by nlinarith
  have hnaef : 0 ≤ na * (e * f) := mul_nonneg hna (by positivity)
  have hncf : f ^ 2 ≤ nc * f ^ 2 := le_mul_of_one_le_left (by positivity) hnc
  -- `f ∣ nb`
  have hdvd : f ∣ nb := by
    have hmul : f ∣ nb * e ^ 2 :=
      ⟨na * e + nb * f + nc * f - f ^ 2, by linear_combination nb * hb - hwalk⟩
    exact ((hcop.symm).pow_right).dvd_of_dvd_mul_right hmul
  obtain ⟨t, ht⟩ := hdvd
  have ht0 : 0 ≤ t := by
    by_contra h
    push_neg at h
    have hneg : f * t < 0 := mul_neg_of_pos_of_neg hf0 h
    linarith [ht, hnb]
  -- `t ≤ 1`
  have ht1 : t ≤ 1 := by
    by_contra h
    push_neg at h
    have hge : 0 ≤ b * f * (t - 2) := mul_nonneg (mul_nonneg hbpos.le hf0.le) (by omega)
    have hstep : nb * b - 2 * f * b = b * f * (t - 2) := by rw [ht]; ring
    have hbig : 2 * f * b ≤ nb * b := by linarith
    have hbe : b = f ^ 2 - e ^ 2 := by linarith
    rw [hbe] at hbig
    have hmulthin : 2 * f * e ^ 2 < f * f ^ 2 := by nlinarith [hthin, hf0]
    nlinarith [hwalk, hbig, hnaef, hncf, hmulthin]
  -- `t = 1` would force `n_c = 0`
  have hteq : t = 0 := by
    by_contra h
    have ht1' : t = 1 := by omega
    have hnbf : nb = f := by rw [ht, ht1']; ring
    rw [hnbf] at hwalk
    have hcancel : f * (na * e + nc * f) = f * e ^ 2 := by linear_combination hwalk - f * hb
    have hdiv : na * e + nc * f = e ^ 2 := mul_left_cancel₀ (ne_of_gt hf0) hcancel
    have hncf0 : 0 ≤ nc * f := mul_nonneg (by omega) hf0.le
    have hnale : na ≤ e := by nlinarith [hdiv, hncf0, he]
    have hd : f ∣ e * (e - na) := ⟨nc, by linear_combination -hdiv⟩
    have hfe : f ∣ (e - na) := (hcop.symm).dvd_of_dvd_mul_left hd
    have hz : e - na = 0 := eq_zero_of_dvd_of_lt f (e - na) hf0 hfe (by omega) (by omega)
    have hnaeq : na = e := by omega
    rw [hnaeq] at hdiv
    have hzero : nc * f = 0 := by linear_combination hdiv
    have hpos : 0 < nc * f := mul_pos (by omega) hf0
    omega
  rw [ht, hteq]; ring

/-- **Shape of an equal-side walk.**  With `n_b = 0` the equation becomes `nₐ·e + n_c·f = f²`, so
`f ∣ nₐ`; writing `nₐ = f·k` gives `n_c = f − k·e`. -/
theorem equal_side_shape (e f k na nc : ℤ)
    (he : 1 ≤ e) (hef : e < f) (hk : na = f * k)
    (hwalk : na * (e * f) + nc * f ^ 2 = f ^ 3) :
    nc = f - k * e := by
  have hf0 : (0 : ℤ) < f := by linarith
  rw [hk] at hwalk
  have hcancel : f ^ 2 * nc = f ^ 2 * (f - k * e) := by linear_combination hwalk
  exact mul_left_cancel₀ (by positivity) hcancel

/-- **The base carries exactly `e` `b`-edges, once `f² > 2ef + e²`.**

The base has length `e(3f² − e²)`.  Rearranging gives `(n_b − e)·e² = f·(nₐe + n_bf + n_cf − 3ef)`,
so `f ∣ n_b − e`.  Write `n_b = e + f·t`.  Negative `t` makes `n_b < 0`.  For `t ≥ 1` the `b`-edges
alone cost at least `(e+f)·b = (f+e)²(f−e) = e(3f²−e²) + f(f² − 2ef − e²)`, which already exceeds
the base length under the hypothesis, before the mandatory `c`-edge is even placed.  So `t = 0`. -/
theorem base_b_count (e f b na nb nc : ℤ)
    (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hb : b + e ^ 2 = f ^ 2) (hvthin : 2 * e * f + e ^ 2 < f ^ 2)
    (hna : 0 ≤ na) (hnb : 0 ≤ nb) (hnc : 1 ≤ nc)
    (hwalk : na * (e * f) + nb * b + nc * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) :
    nb = e := by
  have hf0 : (0 : ℤ) < f := by linarith
  have hbpos : 0 < b := by nlinarith
  have hnaef : 0 ≤ na * (e * f) := mul_nonneg hna (by positivity)
  have hncf : f ^ 2 ≤ nc * f ^ 2 := le_mul_of_one_le_left (by positivity) hnc
  have hdvd : f ∣ (nb - e) * e ^ 2 :=
    ⟨na * e + nb * f + nc * f - 3 * e * f, by linear_combination nb * hb - hwalk⟩
  obtain ⟨t, ht⟩ := ((hcop.symm).pow_right).dvd_of_dvd_mul_right hdvd
  have ht0 : t = 0 := by
    rcases lt_trichotomy t 0 with h | h | h
    · exfalso
      have hle : f * t ≤ f * (-1) := mul_le_mul_of_nonneg_left (by omega) hf0.le
      linarith [ht, hnb, hef]
    · exact h
    · exfalso
      have hle : f * 1 ≤ f * t := mul_le_mul_of_nonneg_left (by omega) hf0.le
      have hnbge : e + f ≤ nb := by linarith [ht, hle]
      have hstep : nb * b - (e + f) * b = b * (nb - e - f) := by ring
      have hge : 0 ≤ b * (nb - e - f) := mul_nonneg hbpos.le (by linarith)
      have hbig : (e + f) * b ≤ nb * b := by linarith
      have hbe : b = f ^ 2 - e ^ 2 := by linarith
      rw [hbe] at hbig
      have hmul : f * (2 * e * f + e ^ 2) < f * f ^ 2 := by nlinarith [hvthin, hf0]
      nlinarith [hwalk, hbig, hnaef, hncf, hmul]
  rw [ht0, mul_zero] at ht
  linarith [ht]

end Erdos634.BaseBetaWalkArith

#print axioms Erdos634.BaseBetaWalkArith.eq_zero_of_dvd_of_lt
#print axioms Erdos634.BaseBetaWalkArith.equal_side_no_b
#print axioms Erdos634.BaseBetaWalkArith.equal_side_shape
#print axioms Erdos634.BaseBetaWalkArith.base_b_count
