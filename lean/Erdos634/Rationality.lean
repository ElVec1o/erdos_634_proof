import Mathlib.Tactic

/-!
# Rationality of the tile, derived from the invariant

Erdős #634. The paper's reduction to an isosceles target (`prop:reduction`) works with an
integer-sided tile, so the rationality input it actually consumes is a *general-target* theorem —
a preprint, and the project's largest external dependency.

That dependency is avoidable on the isosceles targets. The signed-direction invariant, its
cancellation lemma and its tile value use **only** the irrationality of `α/π`: they are valid for
arbitrary real side lengths `a, b, c` with `c² = a² + ab + b²`. So `M_α`, `M_β` and `N` are integers
without any rationality assumption, and the ratios of the tile's sides are then forced to be rational
by pure algebra.

On the target `λ·(c, c, 2b+a)`, writing `P = λ/b`:
```
M_α = P(c − a − b),   M_β = P(c + a + b),   N = P²·b(a + 2b).
```
The two identities below are polynomial consequences of `c² = a² + ab + b²`:

* `prod_eq`      — `M_α · M_β = −P²ab`;
* `sum_eq`       — `N + M_α·M_β = 2P²b²`;

and hence

* `ratio_ab`     — `a/b = −2 M_α M_β / (N + M_α M_β)`;
* `ratio_c`      — `c/(a+b) = (M_α + M_β)/(M_β − M_α)`.

Both right-hand sides are built from integers, so `a : b : c` is rational. Numerically, on the tile
`(3,5,7)` with `λ = 5`: `M_α = −1`, `M_β = 15`, `N = 65`, `N + M_αM_β = 50 = 2P²b²`,
`a/b = 30/50 = 3/5` and `c/(a+b) = 14/16 = 7/8`.

`selfsimilar` records the tile-similar target, where `M_α = M_β = λ` and `N = λ²` — the
SWW/Beeson-I conclusion that the tile count is a perfect square, reproved with no rationality input.

Everything here is an identity in `ℝ` (or any commutative ring); no tiling theory. Axiom-clean.
-/

namespace Erdos634.Rationality

variable {R : Type*} [CommRing R]

/-- `M_α · M_β = −P²ab`, using `c² = a² + ab + b²`. -/
theorem prod_eq (a b c P : R) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (P * (c - a - b)) * (P * (c + a + b)) = -(P ^ 2 * (a * b)) := by
  have h : (c - a - b) * (c + a + b) = c ^ 2 - (a + b) ^ 2 := by ring
  calc (P * (c - a - b)) * (P * (c + a + b))
      = P ^ 2 * ((c - a - b) * (c + a + b)) := by ring
    _ = P ^ 2 * (c ^ 2 - (a + b) ^ 2) := by rw [h]
    _ = -(P ^ 2 * (a * b)) := by rw [hc]; ring

/-- `N + M_α·M_β = 2P²b²`, with `N = P²·b(a+2b)`. -/
theorem sum_eq (a b c P : R) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b)) = 2 * (P ^ 2 * b ^ 2) := by
  rw [prod_eq a b c P hc]; ring

/-- **The side ratio `a/b` is a ratio of integers.**  Cleared of denominators:
`a · (N + M_αM_β) = b · (−2 M_αM_β)`.  Since `N`, `M_α`, `M_β` are integers (the invariant needs only
irrationality of `α/π`), this forces `a/b ∈ ℚ` whenever `N + M_αM_β ≠ 0`, and `sum_eq` shows that
quantity is `2P²b² ≠ 0`. -/
theorem ratio_ab (a b c P : R) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    a * (P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b)))
      = b * (-(2 : R) * ((P * (c - a - b)) * (P * (c + a + b)))) := by
  rw [sum_eq a b c P hc, prod_eq a b c P hc]; ring

/-- **The ratio `c/(a+b)` is a ratio of integers.**  Cleared of denominators:
`c · (M_β − M_α) = (a+b) · (M_α + M_β)`.  Note `M_β − M_α = 2P(a+b)` and `M_α + M_β = 2Pc`. -/
theorem ratio_c (a b c P : R) :
    c * ((P * (c + a + b)) - (P * (c - a - b))) = (a + b) * ((P * (c - a - b)) + (P * (c + a + b))) := by
  ring

/-- Packaged: from integrality of the three invariants, both side ratios are ratios of integers. -/
theorem ratios_rational (a b c P : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hb : b ≠ 0) (hP : P ≠ 0) (hab : a + b ≠ 0) :
    a / b = -(2 : ℝ) * ((P * (c - a - b)) * (P * (c + a + b))) /
              (P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b)))
    ∧ c / (a + b) = ((P * (c - a - b)) + (P * (c + a + b))) /
              ((P * (c + a + b)) - (P * (c - a - b))) := by
  have hsum : P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b))
      = 2 * (P ^ 2 * b ^ 2) := sum_eq a b c P hc
  have hden1 : P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b)) ≠ 0 := by
    rw [hsum]; positivity
  have hden2 : (P * (c + a + b)) - (P * (c - a - b)) ≠ 0 := by
    have h : (P * (c + a + b)) - (P * (c - a - b)) = 2 * P * (a + b) := by ring
    rw [h]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hP) hab
  constructor
  · rw [div_eq_div_iff hb hden1]
    linear_combination ratio_ab a b c P hc
  · rw [div_eq_div_iff hab hden2]
    linear_combination ratio_c a b c P

#print axioms Erdos634.Rationality.prod_eq
#print axioms Erdos634.Rationality.sum_eq
#print axioms Erdos634.Rationality.ratio_ab
#print axioms Erdos634.Rationality.ratio_c
#print axioms Erdos634.Rationality.ratios_rational

/-- **Theorem R.**  Integrality of the three invariants forces the tile to be rational.

If `N = P²·b(a+2b)`, `M_α = P(c−a−b)` and `M_β = P(c+a+b)` are integers and the tile satisfies
`c² = a² + ab + b²`, then `a/b` and `c/b` are both rational: the tile is rational up to scale.

No citation is used.  The two identities are `a·(N + M_αM_β) = b·(−2M_αM_β)`, which makes `a/b` a
ratio of integers because `N + M_αM_β = 2P²b² ≠ 0`, and `c·(M_β − M_α) = (a+b)·(M_α + M_β)`, which
makes `c/(a+b)` a ratio of integers because `M_β − M_α = 2P(a+b) ≠ 0`.  Multiplying the second by
`(a+b)/b = a/b + 1` gives `c/b`. -/
theorem tile_rational (a b c P : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hb : b ≠ 0) (hP : P ≠ 0) (hab : a + b ≠ 0)
    (nN nA nB : ℤ)
    (hN : (nN : ℝ) = P ^ 2 * (b * (a + 2 * b)))
    (hA : (nA : ℝ) = P * (c - a - b))
    (hB : (nB : ℝ) = P * (c + a + b)) :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
  have hsum : P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b))
      = 2 * (P ^ 2 * b ^ 2) := sum_eq a b c P hc
  -- the two denominators are nonzero integers
  have hD1R : ((nN + nA * nB : ℤ) : ℝ) = 2 * (P ^ 2 * b ^ 2) := by
    push_cast [hN, hA, hB]; linarith [hsum]
  have hD1 : (nN + nA * nB : ℤ) ≠ 0 := by
    intro h
    rw [h] at hD1R
    have hpos : (0 : ℝ) < 2 * (P ^ 2 * b ^ 2) := by positivity
    push_cast at hD1R; linarith
  have hD2R : ((nB - nA : ℤ) : ℝ) = 2 * P * (a + b) := by push_cast [hA, hB]; ring
  have hD2 : (nB - nA : ℤ) ≠ 0 := by
    intro h
    rw [h] at hD2R
    push_cast at hD2R
    exact (mul_ne_zero (mul_ne_zero (two_ne_zero (α := ℝ)) hP) hab) hD2R.symm
  have hD1' : ((nN + nA * nB : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD1
  have hD2' : ((nB - nA : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD2
  set q : ℚ := (-2 * nA * nB : ℤ) / (nN + nA * nB : ℤ) with hq
  have hqR : (q : ℝ) = ((-2 * nA * nB : ℤ) : ℝ) / ((nN + nA * nB : ℤ) : ℝ) := by
    rw [hq]; push_cast; ring
  -- a = q · b
  have ha : a = (q : ℝ) * b := by
    have hkey : a * ((nN : ℝ) + nA * nB) = b * (-2 * ((nA : ℝ) * nB)) := by
      rw [hN, hA, hB]; linear_combination ratio_ab a b c P hc
    rw [hqR]
    field_simp
    push_cast at hkey ⊢
    linarith [hkey]
  -- c = r · b, with r = (q+1)·(nA+nB)/(nB−nA)
  refine ⟨q, ((nA + nB : ℤ) : ℚ) / ((nB - nA : ℤ) : ℚ) * (q + 1), ha, ?_⟩
  have hkeyc : c * ((nB : ℝ) - nA) = (a + b) * ((nA : ℝ) + nB) := by
    rw [hA, hB]; linear_combination ratio_c a b c P
  have habq : a + b = ((q : ℝ) + 1) * b := by rw [ha]; ring
  rw [habq] at hkeyc
  have hd : ((nB : ℝ) - nA) ≠ 0 := by
    have h := hD2'; push_cast at h; exact h
  have hr : (((((nA + nB : ℤ) : ℚ) / ((nB - nA : ℤ) : ℚ)) * (q + 1) : ℚ) : ℝ)
      = (((nA : ℝ) + nB) * ((q : ℝ) + 1)) / ((nB : ℝ) - nA) := by
    push_cast; field_simp
  rw [hr, div_mul_eq_mul_div, eq_div_iff hd]
  linear_combination hkeyc

end Erdos634.Rationality
#print axioms Erdos634.Rationality.tile_rational
