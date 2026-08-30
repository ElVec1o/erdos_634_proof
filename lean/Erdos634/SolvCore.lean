import Mathlib

/-!
# The algebraic core of `prop:solv`

Erdős #634, main paper `prop:solv`.  For a primitive `120°` triple with `b = de²`, the condition
`e ∣ (a + b - c)` is equivalent to a parametrisation by an integer `j` with `d < j < 2d`.  The
algebra behind it is here:

* substituting `c = a + et` into `c² = a² + ab + b²` and dividing by `e` gives
  `a(2t - de) = e(de - t)(de + t)`;
* with `2t = ej` that becomes `4a(j - d) = e²(2d - j)(2d + j)`;
* the right side is positive for `0 < j < 2d`, so `j > d`.

At `d = 1` the interval `(1, 2)` holds no integer, which is `lem:nonint` again — recorded here as a
corollary so the two proofs are visibly the same one.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SolvCore

/-- **The substituted equation.**  `c = a + et` in `c² = a² + ab + b²` with `b = de²`. -/
theorem core_identity (d e a t : ℤ) (he : e ≠ 0)
    (heq : (a + e * t) ^ 2 = a ^ 2 + a * (d * e ^ 2) + (d * e ^ 2) ^ 2) :
    a * (2 * t - d * e) = e * (d * e - t) * (d * e + t) := by
  have h : e * (a * (2 * t - d * e) - e * (d * e - t) * (d * e + t)) = 0 := by
    linear_combination heq
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 he
  · linarith

/-- **The `j`-form.**  With `2t = ej`. -/
theorem j_identity (d e a t j : ℤ) (he : e ≠ 0) (h2t : 2 * t = e * j)
    (h : a * (2 * t - d * e) = e * (d * e - t) * (d * e + t)) :
    4 * a * (j - d) = e ^ 2 * (2 * d - j) * (2 * d + j) := by
  have h4 : e * (4 * a * (j - d) - e ^ 2 * (2 * d - j) * (2 * d + j)) = 0 := by
    linear_combination 4 * h - (4 * a + e * (e * j + 2 * t)) * h2t
  rcases mul_eq_zero.mp h4 with h0 | h0
  · exact absurd h0 he
  · linarith

/-- **`j` exceeds `d`.**  For `0 < j < 2d` and `a > 0` the right side is positive, so `j > d`. -/
theorem j_gt_d (d e a j : ℤ) (ha : 0 < a) (he : e ≠ 0) (hj0 : 0 < j) (hj2 : j < 2 * d)
    (h : 4 * a * (j - d) = e ^ 2 * (2 * d - j) * (2 * d + j)) : d < j := by
  have he2 : 0 < e ^ 2 := by positivity
  have hpos : 0 < e ^ 2 * (2 * d - j) * (2 * d + j) := by
    apply mul_pos (mul_pos he2 (by linarith)) (by linarith)
  nlinarith [h, hpos, ha]

/-- **At `d = 1` there is no such `j`**, which is `lem:nonint` in this language: `1 < j < 2` is
empty. -/
theorem no_j_at_d_one (j : ℤ) (h1 : 1 < j) (h2 : j < 2) : False := by omega

end Erdos634.SolvCore
