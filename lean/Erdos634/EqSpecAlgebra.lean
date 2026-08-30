import Mathlib

/-!
# The equilateral admissibility identities

Erdős #634, main paper `prop:eqspec`.  The proposition's numeric chain — `XY = 3ab`, `st = 3N`,
`(t-s)² + 16N = q²`, and the converse proportionality — is algebra once the area ratio
`N = S²/(ab)` and the definitions `s = 3S/X`, `t = 3S/Y` are in hand.  Only the *integrality* of
`s` and `t` comes from the tiling.

Everything here is stated over `ℝ` with `X`, `Y` cleared of denominators, so the identities are
polynomial and hold for the actual quantities.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.EqSpecAlgebra

variable {a b c S : ℝ}

/-- **`XY = 3ab`**, from the `120°` relation `c² = a² + ab + b²`. -/
theorem XY_eq (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c + a - b) * (c + b - a) = 3 * (a * b) := by nlinarith [h]

/-- **`st = 3N`**, with `s·X = 3S`, `t·Y = 3S` and `N·(ab) = S²`. -/
theorem st_eq (X Y s t N : ℝ) (hX : s * X = 3 * S) (hY : t * Y = 3 * S)
    (hXY : X * Y = 3 * (a * b)) (hN : N * (a * b) = S ^ 2) (hab : a * b ≠ 0) :
    s * t * (a * b) = 3 * N * (a * b) := by
  have h1 : (s * X) * (t * Y) = 9 * S ^ 2 := by rw [hX, hY]; ring
  have h2 : (s * t) * (X * Y) = 9 * S ^ 2 := by linarith [h1, mul_comm X t]
  rw [hXY] at h2
  nlinarith [h2, hN]

/-- **The discriminant identity.**  `(t-s)² + 16N` is the square of `q = 2S(a+b)/(ab)`, cleared of
denominators. -/
theorem disc_eq (s t N : ℝ) (hab : a * b ≠ 0)
    (hs : s * (c + a - b) = 3 * S) (ht : t * (c + b - a) = 3 * S)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hN : N * (a * b) = S ^ 2)
    (hsv : s * (a * b) = S * (c + b - a)) (htv : t * (a * b) = S * (c + a - b)) :
    ((t - s) ^ 2 + 16 * N) * (a * b) ^ 2 = (2 * S * (a + b)) ^ 2 := by
  have hts : (t - s) * (a * b) = S * ((c + a - b) - (c + b - a)) := by
    rw [sub_mul, htv, hsv]; ring
  have hts' : (t - s) * (a * b) = S * (2 * a - 2 * b) := by rw [hts]; ring
  have hsq : ((t - s) * (a * b)) ^ 2 = (S * (2 * a - 2 * b)) ^ 2 := by rw [hts']
  linear_combination hsq + 16 * (a * b) * hN

/-- **The converse proportionality.**  With `q² = (t-s)² + 16N`, the triple
`(q + (t-s), q - (t-s), 2(s+t))` satisfies the `120°` relation. -/
theorem converse_triple (u v q : ℝ) (h : q ^ 2 = (v - u) ^ 2 + 16 * (u * v / 3)) :
    (2 * (u + v)) ^ 2 = (q + (v - u)) ^ 2 + (q + (v - u)) * (q - (v - u)) + (q - (v - u)) ^ 2 := by
  nlinarith [h]

end Erdos634.EqSpecAlgebra
