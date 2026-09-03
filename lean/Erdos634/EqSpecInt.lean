import Mathlib.Tactic

/-!
# `prop:eqspecint`: the arithmetic core of equilateral admissibility

`EquilateralConic.*` (VERIFIED) takes the two relations

  `t·s = 3N`   and   `(t-s)² + 16N = q²`

as *hypotheses*.  `prop:eqspecint` is what produces them, from the side relations of an equilateral
`N`-tiling by a `120°`-triple `(a,b,c)`.  The geometric content — that a tiling supplies `X ∣ 3S`,
`Y ∣ 3S` and the area identity — is **not** here: it quantifies over tilings and needs the
tile-placement layer.  What is here is everything after that, stated over `ℤ` with the tiling's
outputs as hypotheses:

* `st_eq_three_N` — from `XY = 3ab`, `sX = 3S`, `tY = 3S` and `S² = N·ab`, derive `s·t = 3N`.
* `conic_of_sides` — from the area identity and `2N(a-b) = S(t-s)`, derive `(t-s)² + 16N = q²`
  for the `q` defined by `S·q = 2N(a+b)`.

Together these are exactly the two inputs `EquilateralConic.factor_2pi3` consumes.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.EqSpecInt

/-- **`s·t = 3N`.**  `XY = c² - (a-b)² = 3ab` by the tile relation; `s`, `t` are the quotients
`3S/X`, `3S/Y`, given here by the equations `sX = 3S`, `tY = 3S` rather than by division. -/
theorem st_eq_three_N (N S a b s t X Y : ℤ) (hab : a * b ≠ 0)
    (hXY : X * Y = 3 * (a * b)) (hs : s * X = 3 * S) (ht : t * Y = 3 * S)
    (harea : S ^ 2 = N * (a * b)) :
    s * t = 3 * N := by
  have h9 : (s * t) * (3 * (a * b)) = 9 * (N * (a * b)) := by
    calc (s * t) * (3 * (a * b)) = (s * X) * (t * Y) := by rw [← hXY]; ring
    _ = 9 * S ^ 2 := by rw [hs, ht]; ring
    _ = 9 * (N * (a * b)) := by rw [harea]
  have h3 : (s * t) * (a * b) = (3 * N) * (a * b) := by linarith [h9]
  exact mul_right_cancel₀ hab h3

/-- **The squared identity.**  `(2N(a+b))² = S²·[(t-s)² + 16N]`, a `ring` consequence of the area
identity `S² = N·ab` and the difference relation `2N(a-b) = S(t-s)`. -/
theorem sq_identity (N S a b s t : ℤ)
    (harea : S ^ 2 = N * (a * b)) (hdiff : 2 * N * (a - b) = S * (t - s)) :
    (2 * N * (a + b)) ^ 2 = S ^ 2 * ((t - s) ^ 2 + 16 * N) := by
  calc (2 * N * (a + b)) ^ 2
      = (2 * N * (a - b)) ^ 2 + 16 * N * (N * (a * b)) := by ring
    _ = (S * (t - s)) ^ 2 + 16 * N * S ^ 2 := by rw [hdiff, ← harea]
    _ = S ^ 2 * ((t - s) ^ 2 + 16 * N) := by ring

/-- **`(t-s)² + 16N = q²`.**  With `q` pinned by `S·q = 2N(a+b)` and `S ≠ 0`, cancelling `S²` from
`sq_identity` gives the conic relation `EquilateralConic` consumes.  This is the step the paper
phrases as "`q` is a rational with integer square, hence an integer". -/
theorem conic_of_sides (N S a b s t q : ℤ) (hS : S ≠ 0)
    (harea : S ^ 2 = N * (a * b)) (hdiff : 2 * N * (a - b) = S * (t - s))
    (hq : S * q = 2 * N * (a + b)) :
    (t - s) ^ 2 + 16 * N = q ^ 2 := by
  have hS2 : S ^ 2 ≠ 0 := pow_ne_zero 2 hS
  have key : S ^ 2 * ((t - s) ^ 2 + 16 * N) = S ^ 2 * q ^ 2 := by
    rw [← sq_identity N S a b s t harea hdiff, ← hq]; ring
  exact mul_left_cancel₀ hS2 key

end Erdos634.EqSpecInt
