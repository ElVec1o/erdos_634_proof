import Mathlib.Tactic

/-!
The equilateral `2π/3`- and `π/3`-tile *necessary conditions* as pure integer algebra
(Erdős #634 paper, "Equilateral admissibility" and "Conic form" propositions), proved here with
no tiling theory and no dependence on any preprint.

For a `2π/3` tile `(a,b,c)` tiling an equilateral triangle of side `S`, the invariant counts
`s = 3S/(c+a-b)`, `t = 3S/(c+b-a)` are positive integers with `s*t = 3N` and `(t-s)^2 + 16N = q^2`
for an integer `q`.  The two lemmas below reduce that square condition to a **factorization of
`16N^2`** (a difference of two squares), which is the elementary necessary side used to enumerate
the finitely many admissible instances per `N`.  The `π/3` companion is a one-line ring identity.
Every proof is `ring`/`linear_combination` over `ℤ`, so the file is axiom-clean.
-/

namespace Erdos634.EquilateralConic

/-- Step 1 (2π/3): the two invariant counts `s,t` with `s*t = 3N` and `(t-s)^2 + 16N = q^2`
force `(q*s)^2 = (s^2 + N)(s^2 + 9N)`.  Pure elimination of `t`. -/
theorem qs_sq (s t N q : ℤ) (hst : t * s = 3 * N) (hq : (t - s) ^ 2 + 16 * N = q ^ 2) :
    (q * s) ^ 2 = (s ^ 2 + N) * (s ^ 2 + 9 * N) := by
  linear_combination (-s ^ 2) * hq + (t * s + 3 * N - 2 * s ^ 2) * hst

/-- Step 2 (2π/3): completing the square turns `(q*s)^2 = (s^2+N)(s^2+9N)` into
`(s^2 + 5N)^2 - (q*s)^2 = 16N^2`. -/
theorem conic_2pi3 (s N q : ℤ) (h : (q * s) ^ 2 = (s ^ 2 + N) * (s ^ 2 + 9 * N)) :
    (s ^ 2 + 5 * N) ^ 2 - (q * s) ^ 2 = 16 * N ^ 2 := by
  linear_combination -h

/-- The `2π/3` necessary condition in its final form: an equilateral `2π/3`-tiling yields an
**explicit factorization of `16N^2`** as a product of two integers of equal parity, namely
`u = s^2 + 5N - q*s` and `v = s^2 + 5N + q*s`.  This is the divisor condition the enumeration uses. -/
theorem factor_2pi3 (s t N q : ℤ) (hst : t * s = 3 * N) (hq : (t - s) ^ 2 + 16 * N = q ^ 2) :
    (s ^ 2 + 5 * N - q * s) * (s ^ 2 + 5 * N + q * s) = 16 * N ^ 2 := by
  have h := qs_sq s t N q hst hq
  linear_combination -h

/-- The `π/3` companion (Beeson's square criterion, restated): the necessary datum
`(9N - M^2)(N - M^2)` being a perfect square is exactly a factorization of `16N^2`, since
`(5N - M^2)^2 - 16N^2 = (9N - M^2)(N - M^2)`.  A pure ring identity. -/
theorem conic_pi3 (N M : ℤ) :
    (5 * N - M ^ 2) ^ 2 - 16 * N ^ 2 = (9 * N - M ^ 2) * (N - M ^ 2) := by
  ring

end Erdos634.EquilateralConic

#print axioms Erdos634.EquilateralConic.qs_sq
#print axioms Erdos634.EquilateralConic.conic_2pi3
#print axioms Erdos634.EquilateralConic.factor_2pi3
#print axioms Erdos634.EquilateralConic.conic_pi3
