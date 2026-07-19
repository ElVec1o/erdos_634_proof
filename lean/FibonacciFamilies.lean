import Mathlib.Tactic

/-!
# The base-`β` families: field of definition, and the Fibonacci extremal cases

For the primitive `3α+2β=π` tile `(a,b,c) = (ef, f²−e², f²)` with `1 ≤ e < f`, `gcd(e,f)=1`, the
base-`β` target at scale `m` has colouring number `M = (f+e)m` and tile count `N = m²(3f²−e²)`.
Three exact facts, all pure integer arithmetic (paper Prop. "Field of definition", Thms. "Fibonacci
families are the extremal ones" and "Arithmetic of the Fibonacci families"):

* `sin_sq_identity` — `4f⁴ − (2f²−e²)² = e²(4f²−e²)`, the identity behind `sin α = e√D/(2f²)`, so
  the tiling's coordinates lie in `ℚ(√D)` with `D = 4f²−e² = (2f−e)(2f+e)`; and `D − N₀ = f²`.
* `M_sq_sub_N` — `M² − N₀ = −2(f² − ef − e²)`. Hence `M² < N₀ ⟺ f² − ef − e² > 0 ⟺ f/e > φ`,
  which is the golden-ratio criterion, and `|M² − N₀| ≥ 2` since the form is a nonzero integer.
* `fib_extremal_iff` — equality `|M² − N₀| = 2` holds exactly when `f² − ef − e² = ±1`, the
  classical characterisation of consecutive Fibonacci pairs.
* `fib_lucas`, `fib_two_add`, `fib_M` — for `(e,f) = (F n, F (n+1))`: `2f − e = L n` (Lucas),
  `2f + e = F (n+3)`, and `M = f + e = F (n+2)`.

The number-theoretic input that `x² − xy − y² = ±1` forces consecutive Fibonacci pairs is *not*
formalized here (it is a Markov-style descent); `fib_extremal_iff` states the equality criterion in
terms of the form itself, which is what the paper's proof uses. Axiom-clean.
-/

namespace Erdos634.FibonacciFamilies

open Nat

/-- The identity behind `sin α = e√D/(2f²)`: `4f⁴ − (2f²−e²)² = e²(4f²−e²)`.  It is what places a
base-`β` tiling's coordinates in `ℚ(√D)` with `D = 4f²−e²`. -/
theorem sin_sq_identity (e f : ℤ) :
    4 * f ^ 4 - (2 * f ^ 2 - e ^ 2) ^ 2 = e ^ 2 * (4 * f ^ 2 - e ^ 2) := by ring

/-- `D = (2f−e)(2f+e)`: the discriminant always factors. -/
theorem D_factors (e f : ℤ) : 4 * f ^ 2 - e ^ 2 = (2 * f - e) * (2 * f + e) := by ring

/-- `D − N₀ = f²`: the field discriminant exceeds the tile count by exactly `f²`. -/
theorem D_sub_N (e f : ℤ) : (4 * f ^ 2 - e ^ 2) - (3 * f ^ 2 - e ^ 2) = f ^ 2 := by ring

/-- **The colouring deficiency is the golden form.**  With `M = f+e` and `N₀ = 3f²−e²`,
`M² − N₀ = −2(f² − ef − e²)`.  So `M² < N₀` exactly when `f² − ef − e² > 0`, i.e. `f/e > φ`. -/
theorem M_sq_sub_N (e f : ℤ) :
    (f + e) ^ 2 - (3 * f ^ 2 - e ^ 2) = -2 * (f ^ 2 - e * f - e ^ 2) := by ring

/-- The golden criterion in the form used by the paper. -/
theorem M_sq_lt_N_iff (e f : ℤ) :
    (f + e) ^ 2 < 3 * f ^ 2 - e ^ 2 ↔ 0 < f ^ 2 - e * f - e ^ 2 := by
  constructor <;> intro h <;> nlinarith [M_sq_sub_N e f]

/-- **`|M² − N₀| ≥ 2`.**  The deficiency is twice a nonzero integer. -/
theorem two_le_abs_deficiency (e f : ℤ) (h : f ^ 2 - e * f - e ^ 2 ≠ 0) :
    2 ≤ |(f + e) ^ 2 - (3 * f ^ 2 - e ^ 2)| := by
  rw [M_sq_sub_N, abs_mul]
  have h1 : (1 : ℤ) ≤ |f ^ 2 - e * f - e ^ 2| := Int.one_le_abs (by omega)
  have h2 : |(-2 : ℤ)| = 2 := by decide
  rw [h2]
  omega

/-- **The extremal case.**  `|M² − N₀| = 2` exactly when the golden form is `±1` --- the condition
characterising consecutive Fibonacci pairs. -/
theorem fib_extremal_iff (e f : ℤ) :
    |(f + e) ^ 2 - (3 * f ^ 2 - e ^ 2)| = 2 ↔ |f ^ 2 - e * f - e ^ 2| = 1 := by
  rw [M_sq_sub_N, abs_mul]
  have h2 : |(-2 : ℤ)| = 2 := by decide
  rw [h2]
  constructor <;> intro h <;> omega

/-! ### The Fibonacci families -/

/-- Lucas numbers. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas n + lucas (n + 1)

/-- `2·F(n+1) + F n = F(n+3)`: the `2f+e` side of a Fibonacci family is again Fibonacci. -/
theorem fib_two_add (n : ℕ) : 2 * Nat.fib (n + 1) + Nat.fib n = Nat.fib (n + 3) := by
  have h1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have h2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  omega

/-- `M = f + e = F(n+2)` for a Fibonacci family. -/
theorem fib_M (n : ℕ) : Nat.fib n + Nat.fib (n + 1) = Nat.fib (n + 2) := Nat.fib_add_two.symm

/-- `2·F(n+1) − F n = L n` (Lucas).  Stated subtraction-free as `L n + F n = 2·F(n+1)`. -/
theorem fib_lucas : ∀ n : ℕ, lucas n + Nat.fib n = 2 * Nat.fib (n + 1)
  | 0 => by decide
  | 1 => by decide
  | (k + 2) => by
      have h1 : lucas k + Nat.fib k = 2 * Nat.fib (k + 1) := fib_lucas k
      have h2 : lucas (k + 1) + Nat.fib (k + 1) = 2 * Nat.fib (k + 2) := fib_lucas (k + 1)
      have hl : lucas (k + 2) = lucas k + lucas (k + 1) := by rw [lucas]
      have hf1 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      have hf2 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      show lucas (k + 2) + Nat.fib (k + 2) = 2 * Nat.fib (k + 3)
      omega

end Erdos634.FibonacciFamilies

#print axioms Erdos634.FibonacciFamilies.sin_sq_identity
#print axioms Erdos634.FibonacciFamilies.D_factors
#print axioms Erdos634.FibonacciFamilies.D_sub_N
#print axioms Erdos634.FibonacciFamilies.M_sq_sub_N
#print axioms Erdos634.FibonacciFamilies.M_sq_lt_N_iff
#print axioms Erdos634.FibonacciFamilies.two_le_abs_deficiency
#print axioms Erdos634.FibonacciFamilies.fib_extremal_iff
#print axioms Erdos634.FibonacciFamilies.fib_two_add
#print axioms Erdos634.FibonacciFamilies.fib_M
#print axioms Erdos634.FibonacciFamilies.fib_lucas
