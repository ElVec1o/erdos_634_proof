# Lean formalization — arithmetic layer of the Erdős #634 proof

`Erdos634.lean` machine-checks the entire **arithmetic layer** of the proof. Every theorem is
axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) with no `sorry`:

- `k_not_dvd_sum_sub`, `M_not_int` — for a primitive 120°-triple with squared leg `b = k²`,
  `k ∤ (a+b−c)`; equivalently the Φ-invariant tile count `M = (c−a−b)/k` is never an integer (the
  isosceles obstruction).
- `iso_reduction_identity` — the algebraic identity `(c−a−b)(c+a−b) = b(a+2b−2c)` behind the
  isosceles boundary computation.
- `add_not_prime` — for a primitive 120°-triple, `a+b` is never prime (the `F1` step of the scalene
  reduction), via `3(a+b)² = (2c−a+b)(2c+a−b)` and a factor analysis.
- `prime_three_mod_four_excluded` — a prime `p ≡ 3 (mod 4)` with `p > 3` is neither a square, a sum
  of two squares, nor `2n²`, `3n²`, `6n²` (the commensurable-angle branch), via Fermat's two-squares
  theorem (`Nat.eq_sq_add_sq_iff`).

The geometric ingredients (the Φ-invariant's cancellation and tile-value lemmas, Laczkovich's case
analysis, Beeson's branch inputs) are **not** formalized — there is no theory of triangle
dissections in Mathlib — and rest on the written proofs in the paper.

## Build
```
lake exe cache get      # download precompiled Mathlib (v4.30.0)
lake build              # checks Erdos634.lean
```
Toolchain: Lean 4.30.0, Mathlib rev v4.30.0.
