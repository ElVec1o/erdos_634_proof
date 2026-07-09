# Lean formalization — arithmetic layer of the Erdős #634 proof

`Erdos634.lean` machine-checks the entire **arithmetic and combinatorial layer** of the proof:
thirteen theorems, all axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; the enumeration
needs only `propext`, `Quot.sound`), no `sorry`.

Isosceles branch (end to end):
- `k_not_dvd_sum_sub`, `M_not_int` — for a primitive 120°-triple with squared leg `b = k²`,
  `k ∤ (a+b−c)`; equivalently the Φ-invariant tile count `M = (c−a−b)/k` is never an integer.
- `iso_reduction_identity` — the identity `(c−a−k²)(c+a−k²) = k²(a+2k²−2c)`.
- `prime_count_forces_scale` — the area equation `N·b = k²(a+2b)` with `N` prime and coprimality
  forces `b = k²` and `N = a+2b`.
- `no_prime_isosceles_count` — **master theorem**: no prime `N` satisfies the 120°-relation, the
  area equation, and the Φ-divisibility `(c+a−b) ∣ k(2b+a−2c)` simultaneously.

Scalene branches:
- `add_not_prime` — `a+b` is never prime for a 120°-triple (via `3(a+b)² = (2c−a+b)(2c+a−b)`).
- `not_prime_of_two_le`, `F1_count_not_prime` … `F4_count_not_prime` — the four scalene tile
  counts are never prime.

Commensurable branch:
- `prime_three_mod_four_excluded` — a prime `p ≡ 3 (mod 4)` with `p > 3` is neither a square, a sum
  of two squares, nor `2n²`, `3n²`, `6n²`, via Fermat's two-squares theorem
  (`Nat.eq_sq_add_sq_iff`).

Shape classification:
- `shape_enumeration` — the eleven-shape completeness: sorted triples of realizable corner types
  `(m, k)` with `Σm = 0`, `Σk = 3` are exactly the eleven of the paper.

The geometric ingredients (the Φ-invariant's cancellation and tile-value lemmas, the direction
grid, Laczkovich's case analysis, Beeson's branch inputs) are **not** formalized — there is no
theory of triangle dissections in Mathlib — and rest on the written proofs in the paper.

## Build
```
lake exe cache get      # download precompiled Mathlib (v4.30.0)
lake build              # checks Erdos634.lean
```
Toolchain: Lean 4.30.0, Mathlib rev v4.30.0.
