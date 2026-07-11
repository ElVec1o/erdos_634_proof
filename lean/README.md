# Lean formalization — arithmetic layer of the Erdős #634 proof

`Tiling28.lean` and `Tiling44.lean` machine-check the **28- and 44-tiling certificates with zero
axioms** (`#print axioms`: none for either): pure kernel
computation over Z[sqrt15] (no imports, not even Mathlib) verifies congruence of all 44 tiles to
(2,3,4), containment, an explicit separating line for each of the 946 pairs, and the exact area
sum. `#print axioms` reports no axioms. With the one-paragraph convexity/measure bridge in the
paper, THEOREMS (unconditional): a triangle can be cut into 28, and into 44, congruent triangles. Build:
`lean Tiling44.lean` (any Lean 4 toolchain; no dependencies).

`Erdos634.lean` machine-checks the entire **arithmetic and combinatorial layer** of the proof:
twenty-three theorems, all axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; the enumeration
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

Towards the full problem:
- `prime_sum_two_pos_squares` — a prime `p ≢ 3 (mod 4)` is a sum of two positive squares
  (the achievability half of the prime dichotomy).
- `iso_admissible` — the general-`N` admissibility theorem: with `b = d·e²`, `d` squarefree, the
  area equation and Φ-divisibility force `k = d·e·w`, `N = d·w²·(a+2b)`, and `e | w(c−a−b)`.

The N = 14, 15 sweep (finite arithmetic of the branch checks):
- `pi3_equilateral_fails_14_15` — Beeson's square criterion `(9N−M²)(N−M²) = □` fails for every
  admissible `M` at `N = 14, 15`.
- `shapeA_fails_14_15` — the tiling equation `N = 2K²−M²` with `K | M²` has no admissible solution.
- `eq_spectrum_unique_14`, `eq_spectrum_unique_15` — in the equilateral criterion `st = 3N` with
  `(t−s)² + 16N = □`, the only factor pairs are `(6,7)` and `(5,9)`: the instances are unique.
- `iso_ab_congruence_kills_14` — the boundary congruence kills the `N = 14` iso-`(α+β)` candidate
  (no `m ≡ 7 (mod 9)` fits `140 = 45p + 56m + 81q`).
- `F1_invariant_kills_21` — the invariant integrality fails on the unique `N = 21` `F₁` candidate
  (tile `(5,16,19)`, `k = 4`: `8 ∤ 28`).
- `parity_kills_46` — the parity refinement kills `N = 46` on `(7,8,13)` (`w = 1` is odd).
- `iso_ab_congruence_kills_22` — both `N = 22` iso-`(α+β)` candidates fall to the boundary
  congruence.

The geometric ingredients (the Φ-invariant's cancellation and tile-value lemmas, the direction
grid, Laczkovich's case analysis, Beeson's branch inputs) are **not** formalized — there is no
theory of triangle dissections in Mathlib — and rest on the written proofs in the paper.

## Build
```
lake exe cache get      # download precompiled Mathlib (v4.30.0)
lake build              # checks Erdos634.lean
```
Toolchain: Lean 4.30.0, Mathlib rev v4.30.0.
