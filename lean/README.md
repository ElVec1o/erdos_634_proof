# Lean formalization — arithmetic layer of the Erdős #634 proof

`Tiling28.lean` and `Tiling44.lean` machine-check the **28- and 44-tiling certificates with zero
axioms** (`#print axioms`: none for either): pure kernel
computation over Z[sqrt15] (no imports, not even Mathlib) verifies congruence of all 44 tiles to
(2,3,4), containment, an explicit separating line for each of the 946 pairs, and the exact area
sum. `#print axioms` reports no axioms. With the one-paragraph convexity/measure bridge in the
paper, THEOREMS (unconditional): a triangle can be cut into 28, and into 44, congruent triangles. Build:
`lean Tiling44.lean` (any Lean 4 toolchain; no dependencies).

`Gamma2Alpha.lean` proves, axiom-clean (`propext, Classical.choice, Quot.sound`), the number-theory
core of the gamma=2alpha branch (Beeson's Lemma 11.2): if `c^2 = a^2 + a*b` with `gcd(a,b,c)=1` then
`(a,b,c) = (k^2, m^2-k^2, k*m)` for coprime `k<m`. Proved from scratch (coprime factors of a square
are squares), so that branch's tile classification no longer depends on any citation.

`Beeson3NotPrime.lean` machine-checks, axiom-clean, the arithmetic cores of Beeson III's "no prime
`N` when `3α+2β=π`" for both **scalene** targets. `triquadratic_not_prime` (Theorem 8, `(2α,β,α+β)`):
given the first tiling equation `N + M² = 2K²` with `K ∣ N`, no **odd prime** `N` is possible
(`K ∣ N` ⟹ `K ∈ {1,N}`; `K=1` ⟹ `N ≤ 2`; `K=N` ⟹ `M² = N(2N−1)` ⟹ `N ∣ 1`).
`fourcomp_not_prime` (Theorem 12, `(2α,α,2β)`): the second tiling equation forces the count to
`N = (2f²−e²)(3f²−e²)k²` (`1 ≤ e < f`), a product of two factors `≥ 7` and `≥ 11`, hence composite
(e.g. `(2,3,4)→77=7·11`, `(3,8,9)→442=17·26`). These remove the *arithmetic* half of the prime
dichotomy's `3α+2β` citation for both scalene targets. No tiling theory.

`BaseAlphaBetaPrime.lean` machine-checks, axiom-clean, the arithmetic core of the **correct** proof
that no base-`(α+β)` isosceles triangle is `N`-tiled for prime `N` — **replacing Beeson III's
Theorem 18, whose printed mod-`N` proof is unsound** (under his scaling `bc = c²−a² = 4NM²`, so
`c²b ≡ 0 (mod N)` identically, not the `M⁴(M²+1)` he needs; a dropped factor of `a`). `gcd_dvd_two`:
for prime `N`, `1≤M`, `M²<N`, `gcd(N−M², N+M²) ∣ 2`. `base_obstruction`: with reduced data
`g > â ≥ 1`, `â + M ≤ g`, the base-length lower bound `(g−M)(g²−â²) + 2g² ≤ M·â·(g+â)` a tiling
forces is impossible (identity `(g−M)(g²−â²) − Mâ(g+â) = g(g+â)(g−â−M) ≥ 0`). Only Beeson's
geometric covering lemmas (6, 42, 45(iii), Thm 17) are cited; the arithmetic is proved here.

`EquilateralConic.lean` machine-checks, axiom-clean, the **necessary side of the equilateral branch**
(paper Prop. "Conic form") as pure integer algebra: for a `2π/3` tile the invariant counts `s,t` with
`t*s = 3N` and `(t-s)^2+16N = q^2` eliminate to `(q*s)^2 = (s^2+N)(s^2+9N)`, hence the divisor
condition `(s^2+5N-q*s)(s^2+5N+q*s) = 16N^2`; the `π/3` companion is the identity
`(5N-M^2)^2-16N^2 = (9N-M^2)(N-M^2)`. No tiling theory, no preprint.

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
