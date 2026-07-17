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
(e.g. `(2,3,4)→77=7·11`, `(3,8,9)→442=17·26`). `prime_mul_sq_ne`: exponent-parity descent — for
prime `N ∤ D`, `N·A² = M²·D` has no solution with `A > 0` (a general lemma). `isobeta_square_not_prime`
is a **true implication** but its perfect-square hypothesis is *not* a genuine iso-`β` necessity
(the real side-integrality is `(f+e) ∣ M`, giving `N = m²(3f²−e²)`, which admits primes), so it does
**not** establish the base-`β` prime exclusion — that shape is the one genuine gap (Beeson's Thm 14
`g ∣ M` is unsound like Thm 19), handled per-value by the engine; see the paper's honest remark.
The scalene targets (Thm 8, Thm 12) and the base-`(α+β)`/base-`α` targets (`BaseAlphaBetaPrime`,
`IsoAlphaPrime`) are the four soundly machine-checked shapes. No tiling theory.

`BaseBetaE1.lean` machine-checks, axiom-clean, the pillars of the **new base-`β` `e=1` no-go theorem**
(paper Thm "The base-β family at e=1 does not tile", killing N = 3f²−1 = 11, 26, 47, 74, 107, 191, …):
`tile_alpha_irrational` — **the Laczkovich citation is not needed**: `sin(α/2) = e/(2f)` lies strictly
in (0,½) for 1≤e<f, so Niven's theorem (Mathlib) forces α/π irrational for *every* valid tile;
`vertex_pi`, `vertex_beta_corner`, `vertex_apex` — the vertex-figure enumeration (each base corner
carries exactly one tile, the apex exactly three); `base_composition_e1` — at e=1,m=1 the base
`3f²−1` has the unique covering `{b,c,c}` among those with ≥2 c-edges. **`direction_free` /
`colouring_well_defined`** — the colouring theorem's foundation, citation-free: irrationality makes
`η = exp(i(α/2+π/2))` a non-root-of-unity (`n(α/2+π/2)=kπ ⟹ n=0`), so `⟨η,−1⟩ ≅ ℤ×ℤ/2` and the sign
character `χ₂(±η^n)=±(−1)^n` is well defined — which is exactly what makes the colouring number
`M = Σ χ₂(d_t)` a well-defined integer. This removes the preprint's colouring theorem from under the
`3α+2β` tiling equations (hence from the triquadratic and four-component necessary sides).

`BaseBetaWalks.lean` machine-checks, axiom-clean, the **boundary-walk classification of the base-`β`
target at `m = 1`** (paper Thm "Boundary walks…"), the first statement in this branch that is uniform
in `e`. A walk along a side is a triple `(P,Q,R)` with `P·a + Q·b + R·c = (side length)`. Both walk
sets are cut out by the *same* linear form `⟨e,f,1⟩` — the base at level `2e`, the equal side at
level `f`: `base_walk_param` (`Q = e+fj`, `P = je+fp`, `pe+jf+R = 2e`) and `side_walk_param`
(`Q = fq`, `P = qe+fp`, `pe+qf+R = f`). Since a level bounds its solutions, the walk set is finite
and explicit for every `(e,f)`. In the **thin regime `f > 2e`** it collapses: `base_trichotomy` — the
base is exactly one of `{b^e, c^{2e}}`, `{a^f, b^e, c^e}`, `{a^{2f}, b^e}`, so it carries **exactly
`e` `b`-edges**; `side_dichotomy` — each equal side is `{a^e, b^f}` or `{a^{fp}, c^{f−pe}}`. This
generalizes `BaseBetaE1.base_composition_e1` (the case `e = 1`, and there only under an extra
"≥ 2 `c`-edges" hypothesis) to the infinite family `e=1, f≥3`; `e=2, f≥5`; `e=4, f≥9`; … covering the
primes `N = 47, 71, 107, 191, 227, 239, 359, …`. Feeding in the paper's **γ-trap** (`R ≥ 1`: every
side carries a `c`-edge, since each `a`- and `b`-edge tile puts a `γ` at a junction, no `γ` sits at a
base corner or the apex, and a `π`-vertex admits at most one `γ` — `BaseBetaE1.vertex_pi/
vertex_beta_corner/vertex_apex`) removes the thinness hypothesis entirely.
`side_no_b`: at `m = 1`, for **every** `(e,f)`, no equal side carries a `b`-edge (if `q ≥ 1` then
`P = qe+fp ≥ 0` forces `fp ≥ -qe > -qf`, so `p ≥ 1-q`, so `R = f-pe-qf ≤ (1-q)(f-e) ≤ 0`) — all
boundary `b`-edges lie on the base. `base_b_bound`: the same computation on the base gives
`j·(f−e) ≤ e−1`, so `e = 1` pins `j = 0` (**exactly one `b`-edge on the base, every `f`**) and
`f > 2e` pins `j = 0` (the trichotomy); `base_trichotomy_cfree` packages the latter. This is the
`e ≥ 2` analogue of the `e = 1` structure theorem, uniform in `(e,f)`. **`gamma_injection` /
`c_edge_exists`** machine-check the combinatorial skeleton of the γ-trap itself: the pigeonhole
(injective edge → γ-junction map on a side with `k−1` interior junctions gives `#a+#b ≤ k−1`, i.e.
`R ≥ 1`), so the hypothesis `hR` consumed by `side_no_b`/`base_b_bound` is now derived, with geometry
entering only through the vertex-figure hypotheses (`vertex_pi`, `vertex_beta_corner`, `vertex_apex`)
— the same interface pattern as the rest of the file. **`apex_leftover_nonrepresentable` /
`pierced_corner_types`** machine-check the arithmetic cores of the **apex-mismatch theorem** (paper
Thm "Apex mismatch: the pierced corner"): whenever both equal sides end with `c` (automatic at
`m = 1`), one inner apex ray pairs the middle tile's `c` against a neighbour's `b` — a T-junction at
distance `b` — and the `e²` leftover of that `c`-edge is never exactly coverable
(`n_a·ef + n_b·(f²−e²) + n_c·f² = e²` has no solution: `n_a = n_c = 0` forced by size, then
`n_b·f² = (n_b+1)·e²` + coprimality force `f² ∣ n_b+1`, collapsing to `f²−e² = 1`, impossible), so a
far-side edge pierces the middle tile's far `β`-corner, with continuation `{α,γ}` or `{3α,β}`.
Validated positionally on the genuine 44-tiling: `V = (10, 2√15)` is pierced by a straight `b`-edge,
sector `β + {α,γ}`. The first *interior* forcing in the branch — every hypothetical thick-regime
tiling (`N = 59` included) must contain it. **`far_near_disjoint` / `far_is_bpow` / `b_not_dvd_fsq`**
machine-check the **alignment theorem**: at `e ≥ 2, m = 1` the mismatch ray's near side is `T2`'s single
unsplittable `c`-edge `[0, f²]`, its far side is exactly `b^f` (no common junction in `(0, f²)`; the
only rep of `f·b` with `n_b ≥ 1` is `(0,f,0)`), and `V = f²` is strictly pierced (`b ∤ f²`). So the
entire interior mismatch ray of any hypothetical thick tiling is pinned to `b^f` out to length `f·b`,
uniform in `(e,f)` — the first *extended interior* forcing. The step that fails at `m ≥ 2` is the first
one (`Q ≡ em mod f`, so `j` may be negative): the genuine 44-tiling has base walk `aaaaccca`,
i.e. `j = −1`, and the 99-tiling has `aabbbbbbbcc`, i.e. `j = 2`. Both satisfy `R ≥ 1`. So the branch
is now reduced to the **thick regime `f ≤ 2e`**, where the smallest open members (`N = 59`, `(4,5)`)
sit; those are settled per value by the search engine.

`IsoAlphaPrime.lean` machine-checks, axiom-clean, the arithmetic core of the **correct replacement**
for Beeson III's Theorem 20 (base-`α` no-prime), whose proof depends on Theorem 19's `g ∣ M` — itself
unsound (its `bc³(a+c)` bookkeeping is false: with `c=g²` it carries `g⁷`), resting further on the
**false** squarefree half of Lemma 8 (counterexample tile `(4,15,16)`, `g=4`). The replacement needs
no `g ∣ M`: `isoalpha_X_forces` (side-integrality `X(2f+e) = M(f+e)f²` forces `(2f+e) ∣ M` by
coprimality) and `isoalpha_not_prime` (the reduced equation `N·d = m²(2e+d)Q`, `Q = e²+4ed+2d²`,
has `gcd(d,Q)=1`, so `N ∣ Q`, and cancelling `N` gives `d ≥ 2e+d` — absurd).

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
