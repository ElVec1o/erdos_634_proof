# A signed-direction invariant for triangle tilings, and the exclusion of primes ≡ 3 (mod 4)

**Author:** Vico Bonfioli — vicobonfioli@gmail.com
**Status:** preprint, not yet independently refereed.

This repository concerns Erdős Problem #634: for which `N` can some triangle be cut into `N`
pairwise-congruent triangles? A folklore conjecture holds that no prime `N ≡ 3 (mod 4)` with `N > 3`
occurs (the value `N = 3` does occur). The problem is recorded at
[erdosproblems.com/634](https://www.erdosproblems.com/634) (a $25 prize problem), where `N = 19` is
listed as a specific open instance.

By the classification of Laczkovich and the branch theorems of Beeson, the conjecture reduces to a
single branch: a tile with a `2π/3` angle on a non-equilateral triangle, where a prime count forces
the large triangle to be isosceles. Within that branch this work:

- introduces a translation-invariant, signed-direction tiling functional and uses it to prove that
  **no prime number of `2π/3` tiles tiles an isosceles triangle** — for *every* prime. For this case
  Beeson proved no tiling exists with `N < 36` and *explicitly left open whether N can be prime*
  (the smallest known tiling has 2673 tiles, due to Herdt); the invariant settles it;
- gives a self-contained reduction of the scalene shapes, showing each forces a composite `N`;
- completes the **prime case of the full problem**: a prime `p` is achievable **iff** `p = 2`,
  `p = 3`, or `p ≡ 1 (mod 4)` (constructions are classical; the exclusion is the theorem above);
- determines the **admissible spectrum** of each sporadic `2π/3` branch — for the isosceles
  target, writing `b = d·e²` with `d` squarefree, every count is `N = d·w²·(a+2b)` with
  `e | w(c−a−b)` — an outer bound on the realizable set (33 and 46 are admissible; no prime is);
- settles **every previously undetermined value up to 41**: no triangle can be cut into **14, 15,
  21, 22, 30, 33, 35, 38, or 39** congruent triangles — a complete branch sweep (published tiling
  equations, the spectra with a **parity refinement** M ≡ N (mod 2) of the invariant counts, and a
  new equilateral criterion `st = 3N` with `(t−s)² + 16N` square) reduces each value to
  uniquely-determined finite instances (22, 30 and 38 die by arithmetic alone), refuted by an
  exhaustive exact search (`code/engine/`, ten instances exhausted, validated on positive controls
  including a non-edge-to-edge tiling, all verdicts robust to disabling the strongest prune);
- proves the **lattice theorem**: the parity-refined spectrum of each isosceles tile is exactly
  `N = d(Eu)²(a+2b)` for an explicit lattice constant E — coinciding with Zhang's constructed
  family exactly when E = e, and exhibiting **admissible values beyond Zhang's families**
  (smallest: N = 354 on (11,24,31)), the new sharpest tests of sufficiency;
- excludes **N = 46**, previously the sharpest open test of Zhang's completeness conjecture,
  by the parity refinement — in agreement with the conjecture;
- proves **decidability**: membership in the tile-count set is algorithmically decidable (every
  branch reduces per-N to finitely many fully-determined instances, each settled by the provably
  complete search). The smallest undetermined values are now 42 and 44;

which together complete the exclusion of primes `≡ 3 (mod 4)` exceeding `3`, conditional on the
cited classification of the remaining branches. As a corollary, no triangle can be cut into 19
congruent triangles.

The **entire arithmetic and combinatorial layer** is machine-checked in Lean 4 + Mathlib (twenty-three
theorems, axiom-clean, no `sorry`): the eleven-shape enumeration, the isosceles branch end-to-end
(non-integrality obstruction, scale-pinning, and a master theorem combining the area equation with
the invariant's divisibility), the scalene compositeness, and the commensurable-branch exclusion of
primes ≡ 3 (mod 4). Only the geometry (the direction grid and the two invariant lemmas) is not
formalized — Mathlib has no dissection theory; those have written proofs in the paper backed by
numerical checks. The whole is offered for refereeing.

## The invariant in one line

Weight a directed edge of direction `θ = j·(π/3) + k·α` by `length · (−1)ʲ`. Since `f(θ+π) = −f(θ)`
and the weight is linear in length, interior edges cancel — even across non-edge-to-edge incidences,
where one long edge meets several shorter collinear ones. Hence the sum over tiles equals the same
functional on the boundary of `ABC`, and every tile contributes `±(c+a−b)`, so the boundary value is
an integer multiple of `c+a−b`. For an isosceles target this forces `(c−a−b)/√b ∈ ℤ`, which never
holds for a primitive triple with `c² = a² + ab + b²`.

## Contents

- `paper/erdos-634.tex`, `paper/erdos-634.pdf` — the paper.
- `code/verify_shapes.py` — the eleven shapes of `ABC` from the vertex enumeration, and the
  closed-form `N₀` of the scalene shapes with their compositeness (exact arithmetic).
- `code/verify_invariant.py` — the tile-value and cancellation lemmas, the role of the two
  invariants, the non-edge-to-edge cancellation, the non-integrality search, and the Herdt
  positive control.
- `code/verify_spectrum.py` — the prime dichotomy's achievability half, the scale structure
  `b | k² ⟺ de | k`, the isosceles admissible spectrum, and the `j`-classification.
- `code/verify_frontier.py` — the complete branch sweep for N = 14, 15 (every branch decided by
  exact finite computation; outputs the four surviving instances).
- `code/engine/` — the exhaustive exact search engine (advancing front over `ℚ(√D)`, provably
  complete corner-anchored branching, sound prunes): `python3 run_all.py validate` then
  `python3 run_all.py A|B|D|E` (or `noP2-A` etc. for the prune-robustness reruns).
- `lean/` — a Lean 4 + Mathlib proof of the entire arithmetic and combinatorial layer (twenty-three theorems), axiom-clean.

## How to verify

```bash
# combinatorial and numerical checks (needs python3 + sympy)
python3 code/verify_shapes.py        # eleven shapes; scalene N composite
python3 code/verify_invariant.py     # tile value; cancellation; non-integrality
python3 code/verify_spectrum.py      # prime dichotomy; admissible spectrum
python3 code/verify_frontier.py      # the N = 14, 15 branch sweep
( cd code/engine && python3 run_all.py validate && for i in A B D E; do python3 run_all.py $i; done )

# the arithmetic layer, machine-checked in Lean (needs elan/lake)
cd lean && lake exe cache get && lake build
```

## What is proven, cited, and machine-checked

- **Proven here (human-checked, in the paper):** the signed-direction invariant and its two
  geometric lemmas (cancellation, tile value); the reduction of the prime `2π/3` case to an
  isosceles target; the exclusion of every prime for the isosceles `2π/3` case; the scalene
  reduction.
- **Machine-checked (Lean 4 + Mathlib, twenty-three theorems, axiom-clean, no `sorry`):** the whole
  arithmetic and combinatorial layer — the eleven-shape enumeration (`shape_enumeration`); the
  isosceles branch end-to-end (`k_not_dvd_sum_sub`, `M_not_int`, `iso_reduction_identity`,
  `prime_count_forces_scale`, and the master theorem `no_prime_isosceles_count`); the scalene
  compositeness (`add_not_prime`, `F1_count_not_prime`–`F4_count_not_prime`); the
  commensurable-branch exclusion (`prime_three_mod_four_excluded`); the two-positive-squares
  decomposition (`prime_sum_two_pos_squares`); and the general-`N` admissibility theorem
  (`iso_admissible`).
- **Machine-checked (Python, exact arithmetic):** the eleven shapes; the `N₀` formulas and scalene
  compositeness; `a+b` never prime; the tile value `±(c+a−b)` over all orientations; the cancellation
  identity on explicit tilings; the non-edge-to-edge cancellation; zero counterexamples to the
  non-integrality over a large search; and, as a positive control, both necessary conditions hold on
  Herdt's genuine 2673-tile isosceles tiling (tile (5,3,7), k=27: N=2673 and M=−9 are integers).
- **Cited, not re-derived:** Laczkovich's classification of triangle tilings; Beeson's branch
  theorems (similar tile and right angle; `3α+2β=π`; the `γ=2α` isosceles tile; the equilateral
  no-prime theorem; the `N < 36` exclusion for the isosceles `2π/3` case); the Beeson–Zhang
  rationality theorem; and Zhang's constructions and conjecture for the `2π/3` shapes.

## Disclosure of AI assistance

This work was carried out by Vico Bonfioli in close collaboration with an AI system (Anthropic's
Claude). The AI proposed the signed-direction invariant, carried out the symbolic and numerical
verification, found the elementary non-integrality argument, and produced the Lean formalization and
drafts of the write-up, under the author's direction and review. The result is an exceptional claim whose
geometric lemmas rest on written proofs backed by numerical checks, not yet refereed; it should not
be regarded as established until checked by experts in the field.

## Key references

- M. Laczkovich, *Tilings of triangles*, Discrete Math. 140 (1995); *Tilings of convex polygons with
  congruent triangles*, Discrete Comput. Geom. 48 (2012).
- M. Beeson, the *Triangle Tiling* series and *Tilings of an isosceles triangle* / *Tiling an
  equilateral triangle* (arXiv:1206.2231, 1206.2229, 1206.1974, 1811.09723, 1812.07014).
- M. Beeson and Y. X. Zhang, *Rationality of certain triangle tilings*, arXiv:2604.01314.
- Y. X. Zhang, *Tiling triangles with 2π/3 angles*, arXiv:2512.22696.
- M. Beeson, M. Laczkovich and Y. X. Zhang, *Solution of Erdős Problem 633*, arXiv:2604.03609.

## License

Text (`paper/`): CC BY 4.0. Code (`code/`, `lean/`): MIT. See `LICENSE`.
