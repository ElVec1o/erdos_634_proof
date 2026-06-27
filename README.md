# A signed-direction invariant for triangle tilings, and the exclusion of primes ≡ 3 (mod 4)

**Author:** Vico Bonfioli — vicobonfioli@gmail.com
**Status:** preprint, not yet independently refereed.

This repository concerns Erdős Problem #634: for which `N` can some triangle be cut into `N`
pairwise-congruent triangles? A folklore conjecture holds that no prime `N ≡ 3 (mod 4)` occurs.
The problem is recorded at [erdosproblems.com/634](https://www.erdosproblems.com/634) (a $25 prize
problem), where `N = 19` is listed as a specific open instance.

By the classification of Laczkovich and the branch theorems of Beeson, the conjecture reduces to a
single branch: a tile with a `2π/3` angle on a non-equilateral triangle, where a prime count forces
the large triangle to be isosceles. Within that branch this work:

- introduces a translation-invariant, signed-direction tiling functional and uses it to prove that
  **no prime number of `2π/3` tiles tiles an isosceles triangle** — for *every* prime. Previously
  only a finite bound was known for this case (`N ≥ 2736`, Beeson), and Zhang's recent constructions
  had led to the conjecture that no prime occurs;
- gives a self-contained reduction of the scalene shapes, showing each forces a composite `N`;

which together complete the exclusion of primes `≡ 3 (mod 4)`, conditional on the cited
classification. As a corollary, no triangle can be cut into 19 congruent triangles.

The number-theoretic core is machine-checked in Lean 4 + Mathlib (axiom-clean, no `sorry`). The
geometric lemmas are verified numerically and are offered for refereeing.

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
  invariants, the non-edge-to-edge cancellation, and the non-integrality search.
- `lean/` — a Lean 4 + Mathlib proof of the arithmetic core (`k ∤ a+b−c`, i.e. `(c−a−b)/√b ∉ ℤ`),
  axiom-clean.

## How to verify

```bash
# combinatorial and numerical checks (needs python3 + sympy)
python3 code/verify_shapes.py        # eleven shapes; scalene N composite
python3 code/verify_invariant.py     # tile value; cancellation; non-integrality

# the arithmetic core, machine-checked in Lean (needs elan/lake)
cd lean && lake exe cache get && lake build
```

## What is proven, cited, and machine-checked

- **Proven here (human-checked, in the paper):** the signed-direction invariant and its lemmas; the
  reduction of the prime `2π/3` case to an isosceles target; the exclusion of every prime for the
  isosceles `2π/3` case; the scalene reduction.
- **Machine-checked (Lean 4 + Mathlib):** the arithmetic core `(c−a−b)/√b ∉ ℤ`
  (`lean/Erdos634.lean`, theorem `k_not_dvd_sum_sub`); axiom-clean.
- **Machine-checked (Python, exact arithmetic):** the eleven shapes; the `N₀` formulas and scalene
  compositeness; `a+b` never prime; the tile value `±(c+a−b)` over all orientations; the cancellation
  identity on explicit tilings; the non-edge-to-edge cancellation; zero counterexamples to the
  non-integrality over a large search.
- **Cited, not re-derived:** Laczkovich's classification of triangle tilings; Beeson's branch
  theorems (similar tile and right angle; `3α+2β=π`; the `γ=2α` isosceles tile; the equilateral
  no-prime theorem; the finite lower bound for the isosceles `2π/3` case); the Beeson–Zhang
  rationality theorem; and Zhang's constructions and conjecture for the `2π/3` shapes.

## Disclosure of AI assistance

This work was carried out by Vico Bonfioli in close collaboration with an AI system (Anthropic's
Claude). The AI proposed the signed-direction invariant, carried out the symbolic and numerical
verification, found the elementary non-integrality argument, and produced the Lean formalization and
drafts of the write-up, under the author's direction and review. The result is an exceptional claim
resting on geometric lemmas that are here verified only numerically; it should not be regarded as
established until checked by experts in the field.

## Key references

- M. Laczkovich, *Tilings of triangles*, Discrete Math. 140 (1995); *Tilings of convex polygons with
  congruent triangles*, Discrete Comput. Geom. 38 (2012).
- M. Beeson, the *Triangle Tiling* series and *Tilings of an isosceles triangle* / *Tiling an
  equilateral triangle* (arXiv:1206.2231, 1206.2229, 1206.1974, 1811.09723, 1812.07014).
- M. Beeson and Y. X. Zhang, *Rationality of certain triangle tilings*, arXiv:2604.01314.
- Y. X. Zhang, *Tiling triangles with 2π/3 angles*, arXiv:2512.22696.
- M. Beeson, M. Laczkovich and Y. X. Zhang, *Solution of Erdős Problem 633*, arXiv:2604.03609.

## License

Text (`paper/`): CC BY 4.0. Code (`code/`, `lean/`): MIT. See `LICENSE`.
