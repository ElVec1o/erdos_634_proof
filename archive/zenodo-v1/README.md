# A resolution of the prime case of Erdős Problem #634

**Author:** Vico Bonfioli
**Status:** preprint / submitted for peer review — *not yet independently refereed.*

This repository contains a proposed proof that **no prime `N ≡ 3 (mod 4)` is a number of
congruent triangles into which some triangle can be cut** — the open ("folklore") conjecture
recorded at [erdosproblems.com/634](https://www.erdosproblems.com/634) (the $25 prize problem;
the database also lists `N = 19` as a specific open instance, which follows as a corollary).

## The idea in one line

Within the only branch of Laczkovich's classification not previously closed for primes — a tile
with a `2π/3` angle on a non-equilateral triangle — a *prime* count forces the large triangle to be
**isosceles**. We introduce a translation-invariant, **T-junction–proof** signed-direction tiling
invariant `Φ`: a directed edge of direction `θ = j·(π/3)+k·α` is weighted `length·(−1)ʲ`. Because
`f(θ+π) = −f(θ)` and the weight is **linear in length**, interior edges cancel even across
non-edge-to-edge T-junctions (a long c-edge equals the sum of the shorter edges it overhangs), so
`Σ_tiles C(tile) = Φ(∂ABC)`. Every tile contributes `±V₀` with `V₀ = c+a−b`, hence
`Φ(∂ABC) = M·V₀` with **`M` a signed tile count, an integer**. For an isosceles target this forces

> `M = (c − a − b)/√b`,  which is **never an integer** for a primitive 120°-triple.

So no such tiling exists. The invariant succeeds where Beeson's colouring fails (it needs no
2-colouring, which the `2π/3` tile does not admit).

## What is in this repo

- `paper/erdos-634.md` — the full paper (Theorems A–E, the classification assembly, references).
- `proof/phi-invariant-proof.md` — the self-contained proof of the central Theorem E with the
  elementary number-theoretic lemma.
- `proof/reviewers-and-journals.md` — suggested expert validators and submission venues.
- `code/` — machine-verification (Python/SymPy exact arithmetic; one Rust tiling solver):
  `phi_invariant.py` validates the invariant on explicit tilings, confirms `C = ±V₀` over all
  orientations, and checks the non-integrality; the others verify the classification/reduction.
- `lean/Erdos634.lean` — a **machine-checked (Lean 4 + Mathlib)** proof of the arithmetic core
  (`k ∤ (a+b−c)`, i.e. `M ∉ ℤ`); axiom-clean, no `sorry`.

## How to verify

```bash
# combinatorial / numeric checks (needs python3 + sympy)
python3 code/phi_invariant.py            # invariant validated on real tilings; M non-integer
python3 code/shape_completeness.py        # the 11 ABC shapes
python3 code/gamma_orientation_closure.py # auxiliary closures

# the arithmetic core, machine-checked in Lean (needs elan/lake)
cd lean && lake exe cache get && lake build
```

## What is proven vs. cited vs. machine-checked

- **Proven here (human-checked, in the paper):** the Φ-invariant and its two lemmas; the reduction
  of the prime case to the isosceles `2π/3` tile; Theorem E; the assembly over Laczkovich's branches.
- **Machine-checked (Lean):** the number-theoretic core `M = (c−a−b)/√b ∉ ℤ`.
- **Machine-checked (Python/Rust):** the invariant identity on explicit tilings, `C = ±V₀` over all
  orientations, the shape enumeration, and `0` counterexamples to the non-integrality up to
  `c ≈ 9·10⁶`.
- **Cited, not re-derived:** Laczkovich's classification of triangle tilings (1995, 2012); the
  Beeson–Zhang rationality theorem (integer-sided `2π/3` tile); and Beeson's equilateral
  no-prime theorem (the only borrowed step inside the `2π/3` branch).

## Disclosure of AI assistance

This work was carried out by **Vico Bonfioli** in close collaboration with an **AI system
(Anthropic's Claude)**. The AI proposed the key Φ-invariant, carried out the symbolic and numeric
verification, found the elementary non-integrality argument, and wrote the Lean formalization and
the first drafts of the write-up, under the author's direction and review. All claims are presented
for **independent human peer review**; the result should not be regarded as established until it has
been checked by experts in the field (see `proof/reviewers-and-journals.md`).

## License

Text (`paper/`, `proof/`): CC BY 4.0. Code (`code/`, `lean/`): MIT. See `LICENSE`.
