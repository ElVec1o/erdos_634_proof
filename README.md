# A signed-direction invariant for triangle tilings, and the exclusion of primes ≡ 3 (mod 4)

**Author:** Vico Bonfioli — vicobonfioli@gmail.com
**Status:** preprint, not yet independently refereed.

Erdős Problem #634: for which `N` can some triangle be cut into `N` pairwise-congruent triangles?
A folklore conjecture holds that no prime `N ≡ 3 (mod 4)` with `N > 3` occurs (the value `N = 3`
does occur). The problem is recorded at [erdosproblems.com/634](https://www.erdosproblems.com/634),
where `N = 19` is listed as a specific open instance.

By the classification of Laczkovich and the branch theorems of Beeson, the prime problem reduces to a
single active branch: a tile with a `2π/3` angle on a non-equilateral triangle, where a prime count
forces the large triangle to be isosceles.

## Main results

- A translation-invariant, signed-direction tiling functional proves that **no prime number of `2π/3`
  tiles tiles an isosceles triangle**, for *every* prime. For this case Beeson proved no tiling exists
  with `N < 36` and explicitly left open whether `N` can be prime (the smallest known tiling has 2673
  tiles, due to Herdt); the invariant settles it.

- A self-contained reduction of the scalene shapes shows each forces a composite `N`. For the
  `3α+2β = π` branch, four of its five targets are excluded by machine-checked arithmetic: the two
  scalene targets (cores of Beeson Thms 8, 12), and the base-`(α+β)` and base-`α` targets by
  Propositions that **replace Beeson Thms 18 and 20**, whose printed proofs are unsound.

- **Theorem (prime exclusion, with one explicit exception).** No prime `N ≡ 3 (mod 4)`, `N > 3`,
  which is not a base-`β` candidate — i.e. `N ≠ 3f² − e²` for all coprime `1 ≤ e < f` — is a number of
  congruent triangles into which a triangle can be cut. In particular **no triangle can be cut into 19
  congruent triangles** (`19` is not of the exceptional form).

- **The exception is genuine, and it is one congruence class.** The prime base-`β` candidates
  `N = 3f² − e²` are **exactly the primes `≡ 11 (mod 12)`** (`11, 23, 47, 59, 71, 83, 107, …`;
  machine-checked in `lean/BaseBetaMod12.lean`). Equivalently, **every prime `≡ 7 (mod 12)` is
  excluded unconditionally** — half of all primes `≡ 3 (mod 4)` — and `19 ≡ 7 (mod 12)`. The `≡ 11`
  candidates satisfy every *sound* necessary condition; the only
  published exclusion, Beeson's Theorem 14, rests on a divisibility `g | M` that is **false** — refuted
  by an explicit `99`-tiling of the `(24,24,33)` triangle by `(2,3,4)` tiles. These candidates are
  settled individually by exact search. Six are settled — `11, 23, 47, 59, 71, 107` — **all by
  search, none by theorem**; `83` was under search. There are `42` candidates below `1000`. See the paper's `rem:isobeta`, `rem:thm14false`, and
  `rem:mainscope`.

- **Realizations, machine-verified with zero axioms.** A triangle can be cut into **28** and into
  **44** congruent triangles (`lean/Tiling28.lean`, `lean/Tiling44.lean`, kernel-only, `#print axioms`
  reports none). The `44`-tiling of the `(16,16,22)` isosceles triangle by the `(2,3,4)` tile is the
  smallest known tiling in an incommensurable branch (previous record `1215`).

- The **admissible spectrum** of each sporadic `2π/3` branch is determined (necessary side); for the
  isosceles target, with `b = d·e²` and `d` squarefree, every count is `N = d·w²·(a+2b)` with
  `e | w(c−a−b)`, and the counts passing all invariant conditions on the isosceles and `F₁` targets are
  exactly Zhang's constructed families. The equilateral square criteria reduce to elementary divisor
  conditions on `16N²`. Membership in the tile-count set is decidable.

- **The contiguous initial segment of the spectrum is every `N ≤ 69`.** The last two gaps below `70`
  — `59` (prime) and `66` — were closed by exhaustive search (1,838,175 and 7,232,464 nodes). `70` is
  the sole remaining gap below `80`; `71–80` are settled, so the record extends to `≤ 80` once it
  resolves. (`28, 44, 77, 80` are realizable.)

## What is open

The **whole** base-`β` branch at `m = 1` has no sound general exclusion — thin (`f > 2e`) and thick
alike. Of the 42 prime candidates below `1000`, 19 are thin and 23 thick, and only six are settled,
all by exhaustive search. An earlier version of this README said the thin regime was understood;
that was wrong. The interior structure of any hypothetical such tiling is pinned
(`lean/BaseBetaWalks.lean`: the boundary-walk classification, the apex-mismatch theorem, and the
alignment theorem, which forces the mismatch apex ray to `b^f`), but a general no-go is not yet proved.
Zhang's sufficiency conjecture and the equilateral general realizability laws are open in the
literature. See `HANDOFF.md` for a complete account of the state of the research.

## The invariant in one line

Weight a directed edge of direction `θ = j·(π/3) + k·α` by `length · (−1)ʲ`. Since `f(θ+π) = −f(θ)`
and the weight is linear in length, interior edges cancel — even across non-edge-to-edge incidences.
Hence the sum over tiles equals the same functional on the boundary of `ABC`, and every tile
contributes `±(c+a−b)`, so the boundary value is an integer multiple of `c+a−b`. For an isosceles
target this forces `(c−a−b)/√b ∈ ℤ`, which never holds for a primitive triple with `c² = a² + ab + b²`.

## Contents

- `paper/erdos-634.tex`, `paper/erdos-634.pdf` — the paper.
- `lean/` — a Lean 4 + Mathlib formalization of the arithmetic and combinatorial layer, across eighteen
  files (138 theorems, no `sorry`, axiom-clean) (axiom-clean, no `sorry`); `lean/README.md` describes every theorem. The two `Tiling*.lean`
  certificates are kernel-only (no Mathlib) and report no axioms.
- `engine/` — the exact corner-anchored search engine (C++ with GMP, the Python reference
  implementation, instance builders) and `engine/tilings/` with the verified 28-, 44- and 99-tiling
  certificates.
- **`STATUS_TABLE.md` — the ledger: what is proved, what is cited, what is open, what was
  once overclaimed, and what is a known dead end. READ THIS FIRST.**
- `HANDOFF.md` — operational detail: what was done, banked, and left to do.
- `archive/zenodo-v1/` — the superseded earlier Zenodo/referee package, kept for provenance.
  It contains a **false claim** that the folklore conjecture was resolved; see
  `archive/zenodo-v1/SUPERSEDED.md`.

## How to verify

```bash
# combinatorial and numerical checks (needs python3 + sympy)
# the arithmetic layer, machine-checked in Lean (needs elan/lake; Lean 4.30.0, Mathlib v4.30.0)
cd lean && lake exe cache get && lake build
```

## Scope of the formalization

The **arithmetic and combinatorial** layer is machine-checked in Lean (`#print axioms` reports only
`propext, Classical.choice, Quot.sound`, or fewer). The **geometric** layer — that a tiling yields the
stated Diophantine equations and vertex-angle relations — rests on the written proofs in the paper, as
Mathlib has no theory of triangle dissections. This caveat applies uniformly to every result.

## Corrections to the cited literature

The base-`β`/base-`α` no-prime theorems of Beeson III are relied on nowhere in this work, because they
are unsound: Theorem 14 (`g | M`) is false (refuted by the `99`-tiling); Theorems 18, 19, 20 have the
same defect; the squarefree half of Lemma 8 is false (counterexample tile `(4,15,16)`). The paper
supplies correct replacements for the base-`(α+β)` and base-`α` targets and documents the base-`β` gap
honestly. Beeson's isosceles `2π/3` paper and the scalene cores (Thms 8, 12) are sound and are used.

## Disclosure of AI assistance

This work was carried out by Vico Bonfioli in collaboration with an AI system (Anthropic's Claude),
under the author's direction and review. It is an exceptional claim whose geometric lemmas rest on
written proofs backed by numerical checks, not yet refereed; it should not be regarded as established
until checked by experts.

## Key references

- M. Laczkovich, *Tilings of triangles*, Discrete Math. 140 (1995); *Tilings of convex polygons with
  congruent triangles*, Discrete Comput. Geom. 48 (2012).
- M. Beeson, the *Triangle Tiling* series and *Tilings of an isosceles triangle* / *Tiling an
  equilateral triangle* (arXiv:1206.2231, 1206.2229, 1206.1974, 1811.09723, 1812.07014).
- M. Beeson and Y. X. Zhang, *Rationality of certain triangle tilings*.
- Y. X. Zhang, *Tiling triangles with 2π/3 angles*.
- M. Beeson, M. Laczkovich and Y. X. Zhang, *Solution of Erdős Problem 633*.

## License

Text (`paper/`): CC BY 4.0. Code (`code/`, `lean/`): MIT. See `LICENSE`.
