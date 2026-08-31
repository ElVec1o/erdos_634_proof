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

## Where the open case stands

The residue is the primes `≡ 11 (mod 12)`, and `GOAL_PRIMES.md` maps it: since a prime `N` forces
`m = 1`, the open case **is** the `m = 1` base-`β` family, splitting `e = 1` / `e ≥ 2`, both reducing
to one crossing question that nine tool classes provably cannot answer (each is invariant under
*relocating* an edge, while the question asks *where* an edge lies).

For `e = 1` the shorter route is `conj:advance`, which if proved closes the branch entirely. Its two
gaps are now one: the double-`c` gap is closed at every block length (`prop:doublec`), and the
remaining gap reduces to a single question — what covers a segment `[V, E]` of length exactly `a`.
That question's chain is machine-checked (`lean/Erdos634/RouteOne.lean`, companion §"Route 1's chain,
formalised"): the flank at `V` lies along the line, a `b`- or `c`-edge would contain `E` strictly and
so dies by the very blocking whose failure defined the escape, and the surviving `a`-advance is a
descent that terminates after finitely many wall edges. What remains unproved is the instantiation of
two hypotheses at the escape configuration itself (`rem:routeoneopen`). The chain is a proof *given*
the configuration, not yet a proof about it.


## Main results

- A translation-invariant, signed-direction tiling functional proves that **no prime number of `2π/3`
  tiles tiles an isosceles triangle**, for *every* prime. For this case Beeson proved no tiling exists
  with `N < 36` and explicitly left open whether `N` can be prime (the smallest known tiling has 2673
  tiles, due to Herdt); the invariant settles it.

- A self-contained reduction of the scalene shapes shows each forces a composite `N`. For the
  `3α+2β = π` branch, four of its five targets are excluded by machine-checked arithmetic: the two
  scalene targets (cores of Beeson Thms 8, 12), and the base-`(α+β)` and base-`α` targets by
  Propositions that **replace Beeson Thms 18 and 20**, whose printed proofs are unsound.

- **Theorem (full prime exclusion).** No prime `N ≡ 3 (mod 4)`, `N > 3`, is a number of congruent
  triangles into which a triangle can be cut. The non-base-`β` primes are excluded by the invariant
  and branch arguments of the main paper; the base-`β` primes (`≡ 11 mod 12`) are excluded by the
  forcing chain of the companion note (walk trichotomy, corner/partner/strip forcing, the surplus
  lattice, the column–filler recursion, the feet budget, the `T_mid` and pentagon kills), with every
  arithmetic component kernel-checked in Lean and the smallest members confirmed by certified
  exhaustive refutations. In particular **no triangle can be cut into 19 congruent triangles**.

- **The exception is genuine, and it is one congruence class.** The prime base-`β` candidates
  `N = 3f² − e²` are **exactly the primes `≡ 11 (mod 12)`** (`11, 23, 47, 59, 71, 83, 107, …`;
  machine-checked in `lean/BaseBetaMod12.lean`). Equivalently, **every prime `≡ 7 (mod 12)` is
  excluded unconditionally** — half of all primes `≡ 3 (mod 4)` — and `19 ≡ 7 (mod 12)`. The `≡ 11`
  candidates satisfy every *sound* necessary condition; the only
  published exclusion, Beeson's Theorem 14, rests on a divisibility `g | M` that is **false** — refuted
  by an explicit `99`-tiling of the `(24,24,33)` triangle by `(2,3,4)` tiles. These candidates are
  settled individually by exact search. **Thirteen are settled** — `11, 23, 26, 47, 59, 66, 71, 107,
  191, 431, 587, 971, 1451` — **all by certified exhaustive search, none by theorem**. Each carries a
  coverage certificate (`code/analysis/verify_sweep.py`) proving every escaping base word is
  exhausted or has an exhausted mirror; `N = 1451` (`f = 22`) is 168 of 168 orbits at both proved
  reaches. There are `42` candidates below `1000`. See the paper's `rem:isobeta`, `rem:thm14false`,
  and `rem:mainscope`.

- **Realizations, machine-verified with zero axioms.** A triangle can be cut into **28**, into
  **44**, into **77** and into **99** congruent triangles (`lean/Tiling28.lean`,
  `lean/Tiling44.lean`, `lean/Tiling77.lean`, `lean/Tiling99.lean`, kernel-only, `#print axioms` reports none). The `44`-tiling of the
  `(16,16,22)` isosceles triangle by the `(2,3,4)` tile is the smallest known tiling in an
  incommensurable branch (previous record `1215`). The `99`-tiling of `(24,24,33)` is the object
  that refutes Beeson's Theorem 14, so that refutation now rests on a kernel-checked certificate
  (99 congruences over `ℤ[√15]`, containment, 4851 separating edge-lines, exact area sum) rather
  than on a search log.

- **The invariant product.** The two signed-direction counts are not independent conditions: on each
  of the eleven `2π/3` target shapes, `M_α·M_β` is a fixed rational multiple of `N` — `3N` on the
  equilateral target, exactly `N` on the tile-similar and `F₁` targets, and an explicit rational
  multiple otherwise. Two consequences need **no rationality input**: the tile-similar target forces
  `N = M_α²` (a perfect square, never prime), and the `F₁` target forces `a/c = (N−1)/(N+1)` for
  prime `N`, hence an irrational tile, which a boundary-walk argument then kills. This removes the
  rationality dependence from three of the eleven shapes; the other eight still carry it.

- The **admissible spectrum** of each sporadic `2π/3` branch is determined (necessary side); for the
  isosceles target, with `b = d·e²` and `d` squarefree, every count is `N = d·w²·(a+2b)` with
  `e | w(c−a−b)`, and the counts passing all invariant conditions on the isosceles and `F₁` targets are
  exactly Zhang's constructed families. The equilateral square criteria reduce to elementary divisor
  conditions on `16N²`. Membership in the tile-count set is decidable.

- **The contiguous initial segment of the spectrum is every `N ≤ 80`, with no exception.** The gaps
  `59` (prime), `66` and finally `70` were each closed by exhaustive search (1,838,175 / 7,232,464 /
  **134,631,158** nodes). `N = 70` was the last: its single surviving instance is the
  isosceles-`α` target `(45,45,70)` of the tile `(6,5,9)`, which passes every sound necessary
  condition and whose published exclusion rested on Beeson III Thm 19's unsound `g | M`; the search
  settles it directly. (`28, 44, 77, 80` are realizable.)

## What is open

**The base-`β` exclusion is not proved.** An adversarial audit of the companion's forcing chain
found that every path through it terminates in a deferral, and the missing step is now isolated
and stated as an explicit hypothesis (companion, Hypothesis (walls)): *in a base-`β` tiling at
`m = 1`, neither base corner is starved or broken.* Both papers are conditional on it, and the
folklore conjecture is open.

What is proved of the hypothesis:

- `e = 1` (thin members): it holds for `f ≤ 6`, that is for `N = 11, 26, 47, 74, 107`.
- `e ≥ 2` (thick members): the base admits only two columns at every member with `f > 2e` — a
  weaker hypothesis than separation, which is `f > (1+√2)e` — by a sharp criterion for the extra
  close-pair columns. Reducing those two to the walls form needs the corner chain, whose induction
  is **not** established at `e ≥ 2`: its step applies straight-junction arithmetic at a vertex that
  is interior for `k ≥ 1`, where the residue is `π + α` rather than `α`. Under Hypothesis (walls)
  the walls form follows in two lines instead, so every downstream use is unaffected; unconditionally
  it holds at `e = 1` only.
- Seven members are settled by independent certified exhaustion of the full `m = 1` target:
  `N = 11, 23, 26, 39, 71, 74, 107`. `N = 146` (the member `(1,7)`) is settled by the same engine
  with the `γ`-trap and corner-type prunes enabled; that certificate depends on the reduction
  theorem those prunes encode, so it is not independent of the theory in the way the other seven are.
- Of the two escapes that the advance-and-collide conjecture names at `e = 1`, the second — an
  initial side `c`-block of length `≥ 2` — is closed for every `f ≥ 3` and every block length.
  The first, a deviating `a`-run whose new `c`-chord ends beyond the forced region, is open, and
  its escape is now known to hold uniformly in `f`: the chord's endpoint overshoots the blocking
  edge by exactly one `a`, so no threshold in `f` closes it and the blocking must be recovered
  another way.
- Close pairs `f ≤ (1+√2)e` are not excluded, but the columns that survive the unconditional
  filters are now described in closed form: writing the base `b`-count as `y = e + kf`, the base
  equation reduces to `xe + zf = 2ef − k(f²−e²)`, `x` is pinned modulo `f`, `k` is bounded by
  `(2ef−3e−f)/(f²−e²)`, and each admissible `k` carries exactly one column.
- The `W`-tower behind the corner chain at `e ≥ 2` (every scale-`k` inflation standard) is now
  attacked in the plane rather than on the chord. Its single open obstruction — the two-sided
  rogue chord at slots `⌊f/e⌋+2 ≤ M ≤ k−2`, whose one-dimensional word system provably cannot
  close (`swap_fits`) — dies on both flanks by closed form. On the `c`-side `AB`: the row-side
  fan at the chord's first breakpoint has total room `(M−1)b`, killing `M = 3` at every member
  and every slot with `(M−1)(f²−e²) < f²`, uniformly in the scale (`RogueFan.lean`, axiom-clean).
  On the `a`-side `BC` — the mirror, new: the second chord from the slot runs parallel to `AB`
  and exits through the `BC`-subdivision vertex at distance `Ma` from `B`
  (`E = Y + (k−M)c·u = C + (k−M)a·v̂`, the exact mirror of `X − (M−1)b·w = B/k ∈ AB`); its
  corridor is floored by the forced row's staircase, its row side can only break at `{c, 2c}`,
  and its rogue side can neither break at `c` nor sum to `(k−M)c` when `k − M < e`: **slot
  `M = k−2` dies at every member with `e ≥ 3`, and `M = k−3` at every member with `e ≥ 4`,
  uniformly in `f`** (`RogueMirror.lean`, axiom-clean; identity layer verified from scratch,
  13,603 exact checks, `f ≤ 12`; the criterion is exact — at `k − M = e` the all-`a` word `a^f`
  flushes and the local structure is genuinely consistent). A soundness audit of the patch
  engine found that its exact-π straight-gap branching used a non-exhaustive flat list — the
  recorded fix path — so every engine kill that passed through such a branch has been retracted;
  the engine now enumerates flats exhaustively whenever the line's contact origin is pinned and
  defers otherwise, and the whole campaign was re-certified from scratch with the fixed engine.
  The re-certified matrix, the theorem-layer coverage, and the exact residual set of open
  `(M, k)` pairs per member: `code/patch_results.txt` and `code/zfan_criterion_table.txt`.
  The forced-row input itself is now scoped exactly: the base side of a scale-`k` inflation is
  `b^k` by arithmetic for `k < f` (`Inflation.b_side_rigid`, with `c_side_no_b` for the `c`-side),
  while at the wall scale `k = f` the whole family `a^{(j+1)f−e}c^{f−(j+1)e}` also solves the base
  equation (`RogueMirror.base_side_wall_family`), so wall-scale kills are conditional on the `b^f`
  reading of the target's base word.

What remains open: the hypothesis in general — the side condition at `e ≥ 2`, the residual
configurations at `e = 1` (route 1 above), and the close pairs, an infinite family that contains
`N = 83` and `N = 131`. No boundary-word argument can settle the close pairs: the base word's
composition, its congruences, its junction figures and the `γ`-injection are all exhausted, so the
bound on `y` must come from the interior. Also open: **external refereeing of the whole work** (an
exceptional claim; see the disclosure below); Zhang's sufficiency conjecture and the equilateral
realizability laws, which are independent of the prime question. Composite `N` realizability remains
a rich open area.

## The invariant in one line

Weight a directed edge of direction `θ = j·(π/3) + k·α` by `length · (−1)ʲ`. Since `f(θ+π) = −f(θ)`
and the weight is linear in length, interior edges cancel — even across non-edge-to-edge incidences.
Hence the sum over tiles equals the same functional on the boundary of `ABC`, and every tile
contributes `±(c+a−b)`, so the boundary value is an integer multiple of `c+a−b`. For an isosceles
target this forces `(c−a−b)/√b ∈ ℤ`, which never holds for a primitive triple with `c² = a² + ab + b²`.

## Contents

- `paper/erdos-634.tex`, `paper/erdos-634.pdf` — the paper.
- `lean/` — a Lean 4 formalization of the arithmetic and combinatorial layer: 47 files, 408 theorems, no `sorry`, **all verified**. 20 files are dependency-free and check with plain `lean <file>` (every tiling certificate and every combinatorial core); the other 18 pin Mathlib v4.30.0 and were checked with `lake env lean` against a local build of that revision. Axioms are `propext`, `Quot.sound`, and `Classical.choice` where `omega` introduces it. `lean/README.md` gives the per-file status and `lean/PAPER_MAP.md` maps every numbered statement of the papers to its Lean declaration, or states why none exists.
  `Tiling*.lean`/`PgramTiling*.lean` certificates and `Collar.lean` are kernel-only (no Mathlib) and report no axioms.
- `code/` — exact-arithmetic verification scripts for the paper's finite and symbolic claims.
- `code/engine/` — the exact corner-anchored search engine (C++ with GMP, the Python reference
  implementation, instance builders) and `code/engine/tilings/` with the verified 28-, 44-, 77- and 99-tiling
  certificates.
  An `e = 1` exclusion sweep is run with `code/engine/run_sweep.sh <f> <engine> [cap]`, which takes
  its instance list from `code/analysis/sweep_configs.py` (one representative per mirror orbit at
  the proved reach) and ends by calling `code/analysis/verify_sweep.py` on its own log, so a sweep
  that misses an orbit fails loudly instead of reporting completion. Sweeps must be run this way:
  the ad hoc drivers it replaces piped their lists into a bare `while read`, which drops a final
  line carrying no newline, and that silently cost one orbit in each of the `f = 14` and `f = 18`
  sweeps.
- `archived/` — superseded material kept for provenance only, and **not part of the work**: the
  earlier Zenodo/referee package (which contains a **false claim** that the folklore conjecture was
  resolved; see `archived/zenodo-v1/SUPERSEDED.md`) and the previous handoff document, two of whose
  claims are known wrong. Excluded from any repository release.

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
