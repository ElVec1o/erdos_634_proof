> **NOTE (2026-07-19).** `STATUS_TABLE.md` in this folder supersedes this file as the
> top-level ledger. Two claims previously made here are now known to be wrong and are
> corrected there: the thin regime (`f > 2e`) of base-`β` is **not** closed structurally,
> and the far-side chase is a **closed branch**, not a live next action.

# Erdős Problem #634 — research handoff

This document is the single source of truth for the state of this project. It is written for a
mathematician or agent picking the work up cold. Read it in full before touching the paper, the Lean,
or the search engine.

---

## 1. The problem

**Erdős #634.** For which integers `N` can *some* triangle be cut into `N` pairwise-congruent
triangles?

Two directions:
- **Existence (easy side).** For most `N` a construction exists. `N = 2` (drop the altitude of a right
  isosceles triangle), `N = 3` (join the centroid of an equilateral triangle to its vertices), any
  perfect square `N = k²` (the `k²`-subdivision), and `N = e² + f²` for a right triangle with legs
  `e, f`. Erdős Problem #633 (square number of tiles) was settled by Beeson–Laczkovich–Zhang.
- **Non-existence (hard side).** Showing a given `N` is *not* achievable requires ruling out every
  tiling. This is the content of this project.

**Laczkovich's classification** (1995, 2012), organized by Beeson across several papers, reduces any
triangle tiling to a finite list of *tile shapes* and *target shapes*. For a **prime** number of
tiles, every branch of the classification is excluded by some existing theorem **except one**: a tile
with a `2π/3` angle tiling a non-equilateral triangle. The `2π/3` case is Zhang's; it splits into six
sporadic similarity types plus an isosceles family.

**The headline result of this project** (paper Theorem 1, `thm:main`): with one explicit exception,
no prime `N ≡ 3 (mod 4)`, `N > 3`, is a number of congruent triangles. In particular no triangle can
be cut into **19** congruent triangles (`19` is prime, `≡ 3 mod 4`, and not of the exceptional form).

---

## 2. The one genuine gap, and why it exists

The exception in Theorem 1 is the **base-β target of the `3α+2β = π` branch**. This is the whole open
frontier of the prime problem and the focus of all recent work.

### The base-β setup (memorize this — everything below uses it)

The primitive `3α+2β = π` tile is
```
(a, b, c) = (ef, f² − e², f²),   1 ≤ e < f,  gcd(e,f) = 1.
```
- `a` is opposite `α`, `b` opposite `β`, `c` opposite `γ`, where `γ = (π+α)/2`, `β = (π−3α)/2`.
- `cos α = (2f²−e²)/(2f²)`, `sin(α/2) = e/(2f)`. **`α/π` is irrational for every valid `(e,f)`**
  (Niven's theorem; machine-checked, no Laczkovich citation needed — see `BaseBetaE1.lean`).
- **Edge–vertex incidence** (used constantly): edge `a` joins the `β`- and `γ`-corners; edge `b`
  joins the `α`- and `γ`-corners; edge `c` joins the `α`- and `β`-corners.

The base-β **target** is isosceles with base angles `β`, apex angle `3α`, scaled by `m ∈ ℤ≥1`:
```
equal sides  X = f³ m,   base  Y = e m (3f² − e²),   number of tiles  N = m² (3f² − e²).
```
**`N` is prime exactly when `m = 1`.** So the prime question lives entirely at `m = 1`, where
`N = 3f² − e²`. These candidate counts are exactly the integers of the form `3f² − e²` with
`gcd(e,f)=1`, `1 ≤ e < f`; the **prime** ones are exactly the primes **`≡ 11 (mod 12)`** (machine-checked,
`BaseBetaMod12.lean`); composite candidates with `e,f` both odd are `≡ 2 (mod 4)` (e.g. 26, 66, 74).
Equivalently **every prime `≡ 7 (mod 12)` is excluded unconditionally**. The smallest prime candidates are
```
11, 23, 47, 59, 71, 83, 107, 131, 167, 179, 191, …
```

### Why the gap is genuine

Beeson's Theorem 14 (base-β no-prime) asserts a divisibility `g | M` (with `g = gcd(a,c) = f`, `M` the
"coloring number" `= (f+e)m`). **This is false.** A concrete `99`-tiling of the `(24,24,33)` triangle
by `99` copies of `(2,3,4)` — `(e,f,m) = (1,2,3)`, `g = 2`, `M = 9`, `g ∤ M` — refutes it directly
(the tiling is in `engine/tilings/tiling_99_isobeta_24_24_33.txt`, independently verified). Beeson's
Theorems 18, 19, 20 have the same defect; Lemma 8's "squarefree" half is also false (counterexample
tile `(4,15,16)`, `g = 4`). See paper `rem:thm14false` and `rem:isobeta`.

Consequence: **the base-β candidates pass every *sound* necessary condition** (integrality of `X, Y`,
parity, range), and there is no correct general exclusion in the literature. This project settles
individual members by exhaustive search and is trying to build a correct general proof.

---

## 3. What is BANKED (machine-checked, axiom-clean Lean)

All Lean files are in `lean/`. Every listed theorem compiles with `#print axioms` reporting only
`[propext, Classical.choice, Quot.sound]` (or a subset) — i.e. **no `sorry`, no custom axioms**. The
geometric layer of the proof (that a tiling yields these Diophantine equations, angle-sums at
vertices, etc.) is **not** formalized — Mathlib has no theory of triangle dissections — and rests on
the written paper. This scope caveat applies uniformly to every result; it is not a defect in the
arithmetic.

Build: `cd lean && lake exe cache get && lake build` (Lean 4.30.0, Mathlib v4.30.0). A single file
checks in isolation with `lake env lean <File>.lean`. **Do not run parallel Lean builds — they OOM.**

### The prime dichotomy, four of five `3α+2β` targets (sound)
- **`Beeson3NotPrime.lean`** — scalene targets. `triquadratic_not_prime` (Beeson Thm 8 core: the
  `(2α,β,α+β)` target has no prime `N`), `fourcomp_not_prime` (Beeson Thm 12 core: the `(2α,α,2β)`
  target forces `N = (2f²−e²)(3f²−e²)k²`, composite), `prime_mul_sq_ne` (exponent-parity descent).
  `isobeta_square_not_prime` is a *true* implication but its hypothesis is **not** a genuine iso-β
  necessity — it is annotated "do not use as an iso-β exclusion" and is kept only as a descent lemma.
- **`BaseAlphaBetaPrime.lean`** — base-`(α+β)` target, replacing Beeson Thm 18 (whose printed mod-`N`
  step is unsound). `gcd_dvd_two`, `base_obstruction`, `base_alphabeta_not_prime`. Uses no `g | M`.
- **`IsoAlphaPrime.lean`** — base-`α` target, replacing Beeson Thm 20 (which depends on the unsound
  Thm 19). `isoalpha_X_forces`, `isoalpha_not_prime`. Uses no `g | M`.

### The base-β target (the open one): structural results, all m=1 unless noted
- **`BaseBetaE1.lean`** (7 theorems) — the `e = 1` foundation. `tile_alpha_irrational` (Niven, replaces
  Laczkovich for this branch), the vertex-figure enumeration (`vertex_pi`, `vertex_beta_corner`,
  `vertex_apex`), `base_composition_e1`, and `direction_free` / `colouring_well_defined` (the coloring
  theorem's foundation made citation-free: `α/π` irrational ⟹ the edge-direction group is free).
- **`BaseBetaWalks.lean`** (17 theorems) — the current front line. This is where the thick-regime
  attack lives. In order:
  - `exists_of_dvd_sub` — a least-nonnegative-residue helper.
  - `base_walk_param`, `side_walk_param` — **the walk classification.** A "walk" along a side of the
    target is a triple `(P,Q,R)` with `P·a + Q·b + R·c = (side length)`. Both walk sets are cut out by
    the *same* linear form `⟨e,f,1⟩`: base at level `2e`, equal side at level `f`.
  - `base_trichotomy`, `side_dichotomy` — in the thin regime `f > 2e`, the base is one of three walks
    and each equal side one of two.
  - `gamma_injection`, `c_edge_exists` — the **γ-trap** pigeonhole: every side carries a `c`-edge
    (`R ≥ 1`). Geometry enters only through the vertex-figure hypotheses.
  - `side_no_b`, `base_b_bound` — **for every `(e,f)` at `m=1`:** no equal side carries a `b`-edge,
    and the base's `b`-count `Q = e + f·j` obeys `j(f−e) ≤ e−1`. (`e=1` ⟹ exactly one base `b`-edge.)
  - `base_trichotomy_cfree` — the trichotomy after removing the `R=0` walk via the γ-trap.
  - `edge_ab_unsplittable` — **for every `(e,f)`:** neither `a` nor `b` is a sum of ≥2 tile edges; `c`
    is one iff `e=1` (then `c = a^f`). **The open thick regime has `e ≥ 2`, so no tile edge splits.**
  - `apex_leftover_nonrepresentable`, `pierced_corner_types` — **the apex-mismatch theorem.** At the
    apex, exactly one inner ray pairs the middle tile's `c`-edge against a neighbour's `b`-edge; the
    length-`e²` leftover is never exactly coverable, so a far edge pierces the middle tile's far
    `β`-corner, with continuation `{α,γ}` or `{3α,β}`.
  - `pre_pierce_dichotomy` — the pre-piercer edges are `b`-edges, only in the super-thick regime.
  - `far_near_disjoint`, `far_is_bpow`, `b_not_dvd_fsq` — **the alignment theorem.** At `e ≥ 2, m=1`
    the mismatch ray's near side is the middle tile's single `c`-edge `[0,f²]`, the far side is exactly
    `b^f`, and `V = f²` is strictly pierced (`b ∤ f²`). The entire interior mismatch ray of any thick
    tiling is pinned to `b^f` out to length `f·b`.

### Realizability certificates (zero-axiom, no Mathlib)
- **`Tiling28.lean`, `Tiling44.lean`** — kernel-checked certificates that a triangle can be cut into
  `28` and into `44` congruent triangles. `#print axioms` reports **none**. Pure computation over
  `ℤ[√15]`: congruence of all tiles to `(2,3,4)`, containment, an explicit separating line for each
  pair, and the exact area sum. With the one-paragraph convexity bridge in the paper, these are
  unconditional theorems. The `44`-tiling is the smallest known incommensurable tiling (previous
  record `1215`).

### Other branches (from earlier phases)
- **`Erdos634.lean`** (23 theorems) — the arithmetic/combinatorial layer of the isosceles `2π/3`
  branch (Φ-invariant, no-prime master theorem), the scalene branches, the commensurable branch, the
  11-shape classification, the general-`N` admissibility theorem, and the `N=14,15` sweep.
- **`Gamma2Alpha.lean`** — the number-theory core of the `γ=2α` branch (Beeson Lemma 11.2), citation-
  free.
- **`EquilateralConic.lean`** — the necessary side of the equilateral branch as pure integer algebra.

---

## 4. What is settled by SEARCH (not by a general theorem)

The base-β candidates have no sound general exclusion, so each is settled individually by a
**corner-anchored exact search** over `ℚ(√D)`. Two independent implementations that agree
node-for-node:
- `engine/engine.py` — the Python reference (exact `ℚ(√D)` arithmetic).
- `engine/cengine_iso.cpp` — the C++ mirror (GMP), with prunes P1 (area), P2 (semigroup runs),
  P4 (corner angle), and **P5** (the walk / γ-trap / corner-parallelogram prune added in this project).

An `EXHAUSTED_NO_TILING` verdict is a **proof of non-existence** (the branching is complete). A
`FOUND_TILING` verdict dumps the tiling, which is then re-checked by `engine.py`'s independent
`reverify` and, for `28`/`44`, by the zero-axiom Lean certificate.

### Base-β members `N ≤ 110` (paper Table `tab:basebeta`)
| N | (e,f) | regime | status |
|---|-------|--------|--------|
| 11 | (1,2) | thick | EXHAUSTED (135 nodes) — also machine-forced, see §6 |
| 23 | (2,3) | thick | EXHAUSTED (19,677) |
| 26 | (1,3) | thin | EXHAUSTED (2,025) — composite |
| 39 | (3,4) | thick | EXHAUSTED (825,724) — composite |
| 47 | (1,4) | thin | EXHAUSTED (12,440) |
| 59 | (4,5) | thick, super-thick | EXHAUSTED (1,838,175) — prime, closed |
| 66 | (3,5) | thick | EXHAUSTED (7,232,464) — composite, closed |
| 71 | (2,5) | thin | EXHAUSTED (553,417) |
| 74 | (1,5) | thin | EXHAUSTED (132,519) — composite |
| 83 | (5,6) | thick, super-thick | **SEARCHING** — prime |
| 107 | (1,6) | thin | EXHAUSTED (1,251,382) |

"thick" means `f ≤ 2e`; "super-thick" means `f² ≤ 2e²`. **The thin regime is understood
structurally** (see §6). The open general problem is the thick regime.

### Record (contiguous determination of the spectrum)
**Every `N ≤ 69` is determined** (`59` and `66` closed by search this cycle). `71–80` are
determined, so `70` is the sole gap below `80` and the record extends to **`N ≤ 80`** when its search
resolves. `28`, `44`, `77`, `80` are realizable; `59`, `83`, `131`, `167`, … are the base-β primes
whose only current route is search.

---

## 5. What is OPEN (what remains to fully prove #634)

Three genuinely open pieces, in rough order of tractability:

1. **The base-β thick regime `f ≤ 2e` (this project's frontier).** A correct general proof that no
   base-β target with `m = 1`, `e ≥ 2` tiles. This would replace all per-value searching and close the
   prime dichotomy unconditionally. Detailed state in §6.

2. **Zhang's sufficiency conjecture (the `2π/3` sporadic wall).** Zhang constructs tiling families for
   each of the six sporadic `2π/3` similarity types and conjectures the constructed (composite) counts
   are the only ones. This project proves the *no-prime* half for the isosceles type and reduces the
   scalene types, but the full sufficiency classification is open in the literature. Not attackable by
   the present methods.

3. **The equilateral general laws.** The necessary side (a conic/divisor condition) is formalized
   (`EquilateralConic.lean`); the general realizability laws for `2π/3` on an equilateral target are
   open mathematics.

Fully resolving #634 (all `N`, not just primes) additionally requires the composite theory, which is
Zhang's program and is not the subject of this project.

---

## 6. State of the base-β thick-regime attack (the live front)

This is where a new agent should focus if continuing the mathematics. The strategy is to force the
local structure of a hypothetical thick tiling until it collapses. Progress is a chain of
machine-checked forcing steps, all `m = 1`:

**The thin regime (`f > 2e`) is closed structurally.** `base_trichotomy` + `side_dichotomy` +
γ-trap reduce it to two possible bases and `b`-free equal sides; combined with the walk arithmetic
this leaves no room. (It is not written up as a full no-go because a few endpoints still need the
apex analysis, but the structure is completely pinned.)

**The thick regime, forcing chain so far** (all in `BaseBetaWalks.lean`, all axiom-clean):
1. **Walk classification** (`base_walk_param`, `side_walk_param`): boundary walks are cut out by
   `⟨e,f,1⟩`.
2. **γ-trap** (`gamma_injection`, `c_edge_exists`): every side has a `c`-edge.
3. **`b`-free equal sides + bounded base `b`-count** (`side_no_b`, `base_b_bound`).
4. **Unsplittability** (`edge_ab_unsplittable`): at `e ≥ 2` no tile edge splits — the thick regime is
   perfectly rigid. This is the key enabler for everything after.
5. **Apex mismatch** (`apex_leftover_nonrepresentable`, `pierced_corner_types`): a forced pierced
   `β`-corner on the mismatch inner apex ray, with exactly two continuation types.
6. **Alignment** (`far_near_disjoint`, `far_is_bpow`, `b_not_dvd_fsq`): the mismatch ray is pinned —
   near side = the middle tile's single `c`-edge `[0,f²]`, far side = **exactly `b^f`**, `V = f²`
   strictly interior to a `b`-edge. Uniform in `(e,f)`.

**What is NOT yet done (rung 3, the open step).** No individual thick member is closed by pure
forcing. Two adversarially-verified multi-agent assaults established:
- The two continuation types at the pierced corner (`{α,γ}` and `{3α,β}`) both survive local analysis;
  the `{α,γ}` type is realized by the genuine `44`-tiling (which is `e=1, m=2`, so it validates the
  machinery but cannot witness the open `e ≥ 2` regime).
- `N = 59` has **five** live piercer branches; `N = 66` has **two of four** killed (the piercer must
  present `α` at the mismatch T-junction, which eliminates the `a`-edge and `c-edge-β` piercers) but
  two survive. Neither is closed.
- The `(0,1,3)`-vertex parity idea is **dead**: the census identity `M₄ = 1 + n₁ + 2M₁ + M₂ ≥ 1`
  (every base-β tiling has an interior `β + 3γ` vertex) is correct, but the "un-pairable edge-ends"
  obstruction leaks through a whole-edge T-junction onto the long `c`-edge (available always, since
  `c > a` and `c > b`), as the `99`-tiling's four such vertices demonstrate.

**The single best next step** (from the second assault's synthesis): chase the forced `b^f` wall's
landing on the base. The alignment theorem pins the far wall of the apex ray to `b^f` terminating
transverse to the base at base-coordinate `e·f²` (strictly interior). This is a `b`-edge ending on
the base at a *specific* coordinate. Coupling (i) the `f−1` forced pierced rungs at `i·b`, (ii) the
base's bounded and positioned `b`-count (`base_b_bound`, corner-parallelogram rule), and (iii) the
local vertex figure where the wall meets the base, is an interaction untouched by any dead method and
tightest at `N = 59` (the wall lands at coordinate `100` of the base of length `236`).

**Four methods are provably dead — do not attempt them:**
1. Linear / coloring invariants `Σ L·χ(θ)` with `χ` odd (Beeson's `g|M` is one such and is false).
2. The `b`-edge census in any modulus (a formal consequence of `N(a+b+c) ≡ 2X+Y mod 2`).
3. Euler / vertex counting (`V−E+F=2` is identically `#α = #β = #γ = N`; the vertex-type system is
   feasible for every thick target).
4. Boundary counting (`N ≥ 2k_S − 1` per side; at `m=1` the boundary is minimal, seeing only `O(f)` of
   the `N = Θ(f²)` tiles).

---

## 7. How to run the search engine

```
cd engine
# build the C++ engine (needs GMP):
g++ -O2 -std=c++17 -I$(brew --prefix gmp)/include -L$(brew --prefix gmp)/lib \
    -o cengine cengine_iso.cpp -lgmpxx -lgmp

# generate an instance for a base-beta member N = 3f^2 - e^2 (uses run_all.py builder):
python3 dump_inst.py ISOB:59:9 /tmp/i59.txt        # N=59, (e,f)=(4,5)

# (recommended) flip apex-down and add the P5 walk prune, for ~28x fewer nodes on thick members:
python3 flip_inst.py /tmp/i59.txt /tmp/f59.txt
python3 add_walks.py /tmp/f59.txt /tmp/fp59.txt 236 125 20 9 25 4 5 1 --baseside 1
#                     Ybase Xside a  b  c e f m  (baseside=1 for flipped)

# run (cap = node budget):
./cengine FILE:/tmp/fp59.txt 2000000000
```
A `FOUND_TILING` dumps `tiling_<name>.txt`; verify it with `engine.py`'s `reverify(tiles, target,
tile)` (see the call pattern used in the campaign). An `EXHAUSTED_NO_TILING` is a non-existence proof.

**Node counts for calibration** (flip + P5): `N=11` → 17, `N=23` → 691, `N=47` → thousands. Thick
primes `N=59, 83` are far larger and had not resolved at handoff time (searches at ~0.9M and ~0.4M
nodes respectively, no verdict). The next engineering lever, if searches stall, is int128 arithmetic
with a GMP fallback (~10–50×); the current bottleneck is GMP, and `-O3/-march=native` buys nothing.

**Prune validation.** P5 is validated three ways: (a) it still `EXHAUSTED`s every settled member with
fewer nodes; (b) `add_walks.py` re-asserts `side_no_b` and `base_b_bound` against the emitted lists on
every run; (c) the engine still *finds* the genuine `44`-tiling under the prune, and the found tiling
passes the independent verifier. The corner-parallelogram half of P5 requires the tile's `b`-edge to
be unsplittable, which `add_walks.py` asserts per instance (always true for `e ≥ 2`).

---

## 8. Pitfalls and hard-won lessons

This project has issued **six corrections/retractions**. Every one came from a claim that was not
checked against a concrete object before being asserted. The discipline that works: *before banking
any base-β claim, test it in exact arithmetic against the two genuine tilings* — `tiling_N44B.txt`
(`e=1,m=2`) and `tiling_99_isobeta_24_24_33.txt` (`e=1,m=3`).

1. **Beeson III is unreliable on the base-β/base-α branches.** Thm 14 (`g|M`) is *false*; Thms 18,
   19, 20 are unsound; Lemma 8's squarefree half is false. Do not cite them. (Beeson's isosceles
   `2π/3` paper and Thms 8, 12 are fine and are used.)
2. **Theorem 1 was over-stated in earlier drafts** — it asserted *all* primes `≡3 mod 4` while the
   base-β candidates (which are all `≡3 mod 4` and infinite) were not excluded. The current statement
   carries the explicit base-β exception. When stating a quantified no-go, check the excluded set is
   actually empty.
3. **The golden-ratio trap.** `b = f²−e²` exceeds `a = ef` iff `f/e > φ`. The thick regime straddles
   this: `N=66 (3,5)` and `N=131 (4,7)` have `b > a`, but `N=23, 59, 83, 167` have `b < a`. **Never
   assume `a < b`** — the `e=1` intuition (both genuine tilings) invites it and it is false exactly in
   the open regime. `e = 1` is the *loose* case; `e ≥ 2` is rigid.
4. **`side_no_b` is `m=1`-only.** The `99`-tiling (`m=3`) has 4 `b`-edges on an equal side. Any claim
   validated only on the genuine tilings (both `e=1`) cannot witness an `e ≥ 2` statement; those must
   be proved by exact arithmetic over a sweep and flagged as such.
5. **Refuted-but-plausible sub-claims:** "b-edges pair perfectly" (false, the 44-tiling has 6 unpaired
   `b`-edges); "base has no `b`-edge ⟹ `f|m`" (false, the 99-tiling has `f∤m` and 7 base `b`-edges);
   the `(0,1,3)`-parity closure (false, c-edge T-junction loophole).
6. **Engine.** `cengine`'s `FOUND` path historically wrote `tiling_<name>.txt` with the raw instance
   name; `FILE:`-based names contain `/` and `:`, so `fopen` returned NULL and the process segfaulted
   *after* printing the (buffered, hence lost) verdict — a `FOUND` masquerading as "no verdict". Fixed
   (filename sanitized, `fflush` after every verdict). For any long run on an *older* binary, a
   segfault-death now means FOUND; a clean exit means the EXHAUSTED verdict is trustworthy.

**Lean gotchas** (Lean 4.30 / Mathlib v4.30):
- `subst h` with `h : nb = f` and both `nb, f` free variables eliminates the *wrong* variable. Thread
  the equality through the goal (`⟨_, hnbeq, _⟩`) instead.
- `Nat.Coprime.pow` needs explicit exponents and `.symm` for the right orientation:
  `Nat.Coprime.pow 2 2 hcop.symm : (f^2).Coprime (e^2)`.
- `omega` cannot see that `f² > e²` from `e < f` (squares are opaque atoms); supply
  `nlinarith [hB, hef, he]`.
- Divisibility witnesses: `(hzc.pow_right).dvd_of_dvd_mul_right ⟨W, by linear_combination …⟩`; compute
  `W` and the `linear_combination` coefficient by hand.
- `#print axioms` after every file; `[propext, Classical.choice, Quot.sound]` is the clean target.
  `sorryAx` in the list means a hidden failure even if the file "builds".
- One Lean process at a time; parallel builds OOM the machine.

---

## 9. Repository, artifacts, provenance

- **Canonical repo:** `github.com/ElVec1o/erdos_634_proof` (paper, `lean/`, `code/`, metadata).
- **Zenodo:** archived per GitHub release via `.zenodo.json` / `CITATION.cff`.
- **This bundle** (`634/`) is a self-contained portable copy: `paper/` (tex + pdf), `lean/` (all 10
  files + build config), `engine/` (the P5 source, the Python reference, the drivers, and the three
  verified tiling certificates in `tilings/`), and this handoff.

Author: elvec1o. Commits are authored as `elvec1o` with no co-author trailer. Releases are cut on
every substantive update (currently at `v2.30`).

---

## 10. Concrete next actions for the incoming agent

1. **Resolve the live searches.** `N = 59`, `66`, `83` were mid-search at handoff (flip + P5,
   apex-down). Re-launch from `engine/` per §7. A `59` or `83` `EXHAUSTED` extends the contiguous
   record; a `FOUND` would be a new realizability result.
2. **Attack rung 3** per §6: the `b^f` wall landing on the base, coupled to `base_b_bound`. If a
   contradiction is found for general `e ≥ 2`, the thick regime closes and Theorem 1 loses its
   exception. Formalize any new arithmetic core in `BaseBetaWalks.lean` in the existing idiom
   (subtraction-free naturals, `omega`/`nlinarith`/`linear_combination`), and **verify it against both
   genuine tilings first**.
3. **Keep the paper honest.** Every green claim must be either machine-checked or search-verified;
   state openly what rests on search. Do not re-introduce any dependence on Beeson III Lem. 6, 8, or
   Thms 14, 18, 19, 20.
