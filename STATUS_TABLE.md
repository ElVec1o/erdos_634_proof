# Erdős Problem #634 — STATUS TABLE

**Read this first.** It is the honest, complete account of where the project stands: what is
proved, what is cited, what is open, what was once claimed and should not have been, and what is
known to be a dead end. `HANDOFF.md` has the operational detail; this file has the ledger.

Last updated: 2026-07-19. Repository: `github.com/ElVec1o/erdos_634_proof`, latest release `v2.58`.

---

## 0. The one-paragraph summary

**The problem.** For which `N` can some triangle be cut into `N` pairwise-congruent triangles?
The folklore conjecture is that no prime `N ≡ 3 (mod 4)` with `N > 3` occurs.
`erdosproblems.com/634` lists `N = 19` as an explicit open instance.

**What we have.** A signed-direction tiling invariant that settles the isosceles `2π/3` branch for
every prime; a self-contained reduction of the scalene shapes; five defects found in the
literature we were standing on, four of them with machine-checked replacements; two
kernel-verified explicit tilings, one of which **refutes a published theorem**; and an exhaustive
determination of the initial segment of the spectrum. **`N = 19` is excluded**, and so is every
prime `≡ 7 (mod 12)`.

**What we do not have.** The general conjecture. The exception is exactly the primes
`≡ 11 (mod 12)` — the base-`β` candidates `N = 3f² − e²`. There are 42 of them below 1000, and
**only six are settled, all by exhaustive computer search, none by theorem.** Anyone who says this
project has proved the folklore conjecture is wrong.

---

## 1. The headline theorem, stated exactly

> **Theorem (thm:main).** Let `N > 3` be a prime with `N ≡ 3 (mod 4)` which is *not* a base-`β`
> candidate — that is, `N ≠ 3f² − e²` for every coprime pair `1 ≤ e < f`. Then `N` is not a number
> of congruent triangles into which some triangle can be cut. In particular, since `19` is not of
> that form, **no triangle can be cut into 19 congruent triangles.**

> **Theorem (thm:mod12).** The prime base-`β` candidates are exactly the primes `≡ 11 (mod 12)`.

Together: **every prime `≡ 7 (mod 12)` is excluded unconditionally** — by Dirichlet, half of all
primes `≡ 3 (mod 4)` — and the open set is exactly the class `11 (mod 12)`.

**Hypotheses carried.** The theorem is conditional on cited classification inputs. Refereed:
Laczkovich (1995, 2012), Snover–Waiveris–Williams (1991). Accepted: Beeson, *Tilings of an
isosceles triangle*. **arXiv preprints, load-bearing:** Beeson's *Triangle Tiling I / III / Seven /
Equilateral*, and **Beeson–Zhang rationality**, which supplies integrality of the tile. That last
one is the single most load-bearing unrefereed input.

---

## 2. 🔴 The honest reckoning: what was claimed to professors, and why it was wrong

An earlier version of this project (preserved verbatim in `archive/zenodo-v1/`) was prepared for
Zenodo and for contacting referees. Two documents there overstate what was proved.

### 2a. `archive/zenodo-v1/proof/phi-invariant-proof.md` — **OVERCLAIM**

Its closing sentence reads:

> "Therefore **no prime ≡ 3 (mod 4) is a number of congruent triangles tiling a triangle** — the
> folklore conjecture, and the open part of Erdős #634, is resolved."

**That is false, and we now know precisely why.** The argument assembles the branches and disposes
of the `3α+2β = π` family "by standing theorems". We have since **proved that those standing
theorems are defective** (§4 below): Beeson III's Theorem 14 is *false* — refuted by an explicit
99-tiling we constructed and machine-verified — and Theorems 18, 19, 20 have unsound proofs, as
does Lemma 8's squarefree half and Lemma 6 as quoted. With those removed, the base-`β` sub-branch
of `3α+2β = π` is **wide open**, and it is exactly the primes `≡ 11 (mod 12)`.

So the error was **not** in the Φ-invariant, which is sound and is still the core of the current
paper. The error was trusting a cited input that nobody had checked. **The conclusion drawn was
stronger than the inputs supported.**

### 2b. `archive/zenodo-v1/proof/N19-citable-note.md` — **conclusion correct, justification since repaired**

This note was more careful, and explicitly says "the *general* 'no prime ≡ 3 (mod 4)' conjecture
remains open". Its conclusion — no triangle can be cut into 19 congruent triangles — **is still
correct**. But its justification routed the `3α+2β = π` row through the same Beeson citations we
have since shown defective. The current paper repairs this: `19 ≡ 7 (mod 12)`, so 19 is *not* a
base-`β` candidate at all, and the other `3α+2β` sub-branches are excluded by our own
machine-checked propositions replacing Beeson's unsound ones.

**Net:** the `N = 19` claim survives, on a repaired and now machine-checked footing. The
"conjecture resolved" claim does not, and must be retracted anywhere it was sent.

### 2c. What to say now, if re-contacting anyone

Say: *no prime `≡ 7 (mod 12)` is a tile count, in particular not 19; the class `11 (mod 12)` is
open; and here are five defects in Beeson's Triangle Tiling III, one of them refuted by an
explicit tiling.* That is defensible, checkable, and interesting on its own. Do not say the
folklore conjecture is proved.

---

## 3. Status by branch (the prime problem)

| Branch of Laczkovich's classification | Status for prime `N` | Where |
|---|---|---|
| Tile similar to `ABC` | `N = n²`, never prime | SWW 1991; Beeson I — **cited** |
| Commensurable tile angles | excluded | Beeson, arXiv:1811.09723 — **cited** |
| Right-angled tile | excluded | Beeson — **cited** |
| Isosceles tile, `γ = 2α` | `N` not squarefree | Beeson — **cited** |
| Equilateral `ABC` | `N` not prime | Beeson, arXiv:1812.07014 — **cited** |
| `2π/3` tile, **scalene** `ABC` (`F₁…F₄`) | `N` composite | **OURS**, self-contained (`prop:reduction`) |
| `2π/3` tile, **isosceles** `ABC` | **impossible for every prime** | **OURS** — the Φ-invariant (`thm:iso`) |
| `3α+2β=π`, scalene targets | `N` composite | **OURS** — Lean cores of Beeson Thms 8, 12 |
| `3α+2β=π`, base-`(α+β)` target | `N` not prime | **OURS** (`prop:b3prime`) — *replaces the unsound Beeson Thm 18* |
| `3α+2β=π`, base-`α` target | `N` not prime | **OURS** (`prop:isoalphaprime`) — *replaces the unsound Beeson Thm 20* |
| `3α+2β=π`, iso-`β` target | `N` not prime | **OURS** (`IsoAlphaPrime.lean`, machine-checked) |
| **`3α+2β=π`, base-`β` target** | 🔴 **OPEN** | §5 |

**The single open cell is the last row**, and it is exactly the primes `≡ 11 (mod 12)`.

---

## 4. 🎆 What we have that the rest of the world does not

These are the defensible novelty claims. Each is checkable from this folder.

1. **The Φ-invariant, and the isosceles `2π/3` theorem.** A translation-invariant signed-direction
   functional, **linear in edge length and hence insensitive to non-edge-to-edge incidence** — the
   property that makes it succeed where 2-colourings fail. It yields: *no prime number of `2π/3`
   tiles tiles an isosceles triangle*, for every prime. Beeson had ruled out `N < 36` here and
   explicitly left the prime case open; the smallest known tiling in this branch has 2673 tiles.

2. **Five defects in Beeson, *Triangle Tiling III*** — found by us, four with replacements:
   - **Theorem 14 is FALSE.** Its divisibility `g ∣ M` is refuted by an explicit **99-tiling** of
     the `(24,24,33)` triangle by `(2,3,4)` tiles, which we constructed and verified in exact
     `ℚ(√15)` arithmetic. *Refuting a stated theorem with an explicit object is the strongest kind
     of correction, and it is ours.*
   - **Lemma 8's squarefree half is false** (counterexample tile `(4,15,16)`, `g = 4`).
   - **Lemma 6 is false as quoted** (counterexample: tile `(2,3,4)`, `ABC = (4,6,8)`, midpoint
     subdivision gives two sides with no `c`-edge). We also now *explain* the failure: our γ-trap
     (§4.5) needs the corner angles to be `β, β, 3α`; on the tile-similar target a corner **is** a
     `γ`, and the forcing chain terminates harmlessly.
   - **Theorems 18, 19, 20 have unsound proofs.** Thm 18's congruence `c²b ≡ M⁴(M²+1) (mod N)` is
     identically 0 (a factor `a` was dropped) and false at `N = 48, M = 4`. We supply correct
     replacements for 18 and 20.

3. **Two kernel-verified explicit tilings**, `Tiling28.lean` and `Tiling44.lean`, which use **no
   Mathlib** and report **zero axioms**. The 44-tiling of `(16,16,22)` by `(2,3,4)` is the
   smallest known tiling in an incommensurable branch (previous record 1215).

4. **The contiguous spectrum is determined up to 69.** Every `N ≤ 69` is settled; `70` is the only
   gap below 80, and `71–80` are settled, so the record extends to `≤ 80` on its resolution.
   `28, 44, 77, 80` are realizable. The last two gaps below 70 — `59` (prime) and `66` — were
   closed by exhaustive search at 1,838,175 and 7,232,464 nodes.

5. **The mod-12 characterization.** The base-`β` prime candidates are *exactly* the primes
   `≡ 11 (mod 12)` (`BaseBetaMod12.lean`). This converts a Diophantine exception into a single
   congruence class, and is what makes the headline unconditional on half of `3 mod 4`.

6. **Rationality from the invariant** (`Rationality.lean`, `tile_rational`). If the three invariant
   values are integers, then `a/b, c/b ∈ ℚ` — no citation. Two identities:
   `M_α M_β = −P²ab` and `M_β − M_α = 2P(a+b)`. This shows tile-rationality and
   invariant-integrality are *equivalent*, not independent, which is not how the literature
   presents them.

7. **The γ-trap and the corner parallelogram, with proofs** (`BaseBetaCorners.lean`).
   At a base corner the angle equation admits only `(p,q,r) = (0,1,0)` — a *single* tile presenting
   `β`; at the apex only `(3,0,0)` — three tiles presenting `α`. Hence **no corner carries a `γ`**,
   and a forcing chain shows **every side carries at least one `c`-edge**. Plus: `b` is
   unsplittable, the corner tile's `b`-chord has both endpoints on the boundary so nothing can
   straddle it, and the matching tile has `α, γ` interchanged.

8. **The walk structure at `m = 1`** (`BaseBetaWalkArith.lean`). If `f² > 2e²` each equal side
   carries **no** `b`-edge; if `f² > 2ef + e²` the base carries **exactly `e`** of them, so
   `R_base ∈ {e, 2e}`. Both hypotheses sharp. Covers 28 and 17 of the 42 candidates below 1000.

9. **Two death certificates** (`LambdaFactor.lean`) — negative results, and the point is that they
   are *exact*. The whole class of linear direction invariants is closed: ideal membership holds
   identically for every root of unity and every `(e,f)`, and the optimal `ℓ¹` bound the class can
   produce falls short of `N` by a factor `≥ 11/6`, growing like `mf`. See §7.

---

## 5. 🔴 The open gap, stated precisely

**Gap 1 — the base-`β` branch at `m = 1`.** This is the whole of what remains for the prime problem.

- Target: isosceles `(f³, f³, e(3f² − e²))` with base angles `β`, tiled by `(ef, f²−e², f²)`,
  `gcd(e,f) = 1`, `1 ≤ e < f`. Tile count `N = m²(3f² − e²)`; **`N` prime ⟺ `m = 1`.**
- **42 prime candidates below 1000** (= the primes `≡ 11 (mod 12)`): **19 thin (`f > 2e`), 23
  thick (`f ≤ 2e`)**.
- **Settled: 6.** All by exhaustive search, **none by theorem**: `11` (135 nodes), `23` (19,677),
  `47` (12,440), `59` (1,838,175), `71` (553,417), `107` (1,251,382). `83` was under search.
- 🔴 **Do not say "the thin regime is understood."** It is not. Thin is 45% of the open set and no
  theorem closes any of it.

**The sharpest reduction we have.** For `e = 1`, `m = 1`, `f ≥ 3` (candidates `N = 3f² − 1`:
11, 47, 107, 191, 431, 587, 971 below 1000), the equal sides carry no `b`-edge and begin and end
with `c`; the base carries exactly one `b`-edge and one `c`-edge and begins and ends with `a`. So
**the base walk is a permutation of `(a^f, b, c)` starting and ending with `a`, with `b` in
position 3..f.** The subfamily reduces to: *is that one walk realizable?*

### The other three gaps

**Gap 2 — the geometric layer is unformalized.** Mathlib has no theory of planar dissections. We
formalized what could be: `Dissection.lean` proves the area identity (via
`Convex.addHaar_frontier`) and the real-angles → integer-multiplicities step. **Absent from
Mathlib entirely:** dissection theory, planarity, `V − E + F = 2`, and any "angles around a point
sum to 2π". The last makes the full geometric layer non-formalizable today. `lem:cancel` and
`lem:value` rest on written proofs; `lem:cancel`'s proof now uses the *common refinement into
minimal pieces*, which removes the overhang case.

**Gap 3 — the Beeson–Zhang rationality preprint.** Load-bearing for integrality of the tile.
Narrowed, not closed, by `tile_rational` (§4.6): rationality is now free *wherever the invariant is
already integral*, which is inside the invariant argument; establishing integrality on the general
target is exactly what the cited theorem does.

**Gap 4 — the composite problem.** The full determination of the spectrum. We have the admissible
spectrum of each sporadic branch (necessary side) and decidability of membership; Zhang's
sufficiency conjecture and the general equilateral realizability laws are open **in the
literature**. A previously-asserted asymptotic for the counting function of the realizable set was
**withdrawn** — it inferred a global bound from a per-family one, and there are `Θ(X)` families
with `N₀ ≤ X`.

---

## 6. Machine-checked inventory

18 Lean 4 + Mathlib files, **138 theorems, zero `sorry`, all axiom-clean** (`#print axioms` reports
only `propext, Classical.choice, Quot.sound`, or fewer). `Tiling28.lean` and `Tiling44.lean` are
kernel-only and report **no axioms at all**.

| File | Thms | What it certifies |
|---|---|---|
| `Erdos634.lean` | 23 | the Φ-invariant core; `k_not_dvd_sum_sub`, `M_not_int` |
| `BaseBetaWalks.lean` | 25 | boundary-walk classification, apex mismatch, alignment |
| `Dissection.lean` | 20 | area identity; real angles → integer multiplicities (**Gap 2**) |
| `InvariantCore.lean` | 10 | cancellation core, tile value, integrality parity |
| `FibonacciFamilies.lean` | 10 | extremal families, `M² − N` identities |
| `BaseBetaE1.lean` | 7 | the `e = 1, f = 2` closure |
| `BaseBetaCorners.lean` | 6 | corner figures, γ-trap, `b` unsplittable (**§4.7**) |
| `Rationality.lean` | 6 | `tile_rational` (**Gap 3**) |
| `LambdaFactor.lean` | 6 | the two death certificates (**§7**) |
| `BaseBetaMod12.lean` | 5 | base-`β` candidates = primes `≡ 11 (mod 12)` |
| `BaseBetaWalkArith.lean` | 4 | walk structure at `m = 1` (**§4.8**) |
| `Beeson3NotPrime.lean` | 4 | Beeson III Thm 8 core |
| `EquilateralConic.lean` | 4 | equilateral necessary condition |
| `BaseAlphaBetaPrime.lean` | 3 | replacement for Beeson III Thm 18 |
| `IsoAlphaPrime.lean` | 2 | replacement for Beeson III Thm 20 |
| `Gamma2Alpha.lean` | 1 | `γ = 2α` branch |
| `Tiling28.lean` / `Tiling44.lean` | 1 + 1 | explicit tilings, **kernel-only, zero axioms** |

---

## 7. ⛔ Dead ends — do not retry

Each of these was pursued and closed. Two are closed *by theorem*, which is stronger than "we
tried and failed".

1. **The entire class of linear direction invariants.** Weighting a directed edge by a function of
   direction alone, antisymmetric under `θ ↦ θ+π`, gives a one-parameter family; every member is a
   specialisation of the paper's own `rem:nogo` master identity. **Closed by theorem**
   (`LambdaFactor.lean`): ideal membership holds identically for every root of unity and every
   `(e,f)`; and the optimal `ℓ¹` bound the class can produce is `m(3f−2e)(f+e)/f`, exactly
   (primal = dual LP), *attained* by the genuine 44-tiling, while `N` exceeds it by `≥ 11/6`
   always and by `~mf` asymptotically. **No `λ`, kernel, moment ladder, Riesz product or `Lᵖ`
   duality can ever exclude a candidate.** Larger candidates are strictly *harder*.
2. **Dividing out the common factor** `(λ−ω)(λ−ω′)` before bounding: a formal **no-op**. Numerator
   and denominator carry the identical factor with identical modulus on the circle. (The
   "degree-neutral division" trick from the other project does *not* transfer — there the orders of
   vanishing differed.)
3. **Galois-conjugate pairing.** `τ = (reflection in the base) ∘ (√D ↦ −√D)` fixes `ℚ(i√D)`
   pointwise, so every tiling is trivially self-conjugate. No information.
4. **Closing `e = 1` by proving `R ≥ 2` on every side.** **False at the base**: the `R = 2` walk is
   exactly the one the corner parallelogram kills, and the survivor has `R = 1`. On the base,
   "`R ≥ 2`" restates the remaining problem rather than reducing it. It *does* hold on the two
   equal sides, and is proved there.
5. **Boundary tile counts.** Measured: 28 of 44 and 44 of 99 tiles touch the boundary — a *falling*
   fraction — and the inter-side overlap is 7, not the 5 that corner tiles alone give. Both
   boundary count and `N` are `O(f²)`; the comparison never bites.
6. **The far side of the mismatch ray** (under the hypothesis that the ray is a complete wall):
   that side is the tile scaled by `f` and is tileable. No obstruction can come from there. This
   was once listed as the top next action; it is a closed branch.
7. **Euler / vertex counting.** `V − E + F = 2` is identically the sum of the three corner
   identities `#α = #β = #γ = N`; the vertex-type system is feasible for every target.
8. **`b`-edge parity, and the "clean ray" corollary.** Both were *shipped and then retracted*. See
   §8.

---

## 8. ⚠️ Traps that have already cost us

1. **Non-edge-to-edge is real, and it has caused every retraction.** A longer edge may **straddle**
   a shorter one rather than partition it. This killed the `b`-edge parity theorem (the 99-tiling
   has 33 matched pairs, 11 boundary, **22 straddled**) and `cor:cleanray`. It also invalidated a
   printed vertex census that omitted the straight-angle vertex types. **Verify the mechanism
   against a genuine tiling, not merely the conclusion.**
2. **The naive norm test is unsound and would have manufactured a false theorem.** `gcd(Norm V₊,
   Norm V₋) ∣ Norm W` "excludes" the *known-realizable* `N = 44` and `N = 99`. **Always run
   known-realizable controls before trusting an exclusion test.**
3. **`α < β < γ` is false** whenever `e/f > (√5−1)/2 ≈ 0.618` — i.e. throughout much of the thick
   regime. Only `γ` is always largest. (Golden-ratio trap: `b > a ⟺ M² < N ⟺ f/e > φ`.)
4. **Lean `subst` trap.** `subst h` with `h : nb = f` where *both* are free variables eliminates
   `f`, breaking everything downstream. Rewrite instead (`rw [h] at ...`).
5. **Never run parallel Lean builds.** One `lake`/`lean` process at a time. A fan-out verification
   workflow OOM'd the machine once.
6. **Heavy compute goes in Rust**, with ETA, progress, interim saves and bounded memory. Python
   OOM'd the machine once and is 100–1000× slower.
7. **`gh release --notes` with backticks** triggers shell command substitution. Use `--notes-file`.

---

## 9. Next moves, ranked

1. **Settle the `e = 1` base walk** (§5). It is one explicit configuration, and it closes seven
   candidates below 1000 plus infinitely many. Three attacks have failed on it — the invariant
   class (closed by theorem), metric bounds (closed by theorem), boundary counting (dead by
   measurement). What remains is the *local geometry* the walk arithmetic cannot see: at each
   interior junction both completions survive. Attack with the engine first to see whether a
   partial configuration is forced, then try to make that forcing uniform in `f`.
2. **Formalize the 99-tiling** (`Tiling99.lean`, clone of `Tiling44.lean`'s code path). It is the
   object that refutes a published theorem, and right now it is the least-verified thing in the
   project while being the most consequential. Cheap and high value.
3. **Resolve `N = 70`**, which extends the contiguous record from `≤ 69` to `≤ 80`.
4. **Close Gap 3** by establishing invariant-integrality on the general target, which would remove
   the Beeson–Zhang preprint dependency outright.
5. **Extend the walk structure into the thick regime** (`f² ≤ 2e²`), where the excluded solutions
   `n_b = 2f` and `n_b = e + f` genuinely appear.

---

## 10. What is in this folder

```
STATUS_TABLE.md      this file — the ledger
HANDOFF.md           operational detail: what was done, banked, and left
README.md            public-facing summary
paper/               erdos-634.{tex,pdf}            main paper, 29 pp
                     erdos-634-companion.{tex,pdf}  the base-β branch, 10 pp
lean/                18 files, 138 theorems, no sorry, axiom-clean
                     lean/README.md describes every theorem
code/                verification scripts (Python, exact arithmetic)
engine/              the exact corner-anchored search engine (C++/GMP + Python reference)
engine/tilings/      verified 28-, 44- and 99-tiling certificates
archive/zenodo-v1/   🔴 SUPERSEDED. The earlier Zenodo/referee package.
                     Contains the OVERCLAIM described in §2. Kept for provenance only.
```

**To verify:** `cd lean && lake exe cache get && lake build` (Lean 4.30.0, Mathlib v4.30.0), and
`python3 code/verify_*.py` (needs sympy).

---

## 11. Scope of verification, stated plainly

The **arithmetic and combinatorial** layer is machine-checked in Lean. The **geometric** layer —
that a tiling yields the stated Diophantine equations and vertex-angle relations — rests on written
proofs in the paper, backed by exact-arithmetic checks against genuine tilings. **This caveat
applies uniformly to every result here.** Search verdicts (`EXHAUSTED`) are declared computer
assistance, not formalized: formalizing them would mean verifying the engine.

This is an exceptional claim in a problem with a history of withdrawn results — including one
withdrawn by Beeson himself, and five defects we found in work we were standing on. It should not
be regarded as established until checked by experts.
