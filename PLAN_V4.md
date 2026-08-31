# Plan for v4.0

Written 2026-09-01 after an external read of v3.0. The reviewer's strategic advice is adopted
almost entirely; three of their factual claims are wrong and are corrected here first, because the
plan should not be built on them.

## 0. Corrections to the external read

| Reviewer's claim | Actual |
|---|---|
| "v3.0: 47 files, 408 theorems" (and "v2: 23 theorems") | **216 Lean files, 2040 theorems/lemmas.** Both figures were read from a stale cache |
| "only `N = 76` left" for the contiguous spectrum | `N = 76` is **settled** — main paper §2192: the live branches are excluded and "hence 76 is not realizable" |
| "Bonfioli should publish the sweep protocol ... fixes the old bug" | Already done and shipped: `run_sweep.sh` + `verify_sweep.py`, and the runner now races both mirror representatives and reaps stale slots |

Everything else in the read is accurate, including the central point: **v3.0 is honest about the gap
and that is worth more than a claimed proof.** The plan below follows their ordering — unconditional
bricks first, conditional cathedral second.

## 1. The split into three papers (adopted)

**Paper A — unconditional.** Nothing in it depends on Hypothesis (walls).
- the signed-direction invariant: definition, the cancellation lemma across non-edge-to-edge
  incidences, tile value `±(c+a−b)`;
- no prime `2π/3` tiling of an isosceles target, for **every** prime (Beeson had `N < 36` against
  Herdt's `N = 2673`);
- `thm:mod12` forward (VERIFIED): every prime `≡ 7 (mod 12)` is excluded unconditionally — half of
  the primes `≡ 3 (mod 4)` — and `19 ≡ 7`, so **`N = 19` is unconditional**;
- the scalene reduction: four of five `3α+2β=π` targets by machine-checked arithmetic.

*State:* the mathematics is done and labelled. The work is extraction and rewriting, not research.

**Paper B — errata and replacements for Beeson III.**
- Theorem 14 refuted by the `99`-tiling of `(24,24,33)` by `(2,3,4)`, kernel-checked (`Tiling99.lean`,
  zero axioms, 99 congruences over `ℤ[√15]`, 4851 separating edge-lines);
- the `44`-tiling of `(16,16,22)`, smallest known in an incommensurable branch (previous 1215);
- Theorems 18 and 20 replaced by machine-checked propositions; Theorem 19's unsound `g | M` recorded;
- **written as errata + replacement, not attack.** Offer joint errata to Beeson.

*State:* `rem:thm14false` exists and the certificates are kernel-checked. Needs assembling into a
standalone note, and the full inventory of unsound lemmas listed in one table.

**Paper C — the conditional programme.**
- the base-`β` forcing chain with Hypothesis (walls) stated as an open problem;
- the adversarial audit that located the deferral;
- the no-go: nine tool classes cannot answer the crossing question, each being invariant under
  relocating an edge; the Conway–Lagarias group collapses to its rank-2 abelianisation;
- the thirteen certified members with their coverage certificates;
- route 1's machine-checked scheme (`RouteOne`, 44 theorems) with its attachment obligation stated.

*State:* all present in the current companion + obstructions notes. Needs separating cleanly so that
A and B carry no conditional dependency.

## 2. Hypothesis (walls) — the kingmaker

The reviewer is right that this is the item that changes standing. Current position:

- **`e = 1`**: route 2 (`conj:advance`) is the shorter path and would close `e = 1` entirely. Its
  gap 2 is closed at every block length (`prop:doublec`). Its gap 1 reduces to the `[V,E]` question,
  whose chain is now machine-checked end to end. **The residue is attachment**: every theorem takes
  the configuration as hypotheses, and a hypothetical tiling must be exhibited to present them. That
  needs the tile-placement layer, which 33 other PROVED statements also wait on.
- **`e ≥ 2`**: untouched by any of the above. `thm:n1`'s induction fails at the interior points
  `V_k` where the residue is `π + α` rather than `α`, and `rem:n1gapexact` shows that missing step
  **is** the crossing question. No family decomposition exists here.

The reviewer's two concrete suggestions are both already logged: the mirror argument
(`RogueMirror`) and the 2D W-tower. Their advice to "attack the interior, not the boundary" matches
the project's own standing directive of 2026-08-29.

## 3. De-AI the presentation (adopted)

- human figures for the interior-cancellation lemma, showing one long edge against several short
  collinear ones;
- `lean/PAPER_MAP.md` becomes a real appendix mapping every paper statement to its Lean name — it is
  already that table, it needs typesetting;
- for the geometry layer, formalize the combinatorial part (`Γ_a, Γ_b, Γ_c` graphs) as Beeson did,
  without Mathlib dissection theory.

## 4. The computational frontier

- the contiguous spectrum is already determined through `N ≤ 80`; **state it as a theorem** rather
  than leaving it in remarks;
- `N = 105 = b(a+b) = 7·15` on the `F₁` target, tile `(8,7,13)`: shown outside every standard
  invariant, so genuinely combinatorial. **This is the best single target for a new result** and the
  no-go is itself publishable;
- finish `f = 24` (`N = 1727`) for the fourteenth certified member, and judge the frozen band
  predictions.

## 5. Ordering for v4.0

1. Paper A extracted and self-contained (no walls dependency anywhere in its chain).
2. Paper B assembled with the unsound-lemma inventory table.
3. Paper C reorganised as "programme with hypothesis".
4. PAPER_MAP typeset as an appendix; figures drawn.
5. `N = 105` attacked; `f = 24` finished.
6. Only then, if walls closes, fold it back and re-cut.

**What v4.0 should not claim.** The prime case is not closed and will not be by this release. The
honest headline is: *half the folklore class is unconditional, thirteen members of the other half
are certified, Beeson III is corrected, and the residue is one named hypothesis with a
machine-checked attack scheme awaiting its instance.*

## 6. The Paper A gate (built 2026-09-01)

`code/analysis/dep_closure.py` computes a statement's transitive reference closure across the three
papers — reading proof blocks, not only statement bodies — and reports the weakest Rule 0 label in
it and whether `hyp:walls` is reachable. A conditional dependency expressed as
`\cite[Hyp.~5.1]{Companion}` or the phrase "complete-corner-wall hypothesis" counts, since that is
how the papers actually express it; without that clause the checker called `thm:fullprime`
unconditional, which is false.

First run: `thm:fullprime` **reaches `hyp:walls`** (correct — it is the conditional theorem);
`cor:mod12` does not. That is the gate Paper A must pass for every statement it contains.

**Known limitation, recorded rather than papered over.** A statement appearing twice — an
introduction summary and a body copy — carries its proof on only one occurrence, so a closure of
size 0 means "no proof block cites anything here", not "no dependencies". `thm:main` and `thm:iso`
report 0 for exactly that reason. Before Paper A ships, each of its statements must be checked
against the occurrence that carries the proof, and the script now says so instead of returning a
clean bill.
