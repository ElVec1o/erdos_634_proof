# THE /goal — READ THIS BEFORE EVERY RESPONSE

**The only acceptable outcomes are:**

1. **The full proof of Erdős #634**, or
2. **The prime case proved** (no prime N > 3 is a tile count), or
3. **A provably novel, significant breakthrough** toward either.

Nothing else counts as progress. Not infrastructure. Not formalization of things already believed.
Not audits. Not bridges. Not "one step away."

## Rules of engagement, learned the hard way

* **NEVER say "one step from done."** It has been said ~15 times in a row on this project and was
  wrong every time. If a step remains, the honest statement is "this is not done and here is what
  is missing," with no estimate of nearness.
* **A Lean theorem is not a result.** A theorem whose hypotheses are unsatisfiable proves nothing
  (this happened twice — `word42_junction_dies`, `uniform_bp2_conditional`). Exhibit a witness for
  every hypothesis before reporting anything as progress.
* **Building machinery is not progress toward the goal** unless a *named* target theorem falls
  because of it. If asked "which of the three outcomes did this advance," and the answer is "none
  yet," it was a side quest.
* **Negative results count** only when they are sharp and close off a named route — "where not to
  look," proved, not "we tried and it was hard."
* **Report the distance honestly**, including when the distance grew.

## The prime-case map (user, 2026-09-01): work the target list, not 4-step batches

`private/GOAL_PRIMES.md` is the dependency map for outcome (2), the prime case, with every
node's Rule 0 label. It was built from the papers, not from memory. Work proceeds against its
**ordered target list** until a target falls or is proved unreachable; report progress by *target*,
not by count of small steps.

The structure it records, so it is not re-derived each session:

* Primes `N ≢ 11 (mod 12)` are **done** (`thm:mod12` forward VERIFIED, `thm:main`, `thm:primefull`).
* Primes `N ≡ 11 (mod 12)` are exactly the base-β candidates, and since `N` prime forces `m = 1`,
  **the prime case is the `m = 1` base-β family**. It splits `e = 1` / `e ≥ 2`, and both reduce to
  the crossing question (`prop:threecostumes`).
* `e = 1` has two routes. Route 1 (exclude every escape word family) needs families, not
  enumeration — orbits grow 24, 41, 87, 149, 186 at `f = 12…24` *at reach 4, which is OPEN*; at
  the **proved** reach 3 they are 33, 52, 102, 168, 207 (2026-09-12 audit: the sweeps' kill list
  assumed reach 4; all five are now exhausted at the proved reach — `f = 24`'s 21 missing orbits were
  run the same day, `verify_sweep.py 24` PASS at R=4) —
  and the march family the recent work advances is **7 of 186 orbits at `f = 24`**. Route 2 is `conj:advance`, which if proved
  closes `e = 1` outright and names exactly two gaps, the second general except for its walk
  enumeration. **Route 2 is shorter and better scoped; prefer it.**
* `e ≥ 2` has no route that is not the crossing question itself.

Standing honesty requirement for this goal: the march work is real and small relative to it. Do not
report march progress as prime-case progress without saying which of the 186 orbit-families it
touches.

## STANDING RULE 0.5 — NO REDISCOVERIES (user, 2026-09-06, after six in one day)

**Read `NOVELTY_PROTOCOL.md` before any computation or novelty claim.** It is binding.

The single most expensive recurring failure on this project is recomputing settled results. On
2026-09-06 alone: `N=66` (11h, published at `erdos-634.tex:825`), then `N=59`, `N=107`, `N=66`
again and `N=62` (~9 core-hours, all rows of `tab:basebeta`), plus the Euler/dual-graph negative
re-deriving `rem:spectral`. In the worst case the agent **quoted the settled-instances table
verbatim in its own audit block and launched three of its rows anyway.**

The lesson, which supersedes every earlier phrasing of Rule 4:

> **A control that must be invoked is not a control. A control sits on the path to the action and
> returns non-zero.** Reciting the audit is not performing it.

Therefore, without exception:

* **Never invoke an engine binary directly.** The only sanctioned launch is
  `code/guard_run.sh <engine> FILE:<instance> [args]`. It refuses settled instances (exit 3) against
  `data/SETTLED.tsv`. A bare `./private/bin/cengine_* FILE:...` — in a command, a script, or a
  driver loop — is a violation regardless of what it finds. **Driver loops are checked per
  iteration, not once at the top**; that is exactly how Mode B cost 9 core-hours.
* **Record every terminated search immediately** with `code/guard_record.sh`. An unrecorded result
  will be recomputed.
* **Grep the CONCLUSION, not the topic**, via `code/novelty_check.sh`, and search `paper/` as well as
  `lean/`.
* **A `CLAUDE.md` blocker is formalization debt, not an open route.** The four blockers below mean
  *no Lean exists*. The mathematics may be published and PROVED. Check `paper/` before calling a
  route unexplored.
* **Run `code/guard_selftest.sh` after any edit to the guard or registry** — it asserts 14 refusals (10 multi-line + 4 packed one-line instances) and 2 allowances. Every guard carries a negative control that must pass. For `guard_run.sh` it is `N=83 (5,6)`,
  the one genuinely open row below `N=110` — it must be *allowed*. A guard that refuses everything
  is broken, and a broken guard already cost four rediscoveries once (`novelty_check.sh`, exit-status
  bug).
* **If a result reproduces a known one, that is the headline, not a footnote.** Presenting a
  reproduction as a fresh measurement is the error that makes this expensive.

**`N = 83 (5,6)` is the only unsettled base-β row below `N = 110`.** Any base-β run below 110 that
is not `N=83` is a rediscovery by construction.

## Second standing goal (user, 2026-08-30): clear the formalization debt

**Every PROVED statement in the three papers is debt** (Rule 5): it must reach VERIFIED, or carry a
recorded blocker. As of 2026-08-30 the exact census is

```
PROVED 136   CONJECTURE 32   VERIFIED 18   HEURISTIC 3   OPEN 2
```

and the standing instruction is to work this down, autonomously and continuously, reporting the
exact count every iteration. Rules:

* **Never move a label up without checking the statement, not its ingredients.** Ten VERIFIED
  labels were wrong for exactly that reason (audit of 2026-08-30); the corrected rule is written at
  the foot of `lean/PAPER_MAP.md`: VERIFIED means the paper statement, as written, is the Lean
  theorem.
* **Build `Erdos634.All` before every commit** that touches Lean.
* **A statement that cannot be formalized keeps its blocker in `PAPER_MAP.md`**, named precisely.
  A named blocker is a discharged obligation; "not yet attempted" is not.
* The blocker list is **STALE and has caused repeated category errors** — corrected 2026-09-07 by room `tileplace`: (i) *no scale or composition map* is **CLOSED** (`thm:ladder` VERIFIED 2026-09-02, `Subdivision.ladderDissection`, `Compose.compose`); (ii) *no dual-graph development* is a **dead route**, not a gap (`rem:spectral`, PROVED); (iii) *no tile-placement layer* is **partly built** (`TilePlacement` 25 decls, `TileAt` 26, `SubDissection`, `DissectionMap`, `Placement`) — what remains is specifically **edge-level placement**: "the corner tile's base edge" is **CLOSED** (2026-09-09, `CornerBaseEdgesReal.congruentDissection_base_corner_edges` + `ApexEdgesReal.congruentDissection_apex_edges`); "matched by exactly one tile" (`prop:cornerpara`) remains open, its obvious route a recorded dead end (`BaseBetaWalks.lean:797-808`); (iv) *no certified-search format* stands. **A blocker being listed is not evidence the mathematics is open — check `paper/` and `lean/` before believing one.** And note the hard lesson of F-4: closing an infrastructure gap does **not** unblock its consumers — `thm:ladder` closed and 0 of its 5 consumers moved, because each carried a second, unnamed blocker. Never promise that one build unlocks N atoms. A fifth — no passage from a
  real vertex figure to multiplicities — was removed on 2026-08-30.

This goal does not replace the /goal above. Debt work is not progress on 634; report them apart.

## Current standing (2026-08-29)

Neither outcome achieved. The prime case reduces to the base-β branch (primes ≡ 11 mod 12); every
route through it reduces to one crossing question, which nine tool classes provably cannot answer.
The e=1 side and the e≥2 side are the same wall in different costumes. Beeson claims the theorem in
an unrevised preprint whose route we refuted.

**Update 2026-09-12 — the `e = 1` half is closed in Lean for `f ≥ 3`, and it never met the crossing
question.** `E1BaseWord.e1_family_f_ge_3_congruent` (Lean, standard axioms, no `sorry`, two
independent adversarial audits): for any `CongruentDissection` whose target is congruent to the
`m = 1`, `e = 1` base-β target and whose model is congruent to the tile `(f, f²−1, f²)`, `f ≥ 3`,
`False`. Quantifies over exactly the paper's class of tilings (isometries incl. reflections, any
vertex relabelling, `N` free); negative control passed by computation on every real dissection in the
corpus. This is `thm:e1family` for `f ≥ 3` (`f = 2`, `N = 11`, stays on the 135-node search); with
`thm:mod12`/`prop:repunique`/`thm:main` (paper-level) every prime `3f² − 1 ≥ 47` is excluded. Route:
the march on the boundary layer (`MarchInduction` → `MarchSlots` → `RunPartition` → `MarchCompose` →
`E1NormalForm`/`E1BaseWord`); `def:crossQ` is never used. **`e ≥ 2` is untouched** (`N = 83` first,
≈99 % of base-β primes by density); the crossing-question assessment above stands for that branch
only. Details: `private/GOAL_PRIMES.md` (2026-09-12), `lean/PAPER_MAP.md` rows `thm:e1family`,
`thm:e1reduce`, `rem:marchobl`.

**Standing directive (user, 2026-08-29): halt local boundary exhaustion, e-parameter edge tracing,
and point-set topology formalization. Work only on global/scale-dependent invariants.**
*(Flag, 2026-09-12: the `e = 1` result above is local boundary exhaustion, done at the user's explicit
2026-09-12 instruction; whether this directive still stands for `e ≥ 2` is the user's call — it has
not been rewritten here.)*
