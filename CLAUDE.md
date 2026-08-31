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

`GOAL_PRIMES.md` at the repo root is the dependency map for outcome (2), the prime case, with every
node's Rule 0 label. It was built from the papers, not from memory. Work proceeds against its
**ordered target list** until a target falls or is proved unreachable; report progress by *target*,
not by count of small steps.

The structure it records, so it is not re-derived each session:

* Primes `N ≢ 11 (mod 12)` are **done** (`thm:mod12` forward VERIFIED, `thm:main`, `thm:primefull`).
* Primes `N ≡ 11 (mod 12)` are exactly the base-β candidates, and since `N` prime forces `m = 1`,
  **the prime case is the `m = 1` base-β family**. It splits `e = 1` / `e ≥ 2`, and both reduce to
  the crossing question (`prop:threecostumes`).
* `e = 1` has two routes. Route 1 (exclude every escape word family) needs families, not
  enumeration — orbits grow 24, 41, 87, 149, 186 at `f = 12…24` — and the march family the recent
  work advances is **7 of 186 orbits at `f = 24`**. Route 2 is `conj:advance`, which if proved
  closes `e = 1` outright and names exactly two gaps, the second general except for its walk
  enumeration. **Route 2 is shorter and better scoped; prefer it.**
* `e ≥ 2` has no route that is not the crossing question itself.

Standing honesty requirement for this goal: the march work is real and small relative to it. Do not
report march progress as prime-case progress without saying which of the 186 orbit-families it
touches.

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
* The four recurring blockers are: no tile-placement layer, no scale or composition map on
  dissections, no certified-search format, no dual-graph development. A fifth — no passage from a
  real vertex figure to multiplicities — was removed on 2026-08-30.

This goal does not replace the /goal above. Debt work is not progress on 634; report them apart.

## Current standing (2026-08-29)

Neither outcome achieved. The prime case reduces to the base-β branch (primes ≡ 11 mod 12); every
route through it reduces to one crossing question, which nine tool classes provably cannot answer.
The e=1 side and the e≥2 side are the same wall in different costumes. Beeson claims the theorem in
an unrevised preprint whose route we refuted.

**Standing directive (user, 2026-08-29): halt local boundary exhaustion, e-parameter edge tracing,
and point-set topology formalization. Work only on global/scale-dependent invariants.**
