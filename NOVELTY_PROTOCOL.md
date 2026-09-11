# The Rediscovery Protocol

**Status: binding. Written 2026-09-06, after six rediscovery events in a single day.**

This document exists because rediscovery on this project is not an occasional slip. It is the
single most expensive recurring failure, it has consumed more compute than every genuine result
combined, and **every previous countermeasure was a rule that an agent could recite and still
violate.** The Erdős seat of room `advance` quoted the settled-instances table *verbatim in its own
audit block* and then launched three of its rows. Reciting is not checking.

The protocol is therefore built on one principle:

> **A control that must be invoked is not a control. A control sits on the path to the action and
> returns non-zero.**

---

## 1. The tools, and what each one is for

| tool | what it does | when |
|---|---|---|
| `code/guard_run.sh` | **Refuses** to launch an engine on an instance already settled in `data/SETTLED.tsv`. Exit 3. | **Every** engine launch. No exceptions. |
| `code/guard_record.sh` | Appends a finished verdict to the registry. | The moment any search terminates. |
| `code/guard_index.sh` | Rebuilds `data/INSTANCE_ALIASES.tsv`, the `(N,tile) → filenames` map. | After adding instance files. |
| `code/guard_selftest.sh` | Both-direction regression: 14 refusals (multi-line and packed formats) + 2 allowances. | After **any** edit to the guard or the registry. |
| `code/novelty_check.sh` | Text search of `lean/`, `paper/`, `private/` for a **conclusion**. | Before formalizing or claiming any statement. |
| `data/SETTLED.tsv` | Registry of settled instances with verdict, node count, citation. | The ground truth. |

**The engine binaries are not to be invoked directly.** `code/guard_run.sh <engine> FILE:<inst>` is
the only sanctioned launch path. A bare `./private/bin/cengine_* FILE:...` in a command,
a script, or a driver loop is a protocol violation regardless of outcome.

---

## 2. The six failure modes, each with its real incident and its control

Every mode below happened. None is hypothetical.

### Mode A — no check at all
**Incident.** `N=66` run for 11 hours. Already published at `paper/erdos-634.tex:825`
(7,232,464 nodes). The run took 32,135,616.
**Why the rule failed.** Rule 4 says "audit before computing". Nothing enforced it.
**Control.** `guard_run.sh` refuses. Verified: exit 3 on this exact instance.

### Mode B — check performed, then not applied to the launch list *(the worst)*
**Incident.** ~9 core-hours on `N=59`, `N=107`, `N=66` again, `N=62`. The seat had
`59 … no tiling 1 838 175` and `107 … no tiling 1 251 382` **quoted verbatim at the top of its own
report**, then reported `(4,5)` as a live measurement and launched `(3,5)` three times.
**Why the rule failed.** The audit was a document produced at the start; the launches came later,
from a driver loop whose instance list nobody re-checked. Auditing the *topic* does not audit the
*queue*.
**Control.** `guard_run.sh` sits per-launch, so a driver loop is checked on every iteration, not
once at the top. Verified on all four instances.

### Mode C — right topic, wrong query
**Incident.** The junction-march was reported as novel; it is
`RunOrientation.corner_anchored_run_all_BG`. `rem:sidenoa` was rediscovered **twice**.
**Why the rule failed.** The grep was for the *subject* ("junction", "march") rather than for the
*conclusion* ("run is all B or all G").
**Control.** `novelty_check.sh` on the **conclusion as you would state it in a theorem**, not on the
object it concerns. If you cannot phrase the conclusion, you do not yet have a result to check.

### Mode D — category error about what a record means
**Incident.** The Euler/dual-graph negative was presented as retiring a `CLAUDE.md` blocker. It is
`rem:spectral` in `paper/erdos-634-obstructions.tex:1746`, already `\lab{PROVED}`.
**Why the rule failed.** `CLAUDE.md`'s four blockers are **formalization** debt (Rule 5 / Lean), not
unexplored mathematical routes. A paper-level proof does not discharge one, and a blocker's
existence does not mean the mathematics is open.
**Control.** Before claiming a route is unexplored, grep `paper/` for the conclusion. "Listed as a
blocker" is evidence the *Lean* is missing and evidence of nothing else.

### Mode E — trusting a broken control
**Incident.** `novelty_check.sh` piped greps into `head`, whose exit status is 0 regardless of
match, so it reported MATCHES FOUND on every run. **Four rediscoveries were committed while it
cried wolf.**
**Why the rule failed.** A control that always fires is indistinguishable from one that never does.
**Control.** `code/guard_selftest.sh` asserts both directions — 10 settled instances must be refused **and** `N=83` must be allowed. It caught a live instance of this mode during its own construction (a `$(basename …)` command substitution silently reset `$?`, so the harness reported the working guard as broken). Every guard ships with a **negative control** that must pass. For `guard_run.sh` the
negative control is `N=83 (5,6)`, the one genuinely open row: it must be *allowed*. If the guard
refuses everything, it is broken. Re-run both directions after any edit.

### Mode F — the same instance under another name
**Incident.** `cev62.txt` and `cevm1_6_7.txt` are the same target. `N=191` exists under **21**
filenames; `N=107` under 7; `N=44` under 8.
**Why the rule failed.** Novelty was judged by filename, which is not the instance's identity.
**Control.** `guard_index.sh` builds the `(N,tile)` alias map and `guard_run.sh` warns when the
target exists elsewhere. It warns rather than refuses, because aliases may carry different
`WALKS`/`CORNERS` riders — same target, different search.

---

## 3. Standing procedure

**Before any engine run** — launch through `guard_run.sh`. If it refuses, read the cited source.
Overriding requires `NOVELTY_OVERRIDE="reason"`, which is logged to `private/guard.log`; the
override exists for re-timing and instrumentation, never for "I want the answer again".

**Before claiming any statement is new** — `code/novelty_check.sh "<the conclusion>"`. Grep the
conclusion, not the topic (Mode C). Search `paper/` as well as `lean/`: a statement can be PROVED in
the papers and absent from Lean, and that is formalization debt, not an open problem (Mode D).

**When a search terminates** — `guard_record.sh` immediately. An unrecorded result will be recomputed.

**When adding instance files** — `guard_index.sh`, and prefer extending an existing instance to
minting a new filename for a target that already exists.

**Reporting.** If a result reproduces a known one, that is the headline, not a footnote. "Reproduces
`tab:basebeta` row N=59" is the finding. Presenting a reproduction as a measurement — as happened
today with `(4,5)` — is the specific error that makes Mode B expensive.

---

## 4. What the registry does not cover, stated honestly

`SETTLED.tsv` covers **computational instances**. It does not cover theorems, lemmas, or
constructions; those are `novelty_check.sh` territory and remain a text search, which is weaker.
Modes C and D are therefore only *mitigated*, not closed. The registry is also only as complete as
what has been recorded into it. The 2026-09-12 data audit (`private/ROOM/data/report_audit.md`)
backfilled the cevian `N=62` and `N=71` exhaustions (both NO_TILING), the `N=104/131/138/92`
figures, the `basealpha N=70` and parallelogram `N=46/52` verdicts, and the two live `m ≥ 2`
searches; it also corrected two wrong rows (cevian `(5,6) N=47` was never finished; `N=63` is
member `(1,2)`, not `(2,3)`). Rows whose instance carries `WALKS`/`CORNERS` riders say so in the
source column — their NO_TILING is conditional on the rider being complete. Backfilling from
`RESEARCH_LOG.md` remains open for anything not listed there.

**The one genuinely open base-β row below 110 is `N=83 (5,6)`.** Everything else in that table is
settled. Any base-β run below `N=110` that is not `N=83` is, by construction, a rediscovery.

---

## 5. Verified witnesses must be persisted (added 2026-09-07)

`guard_record.sh` records **search verdicts**. Nothing recorded **verified geometric witnesses**, and
that gap cost a real object: F1 — a 17-of-23 partial dissection of the `(2,3)` base-β target,
verified in exact `ℚ(√32)` on 2026-09-06 — was written to the log as a *verdict* while its 17 triangles'
coordinates were never saved. A later session searched `private/`, `data/` and `lean/` and found
nothing; the one concrete deliverable in an entire room brief could not be built, from a witness this
project had already verified.

**Rule.** Any geometric object that has been verified — a tiling, a partial dissection, a
counterexample configuration — is written to `data/witnesses/<name>.tsv` **in the same session that
verifies it**, with: the exact field (`ℚ(√D)`), exact coordinates, the verification performed, the
date, the provenance, and the consumer that depends on it. A verdict is not a witness. "It is in the
transcript" is not persistence — transcripts are not greppable by a future session and are not in the
repository.

F1 is now at `data/witnesses/F1_basebeta_2_3_partial17.tsv`, re-verified from disk after writing.

## 6. Stale headers are a rediscovery trap (added 2026-09-07)

Room `tileplace` produced **four** corrections traceable to a single cause: Lean file headers saying
"what this does *not* yet give", written when true and never revised. `DissectionMap.lean` claimed
the `kT → k²` subdivision was unbuilt five days after `thm:ladder` went VERIFIED; `TileAt.lean`
claimed two items were "still untouched" when they were `prop:cornerpara`, not the item named. Two
sessions nearly rebuilt closed work from those headers, and **the moderator repeated the error twice
in the room's own brief**.

**Rule.** A "what is missing" note carries a date. Before believing one, verify against
`lean/PAPER_MAP.md` and the actual declarations — `grep` for the definition, not the prose. When you
close a gap, **delete or date every header that claimed it was open**; a stale note costs more than
no note. A blocker's presence in `CLAUDE.md` is evidence the *Lean* is missing and evidence of
nothing else.
