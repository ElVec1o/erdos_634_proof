"""run_composition_probe.py -- tests the "flat-run composition" idea for non-exhaustive reasoning
about long base words (Erdos #634, e2b16 wildcard room, 2026-09-13).

BACKGROUND (read first: private/ROOM/e2b14/VERDICT.md, e2b15_followup/report.md,
code/analysis/geometric_closability.py). The exact-coordinate oracle geometric_simulate() is
exhaustive over the six-placement branching rule and costs ~150ms/node at depth 8 -- real N=83
words are 16-28 letters, far out of reach by brute force (e2b15's finding).

THE IDEA TESTED HERE (composition / non-exhaustive reduction, not yet a proof):
SYNTHESIS_2026-09-13.md S8 records that a- and c-tiles form a "flat layer" along the base line and
only b-tiles are geometric "spikes". If that is right at the level of the SIX-PLACEMENT BRANCHING
RULE itself (not just heights), then a maximal run of a/c letters between two b's should almost
always have EXACTLY ONE live child at every step (the six-placement rule collapses to a forced
placement when the frontier vertex sits on the flat base line with no b-spike interaction nearby),
and the net effect of the whole run is a pure horizontal translation by the sum of the run's tile
base-lengths. If TRUE and provable, the exhaustive tree over an L-letter a/c run (cost ~6^L) could
be replaced by a single O(1) translation step, and a whole 16-28 letter word's cost would collapse
from exponential-in-length to O(#b-tiles) branching steps -- reaching real N=83 word lengths.

THIS SCRIPT ONLY TESTS THE HYPOTHESIS. It does not claim a proof, and it does not silently assume
the reduction: it runs the REAL exhaustive oracle (geometric_closability.geometric_simulate, via
its internal node structure) on real legal-prefix words up to the tractable depth, and reports,
letter-by-letter, whether branching (more than one live child) ever occurs at an a/c letter versus
a b letter. It is a probe, not an engine, and invokes no engine binary (Rule 0.5).
"""
from __future__ import annotations
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import geometric_closability as gc  # noqa: E402


def branching_profile(prefix_word: str, e: int, f: int, node_cap: int = 4000) -> dict:
    """Run geometric_simulate and, from its returned node list, recover for each *depth* (= index
    into prefix_word, since nodes are emitted in placement order along the single explored path
    when there is no branching) how many live (non-killed) placements existed, and cross-reference
    against the prefix letter nominally being placed at that depth.

    Returns {"depths": [ {"idx","letter","num_live","live_kinds"} ... ], "jam":..., "num_nodes":...}
    honest about any node the oracle could not resolve (cutoff) -- those are reported, not hidden.
    """
    res = gc.geometric_simulate(prefix_word, e, f, node_cap=node_cap)
    depths = []
    for n in res["nodes"]:
        if n["outcome"] not in ("jam", "internal"):
            continue
        letter = prefix_word[n["depth"]] if n["depth"] < len(prefix_word) else None
        live = [p for p in n["placements"] if p["kill"] in (None,) or (isinstance(p["kill"], str) and p["kill"].startswith("child"))]
        # gt.kill_str: None-kill placements show as "child N" once recursed, else "live" marker;
        # count from raw kill field instead for correctness.
        num_live = sum(1 for p in n["placements"] if p["kill"] not in ("escape", "overlap", "baseword"))
        depths.append({
            "idx": n["depth"], "letter": letter, "num_live": num_live,
            "kinds": [p["sides"] for p in n["placements"]],
        })
    return {"depths": depths, "jam": res["jam"], "tiling_found": res["tiling_found"],
            "continues": res["continues"], "num_nodes": res["num_nodes"]}


def summarize(words, e, f, node_cap=4000, max_len=7):
    """For each word truncated to the tractable prefix length, report branching by letter type."""
    by_letter = {"a": [0, 0], "b": [0, 0], "c": [0, 0]}  # letter -> [branch_count, total_count]
    rows = []
    for w in words:
        wt = w[:max_len]
        t0 = time.time()
        try:
            prof = branching_profile(wt, e, f, node_cap=node_cap)
        except Exception as exc:  # honest: record failure, don't hide it
            rows.append({"word": wt, "error": repr(exc)})
            continue
        dt = time.time() - t0
        for d in prof["depths"]:
            if d["letter"] is None:
                continue
            by_letter[d["letter"]][1] += 1
            if d["num_live"] > 1:
                by_letter[d["letter"]][0] += 1
        rows.append({"word": wt, "num_nodes": prof["num_nodes"], "jam": prof["jam"],
                     "continues": prof["continues"], "time_s": round(dt, 3),
                     "branch_depths": [d["idx"] for d in prof["depths"] if d["num_live"] > 1]})
    return rows, by_letter


if __name__ == "__main__":
    # Real N=83 residue prefixes from private/ROOM/SYNTHESIS_2026-09-13.md's family (e,f)=(5,6):
    # take a handful of the R2-legal, un-killed residue words' 7-letter prefixes (constructed from
    # base_word_grammar's own legal alphabet/column structure, not invented ad hoc).
    test_words = [
        "aacbaba", "aabcaba", "acacbab", "aaccbab",
    ]
    if len(sys.argv) > 3:
        test_words = sys.argv[3].split(",")
    e, f = 5, 6
    max_len = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    rows, by_letter = summarize(test_words, e, f, node_cap=cap, max_len=max_len)
    print(f"word truncated-to-{max_len} : num_nodes jam continues branch_depths", flush=True)
    for r in rows:
        if "error" in r:
            print(" ", r["word"], "ERROR", r["error"], flush=True)
        else:
            print(" ", r["word"], r["num_nodes"], r["jam"], r["continues"], r["branch_depths"], flush=True)
    print()
    print("branching by letter type (branch_count / total_times_that_letter_was_the_active_depth):")
    for L, (bc, tot) in by_letter.items():
        print(f"  {L}: {bc}/{tot}")
