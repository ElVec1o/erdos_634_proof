"""geometric_closability_fast.py -- algorithmically-optimized drop-in for geometric_simulate().

WHAT WAS PROFILED (see private/ROOM/e2b16/report_speedup.md for the full writeup):
cProfile on a real N=83 (e=5,f=6) length-8 prefix ("acacbaba", node_cap=200) showed the search
spending essentially all of its wall time (84s of 84s) inside `gen_tree.Cons.pick_point` ->
`free_dirs` -> `blocked_arcs`, which for EVERY node re-scans EVERY previously-placed tile against
EVERY candidate uncovered-boundary vertex from scratch (O(vertices_so_far x tiles_so_far) per
node, and both grow with depth). Fraction arithmetic overhead (gcd-normalization on every op)
riding on top of that O(V*T) re-scan accounted for the bulk of the 2.27M Fraction operations
observed. Coordinate denominators themselves stay modest at real N=83 depths (~10^5 at depth 8,
not exploding) -- so the dominant cost is REDUNDANT RECOMPUTATION (profiling category (c) in the
task), not genuine arithmetic blowup (category (a)).

THE ALGORITHMIC FIX: once `blocked_arcs(v, tiles)` returns arcs that already cover the full
angular range around `v` (`free_dirs(v, tiles) == []`, i.e. v has no free direction left), that
fact is MONOTONE in `tiles`: every placement this module ever makes is added to `tiles` and never
removed except by backtracking to an ancestor prefix, so a vertex fully blocked by prefix `tiles`
stays fully blocked by any superset of `tiles` reachable in the same DFS subtree. This is an
honest geometric fact about the search, not a heuristic: `blocked_arcs` only ever gains arcs as
`tiles` grows (existing arcs are never removed by adding a tile), so full angular coverage is
preserved under any tile-set superset.

We exploit this with a tree-scoped memo `_DeadCache`: `explore()` marks a vertex "dead" (skip
`free_dirs` for it entirely, forever within this subtree) the first time `free_dirs` returns `[]`
for it, tagged with the recursion depth at which that was established; on backtracking out of a
node, every dead-mark made *inside* that node's own recursive calls (i.e. at a strictly greater
depth) is rolled back, since a sibling branch has a different last tile and the monotonicity
argument no longer applies to marks made using a tile that is not its ancestor. Marks made at the
current node's own depth (before any child push) remain valid for every child, since all children
share that exact tile-list prefix.

This turns the per-node vertex scan from "re-run full O(tiles) blocked_arcs work for every
candidate vertex" into "skip it in O(1) for every vertex already proven fully blocked, and pay
the full cost only for the (typically few) vertices still live" -- an asymptotic reduction in
the *number of blocked_arcs re-derivations*, not a constant-factor Python/native-code tweak.

`v` not yet touching the boundary at all (`blocked_arcs` returns None, distinct from `[]`) is
NOT cached: a future tile edge can still pass through such a point (on_seg_interior), so that
status is not monotone and must be re-checked every time. Only the `== []` (fully covered) case
is monotone and cached.

No arithmetic representation was changed (still exact Fraction / gen_tree.Geo), and no geometry
predicate was altered: this file imports `gen_tree` and `geometric_closability` unchanged and
only wraps the vertex-visit policy inside `pick_point`. Every result must therefore be bit-for-
bit identical to `geometric_closability.geometric_simulate` -- this is checked directly, not
merely assumed, by `_validate_lemma_p` and `_cross_check` below.
"""
from __future__ import annotations

import os
import sys
from fractions import Fraction as F
from dataclasses import dataclass, field

_LEAN_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "lean")
if _LEAN_DIR not in sys.path:
    sys.path.insert(0, _LEAN_DIR)

import gen_tree as gt  # noqa: E402
import geometric_closability as gc  # noqa: E402

DEFAULT_NODE_CAP = gc.DEFAULT_NODE_CAP


class _FastPrefixCons(gc._PrefixCons):
    """Same semantics as _PrefixCons; adds a tree-scoped "fully blocked" cache to pick_point so
    vertices already proven to have no free direction are never re-scanned against the tile list.

    `mark(depth)` / `rollback(depth)` are called by the caller (the fast `explore`) exactly once
    per recursion frame, bracketing that frame's own work -- NOT per placement -- so a vertex
    found dead while considering candidates at this node stays dead for every child (they extend
    this exact tile-list prefix), and is forgotten again once this node (and its whole subtree)
    is fully explored and we return to try a different placement at the parent.
    """

    def __init__(self, G, bps):
        super().__init__(G, bps)
        self._dead = {}       # v -> depth at which it was marked dead
        self._log = []        # stack of v's marked, in order, for rollback

    def mark_dead(self, v, depth):
        if v not in self._dead:
            self._dead[v] = depth
            self._log.append(v)

    def rollback(self, min_depth):
        """Undo every dead-mark made at recursion depth >= min_depth (i.e. inside a child
        subtree that is now being abandoned in favour of a sibling)."""
        while self._log and self._dead[self._log[-1]] >= min_depth:
            v = self._log.pop()
            del self._dead[v]

    def pick_point(self, tiles):
        """Identical contract to gt.Cons.pick_point, but skips free_dirs entirely for any
        vertex already known (this subtree) to have no free direction."""
        G = self.G
        depth = len(tiles)
        cands = list(G.T)
        for tri in tiles:
            cands.extend(tri)
        uniq = []
        for P in cands:
            if not any(P == Q for Q in uniq):
                uniq.append(P)
        uniq.sort(key=lambda P: (P[1], P[0]))
        for v in uniq:
            if v in self._dead:
                continue
            fd = self.free_dirs(v, tiles)
            if fd is None:
                continue
            if fd == []:
                self.mark_dead(v, depth)
                continue
            starts = [s for (s, e) in fd]
            import functools
            starts.sort(key=functools.cmp_to_key(lambda a, b: -1 if self.ang_lt(a, b) else (1 if self.ang_lt(b, a) else 0)))
            return v, starts[0]
        return None


def geometric_simulate(prefix_word: str, e: int, f: int, node_cap: int = DEFAULT_NODE_CAP) -> dict:
    """Drop-in replacement for geometric_closability.geometric_simulate: identical inputs,
    identical output schema, identical results -- see module docstring for exactly what changed
    (only the vertex re-scan policy inside pick_point) and why the change is sound."""
    if any(ch not in "abc" for ch in prefix_word):
        raise ValueError("prefix_word must be over the alphabet {a,b,c}, got %r" % prefix_word)
    if (e, f) == (3, 4):
        raise ValueError("tile (3,4,...) parameters are excluded from this tool by instruction")

    Dn, target, (a, b, c) = gc.base_beta_target(e, f)
    LET = gc._letter_lengths(a, b, c)
    bps = [F(0)]
    for ch in prefix_word:
        bps.append(bps[-1] + LET[ch])
    L = e * (3 * f * f - e * e)
    if bps[-1] > L:
        raise ValueError("prefix_word is longer than the base-beta base length L=%d for (e,f)=(%d,%d)" % (L, e, f))

    G = gt.Geo(Dn, target, (a, b, c))
    cons = _FastPrefixCons(G, bps)
    tgt_area2 = gc._target_area2(G)

    nodes: dict[int, gc._Node] = {}
    counter = {"n": 0}
    tiling_found = {"flag": False}
    cutoffs = []

    def explore(tiles):
        depth = len(tiles)
        log_mark = len(cons._log)
        try:
            if counter["n"] >= node_cap:
                cutoffs.append({"depth": depth, "tiles": [gt.fmt(p) for tri in tiles for p in tri]})
                return None
            pk = cons.pick_point(tiles)
            if pk is None:
                if gc._placed_area2(G, tiles) == tgt_area2:
                    tiling_found["flag"] = True
                    nid = counter["n"]; counter["n"] += 1
                    nodes[nid] = gc._Node(id=nid, depth=depth, v=None, d=None, tiles=list(tiles), recs=[], outcome="complete")
                    return nid
                cutoffs.append({"depth": depth, "note": "pick_point None but area mismatch (unexpected)"})
                return None
            v, d0 = pk
            d = G.unit(d0)
            if d is None:
                cutoffs.append({"depth": depth, "note": "irrational ray at v=%s" % gt.fmt(v)})
                return None
            recs = cons.classify(v, d, tiles)
            nid = counter["n"]; counter["n"] += 1
            node = gc._Node(id=nid, depth=depth, v=v, d=d, tiles=list(tiles), recs=recs)
            nodes[nid] = node
            live = [i for i, r in enumerate(recs) if r["kill"] is None]
            if not live:
                node.outcome = "jam"
                return nid
            node.outcome = "internal"
            for i in live:
                tiles.append(recs[i]["tri"])
                cid = explore(tiles)
                tiles.pop()
                # a child's own subtree may have marked vertices dead using tiles that included
                # the just-popped placement; those marks are not valid for the next sibling.
                cons.rollback(depth + 1)
                if cid is not None:
                    node.live_children[i] = cid
            return nid
        finally:
            pass

    root_id = explore([])

    def all_resolved_no_tiling():
        if tiling_found["flag"] or cutoffs:
            return False
        for n in nodes.values():
            if n.outcome == "internal" and len(n.live_children) != sum(1 for r in n.recs if r["kill"] is None):
                return False
        return True

    overall_jam = all_resolved_no_tiling() and root_id is not None

    def node_summary(n: gc._Node) -> dict:
        return {
            "id": n.id,
            "depth": n.depth,
            "outcome": n.outcome,
            "v": gt.fmt(n.v) if n.v is not None else None,
            "d": gt.fmt(n.d) if n.d is not None else None,
            "placements": [
                {
                    "sides": r["l"],
                    "P": gt.fmt(r["P"]),
                    "Q": gt.fmt(r["Q"]),
                    "kill": gt.kill_str(r, n.live_children.get(i)),
                }
                for i, r in enumerate(n.recs)
            ] if n.recs else [],
        }

    return {
        "jam": overall_jam,
        "tiling_found": tiling_found["flag"],
        "continues": cutoffs,
        "nodes": [node_summary(nodes[i]) for i in sorted(nodes)],
        "num_nodes": len(nodes),
        "Dn": Dn,
        "target": [gt.fmt(p) for p in target],
        "tile_sides": (a, b, c),
    }


# --------------------------------------------------------------------------------------------
# validation: identical Lemma P certificate check as geometric_closability.py, plus a direct
# cross-check of this module's output dict against the original, unoptimized module, on every
# case exercised in this room (must be byte-for-byte equal, not just same jam/tiling_found).
# --------------------------------------------------------------------------------------------

def _validate_lemma_p(verbose: bool = True) -> dict:
    result = geometric_simulate("acb", 2, 3)
    expect_nodes = 13
    ok_nodes = result["num_nodes"] == expect_nodes
    ok_jam = result["jam"] is True
    ok_notiling = result["tiling_found"] is False
    ok_cont = result["continues"] == []
    report = {
        "num_nodes": result["num_nodes"], "expect_num_nodes": expect_nodes,
        "jam": result["jam"], "tiling_found": result["tiling_found"], "continues": result["continues"],
        "match": ok_nodes and ok_jam and ok_notiling and ok_cont,
    }
    if verbose:
        print("geometric_closability_fast.geometric_simulate('acb', 2, 3): %s" %
              ("MATCH (13-node, all-jam Lemma P certificate)" if report["match"] else "MISMATCH"))
    return report


def _cross_check(prefix_word: str, e: int, f: int, node_cap: int = 4000, verbose: bool = True) -> bool:
    """Run both the original and this fast module on identical inputs and compare full result
    dicts field by field (not just jam/tiling_found) -- a faster-but-wrong oracle is explicitly
    called out (task instructions) as worse than useless, so this checks everything, including
    the full node-by-node trace, not just the summary verdict."""
    r_orig = gc.geometric_simulate(prefix_word, e, f, node_cap=node_cap)
    r_fast = geometric_simulate(prefix_word, e, f, node_cap=node_cap)
    same = (
        r_orig["jam"] == r_fast["jam"]
        and r_orig["tiling_found"] == r_fast["tiling_found"]
        and r_orig["num_nodes"] == r_fast["num_nodes"]
        and r_orig["continues"] == r_fast["continues"]
        and r_orig["nodes"] == r_fast["nodes"]
    )
    if verbose:
        print("cross-check %r (e=%d,f=%d,cap=%d): %s (num_nodes orig=%d fast=%d)" %
              (prefix_word, e, f, node_cap, "MATCH" if same else "MISMATCH", r_orig["num_nodes"], r_fast["num_nodes"]))
    return same


if __name__ == "__main__":
    rep = _validate_lemma_p()
    ok = rep["match"]
    ok = _cross_check("acb", 2, 3) and ok
    ok = _cross_check("acba", 5, 6, node_cap=200) and ok
    ok = _cross_check("acbaba", 5, 6, node_cap=200) and ok
    ok = _cross_check("acacbaba", 5, 6, node_cap=200) and ok
    ok = _cross_check("a", 2, 3, node_cap=200) and ok
    sys.exit(0 if ok else 1)
