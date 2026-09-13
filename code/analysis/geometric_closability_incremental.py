"""geometric_closability_incremental.py -- algorithmic, exact-arithmetic speedup for pick_point via
an incremental per-vertex blocked-arc cache, COMPLEMENTARY to the tree-scoped dead-vertex memo in
geometric_closability_fast.py (report_speedup.md, e2b16). See private/ROOM/e2b17/report_caching.md
for the full writeup, empirical locality measurement, and validation.

WHY THIS IS SOUND (checked against the code, not assumed): `gt.Cons.blocked_arcs(v, tiles)` walks
`tiles` in order and, for each tile `tri`, either (i) contributes exactly one new arc derived from
`tri` alone if `v` is a vertex of `tri` or lies in the interior of one of `tri`'s edges, (ii) forces
the whole result to None forever if `v` lies strictly inside `tri`, or (iii) contributes nothing at
all. Case (iii) means: if `v` does not touch a given tile geometrically (not a vertex of it, not on
an edge-interior of it, not inside it), that tile's presence in `tiles` has ZERO effect on
`blocked_arcs(v, tiles)` -- so when one new tile is appended, `blocked_arcs(v, tiles + [new])` for
any `v` that does not touch `new` is IDENTICAL to `blocked_arcs(v, tiles)`, not merely "still fully
blocked" (that was the coarser fact geometric_closability_fast.py exploited). This lets a vertex
untouched by the newly-placed tile reuse its PARENT node's cached arcs list verbatim -- an exact,
per-tile-local incremental update, not a heuristic.

Empirical locality (private/ROOM/e2b17/instrument_locality.py, unmodified oracle, no caching):
  - Lemma P ('acb', e=2,f=3):        80.61% of parent/child shared candidate-vertex arc computations
                                       are untouched by the new tile (19/98 touched).
  - N=83 (5,6) 'acacbaba', cap=200:  93.19% untouched (350/5138 touched).

DESIGN: `build_child_cache` builds a NEW dict for the child node from the parent's cache dict: for
each candidate vertex already present in the parent, if the new tile does not touch it, its cached
arcs list is copied by reference (O(1)); if it does touch it, exactly ONE per-tile increment is
applied (`tile_contrib` + `apply_tile`) -- never a re-scan of the whole tile list. Brand-new
candidate vertices (introduced by the new tile's own corners) are computed from scratch against the
full tile list once, then cached going forward. No arc list is ever mutated in place, so recursion's
own call stack gives correct rollback on backtracking for free -- no journal needed.

No Fraction/numerical shortcut of any kind: `Geo`/exact arithmetic from `gen_tree.py` is unchanged,
and every geometric predicate (`ef`, `inside`, `cross`, `on_seg_interior`) is called exactly as in
the original, just fewer times.
"""
from __future__ import annotations

import functools
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


# --------------------------------------------------------------------------------------------
# per-tile-local arc computation (exact re-derivation of gt.Cons.blocked_arcs, split so a single
# tile's contribution can be applied to a cached arcs list without rescanning the others)
# --------------------------------------------------------------------------------------------

def _base_arcs(G, cons, v):
    """blocked_arcs(v, []) equivalent: the target-boundary-only contribution."""
    T = G.T
    arcs = []
    hit = False
    for i in range(3):
        A, B = T[i], T[(i + 1) % 3]
        if v == A:
            C = T[(i + 2) % 3]
            dB, dC = G.sub(B, A), G.sub(C, A)
            arcs.append((dC, G.smul(-1, dB)))
            arcs.append((G.smul(-1, dB), dB))
            hit = True
            break
        if cons.on_seg_interior(v, A, B):
            arcs.append((G.sub(A, B), G.sub(B, A)))
            hit = True
            break
    if not hit and not G.inside(T, v):
        return None
    return arcs


def _tile_contrib(G, cons, v, tri):
    """('none',) | ('arc', (d1,d2)) | ('inside',) -- tri's exact effect on blocked_arcs(v, .)."""
    for i in range(3):
        if v == tri[i]:
            P, Q = tri[(i + 1) % 3], tri[(i + 2) % 3]
            d1, d2 = G.sub(P, v), G.sub(Q, v)
            return ('arc', (d1, d2) if G.cross(d1, d2) > 0 else (d2, d1))
    for i in range(3):
        A, B = tri[i], tri[(i + 1) % 3]
        if cons.on_seg_interior(v, A, B):
            C = tri[(i + 2) % 3]
            if G.cross(G.sub(B, A), G.sub(C, A)) > 0:
                return ('arc', (G.sub(B, A), G.sub(A, B)))
            return ('arc', (G.sub(A, B), G.sub(B, A)))
    if G.inside(tri, v, True):
        return ('inside',)
    return ('none',)


def _apply(arcs, contrib):
    if arcs is None:
        return None
    kind = contrib[0]
    if kind == 'inside':
        return None
    if kind == 'none':
        return arcs
    return arcs + [contrib[1]]  # new list -- never mutates the cached parent list


def _free_dirs_from_arcs(cons, arcs):
    """Exact port of gt.Cons.free_dirs's body, operating on an already-known arcs list."""
    if arcs is None:
        return None
    D_ = []
    for (s, e) in arcs:
        for d in (s, e):
            if not any(cons.ang_eq(d, x) for x in D_):
                D_.append(d)
    if len(D_) < 2:
        return []
    D_.sort(key=functools.cmp_to_key(lambda a, b: -1 if cons.ang_lt(a, b) else (1 if cons.ang_lt(b, a) else 0)))
    free = []
    n = len(D_)
    for i in range(n):
        d1, d2 = D_[i], D_[(i + 1) % n]
        if not any(cons.sub_in_arc(s, e, d1, d2) for (s, e) in arcs):
            free.append((d1, d2))
    return free


def _cand_list(G, tiles):
    cands = list(G.T)
    for tri in tiles:
        cands.extend(tri)
    uniq = []
    for P in cands:
        if not any(P == Q for Q in uniq):
            uniq.append(P)
    uniq.sort(key=lambda P: (P[1], P[0]))
    return uniq


def _get_entry_lazy(G, cons, v, tiles, new_tri, parent_cache, local_cache):
    """Lazy, on-demand version of the per-vertex (arcs, free_dirs) lookup: only ever does work for
    a vertex `pick_point` actually visits (preserving the ORIGINAL's early-termination behaviour --
    it stops at the first candidate with a free direction, so most candidates are never inspected
    at all). Caches BOTH the arcs list and its derived `free_dirs` result together: when the new
    tile does not touch `v`, arcs (hence free_dirs) is provably unchanged (see module docstring),
    so `free_dirs` is not just cheaply re-derivable but reused verbatim -- stacking with the
    dead-vertex idea from geometric_closability_fast.py rather than duplicating it.
    `local_cache` accumulates exactly the entries this node actually queried, and becomes the
    `parent_cache` handed to this node's children -- so a vertex never queried at this node costs
    nothing here and is recomputed (once) only if some descendant later needs it."""
    if v in local_cache:
        return local_cache[v]
    if v in parent_cache:
        arcs, fd = parent_cache[v]
        if new_tri is not None and arcs is not None:
            contrib = _tile_contrib(G, cons, v, new_tri)
            if contrib[0] != 'none':
                new_arcs = _apply(arcs, contrib)
                entry = (new_arcs, _free_dirs_from_arcs(cons, new_arcs))
                local_cache[v] = entry
                return entry
        local_cache[v] = (arcs, fd)
        return (arcs, fd)
    arcs = _base_arcs(G, cons, v)
    for tri in tiles:
        if arcs is None:
            break
        arcs = _apply(arcs, _tile_contrib(G, cons, v, tri))
    entry = (arcs, _free_dirs_from_arcs(cons, arcs))
    local_cache[v] = entry
    return entry


def _pick_point_cached(G, cons, tiles, parent_cache):
    """Returns (result, local_cache) where local_cache holds exactly the vertices queried at this
    node (to be passed down as the parent_cache for this node's children)."""
    new_tri = tiles[-1] if tiles else None
    cands = _cand_list(G, tiles)
    local_cache = {}
    for v in cands:
        _, fd = _get_entry_lazy(G, cons, v, tiles, new_tri, parent_cache, local_cache)
        if fd is None:
            continue
        if fd:
            starts = [s for (s, e) in fd]
            starts.sort(key=functools.cmp_to_key(lambda a, b: -1 if cons.ang_lt(a, b) else (1 if cons.ang_lt(b, a) else 0)))
            return (v, starts[0]), local_cache
    return None, local_cache


# --------------------------------------------------------------------------------------------
# drop-in geometric_simulate, identical schema to geometric_closability.geometric_simulate
# --------------------------------------------------------------------------------------------

def geometric_simulate(prefix_word: str, e: int, f: int, node_cap: int = DEFAULT_NODE_CAP) -> dict:
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
    cons = gc._PrefixCons(G, bps)
    tgt_area2 = gc._target_area2(G)

    nodes: dict[int, gc._Node] = {}
    counter = {"n": 0}
    tiling_found = {"flag": False}
    cutoffs = []

    def explore(tiles, parent_cache):
        depth = len(tiles)
        if counter["n"] >= node_cap:
            cutoffs.append({"depth": depth, "tiles": [gt.fmt(p) for tri in tiles for p in tri]})
            return None
        pk, cache = _pick_point_cached(G, cons, tiles, parent_cache)
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
            cid = explore(tiles, cache)
            tiles.pop()
            if cid is not None:
                node.live_children[i] = cid
        return nid

    root_id = explore([], {})

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
# validation: identical Lemma P certificate check, plus a full field-by-field cross-check against
# the original, unmodified geometric_closability.geometric_simulate.
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
        print("geometric_closability_incremental.geometric_simulate('acb', 2, 3): %s" %
              ("MATCH (13-node, all-jam Lemma P certificate)" if report["match"] else "MISMATCH"))
    return report


def _cross_check(prefix_word: str, e: int, f: int, node_cap: int = 4000, verbose: bool = True) -> bool:
    r_orig = gc.geometric_simulate(prefix_word, e, f, node_cap=node_cap)
    r_inc = geometric_simulate(prefix_word, e, f, node_cap=node_cap)
    same = (
        r_orig["jam"] == r_inc["jam"]
        and r_orig["tiling_found"] == r_inc["tiling_found"]
        and r_orig["num_nodes"] == r_inc["num_nodes"]
        and r_orig["continues"] == r_inc["continues"]
        and r_orig["nodes"] == r_inc["nodes"]
    )
    if verbose:
        print("cross-check %r (e=%d,f=%d,cap=%d): %s (num_nodes orig=%d inc=%d)" %
              (prefix_word, e, f, node_cap, "MATCH" if same else "MISMATCH", r_orig["num_nodes"], r_inc["num_nodes"]))
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
