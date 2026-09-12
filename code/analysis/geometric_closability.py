"""geometric_closability.py -- exact-arithmetic geometric base-word simulator (Erdos #634).

Unlike code/analysis/base_word_grammar.py and code/analysis/forced_continuation_sim.py, which
track only letter counts (na, nb, nc) and never see real coordinates (see
private/ROOM/e2b13_followup/report_precise.md: forced_continuation_sim's verdict is provably a
function of (prefix[0], prefix[1], na, nb, nc) alone -- it cannot see interior structure), this
module tracks REAL tile placements in exact arithmetic over Q(sqrt D) and asks the actual
geometric question: does a congruent dissection whose base word starts with `prefix_word` jam
(every forced placement escapes/overlaps/violates the base word), complete a tiling, or leave live
continuations open.

GEOMETRY REUSED FROM lean/gen_tree.py (imported directly, not reimplemented):
  - `Geo`         : exact point arithmetic in Q(sqrt Dn), the (X, Y) with real point (X, Y*sqrt(Dn))
                    representation, `ef`/`inside`/`overlap_witness` (escape and overlap tests).
  - `Cons`        : the six-placement enumeration (`self.six`, matching SixPlacements.lean's
                    ordering), `pick_point`/`free_dirs`/`blocked_arcs` (lexicographically-least
                    uncovered vertex + clockwise free ray, i.e. PlacementCompleteness.lean's
                    branching rule), `classify` (escape/overlap/baseword kill tests per placement),
                    `base_edges`/`base_ok` (the base-word constraint machinery).
  - `build_tree`'s recursion pattern (node = uncovered vertex + ray + six classified placements,
    recurse on every live placement) -- reimplemented here as `_explore` because gen_tree.py's
    `build_tree` `assert`s that a completed tiling never occurs (it is only ever run on words
    already known to jam); this module must also detect `tiling_found` and a node-budget cutoff
    (`continues`), which `build_tree` does not need.

TARGET / TILE GEOMETRY for general base-beta (e, f): ported from
private/agent_runs_20260829/gen_basebeta_fixed.py `instance()` (m=1 scale), which is itself
validated there against a real engine instance file. Tile sides (a, b, c) = (e f, f^2 - e^2, f^2);
discriminant D = 4 f^2 - e^2; base length L = e (3 f^2 - e^2); target is the isosceles triangle
(0,0), (L,0), (L/2, (f^2-e^2)/2 * sqrt(D)). This reproduces exactly the (e,f)=(2,3) target used by
lean/gen_tree.py's `lemmaP()` (D=32, target (0,0),(46,0),(23, 5/2 r)) and lean/Erdos634/LemmaPTree.lean.

Per CLAUDE.md's tile-(3,4) exclusion: (e,f) with f - e == ... is not filtered generically here since
(3,4) is not a base-beta (e,f) pair as such (e=3,f=4 gives tile (12,7,16), not (3,4)); this module
simply never constructs tile (3,4) because base-beta tiles are always (ef, f^2-e^2, f^2) and no
(e,f) with e<f produces sides (3,4,x). No engine binary is invoked anywhere in this file.
"""
from __future__ import annotations

import os
import sys
from fractions import Fraction as F
from dataclasses import dataclass, field

_LEAN_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "lean")
if _LEAN_DIR not in sys.path:
    sys.path.insert(0, _LEAN_DIR)

import gen_tree as gt  # noqa: E402  (reused geometry: Geo, Cons, fmt, kill_str)

DEFAULT_NODE_CAP = 4000


def base_beta_target(e: int, f: int):
    """(Dn, target_triangle, (a,b,c)) for the base-beta (e,f) family, m=1.

    Ported from private/agent_runs_20260829/gen_basebeta_fixed.py `instance()`: tile
    (a,b,c) = (ef, f^2-e^2, f^2), D = 4f^2-e^2, base L = e(3f^2-e^2), apex (L/2, b/2 * sqrt(D)).
    Reproduces exactly lean/gen_tree.py's lemmaP() target for (e,f)=(2,3): D=32, target
    (0,0),(46,0),(23, 5/2 r).
    """
    a, b, c = e * f, f * f - e * e, f * f
    Dn = 4 * f * f - e * e
    L = e * (3 * f * f - e * e)
    target = [(F(0), F(0)), (F(L), F(0)), (F(L, 2), F(b, 2))]
    return Dn, target, (a, b, c)


def _letter_lengths(a: int, b: int, c: int) -> dict:
    return {"a": F(a), "b": F(b), "c": F(c)}


class _PrefixCons(gt.Cons):
    """gt.Cons restricted by a base-word prefix: only base_ok within the prefix's own span is
    enforced (identical pattern to gen_tree.py's `lemmaP()`'s ConsP), so nodes past the last
    prefix breakpoint are unconstrained -- exactly the "prefix, not full word" semantics asked
    for by geometric_simulate."""

    def __init__(self, G, bps):
        super().__init__(G, bps)
        self._limit = bps[-1] if bps else F(0)

    def base_ok(self, tri):
        for (_, _, x1, x2) in self.base_edges(tri):
            lo, hi = min(x1, x2), max(x1, x2)
            if lo < self._limit:
                if not any(self.bps[k] == lo and self.bps[k + 1] == hi for k in range(len(self.bps) - 1)):
                    return False
        return True


@dataclass
class _Node:
    id: int
    depth: int
    v: tuple
    d: tuple
    tiles: list
    recs: list
    live_children: dict = field(default_factory=dict)  # placement index -> child node id
    outcome: str = None  # 'jam' | 'complete' | 'cutoff' | 'internal'


def _target_area2(G):
    return abs(G.area2(list(G.T)))


def _placed_area2(G, tiles):
    s = F(0)
    for t in tiles:
        s += abs(G.area2(list(t)))
    return s


def geometric_simulate(prefix_word: str, e: int, f: int, node_cap: int = DEFAULT_NODE_CAP) -> dict:
    """Place tiles following base word `prefix_word` for base-beta parameters (e, f), tracking
    REAL tile coordinates (exact arithmetic in Q(sqrt(4f^2-e^2))) and testing escape/overlap/
    base-word violation at each of the six candidate placements the way
    lean/gen_tree.py + PlacementCompleteness.lean/SixPlacements.lean do.

    Returns {"jam": bool, "tiling_found": bool, "continues": [...], "nodes": [...], "num_nodes": int,
             "Dn": int, "target": [...], "tile_sides": (a,b,c)}.

    - jam=True        : the whole search tree rooted at the empty placement is refuted -- every
                         branch dies in escape/overlap/base-word before the node cap, and no
                         branch completes a tiling. (This is exactly what lean/Erdos634/LemmaPTree.lean
                         proves as a Lean theorem for prefix "acb", (e,f)=(2,3).)
    - tiling_found=True: some branch placed tiles covering the entire target with no live vertex
                         remaining (a genuine congruent dissection consistent with the prefix).
    - continues        : node ids (with their v/d/tile coordinates) where the search was cut off
                         by node_cap before being resolved either way -- an honest "don't know",
                         never silently folded into jam/tiling_found.
    """
    if any(ch not in "abc" for ch in prefix_word):
        raise ValueError("prefix_word must be over the alphabet {a,b,c}, got %r" % prefix_word)
    if (e, f) == (3, 4):
        raise ValueError("tile (3,4,...) parameters are excluded from this tool by instruction")

    Dn, target, (a, b, c) = base_beta_target(e, f)
    LET = _letter_lengths(a, b, c)
    bps = [F(0)]
    for ch in prefix_word:
        bps.append(bps[-1] + LET[ch])
    L = e * (3 * f * f - e * e)
    if bps[-1] > L:
        raise ValueError("prefix_word is longer than the base-beta base length L=%d for (e,f)=(%d,%d)" % (L, e, f))

    G = gt.Geo(Dn, target, (a, b, c))
    cons = _PrefixCons(G, bps)
    tgt_area2 = _target_area2(G)

    nodes: dict[int, _Node] = {}
    counter = {"n": 0}
    tiling_found = {"flag": False}
    cutoffs = []

    def explore(tiles):
        if counter["n"] >= node_cap:
            cutoffs.append({"depth": len(tiles), "tiles": [gt.fmt(p) for tri in tiles for p in tri]})
            return None
        pk = cons.pick_point(tiles)
        if pk is None:
            # no uncovered boundary vertex left: either a genuine complete tiling, or (defensively)
            # an internal inconsistency -- distinguish by comparing placed area to the target area.
            if _placed_area2(G, tiles) == tgt_area2:
                tiling_found["flag"] = True
                nid = counter["n"]; counter["n"] += 1
                nodes[nid] = _Node(id=nid, depth=len(tiles), v=None, d=None, tiles=list(tiles), recs=[], outcome="complete")
                return nid
            # covered-but-incomplete-area should not happen under this branching rule; report as a
            # cutoff (honest unknown) rather than mislabel it jam or tiling_found.
            cutoffs.append({"depth": len(tiles), "note": "pick_point None but area mismatch (unexpected)"})
            return None
        v, d0 = pk
        d = G.unit(d0)
        if d is None:
            cutoffs.append({"depth": len(tiles), "note": "irrational ray at v=%s" % gt.fmt(v)})
            return None
        recs = cons.classify(v, d, tiles)
        nid = counter["n"]; counter["n"] += 1
        node = _Node(id=nid, depth=len(tiles), v=v, d=d, tiles=list(tiles), recs=recs)
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
            if cid is not None:
                node.live_children[i] = cid
        return nid

    root_id = explore([])

    def all_resolved_no_tiling():
        if tiling_found["flag"] or cutoffs:
            return False
        for n in nodes.values():
            if n.outcome == "internal" and len(n.live_children) != sum(1 for r in n.recs if r["kill"] is None):
                return False
        return True

    overall_jam = all_resolved_no_tiling() and root_id is not None

    def node_summary(n: _Node) -> dict:
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
# validation against the Lemma P certificate (private/ROOM/e2b3/report_ramanujan.md §5,
# lean/Erdos634/LemmaPTree.lean): prefix "acb", (e,f)=(2,3) -- must be a 13-node, 6-tile,
# all-jam refutation confined to x <= 22.
# --------------------------------------------------------------------------------------------

def _validate_lemma_p(verbose: bool = True) -> dict:
    result = geometric_simulate("acb", 2, 3)
    expect_nodes = 13
    ok_nodes = result["num_nodes"] == expect_nodes
    ok_jam = result["jam"] is True
    ok_notiling = result["tiling_found"] is False
    ok_cont = result["continues"] == []
    report = {
        "num_nodes": result["num_nodes"],
        "expect_num_nodes": expect_nodes,
        "jam": result["jam"],
        "tiling_found": result["tiling_found"],
        "continues": result["continues"],
        "match": ok_nodes and ok_jam and ok_notiling and ok_cont,
    }
    if verbose:
        print("geometric_simulate('acb', 2, 3):")
        print("  num_nodes=%d (expect %d): %s" % (result["num_nodes"], expect_nodes, "OK" if ok_nodes else "MISMATCH"))
        print("  jam=%s tiling_found=%s continues=%r" % (result["jam"], result["tiling_found"], result["continues"]))
        for n in result["nodes"]:
            print("  node %d depth=%d v=%s d=%s outcome=%s" % (n["id"], n["depth"], n["v"], n["d"], n["outcome"]))
            for pl in n["placements"]:
                print("      sides=%s P=%s Q=%s kill=%s" % (pl["sides"], pl["P"], pl["Q"], pl["kill"]))
    return report


if __name__ == "__main__":
    rep = _validate_lemma_p()
    sys.exit(0 if rep["match"] else 1)
