"""float_pick_point.py -- validated float64 port of lean/gen_tree.py's Cons.pick_point
(vertex + free-direction selection), for Erdos #634 geometric closability search.

CONTEXT (private/ROOM/e2b16/VERDICT.md, report_asymptotic.md, report_speedup.md,
report_wildcard_nonexhaustive.md): classify() was sped up 16-18x by
code/analysis/float_geometric_prefilter.py, but end-to-end this did not help, because
pick_point (scanning placed tiles + target boundary to find the lexicographically-least
uncovered vertex and its free clockwise direction, via blocked_arcs/free_dirs) dominates cost
on wide/hard trees and stayed on exact Fraction arithmetic. This module is a float-native
pick_point with a conservative exact fallback ("border" pattern), attempting to close that gap.

WHY THIS IS HARDER THAN classify's TOLERANCE DESIGN: classify's decisions are simple sign
tests on edge functionals / overlap areas. pick_point additionally does ANGULAR SORTING and
ARC MERGING: it tests direction equality (ang_eq: cross==0 and dot>0), point coincidence
(v == A), collinearity + range containment (on_seg_interior), and arc-endpoint-in-arc tests
(in_arc/sub_in_arc) that chain several of the above. A single misjudged equality/sign here does
not just cost time (as an over-cautious "border" flag would in classify) -- it can silently
MERGE OR SPLIT ANGULAR ARCS WRONG, producing a wrong blocked/free decomposition and hence a
wrong (v, d), not merely a slow one. Every one of these decisions is therefore wrapped in a
3-way test: confidently one way, confidently the other, or BORDER -- and BORDER anywhere along
the computation aborts the float attempt for that pick_point call and falls back to the exact
(Fraction) `gen_tree.Cons.pick_point` on the true exact tile coordinates. This module is only
ever run alongside the exact tile list (never asked to reconstruct exactness from floats), so
the fallback is always exact, not a guess.

No engine binary is invoked anywhere in this file; no tile (3,4) is constructed (see
geometric_closability.base_beta_target).
"""
from __future__ import annotations

import functools
import math
import os
import sys

_LEAN_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "lean")
if _LEAN_DIR not in sys.path:
    sys.path.insert(0, _LEAN_DIR)

import gen_tree as gt  # noqa: E402


class PickPointBorder(Exception):
    """Raised the instant any decision inside float pick_point is within tolerance of a
    boundary. Callers must catch this and fall back to the exact oracle -- it is not an error,
    it is the designed escape hatch."""
    def __init__(self, reason, **ctx):
        super().__init__(reason)
        self.reason = reason
        self.ctx = ctx


# Two-band tolerance, same pattern as float_geometric_prefilter.NOISE_FLOOR/EPS:
#   below REL_NOISE_FLOOR * scale  -> confidently a true zero/equal (common: shared tile
#                                      corners, vertices exactly on target boundary)
#   above REL_BORDER * scale       -> confidently nonzero/distinct
#   in between                     -> BORDER, fall back to exact
# Values are RELATIVE to a per-call coordinate scale (not absolute), since base-beta targets
# range from L~46 (e,f)=(2,3) up to L~hundreds for larger (e,f).
REL_NOISE_FLOOR = 1e-10
REL_BORDER = 1e-7


class FGeoPP:
    """Float geometry primitives for pick_point, each decision 3-way (pos/neg/BORDER-raise)."""

    def __init__(self, Dn: int, target):
        self.Dn = float(Dn)
        self.T = [(float(x), float(y)) for (x, y) in target]
        # a fixed coordinate scale for this target, used to make tolerances relative but stable
        # across a whole run (not recomputed per-comparison from the two operands only, which
        # would let two tiny-but-consistent quantities look "confidently equal" to each other).
        self.scale = max(1.0, max(abs(x) for (x, y) in self.T), max(abs(y) for (x, y) in self.T))

    def sub(self, A, B): return (A[0] - B[0], A[1] - B[1])
    def add(self, A, B): return (A[0] + B[0], A[1] + B[1])
    def smul(self, s, A): return (s * A[0], s * A[1])
    def cross(self, u, v): return u[0] * v[1] - u[1] * v[0]
    def dot(self, u, v): return u[0] * v[0] + self.Dn * u[1] * v[1]
    def norm2(self, u): return self.dot(u, u)
    def ef(self, A, B, P): return (B[0] - A[0]) * (P[1] - A[1]) - (P[0] - A[0]) * (B[1] - A[1])

    def _scale_for(self, *vecs_or_scalars):
        s = self.scale
        for v in vecs_or_scalars:
            if isinstance(v, tuple):
                s = max(s, abs(v[0]), abs(v[1]))
            else:
                s = max(s, abs(v))
        return s

    def sgn3(self, x, *scale_inputs, reason="sgn"):
        """3-way sign, relative to a scale derived from the inputs that produced x (e.g. the
        vectors whose cross/dot gave x): pos, neg, or raise PickPointBorder."""
        scale = self._scale_for(*scale_inputs)
        # for a cross/dot of two vectors the natural magnitude is ~scale^2 (or scale for ef of
        # points at this coordinate scale); use scale**2 as the reference so tolerance grows
        # with the actual sizes of the quantities being compared, not just point coordinates.
        ref = max(scale, scale * scale, 1.0)
        if abs(x) < REL_NOISE_FLOOR * ref:
            return 0  # confidently exact zero (common: shared edges/corners by construction)
        if x > REL_BORDER * ref:
            return 1
        if x < -REL_BORDER * ref:
            return -1
        raise PickPointBorder(reason, x=x, ref=ref)

    def pt_eq(self, P, Q, reason="pt_eq"):
        d = max(abs(P[0] - Q[0]), abs(P[1] - Q[1]))
        scale = self._scale_for(P, Q)
        if d < REL_NOISE_FLOOR * scale:
            return True
        if d > REL_BORDER * scale:
            return False
        raise PickPointBorder(reason, P=P, Q=Q, d=d, scale=scale)

    def inside(self, tri, P, strict=False):
        for i in range(3):
            e = self.ef(tri[i], tri[(i + 1) % 3], P)
            s = self.sgn3(e, tri[i], tri[(i + 1) % 3], P, reason="inside_edge")
            if s < 0:
                return False
            if strict and s == 0:
                return False
        return True

    def unit(self, w):
        L2 = self.norm2(w)
        if L2 <= (REL_NOISE_FLOOR * self.scale) ** 2:
            return None
        return (w[0] / math.sqrt(L2), w[1] / math.sqrt(L2))


class FConsPP:
    """Float pick_point, structurally identical to gt.Cons.pick_point/free_dirs/blocked_arcs,
    every equality/sign test routed through FGeoPP's 3-way primitives; any PickPointBorder
    propagates straight up to the caller (geometric_simulate_float2 below), which falls back to
    the exact oracle for that node."""

    def __init__(self, G: FGeoPP):
        self.G = G

    def half(self, d):
        try:
            sy = self.G.sgn3(d[1], d, reason="half_y")
        except PickPointBorder:
            raise
        if sy > 0: return 0
        if sy < 0: return 1
        # d[1] == 0 confidently: sign of d[0] decides
        sx = self.G.sgn3(d[0], d, reason="half_x")
        return 0 if sx > 0 else 1

    def ang_lt(self, d1, d2):
        h1, h2 = self.half(d1), self.half(d2)
        if h1 != h2:
            return h1 < h2
        c = self.G.cross(d1, d2)
        return self.G.sgn3(c, d1, d2, reason="ang_lt_cross") > 0

    def ang_eq(self, d1, d2):
        c = self.G.cross(d1, d2)
        if self.G.sgn3(c, d1, d2, reason="ang_eq_cross") != 0:
            return False
        dt = self.G.dot(d1, d2)
        return self.G.sgn3(dt, d1, d2, reason="ang_eq_dot") > 0

    def in_arc(self, s, e, x):
        if self.ang_eq(s, x) or self.ang_eq(e, x):
            return True
        c1 = self.G.sgn3(self.G.cross(s, x), s, x, reason="in_arc_1")
        c2 = self.G.sgn3(self.G.cross(x, e), x, e, reason="in_arc_2")
        return c1 >= 0 and c2 >= 0

    def sub_in_arc(self, s, e, d1, d2):
        if not (self.in_arc(s, e, d1) and self.in_arc(s, e, d2)):
            return False
        c = self.G.sgn3(self.G.cross(d1, d2), d1, d2, reason="sub_in_arc_cross")
        if c > 0:
            return True
        if c == 0:
            if self.G.sgn3(self.G.dot(d1, d2), d1, d2, reason="sub_in_arc_dot") > 0:
                return True
            return self.ang_eq(s, d1) and self.ang_eq(e, d2)
        return False

    def on_seg_interior(self, P, A, B):
        G = self.G
        d = G.sub(B, A)
        cr = G.cross(d, G.sub(P, A))
        if G.sgn3(cr, d, G.sub(P, A), reason="onseg_cross") != 0:
            return False
        t = G.dot(G.sub(P, A), d)
        dd = G.dot(d, d)
        # 0 < t < dd, both compared with the same scale-aware tolerance
        s1 = G.sgn3(t, d, reason="onseg_t")
        s2 = G.sgn3(dd - t, d, reason="onseg_ddt")
        return s1 > 0 and s2 > 0

    def blocked_arcs(self, v, tiles):
        G = self.G
        T = G.T
        arcs = []
        hit = False
        for i in range(3):
            A, B = T[i], T[(i + 1) % 3]
            if G.pt_eq(v, A, reason="blocked_vA"):
                C = T[(i + 2) % 3]
                dB, dC = G.sub(B, A), G.sub(C, A)
                arcs.append((dC, G.smul(-1, dB)))
                arcs.append((G.smul(-1, dB), dB))
                hit = True
                break
            if self.on_seg_interior(v, A, B):
                arcs.append((G.sub(A, B), G.sub(B, A)))
                hit = True
                break
        if not hit and not G.inside(T, v):
            return None
        for tri in tiles:
            done = False
            for i in range(3):
                if G.pt_eq(v, tri[i], reason="blocked_vtile"):
                    P, Q = tri[(i + 1) % 3], tri[(i + 2) % 3]
                    d1, d2 = G.sub(P, v), G.sub(Q, v)
                    c = G.sgn3(G.cross(d1, d2), d1, d2, reason="blocked_tile_cross")
                    arcs.append((d1, d2) if c > 0 else (d2, d1))
                    done = True
                    break
            if done:
                continue
            for i in range(3):
                A, B = tri[i], tri[(i + 1) % 3]
                if self.on_seg_interior(v, A, B):
                    C = tri[(i + 2) % 3]
                    c = G.sgn3(G.cross(G.sub(B, A), G.sub(C, A)), G.sub(B, A), G.sub(C, A), reason="blocked_tile_edge")
                    if c > 0:
                        arcs.append((G.sub(B, A), G.sub(A, B)))
                    else:
                        arcs.append((G.sub(A, B), G.sub(B, A)))
                    done = True
                    break
            if done:
                continue
            if G.inside(tri, v, True):
                return None
        return arcs

    def free_dirs(self, v, tiles):
        arcs = self.blocked_arcs(v, tiles)
        if arcs is None:
            return None
        D_ = []
        for (s, e) in arcs:
            for d in (s, e):
                if not any(self.ang_eq(d, x) for x in D_):
                    D_.append(d)
        if len(D_) < 2:
            return []
        D_.sort(key=functools.cmp_to_key(lambda a, b: -1 if self.ang_lt(a, b) else (1 if self.ang_lt(b, a) else 0)))
        free = []
        n = len(D_)
        for i in range(n):
            d1, d2 = D_[i], D_[(i + 1) % n]
            if not any(self.sub_in_arc(s, e, d1, d2) for (s, e) in arcs):
                free.append((d1, d2))
        return free

    def pick_point(self, tiles):
        G = self.G
        cands = list(G.T)
        for tri in tiles:
            cands.extend(tri)
        uniq = []
        for P in cands:
            if not any(G.pt_eq(P, Q, reason="pickpoint_dedupe") for Q in uniq):
                uniq.append(P)
        uniq.sort(key=lambda P: (P[1], P[0]))
        for v in uniq:
            fd = self.free_dirs(v, tiles)
            if fd is None:
                continue
            if fd:
                starts = [s for (s, e) in fd]
                starts.sort(key=functools.cmp_to_key(lambda a, b: -1 if self.ang_lt(a, b) else (1 if self.ang_lt(b, a) else 0)))
                return v, starts[0]
        return None


def float_pick_point(Dn, target, tiles_float):
    """Attempt float pick_point; returns (v, d) or None (no candidate) on success, or raises
    PickPointBorder if any internal decision was too close to call -- caller must fall back to
    the exact `gen_tree.Cons.pick_point` on the true exact tiles for that node."""
    G = FGeoPP(Dn, target)
    cons = FConsPP(G)
    return cons.pick_point(tiles_float)


def exact_pick_point(cons_exact, tiles_exact):
    return cons_exact.pick_point(tiles_exact)


def to_float_tiles(tiles_exact):
    return [tuple((float(x), float(y)) for (x, y) in tri) for tri in tiles_exact]


def hybrid_pick_point(cons_exact, tiles_exact, Dn, target):
    """Try float first; on ANY border, fall back to full exact pick_point. Returns
    (result, used_exact: bool). This is the SAFE fallback: if float raises border anywhere
    (including while scanning candidate vertices earlier than the eventual winner), the whole
    call redoes the work exactly from scratch. See `targeted_hybrid_pick_point` for the actual
    speedup mechanism used in the end-to-end test."""
    tf = to_float_tiles(tiles_exact)
    try:
        r = float_pick_point(Dn, target, tf)
        return r, False
    except PickPointBorder:
        return exact_pick_point(cons_exact, tiles_exact), True


def targeted_hybrid_pick_point(cons_exact, tiles_exact, Dn, target):
    """The actual speedup mechanism: exact pick_point's own cost is dominated by re-deriving
    free_dirs (an O(#tiles) scan) from scratch for every candidate vertex up to and including the
    eventual winner, at every node -- most of those earlier candidates are already fully blocked
    and just get discarded. Here, float pick_point (cheap) is used ONLY to identify WHICH
    candidate vertex wins and to skip straight to it; the winning vertex's free_dirs is then
    recomputed EXACTLY (not trusted from float) to get a certified (v, d). This is safe because:
    - if float raises PickPointBorder at any point (including while scanning to find the winner),
      we fall back to the fully exact pick_point, unchanged;
    - if float returns a winner, we still call the EXACT free_dirs on the EXACT vertex that
      matches it (never trusting float's own direction/arc output) -- so the returned (v, d) is
      always exactly what gen_tree.Cons.pick_point would have returned, never an approximation.
    Returns (result, used_exact: bool) where used_exact=True means the float stage could not
    identify a safe target (border, or no float/exact vertex match) and full exact pick_point ran.
    """
    tf = to_float_tiles(tiles_exact)
    try:
        r = float_pick_point(Dn, target, tf)
    except PickPointBorder:
        return exact_pick_point(cons_exact, tiles_exact), True

    G = cons_exact.G
    cands = list(G.T)
    for tri in tiles_exact:
        cands.extend(tri)
    uniq = []
    for P in cands:
        if not any(P == Q for Q in uniq):
            uniq.append(P)
    uniq.sort(key=lambda P: (P[1], P[0]))

    if r is None:
        # float found no free vertex among ALL candidates -- must confirm exactly, since a wrong
        # "no vertex free" verdict would silently mis-classify a live node as complete/jam.
        return exact_pick_point(cons_exact, tiles_exact), True

    vf, _df = r
    match = None
    for v in uniq:
        if abs(float(v[0]) - vf[0]) < 1e-6 and abs(float(v[1]) - vf[1]) < 1e-6:
            match = v
            break
    if match is None:
        return exact_pick_point(cons_exact, tiles_exact), True

    fd = cons_exact.free_dirs(match, tiles_exact)
    if not fd:
        # float said this vertex is free but exact says blocked/invalid -- disagreement, do not
        # trust float; fall back to full exact scan (this should never happen given validation,
        # but the fallback exists precisely so a silent wrong answer is impossible if it did).
        return exact_pick_point(cons_exact, tiles_exact), True
    starts = [s for (s, e) in fd]
    starts.sort(key=functools.cmp_to_key(lambda a, b: -1 if cons_exact.ang_lt(a, b) else (1 if cons_exact.ang_lt(b, a) else 0)))
    return (match, starts[0]), False


def geometric_simulate_hybrid(prefix_word: str, e: int, f: int, node_cap: int = 4000,
                               time_budget: float | None = None) -> dict:
    """End-to-end search combining this module's targeted_hybrid_pick_point with
    float_geometric_prefilter.FCons.classify3 (per-node exact fallback on ANY border flag).
    Ground-truth tile coordinates always stay exact (Fraction); float is used only to (a) pick
    the winning vertex/direction, verified exactly before use, and (b) skip exact `third`/kill
    computation for placements float confidently kills. See report at
    private/ROOM/e2b17/report_pickpoint.md for validation and speedup measurements -- this
    function reproduces exactly what was measured there, not a new untested path.

    Returns {"outcome": "jam"|"complete"|"cutoff", "elapsed": float,
             "num_nodes": int, "pp_exact_fallback": int, "cl_exact_fallback": int}.
    NEVER invokes an engine binary; excludes tile (3,4) via base_beta_target.
    """
    import time as _time
    import geometric_closability as gc
    from float_geometric_prefilter import FGeo, FCons

    Dn, target, (a, b, c) = gc.base_beta_target(e, f)
    Gexact = gt.Geo(Dn, target, (a, b, c))
    from fractions import Fraction as F
    bps = [F(0)]
    LET = {"a": F(a), "b": F(b), "c": F(c)}
    for ch in prefix_word:
        bps.append(bps[-1] + LET[ch])
    cons_exact = gc._PrefixCons(Gexact, bps)

    Gf = FGeo(Dn, target, (a, b, c))
    LETf = {"a": float(a), "b": float(b), "c": float(c)}
    bpsf = [0.0]
    for ch in prefix_word:
        bpsf.append(bpsf[-1] + LETf[ch])
    fcons = FCons(Gf, bpsf)

    stats = {"nodes": 0, "pp_exact_fallback": 0, "cl_exact_fallback": 0}
    t0 = _time.time()

    def explore(tiles):
        if stats["nodes"] >= node_cap or (time_budget is not None and (_time.time() - t0) > time_budget):
            return "cutoff"
        pk, used_exact = targeted_hybrid_pick_point(cons_exact, tiles, Dn, target)
        if used_exact:
            stats["pp_exact_fallback"] += 1
        stats["nodes"] += 1
        if pk is None:
            tgt_area2 = abs(Gexact.area2(list(Gexact.T)))
            placed = sum(abs(Gexact.area2(list(t))) for t in tiles)
            return "complete" if placed == tgt_area2 else "cutoff"
        v, d0 = pk
        d = Gexact.unit(d0)
        if d is None:
            return "cutoff"
        vF = (float(v[0]), float(v[1]))
        dF = (float(d[0]), float(d[1]))
        tilesF = [tuple((float(x), float(y)) for (x, y) in tri) for tri in tiles]
        recs_f = fcons.classify3(vF, dF, tilesF)
        if any(r.get("border") for r in recs_f):
            stats["cl_exact_fallback"] += 1
            recs = cons_exact.classify(v, d, tiles)
            live = [i for i, r in enumerate(recs) if r["kill"] is None]
            if not live:
                return "jam"
            outcomes = []
            for i in live:
                tiles.append(recs[i]["tri"])
                outcomes.append(explore(tiles))
                tiles.pop()
                if outcomes[-1] == "cutoff":
                    break
        else:
            live = [i for i, r in enumerate(recs_f) if r["kill"] is None]
            if not live:
                return "jam"
            outcomes = []
            for i in live:
                l1, l2, l3 = cons_exact.six[i]
                _p, _q, Q = cons_exact.third(v, d, l1, l2, l3)
                P = Gexact.add(v, Gexact.smul(l1, d))
                tiles.append((v, P, Q))
                outcomes.append(explore(tiles))
                tiles.pop()
                if outcomes[-1] == "cutoff":
                    break
        if "complete" in outcomes:
            return "complete"
        if "cutoff" in outcomes:
            return "cutoff"
        return "jam"

    outcome = explore([])
    return {"outcome": outcome, "elapsed": _time.time() - t0, "num_nodes": stats["nodes"],
            "pp_exact_fallback": stats["pp_exact_fallback"], "cl_exact_fallback": stats["cl_exact_fallback"]}


if __name__ == "__main__":
    import geometric_closability as gc
    from fractions import Fraction as F

    def gt_fmt(v):
        return gt.fmt(v) if v is not None else None

    def validate_word(word, e, f, node_cap=4000):
        Dn, target, (a, b, c) = gc.base_beta_target(e, f)
        Gexact = gt.Geo(Dn, target, (a, b, c))
        bps = [F(0)]
        LET = {"a": F(a), "b": F(b), "c": F(c)}
        for ch in word:
            bps.append(bps[-1] + LET[ch])
        cons_exact = gc._PrefixCons(Gexact, bps)
        target_f = [(float(x), float(y)) for (x, y) in target]

        n_total = 0
        n_match = 0
        n_border = 0
        mismatches = []

        def explore(tiles):
            nonlocal n_total, n_match, n_border
            if n_total >= node_cap:
                return
            exact_r = exact_pick_point(cons_exact, tiles)
            n_total += 1
            try:
                float_r = float_pick_point(Dn, target_f, to_float_tiles(tiles))
                if exact_r is None and float_r is None:
                    n_match += 1
                elif exact_r is not None and float_r is not None:
                    ev, ed = exact_r
                    fv, fd = float_r
                    ok = (abs(float(ev[0]) - fv[0]) < 1e-6 and abs(float(ev[1]) - fv[1]) < 1e-6
                          and abs(float(ed[0]) - fd[0]) < 1e-6 and abs(float(ed[1]) - fd[1]) < 1e-6)
                    if ok:
                        n_match += 1
                    else:
                        mismatches.append((word, list(tiles), exact_r, float_r))
                else:
                    mismatches.append((word, list(tiles), exact_r, float_r))
            except PickPointBorder as b:
                n_border += 1
            if exact_r is None:
                return
            v, d0 = exact_r
            d = Gexact.unit(d0)
            if d is None:
                return
            recs = cons_exact.classify(v, d, tiles)
            for r in recs:
                if r["kill"] is None:
                    tiles.append(r["tri"])
                    explore(tiles)
                    tiles.pop()

        explore([])
        return n_total, n_match, n_border, mismatches

    words = [("acb", 2, 3)]
    for w, e, f in words:
        nt, nm, nb, mm = validate_word(w, e, f)
        print("%s (%d,%d): nodes=%d match=%d border=%d mismatches=%d" % (w, e, f, nt, nm, nb, len(mm)))
        for m in mm:
            print("  MISMATCH:", m)
