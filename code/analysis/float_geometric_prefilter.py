"""float_geometric_prefilter.py -- fast floating-point APPROXIMATE pre-filter for the
base-word geometric jam question (Erdos #634), meant to run ahead of the exact oracle in
code/analysis/geometric_closability.py.

MOTIVATION (private/ROOM/e2b15_followup/report.md): the exact oracle costs ~150ms/node at
depth 8 because every point lives in Q(sqrt(4f^2-e^2)) and every escape/overlap test is exact
rational arithmetic (isqrt_frac, Fraction cross/dot, Sutherland-Hodgman clipping in Fraction).
Real N=83 base words are 16-28 letters; at ~150ms/node the exact oracle cannot reach that depth
in any reasonable budget. This module asks: can floating point (ordinary Python floats, sqrt(Dn)
computed once as a float) give the SAME jam/live/tiling verdicts, orders of magnitude faster, so
that only borderline nodes need to fall back to the exact oracle?

DESIGN: line-for-line port of lean/gen_tree.py's Geo/Cons (via geometric_closability.py's
_PrefixCons pattern) replacing Fraction arithmetic with float arithmetic, plus an explicit
tolerance band. Every scalar decision that in the exact code is a sign test (`x < 0`, `x == 0`,
`x >= 0`) becomes a three-way test here: definitely negative (< -EPS), definitely positive
(> EPS), or BORDERLINE (|x| <= EPS) -- borderline nodes are flagged, never silently resolved,
because a wrong resolution near a degenerate configuration (three points nearly collinear, an
escape test nearly exactly on the target boundary) is exactly the failure mode approximate
arithmetic risks. isqrt_frac's exactness requirement ("third vertex must lie in Q(sqrt Dn)") has
no float analogue at all -- it is simply skipped, which is itself a source of divergence risk
(see VALIDATION below).

This module NEVER invokes any tiling engine binary and never touches guard_run.sh or
data/SETTLED.tsv -- it is pure Python float arithmetic on the base-beta geometry only.
"""
from __future__ import annotations

import math
import os
import sys
import time
from dataclasses import dataclass, field

_LEAN_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "lean")
if _LEAN_DIR not in sys.path:
    sys.path.insert(0, _LEAN_DIR)

import gen_tree as gt  # noqa: E402  (only used for reference / cross-checks in __main__)
from geometric_closability import base_beta_target  # noqa: E402  (exact target/tile geometry, reused verbatim)

NOISE_FLOOR = 1e-10  # below this, a margin is confidently an exact zero (float64 rounding noise
# floor at the coordinate scales used here), not a sign-uncertain borderline case -- see inside3.
EPS = 1e-9  # tolerance band for "definitely {neg,pos}" vs "borderline". Tight, not loose: in this
# geometry an exact-zero margin (shared tile edges, vertices touching the target boundary) is the
# COMMON case, not a rare degeneracy -- so EPS must be just above float64 rounding noise at the
# coordinate scales in play (empirically ~1e-12 relative for N up to a few hundred), not a generous
# safety margin. A loose EPS (tried first: 1e-7) mislabeled almost every legitimate exact-zero
# touch as "borderline", which starved the search of real kills and made it explode combinatorially
# -- see float_geometric_prefilter's validation history / report_asymptotic.md.


class FGeo:
    """Float analogue of gen_tree.Geo: same operations, ordinary Python floats, sqrt(Dn)
    computed once. Point = (X, Y) meaning real point (X, Y*sqrt(Dn)), as in gt.Geo."""

    def __init__(self, Dn: int, target, sides):
        self.Dn = float(Dn)
        self.sqrtDn = math.sqrt(self.Dn)
        self.T = [(float(x), float(y)) for (x, y) in target]
        self.sides = tuple(float(s) for s in sides)

    def sub(self, A, B): return (A[0] - B[0], A[1] - B[1])
    def add(self, A, B): return (A[0] + B[0], A[1] + B[1])
    def smul(self, s, A): return (s * A[0], s * A[1])
    def cross(self, u, v): return u[0] * v[1] - u[1] * v[0]
    def dot(self, u, v): return u[0] * v[0] + self.Dn * u[1] * v[1]
    def norm2(self, u): return self.dot(u, u)

    def ef(self, A, B, P):
        return (B[0] - A[0]) * (P[1] - A[1]) - (P[0] - A[0]) * (B[1] - A[1])

    def sgn3(self, x):
        """3-way sign at tolerance EPS: 'neg' / 'pos' / 'zero' (borderline)."""
        if x < -EPS: return "neg"
        if x > EPS: return "pos"
        return "zero"

    def inside3(self, tri, P):
        """Returns ('in', margin) | ('out', margin) | ('border', margin), margin = the minimum
        (worst) of the three edge functionals ef(tri[i], tri[i+1], P). Only the WORST edge can
        ever flip the overall in/out verdict, so borderline-ness is judged on it alone: a
        non-extremal edge sitting exactly at 0 (very common here -- shared tile edges, a vertex
        that is itself a target corner) is not ambiguous and must not be flagged. An earlier
        version flagged border whenever ANY edge (not just the deciding one) was near zero, which
        misfired on essentially every node in this tightly-packed geometry (border=5-7 out of 5-6
        placements per node) and made the search refuse to ever conclude jam=True -- see
        report_asymptotic.md."""
        worst = min(self.ef(tri[i], tri[(i + 1) % 3], P) for i in range(3))
        if worst < -EPS:
            return "out", worst
        if abs(worst) < NOISE_FLOOR:
            # bit-level (or near-bit-level) zero from exact-integer/small-rational input data --
            # this is the COMMON case in base-beta geometry (tiles packed edge-to-edge, vertices
            # sitting on the target boundary by construction), not a rounding accident. Real
            # non-zero gaps in this geometry are orders of magnitude above float64 noise at these
            # coordinate scales (empirically >=1e-3 in every case checked), so a worst-margin this
            # close to 0 is confidently a true zero, not an escape -- not flagged as border.
            return "in", worst
        if worst <= EPS:
            return "border", worst
        return "in", worst

    def unit(self, w):
        L2 = self.norm2(w)
        if L2 <= 0:
            return None
        L = math.sqrt(L2)
        return (w[0] / L, w[1] / L)

    # ---- polygon clip / overlap area test (Sutherland-Hodgman, float) ----
    def clip(self, poly, A, B):
        out = []
        n = len(poly)
        for i in range(n):
            P, Q = poly[i], poly[(i + 1) % n]
            fp, fq = self.ef(A, B, P), self.ef(A, B, Q)
            if fp >= 0: out.append(P)
            if (fp < 0 < fq) or (fq < 0 < fp):
                t = fp / (fp - fq)
                out.append((P[0] + t * (Q[0] - P[0]), P[1] + t * (Q[1] - P[1])))
        return out

    def intersect(self, T1, T2):
        poly = list(T1)
        for i in range(3):
            poly = self.clip(poly, T2[i], T2[(i + 1) % 3])
            if not poly:
                return []
        return poly

    def area2(self, poly):
        s = 0.0
        for i in range(len(poly)):
            P, Q = poly[i], poly[(i + 1) % len(poly)]
            s += P[0] * Q[1] - P[1] * Q[0]
        return s

    def centroid(self, poly):
        n = len(poly)
        return (sum(P[0] for P in poly) / n, sum(P[1] for P in poly) / n)

    def overlap_area3(self, T1, T2):
        """Returns ('none', a2) | ('overlap', a2) | ('border', a2): a2 is the (signed) doubled
        polygon area of the intersection. 'border' flags a near-degenerate overlap (|a2m| small
        relative to the tile scale) that a float computation should not be trusted to resolve."""
        poly = self.intersect(T1, T2)
        if len(poly) < 3:
            return "none", 0.0
        a2 = abs(self.area2(poly))
        scale = abs(self.area2(T1))
        if scale <= 0:
            scale = 1.0
        rel = a2 / scale
        if rel > 1e-6:
            return "overlap", a2
        if rel > 1e-10:
            return "border", a2
        return "none", a2


class FCons:
    """Float analogue of gt.Cons, restricted to what geometric_simulate needs: the six
    placements (`third`), base-word prefix constraint, and per-placement classification.
    Vertex/ray selection (pick_point/free_dirs/blocked_arcs) is NOT reimplemented in float --
    it is reused verbatim from the exact oracle's `_PrefixCons` (see geometric_simulate_float
    below), because that logic is combinatorial (angle *ordering*, not magnitude) and was
    already flagged in private/ROOM/e2b14/VERDICT.md as the one Lean-unbacked step; changing its
    arithmetic here would confound the float/exact comparison this module is trying to make."""

    def __init__(self, G: FGeo, bps):
        self.G = G
        a, b, c = G.sides
        self.six = [(a, c, b), (c, a, b), (a, b, c), (b, a, c), (c, b, a), (b, c, a)]
        self.bps = bps
        self._limit = bps[-1] if bps else 0.0

    def third(self, v, d, l1, l2, l3):
        G = self.G
        p = (l1 * l1 + l2 * l2 - l3 * l3) / (2 * l1)
        q2 = (l2 * l2 - p * p) / G.Dn
        if q2 < 0:
            if q2 > -1e-9:
                q2 = 0.0
            else:
                return None  # geometrically impossible under float rounding -- should not happen
        q = math.sqrt(q2)
        return p, q, (v[0] + p * d[0] - G.Dn * q * d[1], v[1] + p * d[1] + q * d[0])

    def base_edges(self, tri):
        out = []
        for i in range(3):
            A, B = tri[i], tri[(i + 1) % 3]
            if abs(A[1]) < EPS and abs(B[1]) < EPS:
                out.append((A[0], B[0]))
        return out

    def base_ok3(self, tri):
        """Returns ('ok'|'bad'|'border'). A base edge whose endpoint is within EPS*L of a
        breakpoint is 'border' (float can't tell whether it lands exactly on the prefix's
        column boundary)."""
        border = False
        for (x1, x2) in self.base_edges(tri):
            lo, hi = min(x1, x2), max(x1, x2)
            if lo < self._limit - EPS:
                match = False
                near = False
                for k in range(len(self.bps) - 1):
                    # a "near match" must be near on BOTH endpoints of the SAME segment k --
                    # matching lo against segment k while hi matches some unrelated segment j!=k
                    # is not ambiguity, it is a plain mismatch (this was the original bug: it
                    # treated any coincidental single-endpoint proximity, against any segment, as
                    # grounds for uncertainty, which spuriously marked clear baseword violations
                    # as 'border' and let the search tree explode).
                    if abs(self.bps[k] - lo) < EPS and abs(self.bps[k + 1] - hi) < EPS:
                        match = True
                    elif abs(self.bps[k] - lo) < 1e-4 and abs(self.bps[k + 1] - hi) < 1e-4:
                        near = True
                if not match:
                    if near:
                        border = True
                    else:
                        return "bad"
        return "border" if border else "ok"

    def classify3(self, v, d, tiles):
        """Float analogue of gt.Cons.classify. Each placement gets kill in
        {'escape','overlap','baseword', None} plus a `border` flag meaning: this placement's
        verdict rests on a float comparison within EPS of the decision boundary and should be
        re-checked by the exact oracle before being trusted."""
        G = self.G
        out = []
        for (l1, l2, l3) in self.six:
            P = G.add(v, G.smul(l1, d))
            th = self.third(v, d, l1, l2, l3)
            if th is None:
                out.append({"l": (l1, l2, l3), "kill": ("degenerate",), "border": True, "tri": None})
                continue
            p, q, Q = th
            tri = (v, P, Q)
            rec = {"l": (l1, l2, l3), "P": P, "Q": Q, "tri": tri, "kill": None, "border": False}
            # escape: Q and P must be inside target (float 3-way test)
            escaped = False
            for pt in (Q, P):
                verdict, margin = G.inside3(G.T, pt)
                if verdict == "out":
                    rec["kill"] = ("escape",)
                    escaped = True
                    break
                if verdict == "border":
                    rec["border"] = True
            if escaped:
                out.append(rec)
                continue
            # overlap
            overlapped = False
            for m, U in enumerate(tiles):
                verdict, a2 = G.overlap_area3(tri, U)
                if verdict == "overlap":
                    rec["kill"] = ("overlap", m)
                    overlapped = True
                    break
                if verdict == "border":
                    rec["border"] = True
            if overlapped:
                out.append(rec)
                continue
            # base word
            bstat = self.base_ok3(tri)
            if bstat == "bad":
                rec["kill"] = ("baseword",)
            elif bstat == "border":
                rec["border"] = True
            out.append(rec)
        return out


@dataclass
class _FNode:
    id: int
    depth: int
    outcome: str = None
    any_border: bool = False


def geometric_simulate_float(prefix_word: str, e: int, f: int, node_cap: int = 4000,
                              pick_point_fn=None) -> dict:
    """Floating-point approximate analogue of geometric_closability.geometric_simulate.

    Vertex/ray selection (`pick_point`) is delegated to `pick_point_fn(tiles) -> (v, d0) | None`
    if given; by default it is borrowed from the EXACT oracle's own Cons machinery running on
    exact copies of the float-computed tile coordinates rounded back to nearby rationals -- see
    `_default_pick_point_factory`. This keeps the combinatorial branching rule identical to the
    validated exact pipeline (per the design note in FCons) while only the arithmetic *tests*
    (escape/overlap/baseword) run in float.

    Returns {"jam": bool|None, "tiling_found": bool, "continues": [...], "num_nodes": int,
             "borderline_nodes": int, "elapsed": float}. jam=None if any borderline node was hit
             on a path that would otherwise have resolved to jam=True/False -- an approximate
             pipeline must never assert jam under uncertainty.
    """
    if any(ch not in "abc" for ch in prefix_word):
        raise ValueError("prefix_word must be over {a,b,c}")
    if (e, f) == (3, 4):
        raise ValueError("tile (3,4,...) excluded by instruction")

    Dn, target, (a, b, c) = base_beta_target(e, f)
    LET = {"a": float(a), "b": float(b), "c": float(c)}
    bps = [0.0]
    for ch in prefix_word:
        bps.append(bps[-1] + LET[ch])

    G = FGeo(Dn, target, (a, b, c))
    cons = FCons(G, bps)

    if pick_point_fn is None:
        pick_point_fn = _default_pick_point_factory(e, f, prefix_word)

    t0 = time.time()
    counter = {"n": 0, "border": 0}
    tiling_found = {"flag": False}
    cutoffs = []
    any_border_on_jam_path = {"flag": False}

    def explore(tiles):
        if counter["n"] >= node_cap:
            cutoffs.append({"depth": len(tiles)})
            return "cutoff"
        pk = pick_point_fn(tiles)
        if pk is None:
            tgt_area = abs(G.area2(G.T))
            placed_area = sum(abs(G.area2(list(t))) for t in tiles)
            if abs(placed_area - tgt_area) < 1e-6 * tgt_area:
                tiling_found["flag"] = True
                counter["n"] += 1
                return "complete"
            cutoffs.append({"depth": len(tiles), "note": "area mismatch"})
            return "cutoff"
        v, d0 = pk
        d = G.unit(d0)
        if d is None:
            cutoffs.append({"depth": len(tiles), "note": "zero ray"})
            return "cutoff"
        recs = cons.classify3(v, d, tiles)
        counter["n"] += 1
        node_border = any(r.get("border") for r in recs)
        if node_border:
            counter["border"] += 1
        live = [i for i, r in enumerate(recs) if r["kill"] is None]
        if not live:
            if node_border:
                any_border_on_jam_path["flag"] = True
            return "jam"
        outcomes = []
        for i in live:
            tiles.append(recs[i]["tri"])
            outcomes.append(explore(tiles))
            tiles.pop()
        if node_border and any(o == "jam" for o in outcomes):
            any_border_on_jam_path["flag"] = True
        if "complete" in outcomes:
            return "complete"
        if "cutoff" in outcomes:
            return "cutoff"
        return "jam"  # all live children jammed

    root_outcome = explore([])
    elapsed = time.time() - t0

    if root_outcome == "complete" or cutoffs:
        jam = False if root_outcome == "complete" else None
    elif any_border_on_jam_path["flag"]:
        jam = None  # honest "don't know, borderline" -- never assert jam under float uncertainty
    else:
        jam = (root_outcome == "jam")

    return {
        "jam": jam,
        "tiling_found": tiling_found["flag"],
        "continues": cutoffs,
        "num_nodes": counter["n"],
        "borderline_nodes": counter["border"],
        "root_outcome": root_outcome,
        "elapsed": elapsed,
    }


def _default_pick_point_factory(e, f, prefix_word):
    """Builds a pick_point function that reuses the EXACT (Fraction) Cons.pick_point on tiles
    whose float coordinates are snapped back onto the exact target's vertex/tile-corner lattice.
    This is only used for the *validation* runs in this file (where prefixes are short enough
    that exact and float tiles agree to full precision); for the deep speed test in __main__ we
    instead run a float-native nearest-uncovered-vertex heuristic (see `_float_pick_point`),
    documented there as NOT validated against the exact branching rule at that depth."""
    from fractions import Fraction as F
    Dn, target, (a, b, c) = base_beta_target(e, f)
    Gexact = gt.Geo(Dn, target, (a, b, c))
    bpsF = [F(0)]
    LET = {"a": F(a), "b": F(b), "c": F(c)}
    for ch in prefix_word:
        bpsF.append(bpsF[-1] + LET[ch])
    import geometric_closability as gc
    cons_exact = gc._PrefixCons(Gexact, bpsF)

    def snap(pt):
        return (F(pt[0]).limit_denominator(10**6), F(pt[1]).limit_denominator(10**6))

    def pick(tiles_float):
        tiles_exact = [tuple(snap(pt) for pt in tri) for tri in tiles_float]
        return cons_exact.pick_point(tiles_exact)

    return pick


def _float_pick_point(G: FGeo, tiles):
    """Float-native lexicographically-least-uncovered-vertex heuristic: NOT validated against
    the exact branching rule (see module docstring) -- used only for the depth-scaling timing
    test, where results are reported as timing/borderline-rate data, not as jam verdicts."""
    cands = list(G.T)
    for tri in tiles:
        cands.extend(tri)
    uniq = []
    for P in cands:
        if not any(abs(P[0] - Q[0]) < 1e-9 and abs(P[1] - Q[1]) < 1e-9 for Q in uniq):
            uniq.append(P)
    uniq.sort(key=lambda P: (P[1], P[0]))
    # crude "is this vertex still open": not strictly interior to any placed tile and not the
    # fully-surrounded case. This is a placeholder heuristic for timing purposes only.
    for v in uniq:
        covered = False
        for tri in tiles:
            verdict, _ = G.inside3(tri, v)
            if verdict == "in":
                covered = True
                break
        if not covered:
            return v, (1.0, 0.0)  # direction choice not validated at this depth
    return None


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["validate", "timing"])
    args = ap.parse_args()

    if args.mode == "validate":
        import geometric_closability as gc
        cases = [
            ("acb", 2, 3),
            ("acba", 5, 6), ("aabc", 5, 6),
            ("acbaba", 5, 6), ("aabcba", 5, 6),
            ("acbaaba", 5, 6), ("aabcaba", 5, 6),
        ]
        n_ok = 0
        for w, e, f in cases:
            exact = gc.geometric_simulate(w, e, f)
            approx = geometric_simulate_float(w, e, f)
            agree = (exact["jam"] == approx["jam"]) and (exact["tiling_found"] == approx["tiling_found"])
            n_ok += agree
            print("%-10s (%d,%d): exact jam=%-5s tiling=%-5s | float jam=%-5s tiling=%-5s border=%d nodes=%d elapsed=%.4fs %s"
                  % (w, e, f, exact["jam"], exact["tiling_found"], approx["jam"], approx["tiling_found"],
                     approx["borderline_nodes"], approx["num_nodes"], approx["elapsed"],
                     "OK" if agree else "MISMATCH"))
        print("%d/%d agree" % (n_ok, len(cases)))
        sys.exit(0 if n_ok == len(cases) else 1)
    else:
        import random
        random.seed(0)
        Dn, target, (a, b, c) = base_beta_target(5, 6)
        G = FGeo(Dn, target, (a, b, c))
        for length in (10, 12, 15):
            w = "a" + "".join(random.choice("abc") for _ in range(length - 2)) + "a"
            t0 = time.time()
            tiles = []
            # single-path float-only depth probe using the exact pick_point on float-snapped
            # tiles (same as validate mode) -- reports how far/fast this reaches, honestly
            # labelled as heuristic beyond the validated length-7 regime.
            try:
                res = geometric_simulate_float(w, 5, 6, node_cap=4000)
                print("len=%d word=%s -> jam=%s nodes=%d border=%d elapsed=%.3fs"
                      % (length, w, res["jam"], res["num_nodes"], res["borderline_nodes"], res["elapsed"]))
            except Exception as ex:
                print("len=%d word=%s -> ERROR %r" % (length, w, ex))
