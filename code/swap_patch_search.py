#!/usr/bin/env python3
"""Exact 2D patch-forcing search around the rogue chord (Erdős #634, base-β).

swap_fits proves that one-dimensional word arithmetic cannot kill the chord
survivors; this engine searches the two-dimensional neighborhood.  It grows a
patch of exactly-placed congruent tiles around the rogue configuration at slot
M of the step W(k−1) ⟹ W(k), under the leftmost-rogue reduction (row tiles P_j
paper-forced, standard down-tiles Q_j at the slots left of M), and reports per
(e, f, M, mode):

    KILLED    — every completion of the neighborhood is contradictory
    SURVIVES  — a locally consistent completion of the region exists
    OPEN      — caps hit, or only deferrable deficiencies left

Exactness.  Chart (x, ŷ), y = ŷ√D, D = 4f²−e²; every tile angle has rational
cosine and sine (rational)·√D, so rotations are rational and every incidence /
overlap / containment test is exact.  Floats are used only to PICK a candidate
angle combination or to order directions; every load-bearing identity is
confirmed in exact arithmetic, and the float margins are asserted per member.

Soundness of the move enumeration (kills are never spurious):
  * angular pivot — an uncovered arc strictly smaller than π at a placed
    vertex: the filler adjacent to the arc's clockwise boundary ray must have
    its corner there (a flat tile needs a full π); the ≤ 12 snug placements on
    that ray are exhaustive.
  * side pivot — a line interval covered on one side, uncovered on the other,
    whose rear end V (on the uncovered side) is the endpoint of an
    uncovered-side edge: a filler with an edge THROUGH V would double-cover
    that edge on the same side and overlap it; so the filler has a corner at V,
    and the ≤ 12 snug placements on the forward ray are exhaustive.
  * every uncovered arc, of any size, must be a ℕ-combination of α and β
    (flat tiles contribute (3,2) = π, corners (1,0),(0,1),(2,1)); if none
    exists the branch is dead.  Bounded uncovered line gaps must be
    ℕ⟨a,b,c⟩-representable; if not, dead.
  * deficiencies with neither pivot available are deferred; a branch that ends
    with only deferred deficiencies is reported OPEN, never SURVIVES/KILLED.

Modes.  'r2': k = M+2 with full containment in Δ_k (the tightest step);
'open': the base line only — a kill is then valid for every k ≥ M+3.
Chord discipline: 'swap' pins chord 1 to R = a·c (row side), S = c·a (rogue
side); 'free' lets the chord words emerge from the search.
"""
from fractions import Fraction as Fr
from math import gcd, atan2, sqrt, pi as PI
import sys, time, argparse

# ---------------------------------------------------------------- geometry

class Geo:
    def __init__(self, e, f):
        self.e, self.f = e, f
        self.a, self.b, self.c = e * f, f * f - e * e, f * f
        self.D = 4 * f * f - e * e
        self.rot = {
            "A": (Fr(2 * f * f - e * e, 2 * f * f), Fr(e, 2 * f * f)),
            "B": (Fr(e * (3 * f * f - e * e), 2 * f ** 3),
                  Fr(f * f - e * e, 2 * f ** 3)),
            "G": (Fr(-e, 2 * f), Fr(1, 2 * f)),
        }
        self.len_of = {"a": self.a, "b": self.b, "c": self.c}
        self.corner_edges = {"A": ("b", "c"), "B": ("a", "c"), "G": ("a", "b")}
        self.w = (Fr(1), Fr(0))
        self.u = (Fr(2 * f * f - e * e, 2 * f * f), Fr(e, 2 * f * f))
        vraw = (Fr(self.c) * self.u[0] - Fr(self.b), Fr(self.c) * self.u[1])
        self.vh = (vraw[0] / self.a, vraw[1] / self.a)
        import math
        self.fang = {t: math.acos(float(p)) for t, (p, q) in self.rot.items()}
        # margin assert: distinct small ℕ-combinations of α,β are well separated
        vals = {}
        for na in range(0, 8):
            for nb in range(0, 6):
                vals[(na, nb)] = na * self.fang["A"] + nb * self.fang["B"]
        items = sorted(vals.items(), key=lambda kv: kv[1])
        self.min_gap = min(abs(items[i + 1][1] - items[i][1])
                           for i in range(len(items) - 1)
                           if abs(items[i + 1][1] - items[i][1]) > 1e-12)
        assert self.min_gap > 1e-4, (e, f, self.min_gap)

    def rotate(self, d, t, sign=+1):
        p, q = self.rot[t]
        q = q * sign
        return (p * d[0] - q * self.D * d[1], q * d[0] + p * d[1])

    def rot_combo(self, d, na, nb):
        for _ in range(na):
            d = self.rotate(d, "A")
        for _ in range(nb):
            d = self.rotate(d, "B")
        return d

    def ang_float(self, na, nb):
        return na * self.fang["A"] + nb * self.fang["B"]

def sub(P, Q): return (P[0] - Q[0], P[1] - Q[1])
def neg(d): return (-d[0], -d[1])
def addm(P, s, d): return (P[0] + s * d[0], P[1] + s * d[1])
def cross(v1, v2): return v1[0] * v2[1] - v1[1] * v2[0]
def len2(G, v): return v[0] * v[0] + G.D * v[1] * v[1]
def dot(G, v1, v2): return v1[0] * v2[0] + G.D * v1[1] * v2[1]

def canon_dir(d):
    dx, dy = Fr(d[0]), Fr(d[1])
    dd = dx.denominator * dy.denominator // gcd(dx.denominator, dy.denominator)
    p = dx.numerator * (dd // dx.denominator)
    q = dy.numerator * (dd // dy.denominator)
    g = gcd(abs(p), abs(q))
    if g:
        p, q = p // g, q // g
    if p < 0 or (p == 0 and q < 0):
        p, q = -p, -q
    return (p, q)

def line_key(P, d):
    pq = canon_dir(d)
    off = Fr(pq[0]) * P[1] - Fr(pq[1]) * P[0]
    return (pq, off)

def tri_area2(T): return cross(sub(T[1], T[0]), sub(T[2], T[0]))

def tris_overlap(T1, T2):
    for T, O in ((T1, T2), (T2, T1)):
        s = 1 if tri_area2(T) > 0 else -1
        for i in range(3):
            A, B = T[i], T[(i + 1) % 3]
            d = sub(B, A)
            if all(cross(d, sub(P, A)) * s <= 0 for P in O):
                return False
    return True

def seg_dist2(G, P, A, B):
    AB, AP = sub(B, A), sub(P, A)
    L2 = len2(G, AB)
    t = dot(G, AP, AB)
    if t <= 0: return len2(G, AP)
    if t >= L2: return len2(G, sub(P, B))
    return len2(G, AP) - t * t / L2

def ccw_inside(d1, d2, x):
    """Is direction x strictly inside the ccw arc from d1 to d2 (0 < arc < 2π)?"""
    c12 = cross(d1, d2)
    same = lambda u, v: cross(u, v) == 0 and u[0] * v[0] + u[1] * v[1] > 0
    if same(x, d1) or same(x, d2):
        return False
    if c12 > 0:
        return cross(d1, x) > 0 and cross(x, d2) > 0
    if c12 < 0:
        # complement of the small arc d2→d1
        return not (cross(d2, x) > 0 and cross(x, d1) > 0)
    # parallel: opposite (arc = π) or same (empty arc)
    if d1[0] * d2[0] + d1[1] * d2[1] > 0:
        return False
    return cross(d1, x) > 0

# ---------------------------------------------------------------- tiles

OPP_CORNER = {"a": "A", "b": "B", "c": "G"}
OPP_EDGE = {"A": "a", "B": "b", "G": "c"}

class Tile:
    __slots__ = ("pts", "labels", "name")
    def __init__(self, pts, labels, name=""):
        self.pts, self.labels, self.name = tuple(pts), tuple(labels), name
    def edges(self):
        for i in range(3):
            yield (self.pts[(i + 1) % 3], self.pts[(i + 2) % 3],
                   OPP_EDGE[self.labels[i]])
    def sector_at(self, P):
        for i in range(3):
            if self.pts[i] == P:
                d1 = sub(self.pts[(i + 1) % 3], P)
                d2 = sub(self.pts[(i + 2) % 3], P)
                if cross(d1, d2) < 0:
                    d1, d2 = d2, d1
                return (d1, d2, self.labels[i])
        return None
    def key(self):
        return frozenset(self.pts)
    def centroid(self):
        return (sum(p[0] for p in self.pts) / 3, sum(p[1] for p in self.pts) / 3)

def place_tile(G, V, corner, d, edge_choice, ccw=True, name=""):
    """Corner `corner` at V with edge `edge_choice` along ray d; the tile lies
    ccw (or cw) of d.  Exact; returns Tile."""
    e1, e2 = G.corner_edges[corner]
    if edge_choice == e2:
        e1, e2 = e2, e1
    elif edge_choice != e1:
        return None
    L1, L2 = G.len_of[e1], G.len_of[e2]
    d2 = G.rotate(d, corner, +1 if ccw else -1)
    P1 = addm(V, Fr(L1), d)
    P2 = addm(V, Fr(L2), d2)
    lab1 = [x for x in "ABG" if x != corner and x != OPP_CORNER[e1]][0]
    lab2 = [x for x in "ABG" if x != corner and x != OPP_CORNER[e2]][0]
    return Tile((V, P1, P2), (corner, lab1, lab2), name)

# ---------------------------------------------------------------- patch

class Patch:
    def __init__(self, G, mode, k, M, region_segs, r0sq, chord=None):
        self.G, self.mode, self.k, self.M = G, mode, k, M
        self.tiles, self.keys = [], set()
        self.region_segs, self.r0sq = region_segs, r0sq
        self.chord = chord
        # boundary lines of Δ_k (outer side counts as covered)
        C = (Fr(k * G.b), Fr(0))
        B = (Fr(k * G.c) * G.u[0], Fr(k * G.c) * G.u[1])
        self.corner_pts = [(Fr(0), Fr(0)), C, B]
        self.boundary_lks = {line_key((Fr(0), Fr(0)), G.w): "base",
                             line_key((Fr(0), Fr(0)), G.u): "AB"}
        if mode != "open":
            self.boundary_lks[line_key(C, sub(B, C))] = "BC"
        # boundary side spans in the line coordinate dot(·, dd), for demand
        self.boundary_spans = {}
        ends = {"base": ((Fr(0), Fr(0)), C), "AB": ((Fr(0), Fr(0)), B),
                "BC": (C, B)}
        for lk, nm in self.boundary_lks.items():
            (p_, q_), _ = lk
            dd = (Fr(p_), Fr(q_))
            t1 = dot(G, ends[nm][0], dd)
            t2 = dot(G, ends[nm][1], dd)
            self.boundary_spans[lk] = (min(t1, t2), max(t1, t2))

    def clone(self):
        p = Patch(self.G, self.mode, self.k, self.M, self.region_segs,
                  self.r0sq, self.chord)
        p.tiles, p.keys = list(self.tiles), set(self.keys)
        p.boundary_lks = self.boundary_lks
        p.corner_pts = self.corner_pts
        p.boundary_spans = self.boundary_spans
        return p

    def in_region(self, P):
        return any(seg_dist2(self.G, P, A, B) < self.r0sq
                   for A, B in self.region_segs)

    def inside_target(self, P, strict=False):
        G = self.G
        if P[1] < 0 or (strict and P[1] <= 0):
            return False
        if self.mode == "open":
            # the AB half-plane s ≥ 0 is k-independent: cross(u, P) ≤ 0
            cu = G.u[0] * P[1] - G.u[1] * P[0]
            return cu < 0 if strict else cu <= 0
        C = (Fr(self.k * G.b), Fr(0))
        B = (Fr(self.k * G.c) * G.u[0], Fr(self.k * G.c) * G.u[1])
        det = C[0] * B[1] - C[1] * B[0]
        s = (P[0] * B[1] - P[1] * B[0]) / det
        t = (C[0] * P[1] - C[1] * P[0]) / det
        if strict:
            return s > 0 and t > 0 and s + t < 1
        return s >= 0 and t >= 0 and s + t <= 1

    def tile_ok(self, T):
        if T.key() in self.keys:
            return False
        for P in T.pts:
            if not self.inside_target(P):
                return False
        for S in self.tiles:
            if tris_overlap(T.pts, S.pts):
                return False
        if self.chord is not None:
            for A, B, letter in T.edges():
                if not self.chord_edge_ok(T, A, B):
                    return False
        return True

    def chord_edge_ok(self, T, A, B):
        cw = self.chord
        d = sub(B, A)
        if line_key(A, d) != cw["lk"]:
            return True
        sA, sB = cw["arc"](A), cw["arc"](B)
        lo, hi = min(sA, sB), max(sA, sB)
        if hi <= 0 or lo >= cw["L"]:
            return True
        if cw.get("kind") == "grid":
            return (lo, hi) in cw["allowed"]
        side = 1 if cross(cw["dd"], sub(T.centroid(), A)) > 0 else -1
        return (lo, hi) in cw["allowed"][side]

    def add(self, T):
        self.tiles.append(T)
        self.keys.add(T.key())

    # ---- vertex structures

    def sectors_at(self, P):
        out = []
        for T in self.tiles:
            s = T.sector_at(P)
            if s:
                out.append((s[0], s[1]))
        for T in self.tiles:
            if P in T.pts:
                continue
            for A, B, _ in T.edges():
                d = sub(B, A)
                if cross(d, sub(P, A)) != 0:
                    continue
                tA = dot(self.G, sub(P, A), d)
                tB = dot(self.G, sub(P, B), d)
                if tA > 0 and tB < 0:
                    inn = sub(T.centroid(), P)
                    if cross(d, inn) > 0:
                        out.append((d, neg(d)))
                    else:
                        out.append((neg(d), d))
        out.extend(self.boundary_sectors(P))
        return out

    def boundary_sectors(self, P):
        """Virtual outer-half sectors for a point on ∂Δ_k (base always; AB and
        BC in r2 mode).  The ccw arc from d1 to d2 covers the outside."""
        G = self.G
        out = []
        k = self.k
        A0 = (Fr(0), Fr(0))
        C = (Fr(k * G.b), Fr(0))
        B = (Fr(k * G.c) * G.u[0], Fr(k * G.c) * G.u[1])
        # corners: a single outer sector, the complement of the interior angle
        if P == A0:
            return [(G.u, G.w)]                       # interior = (w → u) ccw
        if P == C:
            return [(neg(G.w), G.vh)]                 # interior = (v̂ → −w) ccw
        if P == B and self.mode != "open":
            return [(neg(G.vh), neg(G.u))]            # interior = (−u → −v̂) ccw
        if P[1] == 0:
            out.append(((Fr(-1), Fr(0)), (Fr(1), Fr(0))))
        R = ((C[0] + B[0]) / 3, (C[1] + B[1]) / 3)   # interior reference
        sides = [(A0, G.u)]                           # AB: k-independent
        if self.mode != "open":
            sides.append((B, sub(C, B)))              # BC: only at fixed k
        for (Q0, m) in sides:
            dP = sub(P, Q0)
            if cross(m, dP) != 0:
                continue
            away = sub(P, R)
            if ccw_inside(m, neg(m), away):
                out.append((m, neg(m)))
            else:
                out.append((neg(m), m))
        return out

    def angular_gaps(self, P):
        secs = self.sectors_at(P)
        if not secs:
            return []
        G = self.G
        sd = sqrt(G.D)
        ang = lambda d: atan2(float(d[1]) * sd, float(d[0]))
        secs2 = sorted(secs, key=lambda s: ang(s[0]))
        gaps = []
        for i in range(len(secs2)):
            d_prev = secs2[i][1]
            d_next = secs2[(i + 1) % len(secs2)][0]
            same = cross(d_prev, d_next) == 0 and \
                d_prev[0] * d_next[0] + d_prev[1] * d_next[1] > 0
            if same:
                continue
            gaps.append((d_prev, d_next))
        return gaps

    def arc_combo(self, d1, d2):
        """Exact (na, nb) with rot(d1) = d2 and float match; None if none."""
        G = self.G
        sd = sqrt(G.D)
        th = (atan2(float(d2[1]) * sd, float(d2[0])) -
              atan2(float(d1[1]) * sd, float(d1[0]))) % (2 * PI)
        if th < 1e-9:
            th = 2 * PI
        for na in range(0, 7):
            for nb in range(0, 5):
                if na == 0 and nb == 0:
                    continue
                if abs(G.ang_float(na, nb) - th) < 1e-6:
                    e1 = G.rot_combo(d1, na, nb)
                    if canon_same_ray(e1, d2):
                        return (na, nb)
        return None

    # ---- line arrangement

    def line_arrangement(self):
        arr = {}
        for T in self.tiles:
            for A, B, letter in T.edges():
                d = sub(B, A)
                pq = canon_dir(d)
                dd = (Fr(pq[0]), Fr(pq[1]))
                lk = line_key(A, d)
                tA, tB = dot(self.G, A, dd), dot(self.G, B, dd)
                lo, hi = min(tA, tB), max(tA, tB)
                side = 1 if cross(dd, sub(T.centroid(), A)) > 0 else -1
                arr.setdefault(lk, []).append((lo, hi, side, T, letter))
        return arr

    def point_on_line(self, lk, t):
        (p, q), off = lk
        dd = (Fr(p), Fr(q))
        P0 = (Fr(0), off / p) if p != 0 else (-off / q, Fr(0))
        n2 = dot(self.G, dd, dd)
        s = (t - dot(self.G, P0, dd)) / n2
        return addm(P0, s, dd)

    def side_gaps(self, arr):
        out = []
        for lk, ivs in arr.items():
            bd = self.boundary_lks.get(lk)
            if bd is not None and lk in self.boundary_spans:
                lo0, hi0 = self.boundary_spans[lk]
                ivs = ivs + [(lo0, hi0, 0, None, None)]   # span marker
            cuts = sorted({x for lo, hi, _, _, _ in ivs for x in (lo, hi)})
            outer = None
            if bd is not None:
                # outer side: sign of cross(dd, outward) at any line point
                (p, q), _ = lk
                dd = (Fr(p), Fr(q))
                R = ((self.corner_pts[0][0] + self.corner_pts[1][0] +
                      self.corner_pts[2][0]) / 3,
                     (self.corner_pts[0][1] + self.corner_pts[1][1] +
                      self.corner_pts[2][1]) / 3)
                P0 = self.point_on_line(lk, cuts[0]) if cuts else None
                if P0 is not None:
                    outer = -1 if cross(dd, sub(R, P0)) > 0 else 1
            for i in range(len(cuts) - 1):
                lo, hi = cuts[i], cuts[i + 1]
                mid = (lo + hi) / 2
                Pm = self.point_on_line(lk, mid)
                if not self.in_region(Pm):
                    continue
                if bd is None:
                    if not self.inside_target(Pm, strict=True):
                        continue
                else:
                    if not self.inside_target(Pm, strict=False):
                        continue
                have = {1: False, -1: False}
                if outer is not None:
                    have[outer] = True
                for l2, h2, side, _, _ in ivs:
                    if side != 0 and l2 <= lo and hi <= h2:
                        have[side] = True
                for side in (1, -1):
                    if have[side] and not have[-side]:
                        out.append((lk, lo, hi, -side))
        return out

def canon_same_ray(u, v):
    return cross(u, v) == 0 and u[0] * v[0] + u[1] * v[1] > 0

def unit_dir(G, d):
    """Exact unit vector along d (all patch directions have rational unit form)."""
    from math import isqrt
    L2 = len2(G, d)
    n, m = L2.numerator, L2.denominator
    rn, rm = isqrt(n), isqrt(m)
    assert rn * rn == n and rm * rm == m, ("non-square direction length", d, L2)
    L = Fr(rn, rm)
    return (d[0] / L, d[1] / L)

# ---------------------------------------------------------------- search

REPR_CACHE = {}

def representable(G, gap):
    """Is the rational length `gap` a ℕ-combination of a, b, c?"""
    key = (G.e, G.f, gap)
    if key in REPR_CACHE:
        return REPR_CACHE[key]
    ok = False
    if gap.denominator == 1 and gap >= 0:
        g = int(gap)
        a, b, c = G.a, G.b, G.c
        for x in range(g // a + 1):
            r1 = g - x * a
            for y in range(r1 // b + 1):
                if (r1 - y * b) % c == 0:
                    ok = True
                    break
            if ok:
                break
    REPR_CACHE[key] = ok
    return ok

class Search:
    def __init__(self, G, M, mode, chordmode, node_cap, depth_cap, time_cap):
        self.G, self.M, self.mode, self.chordmode = G, M, mode, chordmode
        self.node_cap, self.depth_cap, self.time_cap = node_cap, depth_cap, time_cap
        self.nodes = 0
        self.t0 = 0.0
        self.survivor = None
        self.kill_reasons = {}
        self.deferred_seen = False

    # ---------------- seeding

    def seed(self):
        G, M = self.G, self.M
        a, b, c = G.a, G.b, G.c
        k = M + 3 if self.mode == "open" else M + int(self.mode[1:])
        self.k = k
        Y = (Fr(M * b), Fr(0))
        X, Z = addm(Y, Fr(a), G.vh), addm(Y, Fr(c), G.vh)
        W = addm(Y, Fr(a + c), G.vh)
        Yau, Zau = addm(Y, Fr(a), G.u), addm(Z, Fr(a), G.u)
        Zcu = addm(Z, Fr(c), G.u)
        if self.mode != "open":
            # demand the whole chord-2/3 corridor up to the BC exit at (k−M)c
            r = self.k - M
            segs = [(Y, W), (Y, addm(Y, Fr(r * c), G.u)),
                    (Z, addm(Z, Fr(r * c), G.u)), (Yau, Zau)]
        else:
            segs = [(Y, W), (Y, Yau), (Z, Zcu), (Yau, Zau)]
        r0sq = Fr(b * b, 4)
        chord = None
        if self.chordmode == "swap":
            pq = canon_dir(G.vh)
            dd = (Fr(pq[0]), Fr(pq[1]))
            scale = dot(G, G.vh, dd)
            tY = dot(G, Y, dd)
            arc = lambda P, tY=tY, dd=dd, scale=scale: \
                (dot(G, P, dd) - tY) / scale
            # side +1 vs −1 relative to canonical dir: row side contains A:
            rowside = 1 if cross(dd, sub((Fr(0), Fr(0)), Y)) > 0 else -1
            allowed = {rowside: {(Fr(0), Fr(a)), (Fr(a), Fr(a + c))},
                       -rowside: {(Fr(0), Fr(c)), (Fr(c), Fr(a + c))}}
            chord = {"lk": line_key(Y, G.vh), "dd": dd, "arc": arc,
                     "L": Fr(a + c), "allowed": allowed}
        P = Patch(G, self.mode, k, M, segs, r0sq, chord)
        for j in range(M - 1, M + 3):
            if j < 1 or j > k:
                continue
            V = (Fr((j - 1) * b), Fr(0))
            T = place_tile(G, V, "A", G.w, "b", name=f"P{j}")
            # P_j = {(j−1)b·w, jb·w, (j−1)b·w + c·u}: α, γ, β
            assert T.pts[1] == (Fr(j * b), Fr(0))
            assert T.pts[2] == addm(V, Fr(c), G.u)
            if not P.tile_ok(T):
                raise RuntimeError(f"seed P{j}")
            P.add(T)
        for j in (M - 2, M - 1):
            if j < 2:
                continue
            V = (Fr(j * b), Fr(0))
            # standard Q_j: β at jb·w, a-edge along v̂, c-edge along u (cw side)
            T = place_tile(G, V, "B", G.vh, "a", ccw=False, name=f"Q{j}")
            assert T.pts[1] == addm(V, Fr(a), G.vh)
            assert T.pts[1] == addm((Fr((j - 1) * b), Fr(0)), Fr(c), G.u)
            assert T.pts[2] == addm(V, Fr(c), G.u)
            if not P.tile_ok(T):
                raise RuntimeError(f"seed Q{j}")
            P.add(T)
        # the rogue: β at Y, c-edge along v̂, a-edge along u (cw side)
        T = place_tile(G, Y, "B", G.vh, "c", ccw=False, name="rogue")
        assert T.pts[1] == Z and T.pts[2] == Yau
        if not P.tile_ok(T):
            raise RuntimeError("seed rogue")
        P.add(T)
        return P

    def seed_transverse(self):
        """The transverse corner block: Δ_f with the a-side read as c^e.
        Seed = the β-corner tile at B laying c on BC (forced by
        corner_beta_unique once the a-side word is c^e)."""
        G = self.G
        a, b, c, f = G.a, G.b, G.c, G.f
        k = f
        self.k = k
        Bpt = (Fr(k * c) * G.u[0], Fr(k * c) * G.u[1])
        Cpt = (Fr(k * b), Fr(0))
        # BC direction from B is −v̂ (BC = −k·v_raw)
        assert addm(Bpt, Fr(k * a), neg(G.vh)) == Cpt
        # second-strip inner line B−a·u → its base hit (squeeze zone near C)
        Bau = addm(Bpt, Fr(a), neg(G.u))
        thit = Fr((k * c - a) * G.e, f)
        Phit = addm(Bau, thit, neg(G.vh))
        assert Phit[1] == 0
        segs = [(Bpt, Cpt), (Bpt, addm(Bpt, Fr(min(a + c, k * c)), neg(G.u))),
                (Bau, Phit), (Cpt, (max(Fr(0), Cpt[0] - c), Fr(0)))]
        r0sq = Fr(b * b, 4)
        pq = canon_dir(neg(G.vh))
        dd = (Fr(pq[0]), Fr(pq[1]))
        scale = dot(G, neg(G.vh), dd)
        tB = dot(G, Bpt, dd)
        arc = lambda P, tB=tB, dd=dd, scale=scale: (dot(G, P, dd) - tB) / scale
        allowed = {(Fr(j * c), Fr((j + 1) * c)) for j in range(G.e)}
        chord = {"kind": "grid", "lk": line_key(Bpt, G.vh), "dd": dd,
                 "arc": arc, "L": Fr(k * a), "allowed": allowed}
        P = Patch(G, "tri", k, 0, segs, r0sq, chord)
        T = place_tile(G, Bpt, "B", neg(G.vh), "c", ccw=False, name="T0")
        assert T.pts[1] == addm(Bpt, Fr(c), neg(G.vh))
        assert T.pts[2] == addm(Bpt, Fr(a), neg(G.u))
        if not P.tile_ok(T):
            raise RuntimeError("seed T0")
        P.add(T)
        return P

    # ---------------- placements

    def snug_options(self, P, V, ray):
        """All legal tiles with a corner at V and an edge along `ray`."""
        G = self.G
        ray = unit_dir(G, ray)
        opts = []
        for corner in "ABG":
            for ec in G.corner_edges[corner]:
                for ccw in (True, False):
                    T = place_tile(G, V, corner, ray, ec, ccw=ccw)
                    if T is not None and P.tile_ok(T):
                        opts.append(T)
        # dedupe by vertex set
        seen, out = set(), []
        for T in opts:
            if T.key() not in seen:
                seen.add(T.key())
                out.append(T)
        return out

    def lt_pi(self, combo):
        v = self.G.ang_float(*combo)
        assert abs(v - PI) > 1e-6 or combo == (3, 2)
        return combo != (3, 2) and v < PI

    # ---------------- pivot scan

    def find_pivot(self, P):
        """('dead', reason) | ('branch', options) | ('defer',) | None."""
        G = self.G
        best = None
        deferred = False
        arr = P.line_arrangement()
        # --- angular gaps
        pts = set()
        for T in P.tiles:
            pts.update(T.pts)
        for V in sorted(pts, key=str):
            if not P.in_region(V):
                continue
            if not P.inside_target(V):
                continue
            if V[1] != 0 and not P.inside_target(V, strict=True):
                # non-base boundary points: demand only where a virtual outer
                # sector is supplied (corners get their outer complement)
                if not P.boundary_sectors(V):
                    continue
            for (d1, d2) in P.angular_gaps(V):
                combo = P.arc_combo(d1, d2)
                if combo is None:
                    return ("dead", ("angle-unfillable", V))
                if not self.lt_pi(combo):
                    if combo == (3, 2):
                        # exact straight gap: corner fills or an anchored flat
                        opts = [T for T in self.snug_options(P, V, d1)
                                if self.sector_inside(T, V, d1, d2)]
                        opts += self.flat_options(P, V, d1)
                        if opts:
                            if len(opts) == 1:
                                return ("branch", opts)
                            if best is None or len(opts) < len(best):
                                best = opts
                        else:
                            deferred = True   # unanchored flat may exist
                    else:
                        deferred = True       # side machinery must handle it
                    continue
                opts = [T for T in self.snug_options(P, V, d1)
                        if self.sector_inside(T, V, d1, d2)]
                if not opts:
                    return ("dead", ("angle-nofill", V))
                if len(opts) == 1:
                    return ("branch", opts)
                if best is None or len(opts) < len(best):
                    best = opts
        # --- side gaps
        for (lk, lo, hi, side) in self.side_gaps_sorted(P, arr):
            ivs = arr[lk]
            (p, q), off = lk
            dd = (Fr(p), Fr(q))
            handled = False
            for V_t, fwd in ((lo, dd), (hi, neg(dd))):
                # frontier condition: an uncovered-side edge ends at V_t,
                # extending away from fwd
                frontier = any(
                    s == side and (h2 == V_t if fwd == dd else l2 == V_t)
                    for l2, h2, s, _, _ in ivs)
                if not frontier:
                    continue
                V = P.point_on_line(lk, V_t)
                opts = [T for T in self.snug_options(P, V, fwd)
                        if self.on_side(T, dd, V, side)]
                if not opts:
                    return ("dead", ("side-nofill", V))
                handled = True
                if len(opts) == 1:
                    return ("branch", opts)
                if best is None or len(opts) < len(best):
                    best = opts
                break
            if not handled:
                # bounded-gap representability prune
                gap = hi - lo
                n2 = dot(G, dd, dd)
                # convert line-coordinate gap to true length: coords are
                # dot(P, dd); unit step along the line changes it by n2/|dd|…
                # true length = gap / sqrt(n2)  — compare squared vs combos:
                # only prune when gap²/n2 is a rational square: skip otherwise
                deferred = True
        if best is not None:
            return ("branch", best)
        if deferred:
            self.deferred_seen = True
            return ("defer",)
        return None

    def flat_options(self, P, V, d1):
        """Flat fillers of an exact-π gap at V starting at ray d1: tiles with an
        edge through V along the d1-line, on the gap (ccw-of-d1) side, whose
        rear endpoint coincides with an existing on-line point (anchored).
        Unanchored flats exist in principle; the caller defers when the list is
        empty, so kills stay sound."""
        G = self.G
        dh = unit_dir(G, d1)
        lk = line_key(V, dh)
        tV = dot(G, V, dh)
        # existing on-line anchor points (vertices and edge endpoints)
        anchors = set()
        for T in P.tiles:
            for Q in T.pts:
                if line_key(Q, dh) == lk or (cross(dh, sub(Q, V)) == 0):
                    anchors.add(dot(G, Q, dh) - tV)
        opts = []
        for letter in "abc":
            x = G.len_of[letter]
            for q in anchors:
                for rear_off in ({q} if -x < q < 0 else set()) | \
                                ({q - x} if 0 < q < x else set()):
                    s = -rear_off
                    if not (0 < s < x):
                        continue
                    rear = addm(V, Fr(rear_off), dh)
                    for corner in [c for c in "ABG"
                                   if letter in G.corner_edges[c]]:
                        T = place_tile(G, rear, corner, dh, letter, ccw=True)
                        if T is not None and P.tile_ok(T):
                            opts.append(T)
        seen, out = set(), []
        for T in opts:
            if T.key() not in seen:
                seen.add(T.key())
                out.append(T)
        return out

    def sector_inside(self, T, V, d1, d2):
        s = T.sector_at(V)
        if s is None:
            return False
        a1, a2, _ = s
        ok = canon_same_ray(a1, d1) or ccw_inside(d1, d2, a1)
        ok2 = canon_same_ray(a2, d2) or ccw_inside(d1, d2, a2)
        return ok and ok2

    def on_side(self, T, dd, V, side):
        return (1 if cross(dd, sub(T.centroid(), V)) > 0 else -1) == side

    def side_gaps_sorted(self, P, arr):
        gaps = P.side_gaps(arr)
        # nearest to the slot first
        G = self.G
        Y = (Fr(self.M * G.b), Fr(0))
        def score(g):
            lk, lo, hi, side = g
            Pm = P.point_on_line(lk, (lo + hi) / 2)
            return float(len2(G, sub(Pm, Y)))
        return sorted(gaps, key=score)

    # ---------------- driver

    def run(self, scenario="slot"):
        self.t0 = time.time()
        P0 = self.seed() if scenario == "slot" else self.seed_transverse()
        return self.dfs(P0, 0)

    def dfs(self, P, depth):
        self.nodes += 1
        if self.nodes > self.node_cap or depth > self.depth_cap or \
           time.time() - self.t0 > self.time_cap:
            return "OPEN"
        piv = self.find_pivot(P)
        if piv is None:
            self.survivor = P
            return "SURVIVES"
        if piv[0] == "dead":
            key = str(piv[1])
            self.kill_reasons[key] = self.kill_reasons.get(key, 0) + 1
            return "KILLED"
        if piv[0] == "defer":
            return "OPEN"
        res = "KILLED"
        for T in piv[1]:
            P2 = P.clone()
            P2.add(T)
            r = self.dfs(P2, depth + 1)
            if r == "SURVIVES":
                self.survivor = self.survivor  # already set deeper
                return "SURVIVES"
            if r == "OPEN":
                res = "OPEN"
        return res

# ---------------------------------------------------------------- main

def members(fmax, emin=2):
    for f in range(3, fmax + 1):
        for e in range(emin, f):
            if gcd(e, f) == 1:
                yield e, f

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fmax", type=int, default=9)
    ap.add_argument("--mode", default="open",
                    choices=["open", "r2", "r3", "r4", "r5"])
    ap.add_argument("--chord", default="swap", choices=["swap", "free"])
    ap.add_argument("--only", default=None, help="e,f[,M]")
    ap.add_argument("--time-cap", type=float, default=90.0)
    ap.add_argument("--node-cap", type=int, default=200000)
    ap.add_argument("--depth-cap", type=int, default=80)
    ap.add_argument("--dump", action="store_true")
    ap.add_argument("--scenario", default="slot",
                    choices=["slot", "transverse"])
    args = ap.parse_args()

    sel = None
    if args.only:
        parts = [int(x) for x in args.only.split(",")]
        sel = (parts[0], parts[1], parts[2] if len(parts) > 2 else None)

    print(f"# patch search: scenario={args.scenario} mode={args.mode} "
          f"chord={args.chord} fmax={args.fmax}")
    if args.scenario == "transverse":
        for e, f in members(args.fmax):
            if sel and (e, f) != sel[:2]:
                continue
            G = Geo(e, f)
            S = Search(G, 0, "tri", "grid",
                       args.node_cap, args.depth_cap, args.time_cap)
            t0 = time.time()
            try:
                verdict = S.run(scenario="transverse")
            except RuntimeError as ex:
                verdict = f"SEED-FAIL {ex}"
            dt = time.time() - t0
            extra = ""
            if verdict == "KILLED":
                top = sorted(S.kill_reasons.items(), key=lambda kv: -kv[1])[:2]
                extra = "  " + "; ".join(f"{kk}×{v}" for kk, v in top)
            print(f"({e},{f}) transverse: {verdict}  "
                  f"[nodes={S.nodes} {dt:.1f}s]{extra}")
            sys.stdout.flush()
        return
    for e, f in members(args.fmax):
        if sel and (e, f) != sel[:2]:
            continue
        Mlo, Mhi = f // e + 2, f - 2
        if Mlo > Mhi:
            continue
        G = Geo(e, f)
        for M in range(Mlo, Mhi + 1):
            if sel and sel[2] is not None and M != sel[2]:
                continue
            if args.mode != "open" and M + int(args.mode[1:]) > f:
                continue
            S = Search(G, M, args.mode, args.chord,
                       args.node_cap, args.depth_cap, args.time_cap)
            t0 = time.time()
            try:
                verdict = S.run()
            except RuntimeError as ex:
                verdict = f"SEED-FAIL {ex}"
            dt = time.time() - t0
            extra = ""
            if verdict == "KILLED":
                top = sorted(S.kill_reasons.items(), key=lambda kv: -kv[1])[:2]
                extra = "  " + "; ".join(f"{k}×{v}" for k, v in top)
            if verdict == "SURVIVES" and S.survivor and args.dump:
                names = [t.name or "t" for t in S.survivor.tiles]
                extra = f"  tiles={len(names)}"
            print(f"({e},{f}) M={M}: {verdict}  [nodes={S.nodes} {dt:.1f}s]"
                  f"{extra}")
            sys.stdout.flush()

if __name__ == "__main__":
    main()
