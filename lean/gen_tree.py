#!/usr/bin/env python3
"""
gen_tree.py -- the certified-search format (Erdős #634, blocker (iv)).

Runs the constructor's branching rule (build23.py: lexicographically least uncovered vertex,
clockwise boundary ray, six oriented placements) in EXACT arithmetic over Q(sqrt Dn), and emits a
Lean file in which every node of the resulting refutation tree is a theorem about an arbitrary
`CongruentDissection`, proved from `Erdos634.CertNode` + `PlacementCompleteness` + `SixPlacements`.

Coordinates: every point is (X, Y) meaning (X, Y*sqrt(Dn)) with X, Y rational.  All membership,
escape, overlap and covering facts are then rational-linear and `linarith` decides them.

Per node the generated proof discharges:
  hlex     -- a closed superset C = target ∩ {Y ≥ yv} ∩ ({X ≥ xv} ∪ ⋃ φ_i ≥ 0) of the unfilled
              region, with U ⊆ C proved by a binary space partition over tile-edge lines
              (every leaf: the point is in a placed tile, or the constraints are infeasible);
  hfree    -- the explicit curve t ↦ v + t(d + t·sqrt(Dn)·d⊥) lies in U for 0 < t ≤ τ;
  hblocked -- the clockwise wedge lies in a placed tile (PlacementCompleteness.wedge_interior) or
              below the base;
  six kills -- escape (vertex outside target), overlap (explicit interior witness point),
              baseword (base_edge_clash against the hypothesised base blocks), or child.

Usage:
  python3 gen_tree.py lemmaP  > Erdos634/LemmaPTree.lean
  python3 gen_tree.py t44     > Erdos634/Tiling44Nodes.lean     (control: real tiling, 3 nodes)
  python3 gen_tree.py lemmaP --flip NODE CASE  (reject control: corrupt one overlap witness)
"""
import sys, math, functools
from fractions import Fraction as F

# ----------------------------------------------------------------------------------------------
# exact arithmetic in rescaled coordinates
# ----------------------------------------------------------------------------------------------

def isqrt_frac(q):
    """sqrt of a nonnegative rational if it is rational, else None"""
    if q < 0: return None
    n, d = q.numerator, q.denominator
    rn, rd = math.isqrt(n), math.isqrt(d)
    if rn*rn != n or rd*rd != d: return None
    return F(rn, rd)

class Geo:
    def __init__(self, Dn, target, sides):
        self.Dn = F(Dn)
        self.T = [(F(x), F(y)) for (x, y) in target]   # CCW, (0,0),(tx,0),(ax,ay)
        self.sides = tuple(F(s) for s in sides)        # (a,b,c) = dist(0,1), dist(1,2), dist(0,2)
    # vectors
    def sub(self, A, B): return (A[0]-B[0], A[1]-B[1])
    def add(self, A, B): return (A[0]+B[0], A[1]+B[1])
    def smul(self, s, A): return (s*A[0], s*A[1])
    def cross(self, u, v): return u[0]*v[1] - u[1]*v[0]          # real cross / sqrt(Dn)
    def dot(self, u, v): return u[0]*v[0] + self.Dn*u[1]*v[1]      # real dot
    def norm2(self, u): return self.dot(u, u)
    def ef(self, A, B, P):  # rational edge functional: >0 left of A->B
        return (B[0]-A[0])*(P[1]-A[1]) - (P[0]-A[0])*(B[1]-A[1])
    def ef_lin(self, A, B):  # coefficients (alpha, beta, gamma) of ef(A,B,(X,Y)) = alpha X + beta Y + gamma
        return (-(B[1]-A[1]), (B[0]-A[0]), -(B[0]-A[0])*A[1] + A[0]*(B[1]-A[1]))
    def inside(self, tri, P, strict=False):
        for i in range(3):
            e = self.ef(tri[i], tri[(i+1) % 3], P)
            if e < 0 or (strict and e == 0): return False
        return True
    def perp(self, d):  # d = (a,b): D-scaled perp = sqrt(Dn)*perp(d) = (-Dn*b, a)
        return (-self.Dn*d[1], d[0])
    def unit(self, w):
        L = isqrt_frac(self.norm2(w))
        if L is None or L == 0: return None
        return (w[0]/L, w[1]/L)
    def clip(self, poly, A, B):
        """Sutherland-Hodgman: keep the closed half-plane ef(A,B,.) >= 0"""
        out = []
        n = len(poly)
        for i in range(n):
            P, Q = poly[i], poly[(i+1) % n]
            fp, fq = self.ef(A, B, P), self.ef(A, B, Q)
            if fp >= 0: out.append(P)
            if (fp < 0 < fq) or (fq < 0 < fp):
                t = fp / (fp - fq)
                out.append((P[0] + t*(Q[0]-P[0]), P[1] + t*(Q[1]-P[1])))
        return out
    def intersect(self, T1, T2):
        poly = list(T1)
        for i in range(3):
            poly = self.clip(poly, T2[i], T2[(i+1) % 3])
            if not poly: return []
        return poly
    def area2(self, poly):
        s = F(0)
        for i in range(len(poly)):
            P, Q = poly[i], poly[(i+1) % len(poly)]
            s += P[0]*Q[1] - P[1]*Q[0]
        return s
    def centroid(self, poly):
        n = len(poly)
        return (sum(P[0] for P in poly)/n, sum(P[1] for P in poly)/n)
    def overlap_witness(self, T1, T2):
        poly = self.intersect(T1, T2)
        if len(poly) < 3 or self.area2(poly) == 0: return None
        # dedupe
        uniq = []
        for P in poly:
            if not any(P == Q for Q in uniq): uniq.append(P)
        if len(uniq) < 3 or self.area2(uniq) == 0: return None
        w = self.centroid(uniq)
        assert self.inside(T1, w, True) and self.inside(T2, w, True)
        return w

# ----------------------------------------------------------------------------------------------
# angular machinery (port of build23.py)
# ----------------------------------------------------------------------------------------------

class Cons:
    def __init__(self, G, bps=None):
        self.G = G; self.bps = bps
        a, b, c = G.sides
        # six placements in SixPlacements.six_placements order: (l1 along d, l2 at v, l3 opposite)
        self.six = [(a, c, b), (c, a, b), (a, b, c), (b, a, c), (c, b, a), (b, c, a)]
    def sgn(self, x): return (x > 0) - (x < 0)
    def half(self, d):
        sy = self.sgn(d[1])
        if sy > 0: return 0
        if sy < 0: return 1
        return 0 if d[0] > 0 else 1
    def ang_lt(self, d1, d2):
        h1, h2 = self.half(d1), self.half(d2)
        if h1 != h2: return h1 < h2
        return self.G.cross(d1, d2) > 0
    def ang_eq(self, d1, d2):
        return self.G.cross(d1, d2) == 0 and self.G.dot(d1, d2) > 0
    def in_arc(self, s, e, x):
        if self.ang_eq(s, x) or self.ang_eq(e, x): return True
        return self.G.cross(s, x) >= 0 and self.G.cross(x, e) >= 0
    def sub_in_arc(self, s, e, d1, d2):
        if not (self.in_arc(s, e, d1) and self.in_arc(s, e, d2)): return False
        c = self.G.cross(d1, d2)
        if c > 0: return True
        if c == 0:
            if self.G.dot(d1, d2) > 0: return True
            return self.ang_eq(s, d1) and self.ang_eq(e, d2)
        return False
    def on_seg_interior(self, P, A, B):
        G = self.G
        if G.cross(G.sub(B, A), G.sub(P, A)) != 0: return False
        d = G.sub(B, A); t = G.dot(G.sub(P, A), d)
        return 0 < t < G.dot(d, d)
    def blocked_arcs(self, v, tiles):
        G = self.G; T = G.T
        arcs = []; hit = False
        for i in range(3):
            A, B = T[i], T[(i+1) % 3]
            if v == A:
                C = T[(i+2) % 3]
                dB, dC = G.sub(B, A), G.sub(C, A)
                arcs.append((dC, G.smul(-1, dB))); arcs.append((G.smul(-1, dB), dB))
                hit = True; break
            if self.on_seg_interior(v, A, B):
                arcs.append((G.sub(A, B), G.sub(B, A))); hit = True; break
        if not hit and not G.inside(T, v): return None
        for tri in tiles:
            done = False
            for i in range(3):
                if v == tri[i]:
                    P, Q = tri[(i+1) % 3], tri[(i+2) % 3]
                    d1, d2 = G.sub(P, v), G.sub(Q, v)
                    arcs.append((d1, d2) if G.cross(d1, d2) > 0 else (d2, d1))
                    done = True; break
            if done: continue
            for i in range(3):
                A, B = tri[i], tri[(i+1) % 3]
                if self.on_seg_interior(v, A, B):
                    C = tri[(i+2) % 3]
                    if G.cross(G.sub(B, A), G.sub(C, A)) > 0: arcs.append((G.sub(B, A), G.sub(A, B)))
                    else: arcs.append((G.sub(A, B), G.sub(B, A)))
                    done = True; break
            if done: continue
            if G.inside(tri, v, True): return None
        return arcs
    def free_dirs(self, v, tiles):
        arcs = self.blocked_arcs(v, tiles)
        if arcs is None: return None
        D_ = []
        for (s, e) in arcs:
            for d in (s, e):
                if not any(self.ang_eq(d, x) for x in D_): D_.append(d)
        if len(D_) < 2: return []
        D_.sort(key=functools.cmp_to_key(lambda a, b: -1 if self.ang_lt(a, b) else (1 if self.ang_lt(b, a) else 0)))
        free = []
        n = len(D_)
        for i in range(n):
            d1, d2 = D_[i], D_[(i+1) % n]
            if not any(self.sub_in_arc(s, e, d1, d2) for (s, e) in arcs): free.append((d1, d2))
        return free
    def pick_point(self, tiles):
        G = self.G
        cands = list(G.T)
        for tri in tiles: cands.extend(tri)
        uniq = []
        for P in cands:
            if not any(P == Q for Q in uniq): uniq.append(P)
        uniq.sort(key=lambda P: (P[1], P[0]))
        for v in uniq:
            fd = self.free_dirs(v, tiles)
            if fd is None: continue
            if fd:
                starts = [s for (s, e) in fd]
                starts.sort(key=functools.cmp_to_key(lambda a, b: -1 if self.ang_lt(a, b) else (1 if self.ang_lt(b, a) else 0)))
                return v, starts[0]
        return None
    def third(self, v, d, l1, l2, l3):
        G = self.G
        p = (l1*l1 + l2*l2 - l3*l3) / (2*l1)
        q2 = (l2*l2 - p*p) / G.Dn
        q = isqrt_frac(q2)
        assert q is not None and q > 0, "third vertex not in Q(sqrt Dn)"
        return p, q, (v[0] + p*d[0] - G.Dn*q*d[1], v[1] + p*d[1] + q*d[0])
    def base_edges(self, tri):
        out = []
        for i in range(3):
            A, B = tri[i], tri[(i+1) % 3]
            if A[1] == 0 and B[1] == 0: out.append((i, (i+1) % 3, A[0], B[0]))
        return out
    def base_ok(self, tri):
        if self.bps is None: return True
        for (_, _, x1, x2) in self.base_edges(tri):
            lo, hi = min(x1, x2), max(x1, x2)
            if not any(self.bps[k] == lo and self.bps[k+1] == hi for k in range(len(self.bps)-1)):
                return False
        return True
    def classify(self, v, d, tiles):
        """for each of the six placements: dict with kill info"""
        G = self.G
        out = []
        for (l1, l2, l3) in self.six:
            P = G.add(v, G.smul(l1, d))
            p, q, Q = self.third(v, d, l1, l2, l3)
            tri = (v, P, Q)
            assert G.cross(G.sub(P, v), G.sub(Q, v)) > 0
            rec = dict(l=(l1, l2, l3), P=P, Q=Q, p=p, q=q, tri=tri, kill=None)
            # escape
            for (name, pt, kidx) in (('Q', Q, 2), ('P', P, 1)):
                for e in range(3):
                    if G.ef(G.T[e], G.T[(e+1) % 3], pt) < 0:
                        rec['kill'] = ('escape', kidx, e); break
                if rec['kill']: break
            if rec['kill']: out.append(rec); continue
            # overlap
            for m, U in enumerate(tiles):
                w = G.overlap_witness(tri, U)
                if w is not None:
                    rec['kill'] = ('overlap', m, w); break
            if rec['kill']: out.append(rec); continue
            # base word
            if not self.base_ok(tri):
                rec['kill'] = ('baseword',)
            out.append(rec)
        return out

# ----------------------------------------------------------------------------------------------
# linear arithmetic: Fourier-Motzkin feasibility with strictness, and the BSP cover
# ----------------------------------------------------------------------------------------------

def fm_feasible(cons):
    """cons: list of ((alpha,beta,gamma), strict) meaning alpha X + beta Y + gamma >= 0 (or > 0)."""
    def elim(cs, idx):
        lo, hi, rest = [], [], []
        for (c, s) in cs:
            if c[idx] > 0: lo.append((c, s))
            elif c[idx] < 0: hi.append((c, s))
            else: rest.append((c, s))
        for (c1, s1) in lo:
            for (c2, s2) in hi:
                # c1[idx]>0, c2[idx]<0: combine c1*(-c2[idx]) + c2*(c1[idx])
                k1, k2 = -c2[idx], c1[idx]
                c = tuple(k1*c1[i] + k2*c2[i] for i in range(3))
                rest.append((c, s1 or s2))
        return rest
    cs = elim(cons, 0)
    cs = elim(cs, 1)
    for (c, s) in cs:
        if s and not (c[2] > 0): return False
        if (not s) and not (c[2] >= 0): return False
    return True

def implies(cons, lin):  # cons ⟹ lin >= 0
    neg = tuple(-x for x in lin)
    return not fm_feasible(cons + [(neg, True)])

class CoverFail(Exception): pass

def bsp(G, cons, tiles, depth=0):
    """returns a tree: ('false',) | ('tile', m) | ('split', lin, left(>=0), right(<0))"""
    if not fm_feasible(cons): return ('false',)
    for m, U in enumerate(tiles):
        if all(implies(cons, G.ef_lin(U[i], U[(i+1) % 3])) for i in range(3)):
            return ('tile', m)
    if depth > 40: raise CoverFail("depth")
    for m, U in enumerate(tiles):
        for i in range(3):
            lin = G.ef_lin(U[i], U[(i+1) % 3])
            neg = tuple(-x for x in lin)
            if fm_feasible(cons + [(lin, False)]) and fm_feasible(cons + [(neg, True)]):
                return ('split', lin, bsp(G, cons + [(lin, False)], tiles, depth+1),
                        bsp(G, cons + [(neg, True)], tiles, depth+1))
    raise CoverFail("uncovered region at depth %d" % depth)

# ----------------------------------------------------------------------------------------------
# Lean emission
# ----------------------------------------------------------------------------------------------

def L(q):
    q = F(q)
    if q.denominator == 1:
        return str(q.numerator) if q >= 0 else "(%d)" % q.numerator
    return "(%d/%d)" % (q.numerator, q.denominator)

def lin_str(lin, X="X", Y="Y"):
    a, b, c = lin
    return "%s * %s + %s * %s + %s" % (L(a), X, L(b), Y, L(c))

class Emitter:
    def __init__(self, G, cons, Dn, ns, hD, srlt, srgt, B, model_sides, tgt_name="TGT", model_name="MODEL"):
        self.G, self.cons, self.Dn, self.ns = G, cons, Dn, ns
        self.hD, self.srlt, self.srgt, self.B = hD, srlt, srgt, B
        self.tgt, self.model = tgt_name, model_name
        self.model_sides = model_sides
        self.out = []
        self.defs = []       # tile definitions, emitted before all node theorems
        self.tiles = {}      # tri -> name
        self.tile_pos = {}   # name -> positivity lemma name
        self.nodes = []      # (id, node record)
        self.flip = None
    def p(self, s=""): self.out.append(s)
    def pd(self, s=""): self.defs.append(s)
    def rp(self, P): return "rp %s %s %s" % (self.Dn, L(P[0]), L(P[1]))
    def tri_name(self, tri):
        if tri not in self.tiles:
            n = "T%d" % len(self.tiles)
            self.tiles[tri] = n
            (x0, y0), (x1, y1), (x2, y2) = tri
            self.pd("theorem %s_pos : 0 < ef %s %s %s %s %s %s := by unfold ef; norm_num" %
                   (n, L(x0), L(y0), L(x1), L(y1), L(x2), L(y2)))
            self.pd("/-- `%s` = `%s`, `%s`, `%s`. -/" % (n, fmt(tri[0]), fmt(tri[1]), fmt(tri[2])))
            self.pd("noncomputable def %s : Tri := rtri %s %s %s %s %s %s %s %s %s_pos" %
                   (n, self.Dn, self.hD, L(x0), L(y0), L(x1), L(y1), L(x2), L(y2), n))
            self.pd("theorem %s_pts : %s.pts 0 = %s ∧ %s.pts 1 = %s ∧ %s.pts 2 = %s := ⟨rfl, rfl, rfl⟩" %
                   (n, n, self.rp(tri[0]), n, self.rp(tri[1]), n, self.rp(tri[2])))
            self.pd()
        return self.tiles[tri]

    # ---- non-vacuity witnesses ----------------------------------------------------------
    def sep_edge(self, A, B):
        """an edge (P,Q) with ef(P,Q,.) <= 0 on all of A and >= 0 on all of B"""
        G = self.G
        for tri in (A, B):
            for i in range(3):
                for (P, Q) in ((tri[i], tri[(i+1) % 3]), (tri[(i+1) % 3], tri[i])):
                    if all(G.ef(P, Q, V) <= 0 for V in A) and all(G.ef(P, Q, V) >= 0 for V in B):
                        return (P, Q)
        return None
    def emit_witnesses(self, nodes):
        G = self.G
        a, b, c = G.sides
        self.p("/-! ## Non-vacuity: every placed tile is congruent to the model and inside the target, and")
        self.p("every node's placed tiles have pairwise disjoint interiors -- the node hypotheses describe")
        self.p("genuine partial configurations, not empty ones. -/")
        self.p()
        placed = []
        for n in nodes:
            for t in n['tiles']:
                if t not in placed: placed.append(t)
        for t in placed:
            nm = self.tiles[t]
            (x0, y0), (x1, y1), (x2, y2) = t
            d01, d12, d20 = G.norm2(G.sub(t[0], t[1])), G.norm2(G.sub(t[1], t[2])), G.norm2(G.sub(t[2], t[0]))
            assert sorted([d01, d12, d20]) == sorted([a*a, b*b, c*c])
            self.p("theorem %s_sides : dist (%s.pts 0) (%s.pts 1) ^ 2 = %s ∧ dist (%s.pts 1) (%s.pts 2) ^ 2 = %s ∧" % (nm, nm, nm, L(d01), nm, nm, L(d12)))
            self.p("    dist (%s.pts 2) (%s.pts 0) ^ 2 = %s := by" % (nm, nm, L(d20)))
            self.p("  rw [%s_pts.1, %s_pts.2.1, %s_pts.2.2, dist_rp_sq %s %s, dist_rp_sq %s %s, dist_rp_sq %s %s]; norm_num" %
                   (nm, nm, nm, self.Dn, self.hD, self.Dn, self.hD, self.Dn, self.hD))
            self.p("theorem %s_inside : %s.carrier ⊆ %s.carrier :=" % (nm, nm, self.tgt))
            self.p("  rtri_subset %s %s_pos _ %s" % (self.hD, nm, " ".join(
                "(mem_rtri %s %s_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))" % (self.hD, self.tgt) for _ in range(3))))
            self.p()
        # one disjointness lemma per co-occurring pair of tiles, then per node a conjunction
        pair_names = {}
        for n in nodes:
            tl = n['tiles']
            for m1 in range(len(tl)):
                for m2 in range(m1 + 1, len(tl)):
                    A, B = tl[m1], tl[m2]
                    key = (self.tiles[A], self.tiles[B])
                    if key in pair_names: continue
                    e = self.sep_edge(A, B)
                    assert e is not None, "no separating edge at node %d tiles %d %d" % (n['id'], m1, m2)
                    (P, Q) = e
                    na, nb = key
                    pn = "disj_%s_%s" % (na, nb)
                    pair_names[key] = pn
                    self.p("theorem %s : Disjoint (interior %s.carrier) (interior %s.carrier) := by" % (pn, na, nb))
                    self.p("  refine disj_of_sep_edge %s %s %s %s %s %s %s (by norm_num) ?_ ?_" %
                           (self.hD, na, nb, L(P[0]), L(P[1]), L(Q[0]), L(Q[1])))
                    for (nm, tri) in ((na, A), (nb, B)):
                        self.p("  · intro k; fin_cases k")
                        for kk in range(3):
                            self.p("    · exact ⟨%s, %s, %s_pts.%s, by unfold ef; norm_num⟩" %
                                   (L(tri[kk][0]), L(tri[kk][1]), nm, ["1", "2.1", "2.2"][kk]))
        self.p()
        for n in nodes:
            tl = n['tiles']
            if len(tl) < 2: continue
            pairs = [(m1, m2) for m1 in range(len(tl)) for m2 in range(m1 + 1, len(tl))]
            self.p("theorem node_%d_config :" % n['id'])
            self.p("    " + " ∧\n    ".join("Disjoint (interior %s.carrier) (interior %s.carrier)" % (self.tiles[tl[m1]], self.tiles[tl[m2]]) for (m1, m2) in pairs) + " :=")
            self.p("  " + ("⟨%s⟩" % ", ".join(pair_names[(self.tiles[tl[m1]], self.tiles[tl[m2]])] for (m1, m2) in pairs) if len(pairs) > 1 else pair_names[(self.tiles[tl[0]], self.tiles[tl[1]])]))
            self.p()

    # ---- hlex certificate -------------------------------------------------------------------
    def hlex_data(self, v, tiles):
        """region (i) `Y < yv` must be covered by tiles (BSP leaves: tile/false); region (ii)
        `X < xv, Y ≥ yv` is partitioned until each leaf is in a tile, infeasible, or a closed cell
        avoiding the lex-below set {Y = yv, X < xv} (checked with the closed constraints)."""
        G = self.G
        xv, yv = v
        tgt = [(G.ef_lin(G.T[i], G.T[(i+1) % 3]), False) for i in range(3)]
        r1 = tgt + [((F(0), F(-1), yv), True)]
        t1 = bsp(G, r1, tiles)                      # tile / false only
        base2 = tgt + [((F(0), F(1), -yv), False), ((F(-1), F(0), xv), True)]
        cells = []
        def bsp2(cons, path, depth):
            if not fm_feasible(cons): return ('false',)
            closed = tgt + [((F(0), F(1), -yv), False)] + [(c, False) for c in path]
            # closed-(i): closed cell ∩ {Y = yv} ∩ {X < xv} = ∅
            if not fm_feasible(closed + [((F(0), F(-1), yv), False), ((F(-1), F(0), xv), True)]):
                cells.append(list(path))
                return ('cell', len(cells) - 1)
            for m, U in enumerate(tiles):
                if all(implies(cons, G.ef_lin(U[i], U[(i+1) % 3])) for i in range(3)):
                    return ('tile', m)
            if depth > 60: raise CoverFail("depth")
            for m, U in enumerate(tiles):
                for i in range(3):
                    lin = G.ef_lin(U[i], U[(i+1) % 3])
                    neg = tuple(-x for x in lin)
                    if fm_feasible(cons + [(lin, False)]) and fm_feasible(cons + [(neg, True)]):
                        return ('split', lin, bsp2(cons + [(lin, False)], path + [lin], depth + 1),
                                bsp2(cons + [(neg, True)], path + [neg], depth + 1))
            raise CoverFail("uncovered region touching the base left of v at depth %d" % depth)
        t2 = bsp2(base2, [], 0)
        return cells, t1, t2

    def emit_bsp(self, tree, ind, hn_names, ncells=None):
        kind = tree[0]
        if kind == 'false':
            self.p(ind + ("exfalso; linarith" if ncells is not None else "linarith"))
        elif kind == 'tile':
            if ncells is not None:
                self.p(ind + "exact (%s ⟨by linarith, by linarith, by linarith⟩).elim" % hn_names[tree[1]])
            else:
                self.p(ind + "exact %s ⟨by linarith, by linarith, by linarith⟩" % hn_names[tree[1]])
        elif kind == 'cell':
            k = tree[1]
            pf = "⟨%s⟩" % ", ".join("by linarith" for _ in self.cells[k]) if len(self.cells[k]) > 1 else "(by linarith)"
            self.p(ind + "exact Or.inr (%s)" % disj_inj(k, ncells, pf))
        else:
            _, lin, left, right = tree
            self.p(ind + "rcases le_or_gt 0 (%s) with hg | hg" % lin_str(lin))
            self.p(ind + "· " + "-- 0 ≤ %s" % lin_str(lin))
            self.emit_bsp(left, ind + "  ", hn_names, ncells)
            self.p(ind + "· " + "-- %s < 0" % lin_str(lin))
            self.emit_bsp(right, ind + "  ", hn_names, ncells)

    # ---- hfree ----------------------------------------------------------------------------
    def hfree_data(self, v, d, tiles):
        G = self.G
        xv, yv = v; a, b = d
        def quad(lin):
            al, be, ga = lin
            return (al*xv + be*yv + ga, al*a + be*b, -al*G.Dn*b + be*a)
        def ok_pos(c, tau, strict):
            c0, c1, c2 = c
            if c0 > 0: return c0 + min(c1, 0)*tau + min(c2, 0)*tau*tau > 0
            if c0 == 0:
                if c1 > 0: return c1 + min(c2, 0)*tau > 0
                if c1 == 0: return (c2 > 0) if strict else (c2 >= 0)
            return False
        def ok_neg(c, tau):
            c0, c1, c2 = c
            if c0 < 0: return c0 + max(c1, 0)*tau + max(c2, 0)*tau*tau < 0
            if c0 == 0:
                if c1 < 0: return c1 + max(c2, 0)*tau < 0
                if c1 == 0: return c2 < 0
            return False
        tq = [quad(G.ef_lin(G.T[i], G.T[(i+1) % 3])) for i in range(3)]
        tau = F(1, 4)
        for _ in range(60):
            good = all(ok_pos(c, tau, False) for c in tq)
            edges = []
            for U in tiles:
                found = None
                for i in range(3):
                    c = quad(G.ef_lin(U[i], U[(i+1) % 3]))
                    if ok_neg(c, tau): found = i; break
                if found is None: good = False; break
                edges.append(found)
            if good: return tau, edges
            tau /= 2
        raise RuntimeError("hfree: no tau")

    # ---- hblocked -------------------------------------------------------------------------
    def hblocked_data(self, v, d, tiles):
        G = self.G
        def wedge_ok(V1, V2):
            e1, e2 = G.sub(V1, v), G.sub(V2, v)
            det = G.cross(e1, e2)
            if det <= 0: return None
            a1, b1 = G.cross(d, e2)/det, G.cross(e1, d)/det
            n = G.perp(d)
            a2, b2 = G.cross(n, e2)/det, G.cross(e1, n)/det
            ha = a1 > 0 or (a1 == 0 and a2 < 0)
            hb = b1 > 0 or (b1 == 0 and b2 < 0)
            if ha and hb: return dict(a1=a1, b1=b1, a2=a2, b2=b2)
            return None
        for m, U in enumerate(tiles):
            for r in range(3):
                if U[r] != v: continue
                V1, V2 = U[(r+1) % 3], U[(r+2) % 3]
                w = wedge_ok(V1, V2)
                if w:
                    return dict(kind='wedge', m=m, r=r, rot=(v, V1, V2), sub=False, **w)
        for m, U in enumerate(tiles):
            for r in range(3):
                A, B, C = U[r], U[(r+1) % 3], U[(r+2) % 3]
                if not self.cons_on_seg(v, A, B): continue
                for (V1, V2) in ((B, C), (C, A)):
                    w = wedge_ok(V1, V2)
                    if w:
                        return dict(kind='wedge', m=m, r=r, rot=(v, V1, V2), sub=True, **w)
        if v[1] == 0 and d == (F(1), F(0)):
            return dict(kind='base')
        raise RuntimeError("hblocked: no blocking tile at v=%s d=%s" % (fmt(v), fmt(d)))
    def cons_on_seg(self, P, A, B):
        return self.cons.on_seg_interior(P, A, B)

    # ---- node -----------------------------------------------------------------------------
    def emit_node(self, nid, tiles, v, d, recs, child_ids, conclusion_false=True, bw_blocks=None):
        """child_ids: for each of the six recs with kill None, the child node id (or None in
        control mode, where live placements become disjuncts of the conclusion)."""
        G = self.G
        k = len(tiles)
        names = [self.tri_name(t) for t in tiles]
        idx = ["i%d" % m for m in range(k)]
        hyp = " ".join("(h%d : (D.tile i%d).carrier = %s.carrier)" % (m, m, names[m]) for m in range(k))
        S = "([%s] : List (Fin N)).toFinset" % ", ".join(idx)
        xv, yv = v; a, b = d
        vstr, dstr = self.rp(v), self.rp(d)
        uses_bw = any(r['kill'] and r['kill'][0] == 'baseword' for r in recs)
        live = [i for i, r in enumerate(recs) if r['kill'] is None]
        if conclusion_false:
            concl = "False"
        else:
            disj = " ∨ ".join("(D.tile j).carrier = %s.carrier" % self.tri_name(recs[i]['tri']) for i in live)
            concl = "∃ j, j ∉ %s ∧ (%s)" % (S, disj)
        bw_hyp = " (hbase : BaseWordHyp D.toDissection)" if bw_blocks is not None else ""
        self.p("/-- Node %d: %d placed tile(s), `v = %s`, `d = %s`; kills: %s. -/" %
               (nid, k, fmt(v), fmt(d), ", ".join(kill_str(r, child_ids[i]) for i, r in enumerate(recs))))
        self.p("theorem node_%d {N : ℕ} (D : CongruentDissection N)" % nid)
        self.p("    (htarget : D.target.carrier = %s.carrier) (hmodel : D.model.Congruent %s)%s" % (self.tgt, self.model, bw_hyp))
        if k: self.p("    (%s : Fin N) %s" % (" ".join(idx), hyp))
        self.p("    : %s := by" % concl)
        self.p("  classical")
        self.p("  have hyT : ∀ p ∈ %s.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg %s (by norm_num) %s_pos hp" % (self.tgt, self.hD, self.tgt))
        # unfilled characterisation
        conj = " ∧ ".join(["p ∈ %s.carrier" % self.tgt] + ["p ∉ %s.carrier" % n for n in names])
        self.p("  have hU : ∀ p, p ∈ unfilled D.toDissection %s ↔ %s := by" % (S, conj))
        self.p("    intro p; rw [mem_unfilled_iff, htarget]")
        self.p("    simp [%s]" % ", ".join(["h%d" % m for m in range(k)]))
        # ---- hlex
        cells, t1, t2 = self.hlex_data(v, tiles)
        self.cells = cells
        def cell_set(path):
            if not path: return "halfR %s 0 0 1" % self.Dn
            items = ["halfR %s %s %s %s" % (self.Dn, L(c[0]), L(c[1]), L(c[2])) for c in path]
            r = items[-1]
            for it in reversed(items[:-1]): r = "%s ∩ (%s)" % (it, r)
            return r
        def cell_closed(path):
            if not path: return "isClosed_halfR _ _ _ _"
            r = "isClosed_halfR _ _ _ _"
            for _ in path[1:]: r = "(isClosed_halfR _ _ _ _).inter (%s)" % r
            return r
        disj_sets = ["halfR %s 1 0 %s" % (self.Dn, L(-xv))] + ["(%s)" % cell_set(c) for c in cells]
        disj_closed = ["isClosed_halfR _ _ _ _"] + [cell_closed(c) for c in cells]
        Cset = "(%s.carrier ∩ halfR %s 0 1 %s) ∩ (%s)" % (self.tgt, self.Dn, L(-yv), union_right(disj_sets))
        closed = "(%s.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter (%s)" % (self.tgt, union_right_closed(disj_closed))
        self.p("  have hlex : ∀ p ∈ closure (unfilled D.toDissection %s), LexLE (%s) p := by" % (S, vstr))
        self.p("    refine hlex_of D.toDissection _ _ (%s) (%s) ?_ ?_" % (Cset, closed))
        self.p("    · intro p hpT hnot")
        self.p("      obtain ⟨X, Y, rfl⟩ := exists_rp %s p" % self.hD)
        self.p("      have hpT' : rp %s X Y ∈ %s.carrier := htarget ▸ hpT" % (self.Dn, self.tgt))
        self.p("      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg %s %s_pos hpT'" % (self.hD, self.tgt))
        self.p("      unfold ef at hT0 hT1 hT2")
        hn_names = []
        for m, U in enumerate(tiles):
            e = [lin_str(G.ef_lin(U[i], U[(i+1) % 3])) for i in range(3)]
            self.p("      have hn%d : ¬ (0 ≤ %s ∧ 0 ≤ %s ∧ 0 ≤ %s) := fun h =>" % (m, e[0], e[1], e[2]))
            self.p("        hnot i%d (by simp) (by rw [h%d]; exact mem_rtri %s %s_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))" %
                   (m, m, self.hD, names[m]))
            hn_names.append("hn%d" % m)
        self.p("      have hY : %s ≤ Y := by" % L(yv))
        self.p("        by_contra hR; push_neg at hR")
        self.emit_bsp(t1, "        ", hn_names)
        self.p("      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp %s]" % self.hD)
        self.p("      refine ⟨⟨hpT', by linarith⟩, ?_⟩")
        self.p("      rcases le_or_gt %s X with hX | hX" % L(xv))
        self.p("      · exact %s" % ("Or.inl (by linarith)" if cells else "(by linarith)"))
        self.p("      · -- the region X < xv, Y ≥ yv")
        self.emit_bsp(t2, "        ", hn_names, ncells=len(cells))
        self.p("    · intro p hp")
        self.p("      obtain ⟨X, Y, rfl⟩ := exists_rp %s p" % self.hD)
        self.p("      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp %s] at hp" % self.hD)
        self.p("      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp")
        self.p("      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg %s %s_pos hpT" % (self.hD, self.tgt))
        self.p("      unfold ef at hT0 hT1 hT2")
        self.p("      refine lexLE_rp %s (by linarith) (fun hYe => ?_)" % self.hD)
        pats = ["h"] + [("⟨%s⟩" % ", ".join("c%d" % i for i in range(len(c)))) if len(c) > 1 else "c0" for c in cells]
        self.p("      rcases hdis with %s <;> linarith" % " | ".join(pats))
        # ---- hfree
        tau, edges = self.hfree_data(v, d, tiles)
        self.p("  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧")
        self.p("      %s + t • (%s + s • perp (%s)) ∈ unfilled D.toDissection %s := by" % (vstr, dstr, dstr, S))
        self.p("    refine hfree_of %s (B := %s) (by norm_num) %s (τ := %s) (by norm_num) _ _ _ ?_" % (self.hD, L(self.B), self.srlt, L(tau)))
        self.p("    intro t ht htτ")
        self.p("    rw [pt_ccw_rp %s %s, hU]" % (self.Dn, self.hD))
        self.p("    have ht2 : t ^ 2 ≤ %s * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]" % L(tau))
        self.p("    have ht2p : 0 < t ^ 2 := by positivity")
        parts = ["mem_rtri %s %s_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith)" % (self.hD, self.tgt)]
        for m in range(k):
            parts.append("not_mem_rtri_of_edge%d %s %s_pos (by unfold ef; linarith)" % (edges[m], self.hD, names[m]))
        self.p("    exact %s" % (parts[0] if k == 0 else "⟨%s⟩" % ", ".join(parts)))
        # ---- hblocked
        hb = self.hblocked_data(v, d, tiles)
        self.p("  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →")
        self.p("      %s + t • (%s - s • perp (%s)) ∉ unfilled D.toDissection %s := by" % (vstr, dstr, dstr, S))
        if hb['kind'] == 'base':
            self.p("    exact hblocked_base %s D.toDissection _ (fun p hp => hyT p (htarget ▸ hp)) %s" % (self.hD, L(xv)))
        else:
            m, r = hb['m'], hb['r']
            rt = hb['rot']
            (x0, y0), (x1, y1), (x2, y2) = rt
            rname = self.tri_name(rt)
            if not hb['sub']:
                ks = [(r + s) % 3 for s in range(3)]  # tile vertex indices in rotated order
                self.p("    have hsub : %s.carrier ⊆ (D.tile i%d).carrier := (h%d.trans" % (rname, m, m))
                self.p("      (carrier_eq_rtri_of_pts %s %s (k₀ := %d) (k₁ := %d) (k₂ := %d) (by decide) (by decide) (by decide) rfl rfl rfl %s_pos)).symm.subset" %
                       (self.hD, names[m], ks[0], ks[1], ks[2], rname))
            else:
                self.p("    have hsub : %s.carrier ⊆ (D.tile i%d).carrier := (rtri_subset %s %s_pos %s %s).trans h%d.symm.subset" %
                       (rname, m, self.hD, rname, names[m], " ".join(
                           "(mem_rtri %s %s_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))" % (self.hD, names[m]) for _ in range(3)), m))
            self.p("    refine hblocked_of_wedge %s %s D.toDissection _ (i := i%d) (by simp) _ _ %s hsub rfl" % (self.hD, self.srgt, m, rname))
            self.p("      (wedge_interior %s (%s) (sr %s • perp (%s)) %s %s %s %s ?_ ?_ ?_ ?_)" %
                   (rname, dstr, self.Dn, dstr, L(hb['a1']), L(hb['b1']), L(hb['a2']), L(hb['b2'])))
            self.p("    · rw [%s_pts.1, %s_pts.2.1, %s_pts.2.2]; refine plane_ext ?_ ?_ <;> simp <;> ring" % (rname, rname, rname))
            self.p("    · rw [sr_smul_perp_rp %s, %s_pts.1, %s_pts.2.1, %s_pts.2.2]; refine plane_ext ?_ ?_ <;> simp <;> ring" % (self.hD, rname, rname, rname))
            self.p("    · exact %s" % ("Or.inl (by norm_num)" if hb['a1'] > 0 else "Or.inr ⟨by norm_num, by norm_num⟩"))
            self.p("    · exact %s" % ("Or.inl (by norm_num)" if hb['b1'] > 0 else "Or.inr ⟨by norm_num, by norm_num⟩"))
        # ---- placement completeness + six placements
        self.p("  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=")
        self.p("    placement_completeness D.toDissection %s (%s) (%s) (rp_unit %s (by norm_num)) hlex hfree hblocked" % (S, vstr, dstr, self.hD))
        self.p("  have hcong : (D.tile j).Congruent %s := (D.tiles_congruent j).trans hmodel" % self.model)
        self.p("  obtain ⟨hMa, hMb, hMc⟩ := %s" % self.model_sides)
        for m in range(k):
            self.p("  have hj%d : j ≠ i%d := fun h => hj (by rw [h]; simp)" % (m, m))
        if uses_bw:
            self.p("  have hyall := tiles_y_nonneg D.toDissection htarget hyT")
            self.p("  obtain ⟨%s⟩ := id hbase" % ", ".join("⟨ib%d, hb%d⟩" % (q, q) for q in range(len(bw_blocks))))
        self.p("  rcases six_placements hcong hMa hMb hMc (rp_unit %s (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with" % self.hD)
        self.p("    %s" % " | ".join("⟨hP, hQ⟩" for _ in range(6)))
        for ci, r in enumerate(recs):
            l1, l2, l3 = r['l']
            P, Q = r['P'], r['Q']
            self.p("  · -- placement %d: (%s, %s, %s)" % (ci + 1, L(l1), L(l2), L(l3)))
            self.p("    have hP' : (D.tile j).pts k₁ = %s := by rw [hP, rp_add_smul]; norm_num" % self.rp(P))
            self.p("    have hQ' : (D.tile j).pts k₂ = %s := by" % self.rp(Q))
            self.p("      rw [hQ, placeThird_rp %s %s %s %s %s %s %s %s %s %s (by norm_num) (by norm_num) (by norm_num)]; norm_num" %
                   (self.hD, L(xv), L(yv), L(a), L(b), L(l1), L(l2), L(l3), L(r['p']), L(r['q'])))
            kill = r['kill']
            if kill is None:
                cname = self.tri_name(r['tri'])
                self.p("    have hjc : (D.tile j).carrier = %s.carrier :=" % cname)
                self.p("      carrier_eq_rtri_of_pts %s _ hk01 hk02 hk12 hk₀ hP' hQ' %s_pos" % (self.hD, cname))
                if conclusion_false:
                    args = " ".join(idx + ["j"] + ["h%d" % m for m in range(k)] + ["hjc"])
                    self.p("    exact node_%d D htarget hmodel%s %s" % (child_ids[ci], " hbase" if bw_blocks is not None else "", args))
                else:
                    pos = live.index(ci)
                    self.p("    exact ⟨j, hj, %s⟩" % disj_inj(pos, len(live), "hjc"))
            elif kill[0] == 'escape':
                _, kidx, e = kill
                hyp = "hQ'" if kidx == 2 else "hP'"
                kk = "k₂" if kidx == 2 else "k₁"
                self.p("    exact (escape_of D.toDissection htarget j %s %s (not_mem_rtri_of_edge%d %s %s_pos (by unfold ef; norm_num)))%s" %
                       (kk, hyp, e, self.hD, self.tgt, "" if conclusion_false else ".elim"))
            elif kill[0] == 'overlap':
                _, m, w = kill
                if self.flip == (nid, ci):
                    w = (w[0] + 100, w[1])   # deliberately wrong witness
                cname = self.tri_name(r['tri'])
                self.p("    have hjc : (D.tile j).carrier = %s.carrier :=" % cname)
                self.p("      carrier_eq_rtri_of_pts %s _ hk01 hk02 hk12 hk₀ hP' hQ' %s_pos" % (self.hD, cname))
                self.p("    exact (overlap_of D.toDissection hj%d.symm h%d hjc (w := %s)" % (m, m, self.rp(w)))
                self.p("      (mem_interior_rtri %s %s_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))" % (self.hD, names[m]))
                self.p("      (mem_interior_rtri %s %s_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))%s" % (self.hD, cname, "" if conclusion_false else ".elim"))
            elif kill[0] == 'baseword':
                # candidate base edge starting at v = (xv, 0) along d = (1,0): [xv, xv + l1]
                assert yv == 0 and d == (F(1), F(0)), "baseword kill only at base-start edges"
                x1p = xv + l1
                blk = [q for q, (bx0, bx1) in enumerate(bw_blocks) if bx0 == xv and bx1 != x1p]
                assert blk, "no clashing block for base edge [%s, %s]" % (xv, x1p)
                q = blk[0]
                self.p("    exact base_edge_clash D.toDissection hyall hb%d" % q)
                self.p("      (⟨k₀, k₁, hk01, by rw [hk₀]; exact rp_eq_mkPt_zero %s _, by rw [hP']; exact rp_eq_mkPt_zero %s _⟩ : HasBaseEdge D.toDissection j %s %s)" %
                       (self.Dn, self.Dn, L(xv), L(x1p)))
                self.p("      (by norm_num) (by norm_num) (by norm_num)")
        self.p()

def union_right(items):
    if len(items) == 1: return items[0]
    return "%s ∪ (%s)" % (items[0], union_right(items[1:]))

def union_right_closed(items):
    if len(items) == 1: return items[0]
    return "(%s).union (%s)" % (items[0], union_right_closed(items[1:]))

def union_closed(n):
    # A ∪ (B ∪ (C ∪ ...)) right-nested chain of isClosed_halfR
    if n == 1: return "isClosed_halfR _ _ _ _"
    return "(isClosed_halfR _ _ _ _).union (%s)" % union_closed(n - 1)

def disj_inj(pos, n, h):
    if n == 1: return h
    if pos == 0: return "Or.inl %s" % h
    return "Or.inr (%s)" % disj_inj(pos - 1, n - 1, h)

def fmt(P):
    def g(u):
        return str(u)
    return "(%s, %s·r)" % (g(P[0]), g(P[1])) if P[1] != 0 else "(%s, 0)" % g(P[0])

def kill_str(r, child):
    k = r['kill']
    if k is None: return "child %s" % child
    if k[0] == 'escape': return "escape(%s, edge %d)" % ("Q" if k[1] == 2 else "P", k[2])
    if k[0] == 'overlap': return "overlap(tile %d)" % k[1]
    return "baseword"

# ----------------------------------------------------------------------------------------------
# tree construction
# ----------------------------------------------------------------------------------------------

def build_tree(G, cons, max_nodes=100000):
    """full refutation tree (every live placement recursed). returns list of nodes in
    post-order-compatible numbering: node dict has id, tiles, v, d, recs, children."""
    nodes = []
    counter = [0]
    def rec(tiles):
        nid = counter[0]; counter[0] += 1
        if nid > max_nodes: raise RuntimeError("cap")
        pk = cons.pick_point(tiles)
        assert pk is not None, "no uncovered point at depth %d" % len(tiles)
        v, d0 = pk
        d = G.unit(d0)
        assert d is not None, "irrational ray"
        recs = cons.classify(v, d, tiles)
        node = dict(id=nid, tiles=list(tiles), v=v, d=d, recs=recs, children=[None]*6)
        nodes.append(node)
        for i, r in enumerate(recs):
            if r['kill'] is None:
                tiles.append(r['tri'])
                node['children'][i] = rec(tiles)
                tiles.pop()
        return nid
    rec([])
    return nodes

def header(ns, imports, Dn, hD, srlt, srgt, B, target, model, model_sides_name, doc):
    lines = []
    for i in imports: lines.append("import %s" % i)
    lines.append("")
    lines.append("/-!")
    lines.append(doc)
    lines.append("-/")
    lines.append("")
    lines.append("set_option maxHeartbeats 4000000")
    lines.append("")
    lines.append("namespace %s" % ns)
    lines.append("")
    lines.append("open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.PlacementCompleteness")
    lines.append("  Erdos634.SixPlacements Erdos634.CertNode")
    lines.append("")
    lines.append("theorem %s : (0:ℝ) < %s := by norm_num" % (hD, Dn))
    lines.append("theorem %s : sr %s < %s := sr_lt %s (by norm_num) (by norm_num)" % (srlt, Dn, L(B), hD))
    lines.append("theorem %s : 1 < sr %s := sr_gt %s (by norm_num) (by norm_num)" % (srgt, Dn, hD))
    lines.append("")
    return lines

def emit_instance(G, cons, nodes, ns, Dn, B, bw_blocks, control, doc, flip=None, chunk=None):
    hD, srlt, srgt = "hD%s" % Dn, "sr%s_lt" % Dn, "sr%s_gt1" % Dn
    em = Emitter(G, cons, Dn, ns, hD, srlt, srgt, B, "MODEL_sides")
    em.flip = flip
    out = header(ns, ["Erdos634.CertNode"], Dn, hD, srlt, srgt, B, G.T, None, "MODEL_sides", doc)
    em.out = out
    # target and model
    (t0, t1, t2) = G.T
    em.p("theorem TGT_pos : 0 < ef %s %s %s %s %s %s := by unfold ef; norm_num" % (L(t0[0]), L(t0[1]), L(t1[0]), L(t1[1]), L(t2[0]), L(t2[1])))
    em.p("/-- The target `%s`, `%s`, `%s`. -/" % (fmt(t0), fmt(t1), fmt(t2)))
    em.p("noncomputable def TGT : Tri := rtri %s %s %s %s %s %s %s %s TGT_pos" % (Dn, hD, L(t0[0]), L(t0[1]), L(t1[0]), L(t1[1]), L(t2[0]), L(t2[1])))
    root = nodes[0]
    # the model: the root's first admissible placement, in (v, P, Q) order -- sides (a,b,c)
    a, b, c = G.sides
    mtri = None
    for r in root['recs']:
        if r['kill'] is None: mtri = r['tri']; break
    # find vertex order with dist(0,1)=a, dist(1,2)=b, dist(0,2)=c
    def d2(P, Q): return G.norm2(G.sub(P, Q))
    import itertools
    for perm in itertools.permutations(range(3)):
        t = tuple(mtri[i] for i in perm)
        if d2(t[0], t[1]) == a*a and d2(t[1], t[2]) == b*b and d2(t[0], t[2]) == c*c and G.ef(t[0], t[1], t[2]) > 0:
            mtri = t; break
    else:
        raise RuntimeError("no CCW vertex order realises sides (a,b,c) on the model")
    (m0, m1, m2) = mtri
    em.p("theorem MODEL_pos : 0 < ef %s %s %s %s %s %s := by unfold ef; norm_num" % (L(m0[0]), L(m0[1]), L(m1[0]), L(m1[1]), L(m2[0]), L(m2[1])))
    em.p("/-- The model tile `%s`, `%s`, `%s`: sides `%s, %s, %s`. -/" % (fmt(m0), fmt(m1), fmt(m2), L(a), L(b), L(c)))
    em.p("noncomputable def MODEL : Tri := rtri %s %s %s %s %s %s %s %s MODEL_pos" % (Dn, hD, L(m0[0]), L(m0[1]), L(m1[0]), L(m1[1]), L(m2[0]), L(m2[1])))
    em.p("theorem MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = %s ∧ dist (MODEL.pts 1) (MODEL.pts 2) = %s ∧" % (L(a), L(b)))
    em.p("    dist (MODEL.pts 0) (MODEL.pts 2) = %s :=" % L(c))
    em.p("  model_sides_rp %s MODEL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)" % hD)
    em.p()
    if bw_blocks is not None:
        em.p("/-- The base-word hypothesis: base blocks %s. -/" % ", ".join("[%s, %s]" % (L(x), L(y)) for (x, y) in bw_blocks))
        em.p("def BaseWordHyp {N : ℕ} (D : Dissection N) : Prop :=")
        em.p("  " + " ∧ ".join("(∃ i, HasBaseEdge D i %s %s)" % (L(x), L(y)) for (x, y) in bw_blocks))
        em.p()
    # nodes in post-order (children before parents)
    order = []
    def post(nid):
        n = nodes[nid]
        for c in n['children']:
            if c is not None: post(c)
        order.append(nid)
    if control:
        order = [n['id'] for n in nodes]
    else:
        post(0)
    pre = em.out
    em.out = []
    if chunk is None:
        for nid in order:
            n = nodes[nid]
            em.emit_node(nid, n['tiles'], n['v'], n['d'], n['recs'], n['children'],
                         conclusion_false=not control, bw_blocks=bw_blocks)
        em.emit_witnesses(nodes)
        em.p("end %s" % ns)
        em.p()
        for nid in (sorted(n['id'] for n in nodes) if control else [0]):
            em.p("#print axioms %s.node_%d" % (ns, nid))
        return "\n".join(pre + em.defs + em.out) + "\n"
    # chunked: every tile of every node and every candidate triangle is defined in chunk 0;
    # nodes are distributed over chunks in post-order; witnesses go last.
    for n in nodes:
        for t in n['tiles']: em.tri_name(t)
        for r in n['recs']:
            if r['kill'] is None or r['kill'][0] == 'overlap': em.tri_name(r['tri'])
    chunks = []
    cur = []
    for k, nid in enumerate(order):
        n = nodes[nid]
        em.out = []
        em.emit_node(nid, n['tiles'], n['v'], n['d'], n['recs'], n['children'],
                     conclusion_false=not control, bw_blocks=bw_blocks)
        cur.extend(em.out)
        if len(cur) > chunk or k == len(order) - 1:
            chunks.append(cur); cur = []
    em.out = []
    em.emit_witnesses(nodes)
    chunks.append(em.out)
    files = []
    imp = "Erdos634.CertNode"
    for ci, body in enumerate(chunks):
        name = "%s%d" % (ns.split('.')[-1], ci)
        head = ["import %s" % imp, "", "/-!", "# %s -- chunk %d of %d, GENERATED by `gen_tree.py`, do not edit" % (ns, ci, len(chunks)), "", doc if ci == 0 else "See chunk 0.", "-/", "",
                "set_option maxHeartbeats 4000000", "", "namespace %s" % ns, "",
                "open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.PlacementCompleteness",
                "  Erdos634.SixPlacements Erdos634.CertNode", ""]
        if ci == 0:
            text = pre + em.defs + body
        else:
            text = head + body
        text = text + ["end %s" % ns, ""]
        if ci == len(chunks) - 1:
            text.append("#print axioms %s.node_0" % ns)
        files.append((name, "\n".join(text) + "\n"))
        imp = "Erdos634." + name
    return files

# ----------------------------------------------------------------------------------------------

def lemmaP(flip=None):
    G = Geo(32, [(0, 0), (46, 0), (23, F(5, 2))], (6, 5, 9))
    word = "acb"; LET = {'a': 6, 'b': 5, 'c': 9}
    bps = [F(0)]
    for ch in word: bps.append(bps[-1] + LET[ch])
    # the full base for base_ok needs all breakpoints; blocks beyond the prefix are unconstrained,
    # so treat only edges inside [0, 20] as constrained
    class ConsP(Cons):
        def base_ok(self, tri):
            for (_, _, x1, x2) in self.base_edges(tri):
                lo, hi = min(x1, x2), max(x1, x2)
                if lo < bps[-1]:
                    if not any(bps[k] == lo and bps[k+1] == hi for k in range(len(bps)-1)):
                        return False
            return True
    cons = ConsP(G, bps)
    nodes = build_tree(G, cons)
    sys.stderr.write("lemmaP: %d nodes\n" % len(nodes))
    for n in nodes:
        sys.stderr.write("  node %d depth %d v=%s d=%s kills=%s\n" % (n['id'], len(n['tiles']), fmt(n['v']), fmt(n['d']),
                         [kill_str(r, n['children'][i]) for i, r in enumerate(n['recs'])]))
    blocks = [(bps[k], bps[k+1]) for k in range(len(bps)-1)]
    doc = """# Lemma P as kernel-checked theorems -- GENERATED by `gen_tree.py lemmaP`, do not edit

Erdős #634, `(e,f) = (2,3)`, tile `(6,5,9)`, `N = 23`.  Every node of the 13-node refutation tree
of `report_ramanujan.md` §5 (base word beginning `a c b`, blocks `[0,6]`, `[6,15]`, `[15,20]`) is a
theorem `node_k` about an arbitrary `CongruentDissection` whose target is the `(2,3)` base-β target
and whose model is congruent to `(6,5,9)`, with the node's placed tiles as explicit hypotheses
(`(D.tile iₘ).carrier = Tₘ.carrier`) and the base-word hypothesis `BaseWordHyp`.  The root,
`node_0`, has no placed tiles: **no such dissection has base word beginning `a c b`**.

Per node the proof discharges `hlex`, `hfree`, `hblocked` of `placement_completeness` by explicit
rational-linear arithmetic (see `CertNode.lean`), applies `six_placements`, and kills each of the six
placements by `escape_of`, `overlap_of`, `base_edge_clash`, or the child node's theorem.

No `sorry`; standard axioms."""
    return emit_instance(G, cons, nodes, "Erdos634.LemmaPTree", 32, 6, blocks, False, doc, flip=flip)

def t44():
    # Tiling44: target (0,0),(176,0),(88,24r), r = sqrt 15; tile sides (16,24,32); real tiles list
    G = Geo(15, [(0, 0), (176, 0), (88, 24)], (16, 24, 32))
    real = [((0, 0), (16, 0), (22, 6)), ((16, 0), (32, 0), (38, 6)), ((16, 0), (38, 6), (22, 6)),
            ((32, 0), (48, 0), (54, 6)), ((32, 0), (54, 6), (38, 6))]
    real = [tuple((F(x), F(y)) for (x, y) in t) for t in real]
    cons = Cons(G, None)
    nodes = []
    tiles = []
    for depth in range(3):
        v, d0 = cons.pick_point(tiles)
        d = G.unit(d0)
        recs = cons.classify(v, d, tiles)
        live = [i for i, r in enumerate(recs) if r['kill'] is None]
        # the real next tile must be among the live placements (a control on the branching rule)
        nxt = None
        for i in live:
            tri = recs[i]['tri']
            for rt in real:
                if set(tri) == set(rt): nxt = (i, rt)
        assert nxt is not None, "real tile not among the live placements at depth %d" % depth
        sys.stderr.write("t44 node %d: v=%s d=%s live=%s realchild=placement %d kills=%s\n" %
                         (depth, fmt(v), fmt(d), live, nxt[0], [kill_str(r, None) for r in recs]))
        nodes.append(dict(id=depth, tiles=list(tiles), v=v, d=d, recs=recs, children=[None]*6, real_child=nxt))
        tiles.append(recs[nxt[0]]['tri'])
    doc = """# Control: the certified-search format on the real 44-tiling -- GENERATED by `gen_tree.py t44`

The first three nodes of the constructor's search on `Tiling44` (target `(0,0),(176,0),(88,24√15)`,
tile `(16,24,32)`), with the real tiling's tiles placed.  Here no node is a refutation: the
conclusion of `node_k` is that some unplaced tile of the dissection is one of the node's *live*
placements.  `Tiling44NodesControl.lean` instantiates these at `Tiling44Bridge.dissection` and
checks the live placement named is the real next tile.  Every kill at these nodes is a genuine
escape/overlap, proved as at Lemma P; nothing is assumed about the constructor.

No `sorry`; standard axioms."""
    return emit_instance(G, cons, nodes, "Erdos634.Tiling44Nodes", 15, 4, None, True, doc)

def word_stats(word, emit=False, chunk=None):
    G = Geo(32, [(0, 0), (46, 0), (23, F(5, 2))], (6, 5, 9))
    LET = {'a': 6, 'b': 5, 'c': 9}
    bps = [F(0)]
    for ch in word: bps.append(bps[-1] + LET[ch])
    cons = Cons(G, bps)
    nodes = build_tree(G, cons)
    from collections import Counter
    kinds = Counter(); bw_bad = 0; nonbase_v = 0
    for n in nodes:
        if n['v'][1] != 0: nonbase_v += 1
        for r in n['recs']:
            k = r['kill']
            kinds[k[0] if k else 'child'] += 1
            if k and k[0] == 'baseword':
                v, d, l1 = n['v'], n['d'], r['l'][0]
                if not (v[1] == 0 and d == (F(1), F(0)) and any(bx0 == v[0] and bx1 != v[0] + l1 for (bx0, bx1) in zip(bps, bps[1:]))):
                    bw_bad += 1
    sys.stderr.write("%s: %d nodes, kills %s, unsupported BW %d, nodes with v above base %d, max depth %d\n" %
                     (word, len(nodes), dict(kinds), bw_bad, nonbase_v, max(len(n['tiles']) for n in nodes)))
    if emit:
        blocks = [(bps[k], bps[k+1]) for k in range(len(bps)-1)]
        doc = "# The `%s` refutation tree -- GENERATED by `gen_tree.py word %s`, do not edit\n\nSee `LemmaPTree.lean` for the format." % (word, word)
        return emit_instance(G, cons, nodes, "Erdos634.Word_%s" % word, 32, 6, blocks, False, doc, chunk=chunk)
    return None

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'lemmaP':
        flip = None
        if len(sys.argv) > 2 and sys.argv[2] == '--flip':
            flip = (int(sys.argv[3]), int(sys.argv[4]))
        sys.stdout.write(lemmaP(flip))
    elif mode == 't44':
        sys.stdout.write(t44())
    elif mode == 'word':
        chunk = int(sys.argv[4]) if len(sys.argv) > 4 else None
        out = word_stats(sys.argv[2], emit=(len(sys.argv) > 3 and sys.argv[3] == '--emit'), chunk=chunk)
        if out is None: pass
        elif chunk is None: sys.stdout.write(out)
        else:
            for (name, text) in out:
                open("Erdos634/%s.lean" % name, "w").write(text)
                sys.stderr.write("wrote Erdos634/%s.lean (%d lines)\n" % (name, text.count("\n")))
