#!/usr/bin/env python3
"""
Exhaustive, exact search for tilings of a triangle by N congruent copies of a tile.

PURPOSE. This engine decides, by exhaustive search, whether a given target triangle can be
dissected into N copies of a given tile (mirror images allowed, tilings need NOT be
edge-to-edge). An exhausted search with no tiling found is a PROOF of non-existence, because
the branching rule below enumerates, at every step, every way any tiling can continue.

EXACTNESS. All coordinates live in Q(sqrt(D)): numbers p + q*sqrt(D) with p, q rational.
Every geometric decision (signs, comparisons, intersections) is exact. No floats anywhere.

COMPLETENESS OF THE BRANCHING (the mathematical core).
  State: the closed unfilled region, a disjoint union of simple polygons; and the count of
  tiles left. Pick the vertex v that is lexicographically smallest by (y, x) over all polygon
  vertices. It is an extreme point of its polygon, so its interior angle is < pi. Let d1 be
  the unit direction of the outgoing boundary edge v -> next (CCW order, interior on the
  left); the interior sector at v spans from d1 counterclockwise to dir(v -> prev).
  FACT: in any tiling of the region, consider the tiles whose closure contains v. Each such
  tile has a corner at v (it cannot have v in the interior of one of its edges, since its
  angle at v would then be pi > interior angle). Their corner angles partition the sector, so
  the clockwise-most of them has one of its two corner sides lying exactly ALONG d1.
  Hence the six placements below (3 corner choices x 2 sides along d1, the two being mirror
  images) exhaust all possibilities, and DFS over them to depth N is an exhaustive search.

SOUND PRUNES (each is a theorem about any completable state).
  P1 (area): every polygon of the region is tiled by whole tiles, so its area is a positive
      integer multiple of the tile area, and the multiples sum to tiles_left.
  P2 (straight runs): a maximal straight boundary run BOTH of whose endpoint corners are
      convex (< pi) must be covered exactly by whole tile edges lying inside it (an edge
      cannot pass a convex corner), so its length lies in the numerical semigroup
      N*a + N*b + N*c. (Runs with a reflex endpoint are NOT pruned: an edge may continue
      past a reflex corner.)
"""
from fractions import Fraction
from math import gcd
import sys

# ----------------------------------------------------------------------------- Q(sqrt D) ----
class QD(object):
    """(pn + qn*sqrt(D))/den, exact; pn,qn,den ints, den>0, gcd(pn,qn,den)=1.
    Integer-triple storage (no per-op Fraction normalization) — ~50x faster than
    the Fraction-backed version it replaces. Same exact semantics. D via QD.D."""
    __slots__ = ('pn', 'qn', 'den')
    D = 3

    def __init__(self, p=0, q=0):
        # p, q are int or Fraction (both expose .numerator/.denominator)
        pn, pd = p.numerator, p.denominator
        qn, qd = q.numerator, q.denominator
        if pd == 1 and qd == 1:
            self.pn = pn; self.qn = qn; self.den = 1
            return
        den = pd // gcd(pd, qd) * qd                    # lcm(pd, qd)
        PN = pn * (den // pd); QN = qn * (den // qd)
        g = gcd(gcd(PN, QN), den)
        if g > 1: PN //= g; QN //= g; den //= g
        self.pn = PN; self.qn = QN; self.den = den

    @staticmethod
    def _raw(pn, qn, den):
        """construct from an unreduced integer triple (den may be negative/zero-free)."""
        o = QD.__new__(QD)
        if den == 1:                                    # common: integer-denominator coords
            o.pn = pn; o.qn = qn; o.den = 1; return o
        if den < 0: pn = -pn; qn = -qn; den = -den
        g = gcd(gcd(pn, qn), den)
        if g > 1: pn //= g; qn //= g; den //= g
        o.pn = pn; o.qn = qn; o.den = den; return o

    @property
    def p(s): return Fraction(s.pn, s.den)
    @property
    def q(s): return Fraction(s.qn, s.den)

    def __add__(s, o):
        if s.den == o.den: return QD._raw(s.pn + o.pn, s.qn + o.qn, s.den)
        return QD._raw(s.pn * o.den + o.pn * s.den, s.qn * o.den + o.qn * s.den, s.den * o.den)
    def __sub__(s, o):
        if s.den == o.den: return QD._raw(s.pn - o.pn, s.qn - o.qn, s.den)
        return QD._raw(s.pn * o.den - o.pn * s.den, s.qn * o.den - o.qn * s.den, s.den * o.den)
    def __neg__(s):
        o = QD.__new__(QD); o.pn = -s.pn; o.qn = -s.qn; o.den = s.den; return o
    def __mul__(s, o):
        if type(o) is QD:
            return QD._raw(s.pn * o.pn + QD.D * s.qn * o.qn, s.pn * o.qn + s.qn * o.pn,
                           s.den * o.den)
        return QD._raw(s.pn * o.numerator, s.qn * o.numerator, s.den * o.denominator)
    __rmul__ = __mul__

    def __truediv__(s, o):
        if type(o) is QD:                              # * conjugate / norm
            pn = o.den * (s.pn * o.pn - QD.D * s.qn * o.qn)
            qn = o.den * (s.qn * o.pn - s.pn * o.qn)
            den = s.den * (o.pn * o.pn - QD.D * o.qn * o.qn)
            return QD._raw(pn, qn, den)
        return QD._raw(s.pn * o.denominator, s.qn * o.denominator, s.den * o.numerator)

    def sign(s):
        pn, qn = s.pn, s.qn                             # den > 0, so sign = sign(pn + qn*sqrt D)
        if pn == 0 and qn == 0: return 0
        if pn >= 0 and qn >= 0: return 1
        if pn <= 0 and qn <= 0: return -1
        t = pn * pn - QD.D * qn * qn
        if pn > 0:                                      # pn > 0 > qn
            return 1 if t > 0 else (-1 if t < 0 else 0)
        return -1 if t > 0 else (1 if t < 0 else 0)     # qn > 0 > pn

    def __eq__(s, o): return s.pn * o.den == o.pn * s.den and s.qn * o.den == o.qn * s.den
    def __hash__(s): return hash((s.pn, s.qn, s.den))
    def __lt__(s, o): return (s - o).sign() < 0
    def __le__(s, o): return (s - o).sign() <= 0
    def __gt__(s, o): return (s - o).sign() > 0
    def __ge__(s, o): return (s - o).sign() >= 0
    def is_zero(s): return s.pn == 0 and s.qn == 0
    def __repr__(s): return f"({Fraction(s.pn, s.den)}+{Fraction(s.qn, s.den)}r{QD.D})"

    def sqrt_rational(s):
        """exact sqrt when s is a nonneg rational perfect square of a rational; else None"""
        if s.qn != 0 or s.pn < 0: return None
        rn, rd = _isqrt(s.pn), _isqrt(s.den)
        if rn * rn == s.pn and rd * rd == s.den:
            return Fraction(rn, rd)
        return None

def _isqrt(n):
    if n < 0: return -1
    x = int(n) ** 0.5
    x = int(x)
    while x * x > n: x -= 1
    while (x + 1) * (x + 1) <= n: x += 1
    return x

ZERO = None  # set after D fixed (QD caches nothing global; helpers below build fresh)

def qd(p=0, q=0): return QD(p, q)

# ------------------------------------------------------------------------------- geometry ---
def cross(o, a, b):
    """z of (a-o) x (b-o), a QD"""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

def vsub(a, b): return (a[0] - b[0], a[1] - b[1])
def vadd(a, b): return (a[0] + b[0], a[1] + b[1])
def dot(u, v): return u[0] * v[0] + u[1] * v[1]
def crossv(u, v): return u[0] * v[1] - u[1] * v[0]

def on_segment(p, a, b):
    """p on closed segment ab (all exact); a != b assumed"""
    if cross(a, b, p).sign() != 0: return False
    return dot(vsub(p, a), vsub(b, a)).sign() >= 0 and dot(vsub(p, b), vsub(a, b)).sign() >= 0

def seg_param(p, a, b):
    """parameter t of p on line ab: p = a + t*(b-a); line direction nondegenerate"""
    d = vsub(b, a)
    dd = dot(d, d)
    return dot(vsub(p, a), d) / dd

def proper_cross(a, b, c, d):
    """segments ab, cd cross at a point interior to both (transversal)"""
    d1 = cross(c, d, a).sign(); d2 = cross(c, d, b).sign()
    d3 = cross(a, b, c).sign(); d4 = cross(a, b, d).sign()
    return d1 * d2 < 0 and d3 * d4 < 0

def seg_intersections(a, b, c, d):
    """all isolated intersection/touch points of segments ab and cd, as points.
    For collinear overlap returns the overlap endpoints."""
    pts = []
    d1 = cross(c, d, a).sign(); d2 = cross(c, d, b).sign()
    d3 = cross(a, b, c).sign(); d4 = cross(a, b, d).sign()
    if d1 == 0 and d2 == 0:                       # collinear
        for p in (c, d):
            if on_segment(p, a, b): pts.append(p)
        for p in (a, b):
            if on_segment(p, c, d): pts.append(p)
        return pts
    if d1 * d2 <= 0 and d3 * d4 <= 0:
        # standard exact line intersection
        r = vsub(b, a); s = vsub(d, c)
        denom = crossv(r, s)
        if denom.sign() != 0:
            t = crossv(vsub(c, a), s) / denom
            p = (a[0] + t * r[0], a[1] + t * r[1])
            if on_segment(p, a, b) and on_segment(p, c, d):
                pts.append(p)
    return pts

def point_in_polygon(pt, poly):
    """'IN', 'ON', or 'OUT' — exact crossing number with half-open rule"""
    n = len(poly)
    for i in range(n):
        a, b = poly[i], poly[(i + 1) % n]
        if on_segment(pt, a, b): return 'ON'
    cnt = 0
    px, py = pt
    for i in range(n):
        a, b = poly[i], poly[(i + 1) % n]
        ay, by = a[1], b[1]
        c1 = (ay - py).sign() <= -1 or (ay - py).sign() == 0
        # half-open: count edge if min(ay,by) <= py < max(ay,by)
        s1 = (ay - py).sign(); s2 = (by - py).sign()
        if (s1 <= 0 and s2 > 0) or (s2 <= 0 and s1 > 0):
            # x coordinate of crossing with horizontal line y = py
            t = (py - a[1]) / (b[1] - a[1])
            xc = a[0] + t * (b[0] - a[0])
            if (xc - px).sign() > 0:
                cnt += 1
    return 'IN' if cnt % 2 == 1 else 'OUT'

def poly_area2(poly):
    """twice the signed area (QD)"""
    s = qd(0)
    n = len(poly)
    for i in range(n):
        a, b = poly[i], poly[(i + 1) % n]
        s = s + (a[0] * b[1] - b[0] * a[1])
    return s

# --------------------------------------------------------------------- angular order (exact)
def ang_class(u):
    """half-plane class for angular sort: 0 for angle in [0,pi), 1 for [pi,2pi)"""
    sy = u[1].sign()
    if sy > 0: return 0
    if sy < 0: return 1
    return 0 if u[0].sign() > 0 else 1

def ang_less(u, v):
    """direction angle of u < that of v, exact, angles in [0, 2pi)"""
    cu, cv = ang_class(u), ang_class(v)
    if cu != cv: return cu < cv
    return crossv(u, v).sign() > 0

# ------------------------------------------------------------------------------- the tile ---
class Tile(object):
    """corner data: for each corner ('A','B','C') exact (cos, sin) and the two adjacent
    side lengths in order (side along ray, other side)."""
    def __init__(self, a, b, c, cosA, sinA, cosB, sinB, cosC, sinC):
        self.a, self.b, self.c = a, b, c
        self.area2 = None  # set by instance (twice tile area, QD)
        # corner angle -> (cos, sin, [(L_along, M_other), (M_other, L_along)])
        # adjacent sides: at corner A (angle alpha): sides b and c; B: a and c; C: a and b
        self.corners = [
            (cosA, sinA, [(b, c), (c, b)]),
            (cosB, sinB, [(a, c), (c, a)]),
            (cosC, sinC, [(a, b), (b, a)]),
        ]
        self.sides = (a, b, c)

def rot(cs, sn, u):
    """rotate vector u by the angle with exact (cos, sin) = (cs, sn) counterclockwise"""
    return (cs * u[0] - sn * u[1], sn * u[0] + cs * u[1])

# ----------------------------------------------------------------------------- semigroup ----
class Semigroup(object):
    def __init__(self, gens):
        self.gens = gens
        self.memo = {}

    def contains(self, x):
        """x a Fraction >= 0: is x in N*g1 + N*g2 + N*g3?"""
        if x < 0: return False
        if x == 0: return True
        if x.denominator != 1: return False
        n = x.numerator
        if n in self.memo: return self.memo[n]
        ok = any(self.contains(Fraction(n - g)) for g in self.gens if n - g >= 0)
        self.memo[n] = ok
        return ok

# ------------------------------------------------------------------------------ subtraction -
def split_edges(edges):
    """edges: list of directed segments (p, q). Split each at every incidence point with any
    other segment (endpoints landing in interiors, crossings, collinear-overlap endpoints)."""
    n = len(edges)
    cutpts = [set() for _ in range(n)]
    for i in range(n):
        a, b = edges[i]
        for j in range(n):
            if i == j: continue
            c, d = edges[j]
            for p in seg_intersections(a, b, c, d):
                if p != a and p != b and on_segment(p, a, b):
                    cutpts[i].add(p)
    out = []
    for i, (a, b) in enumerate(edges):
        if not cutpts[i]:
            out.append((a, b))
            continue
        pts = sorted(cutpts[i], key=lambda p: seg_param(p, a, b))
        prev = a
        for p in pts:
            if p != prev: out.append((prev, p))
            prev = p
        if prev != b: out.append((prev, b))
    return out

def subtract(poly, tri):
    """region polygon (CCW) minus tile triangle (CCW, contained, corner on boundary):
    returns list of CCW polygons (possibly empty). Exact boundary surgery."""
    edges = []
    n = len(poly)
    for i in range(n):
        edges.append((poly[i], poly[(i + 1) % n]))
    for i in range(3):                                  # tile edges reversed (CW)
        edges.append((tri[(i + 1) % 3], tri[i]))
    edges = split_edges(edges)
    # cancel exact opposite pairs
    from collections import defaultdict
    bag = defaultdict(list)
    for e in edges:
        bag[(e[0], e[1])].append(e)
    result = []
    used = set()
    elist = list(bag.keys())
    keyset = defaultdict(int)
    for (p, q) in elist:
        keyset[(p, q)] += len(bag[(p, q)])
    final = []
    for (p, q) in list(keyset.keys()):
        k = keyset[(p, q)]
        if k == 0: continue
        rk = keyset.get((q, p), 0)
        m = min(k, rk)
        keyset[(p, q)] = k - m
        keyset[(q, p)] = rk - m
    for (p, q), k in keyset.items():
        for _ in range(k):
            final.append((p, q))
    if not final:
        return []
    # stitch loops: at each vertex pick, for incoming dir w, the outgoing edge first
    # encountered rotating CLOCKWISE from the reversed incoming direction (keeps interior left)
    from collections import defaultdict as dd
    outmap = dd(list)
    for (p, q) in final:
        outmap[p].append((p, q))
    unused = set(final)
    loops = []
    while unused:
        start = next(iter(unused))
        loop = [start]
        unused.discard(start)
        cur = start
        guard = 0
        while True:
            guard += 1
            if guard > 10000: raise RuntimeError("stitch runaway")
            p, q = cur
            w = vsub(p, q)                              # reversed incoming direction at q
            cands = [e for e in outmap[q] if e in unused or e == start]
            if not cands: raise RuntimeError("open chain in stitching")
            def cw_key(e):
                u = vsub(e[1], e[0])
                # angle of u measured clockwise from w, in (0, 2pi]: we pick the SMALLEST
                # clockwise angle; exact comparator via sorting all candidates
                return u
            if len(cands) == 1:
                nxt = cands[0]
            else:
                # pick candidate with smallest clockwise angle from w
                def cw_less(u, v):
                    # rotate so w is reference: clockwise angle of u from w smaller than v's?
                    # cw angle of u = 2pi - ccw angle; so smaller cw <=> larger ccw... measure
                    # ccw angle from w: use ang order relative to w via cross/dot exact:
                    cu = crossv(w, u).sign(); du = dot(w, u).sign()
                    cv = crossv(w, v).sign(); dv = dot(w, v).sign()
                    def sector(cx, dx):
                        # 0: along w; 1: ccw side; 2: opposite; 3: cw side  (ccw order)
                        if cx == 0 and dx > 0: return 0
                        if cx > 0: return 1
                        if cx == 0: return 2
                        return 3
                    su, sv = sector(cu, du), sector(cv, dv)
                    if su != sv: return su > sv          # larger ccw sector = smaller cw angle
                    return crossv(u, v).sign() < 0       # within sector: more cw first
                best = cands[0]
                for e in cands[1:]:
                    if cw_less(vsub(e[1], e[0]), vsub(best[1], best[0])):
                        best = e
                nxt = best
            if nxt == start:
                break
            loop.append(nxt)
            unused.discard(nxt)
            cur = nxt
        pts = [e[0] for e in loop]
        a2 = poly_area2(pts)
        if a2.sign() > 0:
            loops.append(pts)
        elif a2.sign() < 0:
            raise RuntimeError("negative loop area: stitching bug")
        # zero-area loops are degenerate slivers: error, since exact arithmetic
    return loops

# ------------------------------------------------------------------------------ placement ---
def unit_dir(p, q):
    v = vsub(q, p)
    L2 = dot(v, v)
    L = L2.sqrt_rational()
    if L is None:
        raise RuntimeError("boundary edge length not rational: " + repr(L2))
    return (v[0] / L, v[1] / L), L

def containment_ok(tri, poly):
    """tri (CCW) contained in poly (CCW): no proper crossings; every sub-piece midpoint of
    tri edges (split at boundary touches) inside-or-on; no poly vertex strictly inside tri;
    no poly-edge sub-piece midpoint strictly inside tri."""
    n = len(poly)
    pedges = [(poly[i], poly[(i + 1) % n]) for i in range(n)]
    tedges = [(tri[i], tri[(i + 1) % 3]) for i in range(3)]
    for (a, b) in tedges:
        for (c, d) in pedges:
            if proper_cross(a, b, c, d):
                return False
    # tri-edge pieces inside region
    for (a, b) in tedges:
        cuts = set()
        for (c, d) in pedges:
            for p in seg_intersections(a, b, c, d):
                cuts.add(seg_param(p, a, b))
        params = sorted(set([qd(0), qd(1)]) | cuts)
        for i in range(len(params) - 1):
            t = (params[i] + params[i + 1]) / 2
            mid = (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t)
            if point_in_polygon(mid, poly) == 'OUT':
                return False
    # poly vertices not strictly inside tri; poly-edge pieces not inside tri
    def in_tri(p):
        s1 = cross(tri[0], tri[1], p).sign()
        s2 = cross(tri[1], tri[2], p).sign()
        s3 = cross(tri[2], tri[0], p).sign()
        if s1 > 0 and s2 > 0 and s3 > 0: return 'IN'
        if s1 >= 0 and s2 >= 0 and s3 >= 0: return 'ON'
        return 'OUT'
    for v in poly:
        if in_tri(v) == 'IN':
            return False
    for (c, d) in pedges:
        cuts = set()
        for (a, b) in tedges:
            for p in seg_intersections(c, d, a, b):
                cuts.add(seg_param(p, c, d))
        params = sorted(set([qd(0), qd(1)]) | cuts)
        for i in range(len(params) - 1):
            t = (params[i] + params[i + 1]) / 2
            mid = (c[0] + (d[0] - c[0]) * t, c[1] + (d[1] - c[1]) * t)
            if in_tri(mid) == 'IN':
                return False
    return True

# ---------------------------------------------------------------------------------- search --
class Search(object):
    def __init__(self, tile, target, N, name, log_every=100000, node_cap=30000000):
        self.tile = tile
        self.N = N
        self.name = name
        self.nodes = 0
        self.maxdepth = 0
        self.prune_area = 0
        self.prune_run = 0
        self.prune_dir = 0
        self.placements_tried = 0
        self.found = None
        self.log_every = log_every
        self.node_cap = node_cap
        self.semi = Semigroup(tile.sides)
        self.target = target
        ta2 = poly_area2(target)
        assert ta2.sign() > 0, "target must be CCW"
        r = (ta2 / tile.area2)
        assert r.q == 0 and r.p == N, f"root area: target/tile = {r}, want {N}"
        # P4 setup: cos^2 of the smallest tile angle (opposite the smallest side). A CONVEX region
        # corner sharper than this cannot be filled by any tile corner -> untileable (sound).
        s = sorted(tile.sides); s1, s2 = s[1], s[2]
        cmin = Fraction(s1 * s1 + s2 * s2 - s[0] * s[0], 2 * s1 * s2)
        self.cosmin2 = QD(cmin * cmin)

    def corner_ok(self, poly):
        """P4: no convex corner is sharper than the smallest tile angle."""
        n = len(poly)
        for i in range(n):
            pv = poly[(i - 1) % n]; v = poly[i]; nx = poly[(i + 1) % n]
            if cross(pv, v, nx).sign() <= 0:
                continue                                        # reflex/straight
            u = (pv[0] - v[0], pv[1] - v[1]); w = (nx[0] - v[0], nx[1] - v[1])
            uw = dot(u, w)
            if uw.sign() <= 0:
                continue                                        # angle >= 90 deg, never too sharp
            if (uw * uw - self.cosmin2 * dot(u, u) * dot(w, w)).sign() > 0:
                return False                                    # cos^2 > cos^2(min) => angle < min
        return True

    def area_multiple(self, poly):
        r = poly_area2(poly) / self.tile.area2
        if r.q != 0 or r.p.denominator != 1 or r.p <= 0:
            return None
        return int(r.p)

    def runs_ok(self, poly):
        """P2: convex-ended maximal straight runs must lie in the side semigroup"""
        n = len(poly)
        # interior angle at vertex i convex iff cross(prev, v, next) > 0 (CCW polygon)
        conv = []
        for i in range(n):
            a, v, b = poly[i - 1], poly[i], poly[(i + 1) % n]
            s = cross(a, v, b).sign()
            conv.append(s)                      # >0 convex, 0 straight, <0 reflex
        # walk maximal straight runs
        for i in range(n):
            if conv[i] == 0:
                continue
            # start a run at vertex i
            j = i
            length = qd(0)
            steps = 0
            while True:
                jn = (j + 1) % n
                seg = vsub(poly[jn], poly[j])
                L2 = dot(seg, seg)
                L = L2.sqrt_rational()
                if L is None:
                    return False                # non-rational boundary length: impossible
                length = length + qd(L)
                j = jn
                steps += 1
                if steps > n: raise RuntimeError("run walk loop")
                if conv[j] != 0:
                    break
            if conv[i] > 0 and conv[j] > 0:     # both endpoints convex: prune applies
                Lr = length.p if length.q == 0 else None
                if Lr is None or not self.semi.contains(Lr):
                    return False
        return True

    def lowest_vertex(self, polys):
        best = None
        for pi, poly in enumerate(polys):
            for vi, v in enumerate(poly):
                key = (v[1], v[0])
                if best is None or key[0] < best[0][0] or (key[0] == best[0][0] and key[1] < best[0][1]):
                    # exact lexicographic compare
                    if best is None:
                        best = (key, pi, vi)
                    else:
                        dy = (key[0] - best[0][0]).sign()
                        if dy < 0 or (dy == 0 and (key[1] - best[0][1]).sign() < 0):
                            best = (key, pi, vi)
        return best[1], best[2]

    def placements(self, poly, vi):
        """the six corner-anchored candidate triangles at vertex vi of poly"""
        n = len(poly)
        v = poly[vi]
        nxt = poly[(vi + 1) % n]
        prv = poly[(vi - 1) % n]
        u, _ = unit_dir(v, nxt)
        w, _ = unit_dir(v, prv)
        out = []
        for (cs, sn, sidepairs) in self.tile.corners:
            r = rot(cs, sn, u)                          # corner ray at angle phi ccw from u
            # r must lie inside-or-on the sector [u ccw-> w]; sector < pi since v convex
            c1 = crossv(u, r).sign()
            c2 = crossv(r, w).sign()
            if c1 < 0 or c2 < 0:
                continue
            for (L, M) in sidepairs:
                p2 = (v[0] + u[0] * L, v[1] + u[1] * L)
                p3 = (v[0] + r[0] * M, v[1] + r[1] * M)
                tri = [v, p2, p3]
                if poly_area2(tri).sign() <= 0:
                    tri = [v, p3, p2]
                out.append(tri)
        return out

    def run(self):
        import time
        self.t0 = time.time()
        polys = [self.target]
        try:
            self.dfs(polys, self.N, [])
        except KeyboardInterrupt:
            return 'INCONCLUSIVE'
        if self.found is not None:
            return 'FOUND_TILING'
        if self.nodes >= self.node_cap:
            return 'INCONCLUSIVE'
        return 'EXHAUSTED_NO_TILING'

    def dfs(self, polys, left, placed):
        if self.found is not None or self.nodes >= self.node_cap:
            return
        self.nodes += 1
        d = self.N - left
        if d > self.maxdepth: self.maxdepth = d
        if self.nodes % self.log_every == 0:
            import time
            print(f"  [{self.name}] nodes={self.nodes} depth={d} max={self.maxdepth} "
                  f"pruneA={self.prune_area} pruneR={self.prune_run} "
                  f"t={time.time()-self.t0:.0f}s", flush=True)
        if not polys:
            if left == 0:
                self.found = list(placed)
            return
        if left == 0:
            return
        # P1 per polygon
        mult = []
        for poly in polys:
            m = self.area_multiple(poly)
            if m is None:
                self.prune_area += 1
                return
            mult.append(m)
        if sum(mult) != left:
            self.prune_area += 1
            return
        # P2
        for poly in polys:
            if not self.runs_ok(poly):
                self.prune_run += 1
                return
        # P4 corner-angle: a convex corner sharper than the smallest tile angle is unfillable
        for poly in polys:
            if not self.corner_ok(poly):
                self.prune_dir += 1
                return
        pi, vi = self.lowest_vertex(polys)
        poly = polys[pi]
        rest = polys[:pi] + polys[pi + 1:]
        for tri in self.placements(poly, vi):
            self.placements_tried += 1
            if not containment_ok(tri, poly):
                continue
            try:
                pieces = subtract(poly, tri)
            except RuntimeError:
                # surgery degenerate: treat as invalid placement (conservative? NO —
                # skipping a VALID placement would break exhaustiveness. Re-raise.)
                raise
            self.dfs(rest + pieces, left - 1, placed + [tri])
            if self.found is not None:
                return

# ------------------------------------------------------------------- independent reverify ---
def reverify(tiles, target, tile):
    """tiles: list of triangles; checks pairwise interior-disjointness (via area of overlap
    being zero <= no proper crossings and no vertex strictly inside) and total area."""
    tot = qd(0)
    for t in tiles:
        a2 = poly_area2(t)
        if (a2 - tile.area2).sign() != 0 and (a2 + tile.area2).sign() != 0:
            return False, "a tile has wrong area"
        tot = tot + (a2 if a2.sign() > 0 else -a2)
    if (tot - poly_area2(target)).sign() != 0:
        return False, "total area mismatch"
    def in_tri_strict(p, tri):
        s1 = cross(tri[0], tri[1], p).sign()
        s2 = cross(tri[1], tri[2], p).sign()
        s3 = cross(tri[2], tri[0], p).sign()
        return (s1 > 0 and s2 > 0 and s3 > 0) or (s1 < 0 and s2 < 0 and s3 < 0)
    for i in range(len(tiles)):
        for j in range(i + 1, len(tiles)):
            A, B = tiles[i], tiles[j]
            for k in range(3):
                for l in range(3):
                    if proper_cross(A[k], A[(k + 1) % 3], B[l], B[(l + 1) % 3]):
                        return False, f"tiles {i},{j} cross"
            for p in A:
                if in_tri_strict(p, B): return False, f"vertex of {i} inside {j}"
            for p in B:
                if in_tri_strict(p, A): return False, f"vertex of {j} inside {i}"
    return True, "ok"
