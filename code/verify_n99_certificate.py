#!/usr/bin/env python3
"""
verify_n99_certificate.py

Exact-arithmetic verification of the N = 99 tiling certificate:
the triangle T = (24, 24, 33) is tiled by 99 congruent copies of the
triangle t = (2, 3, 4).

This is a counterexample to the clause "g divides M" of Theorem 14 of
M. Beeson, "Triangle tiling: the case 3a+2b=pi", arXiv:1206.2229v3,
and hence to Corollary 2 / Table 3 of the same paper.

NO FLOATING POINT is used anywhere that a claim is decided: all
arithmetic is over the integers and over fractions.Fraction.

COORDINATES.  Everything is scaled by 16 and lives in Q(sqrt 15).
A pair (x, y) denotes the point (x, y*sqrt(15)) of the plane.
The target triangle is  T = (0,0), (528,0), (264, 72*sqrt 15),
whose side lengths are 384, 384, 528 = 16*(24, 24, 33).
Each of the 99 tiles has squared side lengths {1024, 2304, 4096}
 = 16^2 * (2^2, 3^2, 4^2).

For two points P=(x1,y1), Q=(x2,y2) in this notation:
    |PQ|^2               = (x2-x1)^2 + 15*(y2-y1)^2          (rational)
    2*signed area(O,P,Q) = [cross] * sqrt(15),  cross rational,
where cross(O,P,Q) = (Px-Ox)(Qy-Oy) - (Py-Oy)(Qx-Ox).
Because the sqrt(15) factors out of every cross product, all
line/polygon clipping parameters are rational, so exact polygon
clipping in this representation is exact rational arithmetic.

Run:  python3 verify_n99_certificate.py
"""

from fractions import Fraction as F
from itertools import combinations
from math import gcd

# ---------------------------------------------------------------- data
TARGET = ((0, 0), (528, 0), (264, 72))

TILES = [
    ((0,0), (32,0), (44,12)),
    ((32,0), (64,0), (76,12)),
    ((32,0), (76,12), (44,12)),
    ((64,0), (112,0), (120,8)),
    ((64,0), (92,4), (80,16)),
    ((112,0), (160,0), (168,8)),
    ((112,0), (140,4), (128,16)),
    ((160,0), (208,0), (216,8)),
    ((160,0), (188,4), (176,16)),
    ((208,0), (256,0), (264,8)),
    ((208,0), (236,4), (224,16)),
    ((256,0), (304,0), (312,8)),
    ((256,0), (284,4), (272,16)),
    ((304,0), (352,0), (360,8)),
    ((304,0), (332,4), (320,16)),
    ((352,0), (400,0), (408,8)),
    ((352,0), (408,8), (360,8)),
    ((400,0), (464,0), (442,6)),
    ((400,0), (456,8), (408,8)),
    ((464,0), (528,0), (506,6)),
    ((464,0), (506,6), (442,6)),
    ((92,4), (120,8), (108,20)),
    ((92,4), (108,20), (80,16)),
    ((140,4), (168,8), (156,20)),
    ((140,4), (156,20), (128,16)),
    ((188,4), (216,8), (204,20)),
    ((188,4), (204,20), (176,16)),
    ((236,4), (264,8), (252,20)),
    ((236,4), (252,20), (224,16)),
    ((284,4), (312,8), (300,20)),
    ((284,4), (300,20), (272,16)),
    ((332,4), (360,8), (348,20)),
    ((332,4), (348,20), (320,16)),
    ((442,6), (506,6), (484,12)),
    ((120,8), (136,24), (108,20)),
    ((168,8), (184,24), (156,20)),
    ((216,8), (232,24), (204,20)),
    ((264,8), (280,24), (252,20)),
    ((312,8), (328,24), (300,20)),
    ((360,8), (392,8), (348,20)),
    ((392,8), (456,8), (434,14)),
    ((392,8), (434,14), (370,14)),
    ((456,8), (484,12), (423,17)),
    ((44,12), (76,12), (88,24)),
    ((484,12), (451,21), (423,17)),
    ((370,14), (434,14), (412,20)),
    ((370,14), (412,20), (348,20)),
    ((80,16), (136,24), (88,24)),
    ((128,16), (184,24), (136,24)),
    ((176,16), (204,20), (192,32)),
    ((224,16), (280,24), (232,24)),
    ((272,16), (328,24), (280,24)),
    ((320,16), (376,24), (328,24)),
    ((423,17), (451,21), (390,26)),
    ((204,20), (232,24), (220,36)),
    ((204,20), (220,36), (192,32)),
    ((348,20), (412,20), (390,26)),
    ((451,21), (418,30), (390,26)),
    ((88,24), (120,24), (132,36)),
    ((120,24), (152,24), (164,36)),
    ((120,24), (164,36), (132,36)),
    ((152,24), (184,24), (196,36)),
    ((152,24), (196,36), (164,36)),
    ((232,24), (264,24), (220,36)),
    ((264,24), (312,24), (256,32)),
    ((264,24), (252,36), (220,36)),
    ((312,24), (376,24), (354,30)),
    ((312,24), (354,30), (346,38)),
    ((312,24), (329,31), (296,40)),
    ((312,24), (304,32), (256,32)),
    ((376,24), (418,30), (354,30)),
    ((354,30), (386,30), (342,42)),
    ((386,30), (418,30), (374,42)),
    ((386,30), (374,42), (342,42)),
    ((329,31), (346,38), (313,47)),
    ((329,31), (313,47), (296,40)),
    ((192,32), (220,36), (208,48)),
    ((256,32), (304,32), (248,40)),
    ((304,32), (296,40), (248,40)),
    ((132,36), (164,36), (176,48)),
    ((164,36), (196,36), (208,48)),
    ((164,36), (208,48), (176,48)),
    ((220,36), (252,36), (208,48)),
    ((252,36), (240,48), (208,48)),
    ((346,38), (330,54), (313,47)),
    ((248,40), (296,40), (240,48)),
    ((296,40), (313,47), (280,56)),
    ((296,40), (280,56), (268,44)),
    ((342,42), (374,42), (330,54)),
    ((268,44), (280,56), (252,60)),
    ((268,44), (252,60), (240,48)),
    ((313,47), (330,54), (297,63)),
    ((313,47), (297,63), (280,56)),
    ((176,48), (208,48), (220,60)),
    ((208,48), (240,48), (252,60)),
    ((208,48), (252,60), (220,60)),
    ((280,56), (297,63), (264,72)),
    ((280,56), (264,72), (252,60)),
    ((220,60), (252,60), (264,72)),]

# ------------------------------------------------------------ helpers
def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])

def cross(o, a, b):
    """2*signed area of (o,a,b), in units of sqrt(15).  Exact, rational."""
    ax, ay = sub(a, o)
    bx, by = sub(b, o)
    return ax * by - ay * bx

def d2(p, q):
    """Squared euclidean distance.  Exact, rational."""
    dx, dy = sub(q, p)
    return dx * dx + 15 * dy * dy

def clip(poly, A, B):
    """Sutherland-Hodgman: keep the part of convex `poly` on the
    closed left side (cross(A,B,.) >= 0) of the directed line A->B.
    Exact rational arithmetic."""
    out = []
    n = len(poly)
    for i in range(n):
        P, Q = poly[i], poly[(i + 1) % n]
        sp, sq = cross(A, B, P), cross(A, B, Q)
        if sp >= 0:
            out.append(P)
        if (sp > 0 and sq < 0) or (sp < 0 and sq > 0):
            t = F(sp, 1) / F(sp - sq, 1)
            out.append((P[0] + t * (Q[0] - P[0]),
                        P[1] + t * (Q[1] - P[1])))
    return out

def area2(poly):
    """2*area of a polygon, in units of sqrt(15).  Exact, rational."""
    s = 0
    n = len(poly)
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        s += x1 * y2 - x2 * y1
    return abs(s)

def ccw(t):
    return [t[0], t[1], t[2]] if cross(*t) > 0 else [t[0], t[2], t[1]]

def overlap_area2(A, B):
    """2*area of the intersection of two triangles, exact."""
    P = ccw(A)
    Q = ccw(B)
    for i in range(3):
        P = clip(P, Q[i], Q[(i + 1) % 3])
        if len(P) < 3:
            return 0
    return area2(P)

# --------------------------------------------------------------- tests
results = []

def check(name, ok, detail=""):
    results.append((name, ok, detail))
    print(("PASS  " if ok else "FAIL  ") + name + (("   " + detail) if detail else ""))

print("=" * 70)
print("N = 99 CERTIFICATE:  99 copies of (2,3,4) tile (24,24,33)")
print("exact arithmetic only (int / fractions.Fraction)")
print("=" * 70)

# --- A. the target is the triangle (24,24,33), scaled by 16
tsq = [d2(TARGET[0], TARGET[1]), d2(TARGET[1], TARGET[2]), d2(TARGET[2], TARGET[0])]
check("A1  target squared sides = 16^2*(33,24,24)",
      tsq == [528 ** 2, 384 ** 2, 384 ** 2], str(tsq))
check("A2  target is isosceles with apex at (264,72*sqrt15)",
      tsq[1] == tsq[2])

# --- B. the tile and the shape identities
a, b, c = 2, 3, 4
g = gcd(a, c)
check("B1  tile sides (2,3,4), gcd(a,c)=2, gcd(a,b,c)=1",
      g == 2 and gcd(gcd(a, b), c) == 1, "g = %d" % g)
# cos alpha = (b^2+c^2-a^2)/(2bc) : alpha opposite a
cos_al = F(b * b + c * c - a * a, 2 * b * c)
cos_3al = 4 * cos_al ** 3 - 3 * cos_al
cos_be = F(a * a + c * c - b * b, 2 * a * c)
check("B2  cos(alpha) = 7/8, cos(3 alpha) = 7/128",
      cos_al == F(7, 8) and cos_3al == F(7, 128),
      "cos a=%s cos 3a=%s" % (cos_al, cos_3al))
check("B3  cos(beta) = 11/16", cos_be == F(11, 16), str(cos_be))
# target base angle cosine = (33/2)/24 ; apex cosine from law of cosines
tb = F(33, 2) / 24
tap = F(24 ** 2 + 24 ** 2 - 33 ** 2, 2 * 24 * 24)
check("B4  target base angle = beta, apex angle = 3 alpha",
      tb == cos_be and tap == cos_3al, "base %s apex %s" % (tb, tap))
check("B5  Lemma 7 relation b = c - a^2/c holds for (2,3,4)",
      F(b) == c - F(a * a, c))
check("B6  Lemma 8: c = g^2 and g squarefree", c == g * g)

# --- C. the 99 tiles
check("C1  exactly 99 tiles", len(TILES) == 99, "%d" % len(TILES))

ok = True
bad = None
for i, t in enumerate(TILES):
    s = sorted([d2(t[0], t[1]), d2(t[1], t[2]), d2(t[2], t[0])])
    if s != [1024, 2304, 4096]:
        ok = False
        bad = (i, s)
        break
check("C2  every tile congruent to 16*(2,3,4)  (sq. sides {1024,2304,4096})",
      ok, "" if ok else "tile %d: %s" % bad)

ok = all(cross(*t) != 0 for t in TILES)
check("C3  no degenerate tile", ok)

# containment: every tile vertex inside the closed target
Tc = ccw(TARGET)
ok = True
for i, t in enumerate(TILES):
    for v in t:
        for k in range(3):
            if cross(Tc[k], Tc[(k + 1) % 3], v) < 0:
                ok = False
check("C4  every tile vertex lies in the closed target", ok)

# --- D. pairwise interior-disjointness, 4851 pairs, exact clipping
npairs = 0
worst = None
for i, j in combinations(range(99), 2):
    npairs += 1
    ov = overlap_area2(TILES[i], TILES[j])
    if ov != 0:
        worst = (i, j, ov)
        break
check("D1  all %d pairs have exactly zero overlap area" % npairs,
      worst is None and npairs == 4851,
      "" if worst is None else "pair %d,%d overlap 2A=%s*sqrt15" % worst)

# --- E. areas
tile_a2 = [abs(cross(*t)) for t in TILES]
check("E1  every tile has 2*area = 384*sqrt(15)",
      all(x == 384 for x in tile_a2), str(sorted(set(tile_a2))))
tot = sum(tile_a2)
tgt = abs(cross(*TARGET))
check("E2  sum of tile areas = target area  (%s = %s, in units of sqrt15/2)"
      % (tot, tgt), tot == tgt)
check("E3  99 * area(tile) = area(target): 99*384 = 38016", 99 * 384 == 38016)

# containment + zero pairwise overlap + equal total area  =>  union = target
check("E4  union of tiles = target  (from C4, D1, E2)",
      all(r[1] for r in results if r[0][:2] in ("C4", "D1", "E2")))

# --- F. the coloring number and the refutation
# Beeson Thm 14: N/M^2 = (3-s^2)/(1+s)^2 with s = a/c
s = F(a, c)
N = 99
M2 = F(N) * (1 + s) ** 2 / (3 - s ** 2)
check("F1  Theorem 14 relation N/M^2=(3-s^2)/(1+s)^2 gives M^2=81, M=9",
      M2 == 81)
M = 9
# coloring equation M(a+b+c) = X+Y+Z with (X,Y,Z)=(24,24,33) in tile units
check("F2  coloring equation M(a+b+c)=X+Y+Z: 9*9 = 24+24+33 = 81",
      M * (a + b + c) == 24 + 24 + 33)
check("F3  Theorem 14's other conclusions hold: 0 < N/3 < M^2 < 2N",
      0 < F(N, 3) < M ** 2 < 2 * N, "33 < 81 < 198")
check("F4  REFUTATION: g = 2 does NOT divide M = 9", M % g != 0)

# --- G. the valuation error in the printed proof
# eq (19): X^2 a(c^2-a^2)(a+c)^2 = a b c^5 M^2 ; a = g*ah, c = g^2
def vg(n, g):
    """exponent of g in n, for g the (squarefree) gcd; here g=2 is prime."""
    e = 0
    while n % g == 0:
        n //= g
        e += 1
    return e

ah = a // g
lhs_coeff = a * (c * c - a * a) * (a + c) ** 2
rhs_coeff = a * b * c ** 5
check("G1  v_g(a(c^2-a^2)(a+c)^2) = 5  (Beeson's left-side count is CORRECT)",
      vg(lhs_coeff, g) == 5, "= %d" % vg(lhs_coeff, g))
check("G2  v_g(a*b*c^5) = 11, NOT 6  (Beeson's right-side count is WRONG)",
      vg(rhs_coeff, g) == 11, "= %d" % vg(rhs_coeff, g))
# and symbolically:  a b c^5 = g*ah * b * g^10 = g^11 * ah * b, gcd(b,g)=1
check("G3  symbolic: a*b*c^5 = g^11*(ah*b) with gcd(ah*b, g) = 1",
      rhs_coeff == g ** 11 * (ah * b) and gcd(ah * b, g) == 1)

# eq (19) balances at the witness: X = 24 (in tile units), a=2,b=3,c=4,M=9
X = 24
L = X * X * a * (c * c - a * a) * (a + c) ** 2
R = a * b * c ** 5 * M * M
check("G4  eq (19) balances at the witness: both sides = 497664",
      L == R == 497664, "L=%d R=%d" % (L, R))

# --- H. eq (20) typo
check("H1  eq (20) as printed, N(a^2+c^2)=M^2(3c^2-a^2), FAILS: 1980 != 3564",
      N * (a * a + c * c) != M * M * (3 * c * c - a * a),
      "%d vs %d" % (N * (a * a + c * c), M * M * (3 * c * c - a * a)))
check("H2  corrected eq (20), N(a+c)^2 = M^2(3c^2-a^2), HOLDS: 3564 = 3564",
      N * (a + c) ** 2 == M * M * (3 * c * c - a * a))

# --- I. sibling values excluded by the same `M % g == 0` filter
sib = []
for m in range(1, 40):
    n = F(m * m) * (3 - s ** 2) / (1 + s) ** 2
    if n.denominator == 1 and n <= 1000:
        sib.append((int(n), m, m % g == 0))
check("I1  N<=1000 with tile (2,3,4): N = 11*M^2/9, M a multiple of 3",
      all(n == 11 * m * m // 9 for n, m, _ in sib),
      str([(n, m) for n, m, _ in sib]))
excluded = [n for n, m, keep in sib if not keep]
check("I2  values dropped by Beeson's `if M % g == 0` filter (odd M) are"
      " {11, 99, 275, 539, 891}; Table 3 keeps {44,176,396,704}",
      excluded == [11, 99, 275, 539, 891]
      and [n for n, m, k in sib if k] == [44, 176, 396, 704],
      "dropped %s ; kept %s"
      % (excluded, [n for n, m, k in sib if k]))
check("I3  only N = 99 is certified here; 11, 275, 539, 891 remain OPEN",
      True, "no certificate produced for these")

print("=" * 70)
nf = sum(1 for _, ok, _ in results if not ok)
print("%d checks, %d failed" % (len(results), nf))
print("OVERALL: " + ("PASS" if nf == 0 else "FAIL"))
raise SystemExit(1 if nf else 0)
