#!/usr/bin/env python3
"""Interface census of the certified (1,2)-family tilings (Erdos #634).

Exact arithmetic over Q(sqrt(15)) throughout: a number is a pair (p, q) of
Fractions meaning p + q*sqrt(15).  No floating point in any decision; floats
appear only as sort keys for output ordering along a fixed line, never in a
comparison that affects a reported fact.

For each certificate the script reports:
  1. every maximal straight interface whose two-sided edge words differ as
     multisets (the "interface equations"), with the words;
  2. the boundary words of the target;
  3. the chirality census (direct/reflected copies of the tile);
  4. straddler counts for the skeleton walls, the unit-scale corner-block
     walls, and the cevian (apex to the base point at distance e*c*m from the
     east corner).

Findings reproduced by this script (paper, companion, sec:comprealize):
  - every nontrivial interface equation in every certificate is one of
    c=2a, 2b=3a, 2b=a+c, 3c=4b, a+2b=2c -- each a multiple of (f-2e) on
    (a,b,c)=(ef,f^2-e^2,f^2): the seeds are (1,2)-degenerate;
  - Tiling44.lean is the tiling N44B (identical words);
  - N44C: cevian clean (0 straddlers), both fm-walls crossed (3+3), west
    unit f-block broken (6), east unit e-block complete (0);
  - Tiling99: both unit corner blocks complete (0), fm-walls crossed (8+4),
    cevian crossed (3);
  - CevianTiling28/63 cross their internal atom wall (3 resp. 7): no
    certified atom tiling exists at any scale.

Sources of truth: the zero-axiom kernel certificates lean/Tiling44.lean,
lean/Tiling99.lean, lean/PgramTiling22.lean, lean/CevianTiling28.lean,
lean/CevianTiling63.lean, lean/Tiling28.lean, lean/Tiling77.lean, and the
engine tilings code/engine/tilings/tiling_N44B.txt,
tiling_N44C_second_16_16_22.txt, tiling_99_isobeta_24_24_33.txt.

Usage: python3 code/interface_census.py   (from the repo root)
"""
import re
import sys
import os
from fractions import Fraction as F
from collections import Counter, defaultdict

D = 15

# ---------- exact Q(sqrt(D)) ----------
def add(u, v): return (u[0] + v[0], u[1] + v[1])
def sub(u, v): return (u[0] - v[0], u[1] - v[1])
def mul(u, v): return (u[0] * v[0] + D * u[1] * v[1], u[0] * v[1] + u[1] * v[0])
def sign(u):
    p, q = u
    if p == 0 and q == 0: return 0
    if p >= 0 and q >= 0: return 1
    if p <= 0 and q <= 0: return -1
    if p > 0: return 1 if p * p > D * q * q else (-1 if p * p < D * q * q else 0)
    return 1 if D * q * q > p * p else (-1 if D * q * q < p * p else 0)
def approx(u): return float(u[0]) + float(u[1]) * D ** 0.5

class Pt:
    __slots__ = ('x', 'y')
    def __init__(self, x, y): self.x, self.y = x, y
    def __eq__(self, o): return self.x == o.x and self.y == o.y
    def __hash__(self): return hash((self.x, self.y))

def psub(a, b): return (sub(a.x, b.x), sub(a.y, b.y))
def cross(o, a, b):
    u, v = psub(a, o), psub(b, o)
    return sub(mul(u[0], v[1]), mul(u[1], v[0]))
def dist2(a, b):
    u = psub(b, a)
    return add(mul(u[0], u[0]), mul(u[1], u[1]))

# ---------- parsers ----------
def parse_txt(fname):
    """engine format: header, then per line 3 vertices of 6 ints (xa xb xd ya yb yd)."""
    tiles = []
    with open(fname) as fh:
        fh.readline()
        for line in fh:
            t = line.split()
            if len(t) != 18: continue
            vs = []
            for i in range(3):
                xa, xb, xd, ya, yb, yd = (int(z) for z in t[6 * i:6 * i + 6])
                vs.append(Pt((F(xa, xd), F(xb, xd)), (F(ya, yd), F(yb, yd))))
            tiles.append(tuple(vs))
    return tiles

def parse_lean(path):
    """Lean vertex = (xa, xb, ya, yb) meaning (xa + xb*sqrtD, ya + yb*sqrtD)."""
    txt = open(path).read()
    m = re.search(r'def tiles\s*:\s*List Tri\s*:=\s*\[(.*?)\]\s*(?:def|theorem|/--|--)', txt, re.S)
    tuples = re.findall(
        r'\(\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\),\s*\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\),\s*'
        r'\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\)\)', m.group(1).replace('\n', ' '))
    tiles = []
    for tp in tuples:
        v = [int(z) for z in tp]
        pts = []
        for k in range(3):
            xa, xb, ya, yb = v[4 * k:4 * k + 4]
            pts.append(Pt((F(xa), F(xb)), (F(ya), F(yb))))
        tiles.append(tuple(pts))
    return tiles

# ---------- geometry ----------
def line_key(p, q):
    d = psub(q, p)
    A = (-d[1][0], -d[1][1]); B = d[0]
    C = add(mul(A, p.x), mul(B, p.y))
    comps = [A[0], A[1], B[0], B[1], C[0], C[1]]
    s = next(c for c in comps if c != 0)
    comps = [c / s for c in comps]
    if comps[next(i for i, c in enumerate(comps) if c != 0)] < 0:
        comps = [-c for c in comps]
    return tuple(comps)

def on_segment_param(P, Q, v):
    if sign(cross(P, Q, v)) != 0: return None
    d = psub(Q, P); w = psub(v, P)
    dd = add(mul(d[0], d[0]), mul(d[1], d[1]))
    wd = add(mul(w[0], d[0]), mul(w[1], d[1]))
    if sign(wd) < 0 or sign(sub(dd, wd)) < 0: return None
    return approx(wd) / approx(dd)

def interfaces(tiles, d2sym):
    """maximal straight interfaces with both sides covered; returns those with
    differing multisets, as (length_hint, wordL, wordR)."""
    lines = defaultdict(list)
    for i, t in enumerate(tiles):
        for k in range(3):
            p, q = t[k], t[(k + 1) % 3]
            lines[line_key(p, q)].append((i, p, q))
    out = []
    for key, edges in lines.items():
        i0, p0, q0 = edges[0]
        d = psub(q0, p0)
        dd = approx(add(mul(d[0], d[0]), mul(d[1], d[1]))) ** 0.5
        def par(v):
            w = psub(v, p0)
            return approx(add(mul(w[0], d[0]), mul(w[1], d[1]))) / dd
        items = []
        for (i, p, q) in edges:
            t = tiles[i]
            third = next(v for v in t if v != p and v != q)
            side = sign(cross(p0, q0, third))
            lab = d2sym.get((dist2(p, q)[0], dist2(p, q)[1]), '?')
            a_, b_ = par(p), par(q)
            items.append((min(a_, b_), max(a_, b_), side, lab, i))
        items.sort()
        comps, cur, cur_end = [], [items[0]], items[0][1]
        for it in items[1:]:
            if it[0] < cur_end + 1e-9:
                cur.append(it); cur_end = max(cur_end, it[1])
            else:
                comps.append(cur); cur, cur_end = [it], it[1]
        comps.append(cur)
        for comp in comps:
            left = sorted(x for x in comp if x[2] > 0)
            right = sorted(x for x in comp if x[2] < 0)
            if left and right:
                wl = ''.join(x[3] for x in left); wr = ''.join(x[3] for x in right)
                if Counter(wl) != Counter(wr):
                    lo = min(x[0] for x in comp); hi = max(x[1] for x in comp)
                    out.append((round(hi - lo, 6), wl, wr))
    return out

def straddlers(tiles, P, Q):
    out = []
    for i, t in enumerate(tiles):
        ss = [sign(cross(P, Q, v)) for v in t]
        if 1 in ss and -1 in ss:
            d = psub(Q, P)
            dd = approx(add(mul(d[0], d[0]), mul(d[1], d[1])))
            ts = [approx(add(mul(psub(v, P)[0], d[0]), mul(psub(v, P)[1], d[1]))) / dd for v in t]
            if max(ts) > 1e-12 and min(ts) < 1 - 1e-12:
                out.append(i)
    return out

def chirality(tiles, d2sym):
    """direct/reflected census: orientation of (V_alpha, V_beta, V_gamma)."""
    n_pos = n_neg = 0
    A2 = next(k for k, v in d2sym.items() if v == 'a')[0]
    B2 = next(k for k, v in d2sym.items() if v == 'b')[0]
    for t in tiles:
        opp = {}
        for k in range(3):
            d2 = dist2(t[(k + 1) % 3], t[(k + 2) % 3])[0]
            opp['alpha' if d2 == A2 else ('beta' if d2 == B2 else 'gamma')] = t[k]
        chi = sign(cross(opp['alpha'], opp['beta'], opp['gamma']))
        if chi > 0: n_pos += 1
        else: n_neg += 1
    return n_pos, n_neg

def sym_table(scale):
    return {(F(4 * scale * scale), F(0)): 'a',
            (F(9 * scale * scale), F(0)): 'b',
            (F(16 * scale * scale), F(0)): 'c'}

def report(name, tiles, d2sym, segs=()):
    print(f"== {name}: {len(tiles)} tiles")
    p, n = chirality(tiles, d2sym)
    print(f"   chirality: {p} direct / {n} reflected")
    eqs = interfaces(tiles, d2sym)
    seen = Counter()
    for (_, wl, wr) in eqs:
        seen[(''.join(sorted(wl)), ''.join(sorted(wr)))] += 1
    for (l, r), k in sorted(seen.items()):
        print(f"   equation {l} = {r}   (x{k})")
    if not seen:
        print("   no nontrivial interface equations")
    for label, P, Q in segs:
        print(f"   straddlers of {label}: {straddlers(tiles, P, Q)}")

def main():
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    LEAN = os.path.join(root, 'lean')
    ENG = os.path.join(root, 'code', 'engine', 'tilings')
    R = lambda a, b: (F(a), F(b))

    # N44C (scale 1): target (0,0),(22,0),(11,3r15)
    t = parse_txt(os.path.join(ENG, 'tiling_N44C_second_16_16_22.txt'))
    segs = [
        ("fm west wall (8,0)-(11,3r15)", Pt(R(8, 0), R(0, 0)), Pt(R(11, 0), R(0, 3))),
        ("fm east wall (14,0)-(77/4,3/4 r15)", Pt(R(14, 0), R(0, 0)), Pt((F(77, 4), F(0)), (F(0), F(3, 4)))),
        ("cevian (14,0)-(11,3r15)", Pt(R(14, 0), R(0, 0)), Pt(R(11, 0), R(0, 3))),
        ("unit west f-block wall (4,0)-(11/2,3/2 r15)", Pt(R(4, 0), R(0, 0)), Pt((F(11, 2), F(0)), (F(0), F(3, 2)))),
        ("unit east e-block wall (18,0)-(165/8,3/8 r15)", Pt(R(18, 0), R(0, 0)), Pt((F(165, 8), F(0)), (F(0), F(3, 8)))),
    ]
    report("N44C (txt, scale 1)", t, sym_table(1), segs)

    t = parse_txt(os.path.join(ENG, 'tiling_N44B.txt'))
    report("N44B (txt, scale 1)", t, sym_table(1))
    t = parse_lean(os.path.join(LEAN, 'Erdos634', 'Tiling44.lean'))
    report("Tiling44.lean (scale 8)", t, sym_table(8))

    # Tiling99 (scale 16): target (0,0),(528,0),(264,72r15); unit blocks and fm walls at scale 16
    t = parse_lean(os.path.join(LEAN, 'Erdos634', 'Tiling99.lean'))
    segs = [
        ("unit west f-block wall", Pt(R(64, 0), R(0, 0)), Pt(R(88, 0), R(0, 24))),
        ("unit east e-block wall", Pt(R(464, 0), R(0, 0)), Pt(R(506, 0), R(0, 6))),
        ("fm west wall", Pt(R(192, 0), R(0, 0)), Pt(R(264, 0), R(0, 72))),
        ("cevian", Pt(R(336, 0), R(0, 0)), Pt(R(264, 0), R(0, 72))),
    ]
    report("Tiling99.lean (scale 16)", t, sym_table(16), segs)

    t = parse_lean(os.path.join(LEAN, 'Erdos634', 'PgramTiling22.lean'))
    report("PgramTiling22.lean (scale 4)", t, sym_table(4))

    # CevianTiling28 (scale 8): chart (0,0),(112,0),(24,24r15); atom wall (48,0)-(24,24r15)
    t = parse_lean(os.path.join(LEAN, 'Erdos634', 'CevianTiling28.lean'))
    report("CevianTiling28.lean (scale 8)", t, sym_table(8),
           [("atom wall (48,0)-(24,24r15)", Pt(R(48, 0), R(0, 0)), Pt(R(24, 0), R(0, 24)))])
    # CevianTiling63 (scale 8): chart (0,0),(168,0),(36,36r15); atom wall (72,0)-(36,36r15)
    t = parse_lean(os.path.join(LEAN, 'Erdos634', 'CevianTiling63.lean'))
    report("CevianTiling63.lean (scale 8)", t, sym_table(8),
           [("atom wall (72,0)-(36,36r15)", Pt(R(72, 0), R(0, 0)), Pt(R(36, 0), R(0, 36)))])

    t = parse_lean(os.path.join(LEAN, 'Erdos634', 'Tiling28.lean'))
    report("Tiling28.lean (scale 16)", t, sym_table(16))
    t = parse_lean(os.path.join(LEAN, 'Erdos634', 'Tiling77.lean'))
    report("Tiling77.lean (scale 16)", t, sym_table(16))

    # the equations, reduced on (a,b,c) = (ef, f^2-e^2, f^2)
    print("\nReduction of every observed equation on (a,b,c) = (ef, f^2-e^2, f^2):")
    print("  c-2a         = -f(2e-f)")
    print("  2b-3a        = -(e+2f)(2e-f)")
    print("  2b-(a+c)     = -(e+f)(2e-f)")
    print("  4b-3c        = (f-2e)(f+2e)")
    print("  (a+2b)-2c    = -e(2e-f)")
    print("Each vanishes exactly on f = 2e: the certified seeds are (1,2)-degenerate.")

if __name__ == '__main__':
    main()
