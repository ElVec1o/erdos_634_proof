#!/usr/bin/env python3
"""gencert_quad.py — kernel-certificate generator for PARALLELOGRAM (quad) targets.

Companion to gencert.py (triangle targets). Re-checks every condition exactly in Python over
Z[sqrt D] before emitting the Lean file:
  C1 congruence: each tile's squared side multiset = (scale*(a,b,c))^2, all rational
  C2 containment: CCW orientation + all vertices in the closed quad (4 half-planes)
  C3 disjointness: an explicit separating edge-line for every tile pair
  C4 area: signed 2-areas sum to the quad's 2-area

Corner convention: a quad corner "x,y" denotes the point (x, y*sqrt D) in SCALED coordinates;
the base-beta unit parallelogram always has this shape (rational x, sqrt-multiple y).

Usage:
  python3 gencert_quad.py <witness.txt> <Out.lean> <Namespace> <D> <a,b,c> <scale> "<4 corners>"
Examples (the two members settled so far):
  python3 gencert_quad.py ../code/engine/tiling_FILE_.._private_inst_pgram22.txt.txt \\
      PgramTiling22.lean PgramTiling22 15 2,3,4 4 "0,0 44,0 66,6 22,6"
  python3 gencert_quad.py ../private/tiling_FILE_inst_pgram52.txt.txt \\
      PgramTiling52.lean PgramTiling52 35 3,8,9 3 "0,0 78,0 117,12 39,12"
"""
from fractions import Fraction
import itertools, sys

if len(sys.argv) != 8:
    print(__doc__); sys.exit(1)
SRC, OUT, NS = sys.argv[1], sys.argv[2], sys.argv[3]
D = int(sys.argv[4])
ABC = tuple(int(x) for x in sys.argv[5].split(","))
SCALE = int(sys.argv[6])
QUAD = [tuple(int(v) for v in c.split(",")) for c in sys.argv[7].split()]
assert len(QUAD) == 4, "quad needs 4 corners"

# ---- exact Z[sqrt D] = a + b*sqrt(D), integer coefficients ----
def zmul(u, v): return (u[0]*v[0] + D*u[1]*v[1], u[0]*v[1] + u[1]*v[0])
def zsub(u, v): return (u[0]-v[0], u[1]-v[1])
def zadd(u, v): return (u[0]+v[0], u[1]+v[1])
def znonneg(z):
    a, b = z
    if a >= 0: return True if b >= 0 else D*b*b <= a*a
    return False if b < 0 else a*a <= D*b*b
def znonpos(z): return znonneg((-z[0], -z[1]))
def zpos(z): return not znonpos(z)
def cross(o, a, b):
    return zsub(zmul(zsub(a[0], o[0]), zsub(b[1], o[1])),
                zmul(zsub(a[1], o[1]), zsub(b[0], o[0])))
def dist2(p, q):
    dx, dy = zsub(q[0], p[0]), zsub(q[1], p[1])
    return zadd(zmul(dx, dx), zmul(dy, dy))

# ---- parse the engine witness (each vertex component is (p + q*sqrt D)/r) ----
tiles = []
with open(SRC) as fh:
    fh.readline()
    for line in fh:
        t = line.split()
        if len(t) != 18: continue
        vs = []
        for k in range(3):
            p, q, r, s, tt, u = (int(x) for x in t[6*k:6*k+6])
            xr, xi = Fraction(p*SCALE, r), Fraction(q*SCALE, r)
            yr, yi = Fraction(s*SCALE, u), Fraction(tt*SCALE, u)
            assert all(f.denominator == 1 for f in (xr, xi, yr, yi)), f"scale {SCALE} too small: {line}"
            vs.append(((int(xr), int(xi)), (int(yr), int(yi))))
        tiles.append(tuple(vs))
N = len(tiles)
print(f"{N} tiles read")

tiles = [t if zpos(cross(*t)) else (t[0], t[2], t[1]) for t in tiles]

# ---- C1 ----
SQ = sorted((SCALE*s)**2 for s in ABC)
for t in tiles:
    ds = sorted(dist2(t[i], t[(i+1) % 3]) for i in range(3))
    assert [d[0] for d in ds] == SQ and all(d[1] == 0 for d in ds), ds
print(f"C1 ok: all {N} tiles congruent to {SCALE}*{ABC}")

# ---- C2 ----
Q = [((c[0], 0), (0, c[1])) for c in QUAD]
for t in tiles:
    for v in t:
        for k in range(4):
            assert znonneg(cross(Q[k], Q[(k+1) % 4], v)), (v, k)
print("C2 ok: all vertices inside the quad")

# ---- C4 ----
tot = (0, 0)
for t in tiles: tot = zadd(tot, cross(*t))
qarea = zadd(cross(Q[0], Q[1], Q[2]), cross(Q[0], Q[2], Q[3]))
assert tot == qarea, (tot, qarea)
print(f"C4 ok: area sum {tot} = quad 2-area")

# ---- C3 ----
def sepBy(P, Qp, A, B):
    sA = [cross(P, Qp, v) for v in A]; sB = [cross(P, Qp, v) for v in B]
    return (all(znonneg(s) for s in sA) and all(znonpos(s) for s in sB)) or \
           (all(znonpos(s) for s in sA) and all(znonneg(s) for s in sB))
wit = []
for i, j in itertools.combinations(range(N), 2):
    A, B = tiles[i], tiles[j]
    found = None
    for flip, e in itertools.product((True, False), range(3)):
        T = A if flip else B
        if sepBy(T[e], T[(e+1) % 3], A, B): found = (flip, e); break
    assert found, f"no separator for pair {i},{j}"
    wit.append(found)
print(f"C3 ok: separators for all {len(wit)} pairs")

# ---- emit Lean ----
def pt(v): return f"({v[0][0]},{v[0][1]},{v[1][0]},{v[1][1]})"
tile_lines = ",\n".join("  ({}, {}, {})".format(*(pt(v) for v in t)) for t in tiles)
chunks, cur = [], []
for f, e in wit:
    cur.append(f"({'true' if f else 'false'},{e})")
    if len(cur) == 12: chunks.append("  " + ", ".join(cur) + ","); cur = []
if cur: chunks.append("  " + ", ".join(cur) + ",")
chunks[-1] = chunks[-1].rstrip(",")
wit_lines = "\n".join(chunks)
sqset = " && ".join(f"s.contains (({q}:Int),(0:Int))" for q in SQ)
qdefs = "\n".join(f"def q{k+1} : Pt := ({QUAD[k][0]},0,0,{QUAD[k][1]})" for k in range(4))

lean = f"""-- {OUT} — zero-axiom kernel verification of a parallelogram tiling certificate (Erdos #634).
-- {N} copies of the tile {ABC} tile the parallelogram with corners {QUAD} (scaled by {SCALE} into
-- Z[sqrt{D}]; a corner (x,y) denotes the point x + y*sqrt{D}). Kernel checks: (C1) squared side
-- multiset {SQ}; (C2) CCW + vertices in the closed quad (4 half-planes); (C3) an explicit
-- separating edge-line per pair ({len(wit)} pairs) => disjoint interiors; (C4) signed 2-areas sum
-- to the quad's. Generated by gencert_quad.py, which re-checks all four exactly in Python first.
-- No imports, no axioms.
namespace {NS}
abbrev ZD := Int × Int
abbrev Pt := Int × Int × Int × Int
def zmul (u v : ZD) : ZD := (u.1*v.1 + {D}*u.2*v.2, u.1*v.2 + u.2*v.1)
def zsub (u v : ZD) : ZD := (u.1 - v.1, u.2 - v.2)
def zadd (u v : ZD) : ZD := (u.1 + v.1, u.2 + v.2)
def znonneg (z : ZD) : Bool :=
  if 0 <= z.1 then (if 0 <= z.2 then true else {D}*z.2*z.2 <= z.1*z.1)
  else (if z.2 < 0 then false else z.1*z.1 <= {D}*z.2*z.2)
def znonpos (z : ZD) : Bool := znonneg (-z.1, -z.2)
def zpos (z : ZD) : Bool := !(znonpos z)
def px (p : Pt) : ZD := (p.1, p.2.1)
def py (p : Pt) : ZD := (p.2.2.1, p.2.2.2)
def cross (o a b : Pt) : ZD :=
  zsub (zmul (zsub (px a) (px o)) (zsub (py b) (py o))) (zmul (zsub (py a) (py o)) (zsub (px b) (px o)))
def dist2 (p q : Pt) : ZD :=
  zadd (zmul (zsub (px q) (px p)) (zsub (px q) (px p))) (zmul (zsub (py q) (py p)) (zsub (py q) (py p)))
abbrev Tri := Pt × Pt × Pt
def t1 (t : Tri) : Pt := t.1
def t2 (t : Tri) : Pt := t.2.1
def t3 (t : Tri) : Pt := t.2.2
def congOK (t : Tri) : Bool :=
  let d1 := dist2 (t1 t) (t2 t); let d2 := dist2 (t2 t) (t3 t); let d3 := dist2 (t3 t) (t1 t)
  let s : List ZD := [d1, d2, d3]
  {sqset}
  && d1.2 == 0 && d2.2 == 0 && d3.2 == 0 && (d1.1 + d2.1 + d3.1 == {sum(SQ)})
{qdefs}
def insideOK (t : Tri) : Bool :=
  zpos (cross (t1 t) (t2 t) (t3 t)) &&
  [t1 t, t2 t, t3 t].all (fun v =>
    znonneg (cross q1 q2 v) && znonneg (cross q2 q3 v) &&
    znonneg (cross q3 q4 v) && znonneg (cross q4 q1 v))
def sepBy (P Q : Pt) (A B : Tri) : Bool :=
  let sA := [t1 A, t2 A, t3 A].map (fun v => cross P Q v)
  let sB := [t1 B, t2 B, t3 B].map (fun v => cross P Q v)
  (sA.all znonneg && sB.all znonpos) || (sA.all znonpos && sB.all znonneg)
def edgeOf (t : Tri) (e : Nat) : Pt × Pt :=
  if e == 0 then (t1 t, t2 t) else if e == 1 then (t2 t, t3 t) else (t3 t, t1 t)
def area2 (t : Tri) : ZD := cross (t1 t) (t2 t) (t3 t)
def area2target : ZD := (({qarea[0]}:Int), ({qarea[1]}:Int))
def tiles : List Tri := [
{tile_lines}
]
def wit : List (Bool × Nat) := [
{wit_lines}
]
def pairSep (A B : Tri) (w : Bool × Nat) : Bool :=
  let pq := edgeOf (if w.1 then A else B) w.2
  sepBy pq.1 pq.2 A B
def checkPairs : List Tri → List (Bool × Nat) → Bool
  | [], ws => ws.isEmpty
  | t :: rest, ws =>
      let n := rest.length
      (ws.take n).length == n
      && (List.zip rest (ws.take n)).all (fun (u, w) => pairSep t u w)
      && checkPairs rest (ws.drop n)
def zsum (l : List ZD) : ZD := l.foldl zadd ((0:Int),(0:Int))
def checkAll : Bool :=
  tiles.length == {N} && tiles.all congOK && tiles.all insideOK
  && checkPairs tiles wit && zsum (tiles.map area2) == area2target
set_option maxRecDepth 16384 in
theorem {NS.lower()}_certificate : checkAll = true := by decide
end {NS}
"""
with open(OUT, "w") as fh: fh.write(lean)
print("wrote", OUT)
