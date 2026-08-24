#!/usr/bin/env python3
"""Scan a certified tiling for lines that no tile crosses.

Reads the tile coordinates out of a Tiling*.lean certificate (exact ZZ[sqrt D]),
enumerates every line through two tiling vertices, and reports those no tile
crosses, with the tile counts on each side.

Regenerates the numbers quoted in Erdos634/CornerBlock.lean:
  99-tiling: 8 uncrossed lines -- 3 target sides, and 5 interior cutting off 1,1,4,4,25.
Usage:  python3 code/analysis/uncrossed_lines.py lean/Erdos634/Tiling99.lean 15
"""
import re, sys, itertools

def load(path):
    src = open(path).read()
    body = src[src.index('def tiles'):]
    body = body[:body.index(']') + 1]
    rx = re.compile(r'\(\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\),\s*'
                    r'\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\),\s*'
                    r'\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\)\)')
    out = []
    for m in rx.finditer(body):
        v = [int(x) for x in m.groups()]
        out.append((((v[0], v[1]), (v[2], v[3])),
                    ((v[4], v[5]), (v[6], v[7])),
                    ((v[8], v[9]), (v[10], v[11]))))
    return out

def main(path, D):
    def zmul(u, v): return (u[0]*v[0] + D*u[1]*v[1], u[0]*v[1] + u[1]*v[0])
    def zsub(u, v): return (u[0]-v[0], u[1]-v[1])
    def zsign(z):
        p, q = z
        if p == 0 and q == 0: return 0
        if p >= 0 and q >= 0: return 1
        if p <= 0 and q <= 0: return -1
        if p > 0:  return 1 if p*p > D*q*q else -1
        return -1 if p*p > D*q*q else 1
    def cross(o, a, b):
        return zsub(zmul(zsub(a[0], o[0]), zsub(b[1], o[1])),
                    zmul(zsub(a[1], o[1]), zsub(b[0], o[0])))

    tiles = load(path)
    verts = sorted({v for t in tiles for v in t})
    print(f"{len(tiles)} tiles, {len(verts)} distinct vertices")

    unc = [(P, Q) for P, Q in itertools.combinations(verts, 2)
           if not any((lambda s: 1 in s and -1 in s)([zsign(cross(P, Q, v)) for v in t])
                      for t in tiles)]
    lines = []
    for P, Q in unc:
        for (A, B), pts in lines:
            if zsign(cross(A, B, P)) == 0 and zsign(cross(A, B, Q)) == 0:
                pts.add(P); pts.add(Q); break
        else:
            lines.append(((P, Q), {P, Q}))

    print(f"distinct uncrossed lines: {len(lines)}")
    for i, ((A, B), pts) in enumerate(lines):
        lo = sum(1 for t in tiles if all(zsign(cross(A, B, v)) <= 0 for v in t)
                 and any(zsign(cross(A, B, v)) < 0 for v in t))
        hi = sum(1 for t in tiles if all(zsign(cross(A, B, v)) >= 0 for v in t)
                 and any(zsign(cross(A, B, v)) > 0 for v in t))
        kind = "target side" if 0 in (lo, hi) else f"interior, cuts off {min(lo, hi)}"
        print(f"  line {i}: {len(pts)} vertices, splits {lo} | {hi}   {kind}")

if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 15)
