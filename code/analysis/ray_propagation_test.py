#!/usr/bin/env python3
"""Falsifier: does an edge-chain from the boundary propagate to the perimeter?

Walks every edge-ray starting on the base of the certified 44-tiling and reports how many die in
the interior.  Nine of fifteen do, which refutes any argument that assumes such chains reach the
boundary.  Kept as the first test to run against future claims of that shape.
"""
import math, sys
D = 15
L = open('private/tiling_FILE_private_inst_g44.txt.txt').read().split('\n')
tris = []
for line in L[1:]:
    t = line.split()
    if len(t) < 18:
        continue
    v = []
    for k in range(3):
        p, q, d, p2, q2, d2 = t[6 * k:6 * k + 6]
        v.append(((int(p) + int(q) * math.sqrt(D)) / int(d),
                  (int(p2) + int(q2) * math.sqrt(D)) / int(d2)))
    tris.append(v)
edges = [(t[k], t[(k + 1) % 3]) for t in tris for k in range(3)]
pts = [q for t in tris for q in t]
X0, X1 = min(p[0] for p in pts), max(p[0] for p in pts)
apex = max(pts, key=lambda z: z[1])
near = lambda p, q: math.hypot(p[0] - q[0], p[1] - q[1]) < 1e-6
def dirn(p, q):
    d = (q[0] - p[0], q[1] - p[1]); n = math.hypot(*d); return ((d[0] / n, d[1] / n), n)
def on_boundary(p):
    if abs(p[1]) < 1e-6: return True
    for A, B in (((X0, 0.0), apex), ((X1, 0.0), apex)):
        cr = (B[0] - A[0]) * (p[1] - A[1]) - (B[1] - A[1]) * (p[0] - A[0])
        if abs(cr) / math.hypot(B[0] - A[0], B[1] - A[1]) < 1e-6: return True
    return False
stops = walks = 0
for (p, q) in edges:
    if abs(p[1]) > 1e-7: continue
    u, _ = dirn(p, q)
    if u[1] < 1e-9: continue
    cur, steps = q, 1
    while steps < 300:
        nxt = None
        for (r, s) in edges:
            if near(r, cur):
                v, l2 = dirn(r, s)
                if abs(v[0] - u[0]) < 1e-6 and abs(v[1] - u[1]) < 1e-6:
                    nxt = s; break
        if nxt is None: break
        cur = nxt; steps += 1
    walks += 1
    if not on_boundary(cur):
        stops += 1
print(f"rays walked from the base: {walks};  dying in the interior: {stops}")
sys.exit(0 if stops > 0 else 1)
