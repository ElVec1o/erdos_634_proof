#!/usr/bin/env python3
"""Incidence census of the certified 99-tiling (Erdos #634, member (1,2) at m=3).

Reproduces the counts quoted in Remark~\\ref{rem:noedgetoedge} of the companion:
the tiling is not edge-to-edge, and pairs of vertices at a tile-side distance
routinely span no tile edge.

Source of truth is lean/Tiling99.lean, the zero-axiom kernel-checked certificate.
Points there are Pt = (x_a, x_b, y_a, y_b) meaning x = x_a + x_b*sqrt(15),
y = y_a + y_b*sqrt(15).  The script asserts x_b = y_a = 0 throughout, so
(x_a, y_b) is an affine rescaling of the plane; collinearity and betweenness are
therefore decided faithfully by integer arithmetic in that chart, while true
squared lengths are recovered as dx^2 + 15*dy^2.

Usage:  python3 code/incidence_census.py [path/to/Tiling99.lean]
"""

import re
import sys
from collections import Counter, defaultdict

# tile (2,3,4) scaled by 16 -> sides 32, 48, 64
SIDE = {32 ** 2: "a", 48 ** 2: "b", 64 ** 2: "c"}


def load(path):
    src = open(path).read()
    body = src.split("def tiles : List Tri := [", 1)[1].split("\n]", 1)[0]
    quads = [
        tuple(map(int, q))
        for q in re.findall(r"\((-?\d+),\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)\)", body)
    ]
    assert len(quads) % 3 == 0, "vertex count is not a multiple of 3"
    assert all(q[1] == 0 for q in quads), "some x is irrational; chart is not faithful"
    assert all(q[2] == 0 for q in quads), "some y has a rational part; chart is not faithful"
    pts = [(q[0], q[3]) for q in quads]
    return [[pts[i + k] for k in range(3)] for i in range(0, len(pts), 3)]


def norm2(u, v):
    return (u[0] - v[0]) ** 2 + 15 * (u[1] - v[1]) ** 2


def interior_to(p, u, v):
    """Is p strictly between u and v on the segment [u,v]?"""
    if p == u or p == v:
        return False
    if (v[0] - u[0]) * (p[1] - u[1]) - (v[1] - u[1]) * (p[0] - u[0]) != 0:
        return False
    dot = (p[0] - u[0]) * (v[0] - u[0]) + 15 * (p[1] - u[1]) * (v[1] - u[1])
    return 0 < dot < norm2(u, v)


def main(path):
    tiles = load(path)
    verts = sorted({p for t in tiles for p in t})
    edges = {
        (min(t[i], t[(i + 1) % 3]), max(t[i], t[(i + 1) % 3]))
        for t in tiles
        for i in range(3)
    }

    split = defaultdict(list)
    for u, v in edges:
        for p in verts:
            if interior_to(p, u, v):
                split[(u, v)].append(p)

    print(f"tiles {len(tiles)}   vertices {len(verts)}   distinct edges {len(edges)}")
    print(f"edges carrying a vertex in their relative interior: {len(split)}")
    mult = Counter(len(ps) for ps in split.values())
    print(f"  interior vertices per split edge: {dict(sorted(mult.items()))}")
    if len(split):
        print("  => the tiling is NOT edge-to-edge")

    print("pairs of vertices at an exact tile-side distance that span no tile edge:")
    for name, L in (("a", 32 ** 2), ("b", 48 ** 2), ("c", 64 ** 2)):
        pairs = [
            (u, v)
            for i, u in enumerate(verts)
            for v in verts[i + 1:]
            if norm2(u, v) == L
        ]
        loose = [p for p in pairs if (min(*p), max(*p)) not in edges]
        print(f"  {name}: {len(loose):3d} of {len(pairs):3d}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "lean/Tiling99.lean")
