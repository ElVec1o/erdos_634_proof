#!/usr/bin/env python3
"""Flip a base-beta instance apex-down, so the corner-anchored engine builds the APEX first.

The apex-mismatch theorem (paper Thm "Apex mismatch", rung 2) shows the apex neighbourhood is
near-rigid at m=1: three forced alpha-tiles, a forced c|b mismatch ray, a forced T-junction at
distance b, a forced piercer start, a forced alpha-corner.  The engine anchors each step at the
lowest remaining vertex, so with the standard orientation (base at y=0) it explores the FAT part of
the tree (the base, with its several walks) first and meets the rigid apex last.  Flipping the
target puts the apex at the bottom: the forced chain is built in the first few placements and every
contradiction there prunes the whole tree above it.

The flip is the reflection (x,y) -> (x, H-y): a tiling of the flipped target is exactly a reflected
tiling of the original (mirror images of the tile are congruent and the engine places both
chiralities), so EXHAUSTED/FOUND verdicts transfer verbatim.

Usage: flip_inst.py <in.txt> <out.txt>
"""
import sys


def main():
    src, dst = sys.argv[1], sys.argv[2]
    tok = open(src).read().split()
    # layout: D | a b c | 3 x (cos qd, sin qd) = 18 | area2 qd = 3 | N | 3 points x 2 qd = 18
    head = tok[:1 + 3 + 18 + 3 + 1]
    pts = tok[1 + 3 + 18 + 3 + 1:]
    assert len(pts) == 18, len(pts)
    P = [pts[i * 6:(i + 1) * 6] for i in range(3)]  # each: x(pn qn den) y(pn qn den)
    # identify: two base points (y = 0 0 1) and the apex (y = H)
    base = [p for p in P if p[3:6] == ['0', '0', '1']]
    apex = [p for p in P if p[3:6] != ['0', '0', '1']]
    assert len(base) == 2 and len(apex) == 1, P
    A = apex[0]
    b1, b2 = sorted(base, key=lambda p: int(p[0]) / int(p[2]))   # left, right base corner
    H = A[3:6]
    # flipped, CCW, apex lowest: (apex.x, 0), (right.x, H), (left.x, H)
    newP = [A[0:3] + ['0', '0', '1'], b2[0:3] + H, b1[0:3] + H]
    out = head + [t for p in newP for t in p]
    with open(dst, 'w') as fh:
        fh.write(' '.join(out) + '\n')
    print("flipped %s -> %s  (apex at y=0)" % (src, dst))


if __name__ == "__main__":
    main()
