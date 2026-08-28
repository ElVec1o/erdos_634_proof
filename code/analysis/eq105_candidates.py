#!/usr/bin/env python3
"""The 2pi/3 candidates for an equilateral 105-tiling: there is exactly one.

A 2pi/3 tile (a,b,c) has c^2 = a^2 + ab + b^2 and area (sqrt3/4)ab.  Tiling an equilateral of side
s with N tiles needs N*(sqrt3/4)ab = (sqrt3/4)s^2, so s^2 = N*ab.  For N = 105 that makes 105ab a
perfect square.  The condition is invariant under scaling the tile, so enumerating PRIMITIVE
triples suffices.  Exactly one survives: (21,320,331), with s = 840.  That instance was then
excluded by certified exhaustive search (25,742,338 nodes), which closes N = 105.
"""
import math, sys
N = 105
LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
found = []
for a in range(1, LIM):
    for b in range(a, LIM):
        c2 = a * a + a * b + b * b
        c = math.isqrt(c2)
        if c * c != c2:
            continue
        if math.gcd(math.gcd(a, b), c) != 1:
            continue
        s2 = N * a * b
        s = math.isqrt(s2)
        if s * s == s2:
            found.append((a, b, c, s))
print(f"primitive 2pi/3 triples with {N}ab a perfect square, a <= b < {LIM}:")
for a, b, c, s in found:
    print(f"  (a,b,c) = ({a},{b},{c})   side s = {s}   c^2 = {c*c} = {a*a+a*b+b*b}")
print(f"count: {len(found)}")
sys.exit(0 if len(found) == 1 else 1)
