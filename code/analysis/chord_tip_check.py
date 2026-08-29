#!/usr/bin/env python3
"""The V_1 repair is a k=1 phenomenon: only the first chord tip is on the boundary.

W_k = ((k-1)c, 0) + 2a*u is the tip of the chord's extension at the corner-chain's step k.
The repair blocks escapes because nothing continues past W_k when it lies on the target's equal
side.  That happens exactly at k = 1 (the offset ((k-1)c, 0) is horizontal, u is not).  Prints
the distance from W_k to the equal side, confirming 0 at k=1 and interior at k=2.
"""
import math, sys
ok = True
for e, f in ((2, 5), (3, 7), (2, 9), (4, 9), (5, 11)):
    a, b, c = e * f, f * f - e * e, f * f
    cb = (a * a + c * c - b * b) / (2 * a * c)
    sb = math.sqrt(1 - cb * cb)
    u = (cb, sb)
    for k in (1, 2):
        W = ((k - 1) * c + 2 * a * u[0], 2 * a * u[1])
        proj = W[0] * u[0] + W[1] * u[1]
        perp = math.hypot(W[0] - proj * u[0], W[1] - proj * u[1])
        on = perp < 1e-9
        if k == 1 and not on: ok = False
        if k == 2 and on: ok = False
        print(f"(e,f)=({e},{f}) k={k}: dist to equal side = {perp:9.4f}  on boundary = {on}")
sys.exit(0 if ok else 1)
