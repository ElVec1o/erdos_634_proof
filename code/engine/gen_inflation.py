#!/usr/bin/env python3
"""Generate an inflation instance for member (e,f): the tile scaled by f, to be tiled by f^2 copies.

Writes the engine instance for a chosen c-side word.  p=0 is the standard boundary c^f (a positive
control: it must return FOUND).  p=1 is the other word permitted by prop:inflbdy, f a-edges and
(f-e) c-edges (it must return EXHAUSTED if the inflation is rigid).

Regression-tested against the hand-built (3,7) instances; see --selftest.
"""
import sys
from fractions import Fraction as F

def qd(p, q, d):
    """(p + q*sqrt D)/d in lowest terms, as the engine's 'p q d' triple."""
    from math import gcd
    g = gcd(gcd(abs(p), abs(q)), abs(d))
    if g: p, q, d = p//g, q//g, d//g
    if d < 0: p, q, d = -p, -q, -d
    return f"{p} {q} {d}"

def squarefree(D):
    """Write D = s^2 * D0 with D0 squarefree; return (D0, s).  The engine requires a squarefree
    radicand, so every surd coefficient must then be multiplied by s."""
    s = 1
    d = 2
    while d * d <= D:
        while D % (d * d) == 0:
            D //= d * d
            s *= d
        d += 1
    return D, s

def instance(e, f, word):
    a, b, c = e*f, f*f - e*e, f*f
    D, S = squarefree(4*f*f - e*e)
    L = []
    L.append(f"{D}")
    L.append(f"{a} {b} {c}")
    # alpha: cos = (2f^2-e^2)/(2f^2),  sin = e*sqrt D/(2f^2)
    L.append(f"{qd(2*f*f - e*e, 0, 2*f*f)}  {qd(0, e*S, 2*f*f)}")
    # beta:  cos = e(3f^2-e^2)/(2f^3),  sin = (f^2-e^2)sqrt D/(2f^3)
    L.append(f"{qd(e*(3*f*f - e*e), 0, 2*f**3)}  {qd(0, (f*f - e*e)*S, 2*f**3)}")
    # gamma: cos = -e/(2f),             sin = sqrt D/(2f)
    L.append(f"{qd(-e, 0, 2*f)}  {qd(0, S, 2*f)}")
    # area2 is the UNIT TILE's doubled area: a*b*sin(gamma) = e(f^2-e^2) sqrt D / 2
    L.append(qd(0, e*(f*f - e*e)*S, 2))
    L.append(f"{f*f}")
    # vertices: (0,0), (f c, 0), third
    L.append(f"{qd(0,0,1)}  {qd(0,0,1)}")
    L.append(f"{qd(f*c,0,1)}  {qd(0,0,1)}")
    # x = ((fc)^2 + (fb)^2 - (fa)^2)/(2 fc) = f*(c^2+b^2-a^2)/(2c)
    num, den = f*(c*c + b*b - a*a), 2*c
    # y = 2*Area(T_f)/(f c), with 2*Area(T_f) = f^2 * e(f^2-e^2) sqrt D / 2
    L.append(f"{qd(num,0,den)}  {qd(0, f*f*e*(f*f - e*e)*S, 2*f*c)}")
    L.append("WALKS 0 1")
    L.append(f"  {word[0]} {word[1]} {word[2]}")
    L.append("2")
    L.append(f"  0 {f} 0")
    L.append(f"  {f} 0 0")
    return "\n".join(L) + "\n"

if __name__ == "__main__":
    if "--selftest" in sys.argv:
        import os
        ok = True
        for tag, word in [("p1", None), ("p0", None)]:
            e, f = 3, 7
            w = (f, 0, f - e) if tag == "p1" else (0, 0, f)
            got = instance(e, f, w)
            ref = open(f"code/engine/inflation/inst_infl37_{tag}.txt").read()
            same = got.split() == ref.split()
            print(f"  (3,7) {tag}: {'MATCH' if same else 'MISMATCH'}")
            if not same:
                ok = False
                for i,(g,r) in enumerate(zip(got.split('\n'), ref.split('\n'))):
                    if g.split()!=r.split(): print(f"    line {i}: got {g!r}  ref {r!r}")
        sys.exit(0 if ok else 1)
    e, f, p = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    w = (f, 0, f - e) if p == 1 else (0, 0, f)
    sys.stdout.write(instance(e, f, w))
