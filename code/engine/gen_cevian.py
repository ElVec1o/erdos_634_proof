#!/usr/bin/env python3
"""
gen_cevian.py -- engine instances for the cevian family (scalene 3a+2b=pi shape).

Member (e,f), gcd(e,f)=1, e<f, multiplier m >= 1:
  tile (a,b,c) = (ef, f^2-e^2, f^2),
  target angles (alpha+beta, beta, 2alpha) at the vertices below,
  target sides m*(f(f^2-e^2), e(2f^2-e^2), f^3),  N = m^2 (2f^2 - e^2).

Layout (verified byte-for-byte against the three existing instances, --selftest):
  D_red                                    squarefree part of 4f^2 - e^2
  a b c
  cos sin pairs for alpha, beta, gamma     each fraction reduced; sin coefficient of sqrt(D_red)
  0 q r                                    2*area(tile) = (q/r) sqrt(D_red)
  N
  three vertices                           (0,0), (m e(2f^2-e^2), 0),
                                           apex (m e(f^2-e^2)/2, (m(f^2-e^2)k/2) sqrt(D_red))
where 4f^2 - e^2 = k^2 D_red.

Self-checks per instance: the three corner angles match (alpha+beta, beta, 2alpha) by exact
law-of-cosines, and 2*area(target) = N * area2.

Usage:  gen_cevian.py e f m [out.txt]      |      gen_cevian.py --selftest
"""
import sys
from fractions import Fraction as F
from math import gcd, isqrt


def squarefree_split(D):
    """D = k^2 * D_red with D_red squarefree; returns (k, D_red)."""
    k = 1
    d = 2
    while d * d <= D:
        while D % (d * d) == 0:
            D //= d * d
            k *= d
        d += 1
    return k, D


def frac_pair(x):
    """Fraction -> 'p 0 r' (rational) storage."""
    return f"{x.numerator} 0 {x.denominator}"


def sqrt_pair(t):
    """coefficient t of sqrt(D_red) -> '0 t u' storage."""
    return f"0 {t.numerator} {t.denominator}"


def build(e, f, m):
    assert 1 <= e < f and gcd(e, f) == 1 and m >= 1
    a, b, c = e * f, f * f - e * e, f * f
    D = 4 * f * f - e * e
    k, Dr = squarefree_split(D)
    N = m * m * (2 * f * f - e * e)

    cosA, sinA = F(2 * f * f - e * e, 2 * f * f), F(e * k, 2 * f * f)
    cosB, sinB = F(e * (3 * f * f - e * e), 2 * f ** 3), F(b * k, 2 * f ** 3)
    cosG, sinG = F(-e, 2 * f), F(k, 2 * f)
    area2 = F(e * b * k, 2)                       # 2*area(tile) = area2 * sqrt(Dr)

    Vx = m * e * (2 * f * f - e * e)              # base vertex
    apex_x, apex_y = F(m * e * b, 2), F(m * b * k, 2)

    # ---- self-checks (exact) ----
    # tile angle identities: law of cosines on (a,b,c)
    assert cosA == F(b * b + c * c - a * a, 2 * b * c)
    assert cosB == F(a * a + c * c - b * b, 2 * a * c)
    assert cosG == F(a * a + b * b - c * c, 2 * a * b)
    for cs, sn in ((cosA, sinA), (cosB, sinB), (cosG, sinG)):
        assert cs * cs + Dr * sn * sn == 1        # cos^2 + sin^2 = 1
    # target sides from the vertices: (0,0), (Vx,0), (apex_x, apex_y sqrt(Dr))
    s_base = F(Vx)
    s_left2 = apex_x ** 2 + Dr * apex_y ** 2
    s_right2 = (apex_x - Vx) ** 2 + Dr * apex_y ** 2
    assert s_base == m * e * (2 * f * f - e * e)
    assert s_left2 == (m * f * b) ** 2            # side m f(f^2-e^2)
    assert s_right2 == F(m * f ** 3) ** 2         # side m f^3
    # corner angles: origin = alpha+beta (cos = e/2f); base vertex = beta; apex = 2alpha
    L, R = m * f * b, m * f ** 3
    assert F(apex_x, 1) / L == F(e, 2 * f)                       # cos(alpha+beta)
    assert F(Vx * (Vx - apex_x) - 0, 1) / (s_base * R) == cosB  # cos(beta) at base vertex
    cos2A = 2 * cosA * cosA - 1
    assert (apex_x * (apex_x - Vx) + Dr * apex_y * apex_y) / (L * R) == cos2A
    # area: 2*area(target) = base * height = Vx * apex_y * sqrt(Dr) must equal N * area2
    assert F(Vx) * apex_y == N * area2

    lines = [
        str(Dr),
        f"{a} {b} {c}",
        f"{frac_pair(cosA)}  {sqrt_pair(sinA)}",
        f"{frac_pair(cosB)}  {sqrt_pair(sinB)}",
        f"{frac_pair(cosG)}  {sqrt_pair(sinG)}",
        f"0 {area2.numerator} {area2.denominator}",
        str(N),
        "0 0 1  0 0 1",
        f"{Vx} 0 1  0 0 1",
        f"{frac_pair(apex_x)}  {sqrt_pair(apex_y)}",
    ]
    return "\n".join(lines) + "\n"


def selftest():
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    repo = os.path.dirname(os.path.dirname(here))
    refs = [((1, 2, 3), "cev63.txt"), ((1, 2, 2), "cev28.txt"), ((1, 3, 2), "cev68.txt")]
    for (e, f, m), fn in refs:
        path = os.path.join(repo, "private", "inst", fn)
        want = open(path).read()
        got = build(e, f, m)
        assert got == want, f"regression MISMATCH for {fn} at (e,f,m)=({e},{f},{m})"
        print(f"  regression MATCH: {fn}  <-  (e,f,m)=({e},{f},{m})")
    print("selftest OK")


if __name__ == "__main__":
    if sys.argv[1:2] == ["--selftest"]:
        selftest()
    else:
        e, f, m = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
        text = build(e, f, m)
        if len(sys.argv) > 4:
            open(sys.argv[4], "w").write(text)
            print(f"wrote {sys.argv[4]}  (N = {m*m*(2*f*f-e*e)})")
        else:
            sys.stdout.write(text)
