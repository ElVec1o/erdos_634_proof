#!/usr/bin/env python3
"""Emit an exact base-beta instance file for cengine_iso, optionally seeded with a base word (P7).

Tile (a,b,c) = (ef, f^2-e^2, f^2); D = 4f^2 - e^2; at scale m the target is
(f^3 m, f^3 m, e(3f^2-e^2) m) with N = m^2 (3f^2-e^2).  A QD number is written as three integers
p q d meaning (p + q sqrt(D))/d.  Validated by reproducing private/inst/w26.txt exactly.
"""
import sys
from fractions import Fraction as F
from math import gcd


def qd(p, q, d):
    """normalise (p + q sqrt D)/d to integers"""
    g = gcd(gcd(abs(p), abs(q)), abs(d)) or 1
    if d < 0:
        p, q, d = -p, -q, -d
    return f"{p//g} {q//g} {d//g}"


def instance(e, f, m=1, baseword=None):
    a, b, c = e * f, f * f - e * e, f * f
    D = 4 * f * f - e * e
    N0 = 3 * f * f - e * e
    base, side, N = e * N0 * m, f ** 3 * m, m * m * N0
    L = []
    L.append(str(D))
    L.append(f"{a} {b} {c}")
    # corner 0 = alpha (opp a), 1 = beta (opp b), 2 = gamma (opp c); cos then sin
    ca = F(b * b + c * c - a * a, 2 * b * c); sa = (F(e, 2 * f * f), 1)          # sin a = e*sqrt(D)/(2f^2)
    cb = F(a * a + c * c - b * b, 2 * a * c); sb = (F(b, 2 * f ** 3), 1)         # sin b = b sqrt(D)/(2f^3)
    cg = F(a * a + b * b - c * c, 2 * a * b); sg = (F(1, 2 * f), 1)              # sin g = sqrt(D)/(2f)
    for cs, (sn, _) in ((ca, sa), (cb, sb), (cg, sg)):
        L.append(qd(cs.numerator, 0, cs.denominator) + "  " + qd(0, sn.numerator, sn.denominator))
    area2 = F(a * c * b, 2 * f ** 3)                                             # 2*Area = a c sin(beta); tile is fixed-size, only the target scales with m
    L.append(qd(0, area2.numerator, area2.denominator))
    L.append(str(N))
    L.append(qd(0, 0, 1) + "  " + qd(0, 0, 1))
    L.append(qd(base, 0, 1) + "  " + qd(0, 0, 1))
    hx = F(base, 2); hy = F(b * m, 2)                                            # apex (base/2, b m sqrt(D)/2)
    L.append(qd(hx.numerator, 0, hx.denominator) + "  " + qd(0, hy.numerator, hy.denominator))

    def walks(t):
        out = []
        for Q in range(t // b + 1):
            for R in range(1, (t - Q * b) // c + 1):        # gamma-trap R >= 1
                rem = t - Q * b - R * c
                if rem >= 0 and rem % a == 0:
                    out.append((rem // a, Q, R))
        return out
    wb, ws = walks(base), walks(side)
    L.append("WALKS 0 " + str(len(wb)) + " " + " ".join(f"{p} {q} {r}" for p, q, r in wb)
             + " " + str(len(ws)) + " " + " ".join(f"{p} {q} {r}" for p, q, r in ws))
    L.append("CORNERS 0 2 2" if e == 1 else "CORNERS -1 -1 -1")
    if baseword is not None:
        assert sum({0: a, 1: b, 2: c}[t] for t in baseword) == base, "base word length mismatch"
        L.append(f"BASEWORD 0 {len(baseword)} " + " ".join(map(str, baseword)))
    return "\n".join(L) + "\n"


def word_from_config(f, bp, cp):
    """base word: f+2 letters, all 'a' except the b at position bp and the c at cp (1-indexed)"""
    w = [0] * (f + 2)
    w[bp - 1] = 1
    w[cp - 1] = 2
    return w


if __name__ == '__main__':
    if sys.argv[1:2] == ['--selftest']:
        got = instance(1, 3).split('WALKS')[0].split()
        want = open(sys.argv[2]).read().split()[:len(got)]
        print("selftest:", "PASS" if got == want else "FAIL")
        if got != want:
            print(" got :", got); print(" want:", want)
        sys.exit(0 if got == want else 1)
    e, f, bp, cp = (int(x) for x in sys.argv[1:5])
    sys.stdout.write(instance(e, f, 1, word_from_config(f, bp, cp)))
