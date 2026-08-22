#!/usr/bin/env python3
"""Generate engine instances for Beeson's Table 2.

Beeson, "Tiling an Equilateral Triangle" (arXiv:1812.07014v3), Table 2:
"Tilings not ruled out by the area and coloring equations and Lemma 3".
Each row is (N, M, (a,b,c), side of ABC): an equilateral triangle of the given
side, to be cut into N copies of the triangle (a,b,c).  For most rows it is not
known whether a tiling exists; Beeson's Theorem 4 says each is decidable in
finitely many steps.

Every tile is a 60-degree triple: c^2 = a^2 + b^2 - a*b, so the angle opposite c
is exactly pi/3 and the other two angles are irrational multiples of pi
(Laczkovich's fourth family).  All the arithmetic therefore lives in Q(sqrt 3),
i.e. D = 3, and the side lengths are integers, so these instances run on
cengine_iso with every prune active.

Writes one instance per row, named b_<N>_<a>_<b>_<c>.txt.
"""
import math
from fractions import Fraction as F

TABLE2 = [
    # (N, tile (a,b,c), side of ABC).  Rows recovered from the v3 HTML; the table has 55 lines
    # in total and the remainder are elided there, so this is a prefix, sorted by N.
    (54,   (3, 8, 7),           36),
    (96,   (3, 8, 7),           48),
    (105,  (5, 21, 19),        105),
    (105,  (7, 15, 13),        105),
    (150,  (3, 8, 7),           60),
    (216,  (3, 8, 7),           72),
    (220,  (16, 55, 49),       440),
    (270,  (8, 15, 13),        180),
    (280,  (7, 40, 37),        280),
    (294,  (3, 8, 7),           84),
    (374,  (88, 153, 133),    2244),
    (384,  (3, 8, 7),           96),
    (385,  (11, 35, 31),       385),
    (399,  (57, 112, 97),     1596),
    (1360, (17, 80, 73),      1360),
    (1377, (17, 225, 217),    2295),
    (1394, (369, 544, 481),  16728),
    (1404, (13, 48, 43),       936),
    (1440, (5, 8, 7),          240),   # Herdt exhibited a tiling here: positive control
]


def qd(p: F, q: F) -> str:
    """Render p + q*sqrt(3) as the engine's 'p q d' triple over a common denominator."""
    d = 1
    for x in (p, q):
        d = d * x.denominator // math.gcd(d, x.denominator)
    return f"{p.numerator * d // p.denominator} {q.numerator * d // q.denominator} {d}"


def sin_of(cos_v: F) -> F:
    """sin from cos, given that sin = r*sqrt(3) for a rational r (true for 60-degree triples)."""
    r2 = (1 - cos_v * cos_v) / 3
    rn, rd = math.isqrt(r2.numerator), math.isqrt(r2.denominator)
    assert rn * rn == r2.numerator and rd * rd == r2.denominator, cos_v
    return F(rn, rd)


def build(N, tile, S):
    a, b, c = tile
    assert c * c == a * a + b * b - a * b, f"{tile} is not a 60-degree triple"

    def cos_opp(opp, s1, s2):
        return F(s1 * s1 + s2 * s2 - opp * opp, 2 * s1 * s2)

    cA, cB, cC = cos_opp(a, b, c), cos_opp(b, a, c), cos_opp(c, a, b)
    sA, sB, sC = sin_of(cA), sin_of(cB), sin_of(cC)
    area2 = F(a * b, 1) * sC                      # 2*area(tile) = a*b*sin C
    tgt2 = F(S * S, 2)                            # 2*area(equilateral) = S^2*sqrt3/2
    assert tgt2 / area2 == N, f"N={N}: area ratio is {tgt2 / area2}"

    return "\n".join([
        "3",
        f"{a} {b} {c}",
        f"{qd(cA, F(0))}  {qd(F(0), sA)}",
        f"{qd(cB, F(0))}  {qd(F(0), sB)}",
        f"{qd(cC, F(0))}  {qd(F(0), sC)}",
        f"{qd(F(0), area2)}",
        f"{N}",
        "0 0 1  0 0 1",
        f"{S} 0 1  0 0 1",
        f"{qd(F(S, 2), F(0))}  {qd(F(0), F(S, 2))}",
    ]) + "\n"


if __name__ == "__main__":
    for N, tile, S in TABLE2:
        a, b, c = tile
        name = f"b_{N}_{a}_{b}_{c}.txt"
        with open(name, "w") as fh:
            fh.write(build(N, tile, S))
        print(f"{name}: equilateral side {S}, {N} copies of {tile}")
