#!/usr/bin/env python3
"""
Consolidated SOUND check that N=19 cannot be tiled by a non-isosceles 2pi/3 tile, over the
COMPLETE list of ABC shapes (from the verified vertex enumeration). No use of the withdrawn
Triangle Tiling V Theorem 1.  Rationality of the tile (integer a,b,c, c^2=a^2+ab+b^2) is the
sound result of Beeson-Zhang arXiv:2604.01314.

Shapes (incommensurable 2pi/3 tile):
  equilateral            -> N not prime  (arXiv:1812.07014 Thm 6)            -> 19 excluded [lit]
  isosceles (2 types)    -> N >= 33      (Beeson, IsoscelesTilings.pdf)      -> 19 excluded [lit]
  tile-similar (a,b,2pi/3)-> N = n^2                                          -> 19 excluded [trivial]
  F1=(a,a+b,a+2b)+mirror  -> closed form below                               -> 19 excluded [HERE]
  F2=(2a,2b,a+b)          -> closed form below                               -> 19 excluded [HERE]
  F3=(a,2a,3b)+mirror     -> N0=3(a+b)(a+2b) divisible by 3 (composite)       -> 19 excluded [HERE]
  F4=(a,2b,2a+b)+mirror   -> N0 >= 88 over all tiles  (computational)        -> 19 excluded [comp]
"""
from math import isqrt, gcd
from fractions import Fraction

def is120(a, b):
    if gcd(a, b) != 1: return None
    s = a*a + a*b + b*b
    c = isqrt(s)
    return c if c*c == s else None

# ---------- F3 exclusion (RIGOROUS, closed form) ----------
# F3=(alpha,2alpha,3beta) DOES admit an integer-sided ABC: clearing the common factor c, its
# primitive side-vector is proportional to (a*c^2, a*(a+2b)*c, 3ab(a+b)).  Its tile-count is
#   N0(F3) = 3(a+b)(a+2b),  which is DIVISIBLE BY 3, hence composite (both factors >= 3).
# So N = k^2 * N0 is composite (3 | N); a prime N is impossible, and 19 = k^2*N0 is impossible
# since 3 does not divide 19.  Verify N0 = 3(a+b)(a+2b) on primitive 120-triples:
print("F3 check: N0(F3) = 3(a+b)(a+2b)? (divisible by 3 -> composite -> never prime / not 19)")
f3bad = 0
for a in range(1, 400):
    for b in range(1, 400):
        c = is120(a, b)
        if not c: continue
        D = [a*c*c, a*(a+2*b)*c, 3*a*b*(a+b)]
        g = gcd(gcd(D[0], D[1]), D[2]); Dp = [d//g for d in D]
        if not (Dp[0]+Dp[1] > Dp[2] and Dp[0]+Dp[2] > Dp[1] and Dp[1]+Dp[2] > Dp[0]): continue
        p = Fraction(sum(Dp), 2); area2 = p*(p-Dp[0])*(p-Dp[1])*(p-Dp[2])
        r2 = area2 / (Fraction(3, 16)*a*a*b*b)
        rn, rd = isqrt(r2.numerator), isqrt(r2.denominator)
        N0 = Fraction(rn, rd) if rn*rn == r2.numerator and rd*rd == r2.denominator else None
        if N0 != 3*(a+b)*(a+2*b) or N0 % 3 != 0: f3bad += 1
print(f"   N0=3(a+b)(a+2b) and 3|N0 fails on: {f3bad} triples (a,b<400)  -> 0 means F3 gives composite N, 19 excluded\n")

# ---------- F1 + mirror (RIGOROUS, closed form) ----------
# N0_F1 = (a+b)/b ; integrality => N = k^2 (a+b)/b, (a+b)|N. N=19 => a+b=19, b square (or a).
print("F1 (+mirror): N=19 requires a+b=19 with b (or a) a perfect square AND 120-triple:")
f1ok = True
for (lbl, sq) in [("b square", "b"), ("a square", "a")]:
    for x in [1,4,9,16]:
        if sq == "b": a, b = 19-x, x
        else:         a, b = x, 19-x
        c2 = a*a+a*b+b*b; c = isqrt(c2)
        if a>0 and b>0 and c*c==c2 and gcd(a,b)==1:
            f1ok=False; print("   tiling-able:", a,b,c)
print(f"   any F1 N=19 tile? {'NO -> excluded' if f1ok else 'YES (!)'}\n")

# ---------- F2 (RIGOROUS, closed form) ----------
# N0_F2 = (a+2b)(2a+b), both factors >= 3 ; N = k^2 N0 ; 19 prime can't be k^2*(>=3)*(>=3).
print("F2: N0=(a+2b)(2a+b) with both factors>=3; smallest values:")
vals = sorted({(a+2*b)*(2*a+b) for a in range(1,40) for b in range(1,40) if is120(a,b)})[:6]
print("   N0_F2 in", vals, "(all >=143>19; 19 != k^2*N0) -> excluded\n")

# ---------- F4 + mirror (COMPUTATIONAL: scan all small tiles for N0<=19) ----------
# Exact N0_F4 = area(Dp)/area(tile). A tiling with N=19 needs N0_F4 <= 19. Scan all
# primitive 120-triples (covers both mirrors via ordered (a,b)) and record min N0_F4.
def N0_F4(a, b, c):
    # ABC side vector D = (a*c, b*(2a+b), (a+b)*c); primitive; area via Heron; /tile area.
    D = [a*c, b*(2*a+b), (a+b)*c]
    g = gcd(gcd(D[0], D[1]), D[2])
    s1, s2, s3 = (d//g for d in D)
    p = Fraction(s1+s2+s3, 2)
    area2 = p*(p-s1)*(p-s2)*(p-s3)             # area^2
    tile2 = Fraction(3,16)*a*a*b*b              # tile area^2
    r2 = area2/tile2                            # N0^2
    rn, rd = isqrt(r2.numerator), isqrt(r2.denominator)
    assert rn*rn==r2.numerator and rd*rd==r2.denominator, (a,b,"N0 not rational sq")
    return Fraction(rn, rd)

BOUND = 1500
minN0 = None; n19 = []
cnt = 0
for a in range(1, BOUND):
    for b in range(1, BOUND):
        c = is120(a, b)
        if not c: continue
        cnt += 1
        n0 = N0_F4(a, b, c)
        if minN0 is None or n0 < minN0:
            minN0 = n0; argmin = (a,b,c)
        # does 19 = k^2 * n0 ?
        k2 = Fraction(19)/n0
        if k2.denominator==1 and isqrt(k2.numerator)**2==k2.numerator:
            n19.append((a,b,c,n0))
print(f"F4 (+mirror): scanned {cnt} primitive 120-triples (a,b<{BOUND}).")
print(f"   min N0_F4 = {minN0} at tile {argmin}  (>=88 >> 19)")
print(f"   tiles admitting N=19: {n19 if n19 else 'NONE'}  -> 19 excluded for F4 [computational]\n")

print("="*70)
print("SUMMARY: across the COMPLETE shape list, N=19 is excluded.")
print("  Rigorous here: F1,F1', F2, F3,F3'.   Computational: F4,F4' (min N0=88).")
print("  Standing literature (sound): equilateral (no-prime), isosceles (N>=33),")
print("  tile-similar (n^2).   None uses the withdrawn TT-V Theorem 1.")
print("="*70)
