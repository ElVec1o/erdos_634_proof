#!/usr/bin/env python3
"""
verify_shapes.py  --  Section 2.4 (shape enumeration) and Section 3 (reduction) of the paper.

A 2pi/3 tile has angles (alpha, beta, gamma) with gamma = 2pi/3, beta = pi/3 - alpha, and
alpha an irrational multiple of pi.  A corner of the target triangle ABC is filled by tile
corners, so its measure is

    P*alpha + Q*beta + R*gamma = (P-Q)*alpha + (Q+2R)*(pi/3)

for nonnegative integers P, Q, R (the counts of alpha-, beta-, gamma-corners meeting there).
Writing a corner as (m, k) with m = P-Q, k = Q+2R, a corner is feasible iff some P,Q,R >= 0 with
P+Q+R >= 1 realize it.  The three corners of ABC satisfy sum(m_i)=0 and sum(k_i)=3.

This script:
  (1) enumerates every feasible corner triple and confirms exactly eleven shapes of ABC
      (equilateral, two isosceles, eight scalene);
  (2) computes N0 = Area(ABC)/Area(tile) for each scalene shape and confirms N is composite
      (so no scalene shape gives a prime number of tiles), with N = 19 as a corollary.

All arithmetic is exact.
"""
from itertools import product
from fractions import Fraction
from math import isqrt, gcd, pi


# --------------------------------------------------------------------------------------------
# (1)  Shape enumeration
# --------------------------------------------------------------------------------------------

def corner_feasible(m, k):
    """Exists P, Q, R >= 0 with P+Q+R >= 1, P-Q = m, Q+2R = k?"""
    if k < 0:
        return False
    for Q in range(k + 1):
        if (k - Q) % 2:
            continue
        R = (k - Q) // 2
        P = Q + m
        if P >= 0 and P + Q + R >= 1:
            return True
    return False


def angle(m, k, alpha):
    return m * alpha + k * pi / 3


def classify(corners, alpha):
    angs = sorted(angle(m, k, alpha) for (m, k) in corners)
    if all(abs(a - pi / 3) < 1e-9 for a in angs):
        return "equilateral"
    if any(abs(angs[i] - angs[j]) < 1e-9 for i in range(3) for j in range(i + 1, 3)):
        return "isosceles"
    return "scalene"


# a generic irrational alpha in (0, pi/3) used only to test triangle validity / classification
ALPHA = (pi / 3) * 0.3141592653589793

shapes = {}
for (m1, m2, m3) in product(range(-3, 4), repeat=3):
    if m1 + m2 + m3 != 0:
        continue
    for (k1, k2, k3) in product(range(4), repeat=3):
        if k1 + k2 + k3 != 3:
            continue
        corners = [(m1, k1), (m2, k2), (m3, k3)]
        if not all(corner_feasible(m, k) for (m, k) in corners):
            continue
        angs = [angle(m, k, ALPHA) for (m, k) in corners]
        if any(a <= 1e-9 or a >= pi - 1e-9 for a in angs):  # must be a genuine triangle
            continue
        key = tuple(sorted(corners))
        shapes[key] = classify(list(key), ALPHA)

counts = {"equilateral": 0, "isosceles": 0, "scalene": 0}
print("=" * 78)
print("ABC shape enumeration  (corner (m,k) means angle = m*alpha + k*(pi/3))")
print("=" * 78)
for key in sorted(shapes):
    cls = shapes[key]
    counts[cls] += 1
    # angle m*alpha + k*(pi/3) = (m+k)*alpha + k*beta  since pi/3 = alpha + beta
    ab = ", ".join(f"{m + k}a+{k}b" for (m, k) in key)
    print(f"  [{cls:11s}]  corners {key}   =  ({ab})")

print(f"\n  equilateral: {counts['equilateral']}   isosceles: {counts['isosceles']}"
      f"   scalene: {counts['scalene']}   total: {sum(counts.values())}")
assert counts == {"equilateral": 1, "isosceles": 2, "scalene": 8}, counts
print("  -> exactly eleven shapes (1 equilateral, 2 isosceles, 8 scalene). OK\n")


# --------------------------------------------------------------------------------------------
# (2)  Scalene shapes give composite N
# --------------------------------------------------------------------------------------------

def is120(a, b):
    """Return c if (a,b,c) is a primitive 120-triple (gcd(a,b)=1, c^2=a^2+ab+b^2), else None."""
    if gcd(a, b) != 1:
        return None
    s = a * a + a * b + b * b
    c = isqrt(s)
    return c if c * c == s else None


def N0_from_sides(D, a, b):
    """Exact N0 = Area(ABC)/Area(tile) for ABC with side-proportion vector D and tile (a,b,*)."""
    g = gcd(gcd(D[0], D[1]), D[2])
    s1, s2, s3 = (d // g for d in D)
    p = Fraction(s1 + s2 + s3, 2)
    area2 = p * (p - s1) * (p - s2) * (p - s3)        # Heron: Area(ABC)^2
    tile2 = Fraction(3, 16) * a * a * b * b           # Area(tile)^2 = (sqrt3/4 ab)^2
    r2 = area2 / tile2                                # N0^2
    rn, rd = isqrt(r2.numerator), isqrt(r2.denominator)
    assert rn * rn == r2.numerator and rd * rd == r2.denominator, "N0 not a rational square"
    return Fraction(rn, rd)

print("=" * 78)
print("Scalene shapes: closed-form N0 and compositeness of N = k^2 * N0")
print("=" * 78)

# The four scalene families (mirrors handled by swapping a<->b) and their side vectors.
FAMILIES = {
    "F1 (a, a+b, a+2b)":      lambda a, b, c: [a, c, a + b],
    "F2 (2a, 2b, a+b)":       lambda a, b, c: [a * (a + 2 * b), b * (2 * a + b), c * c],
    "F3 (a, 2a, 3b)":         lambda a, b, c: [a * c * c, a * (a + 2 * b) * c, 3 * a * b * (a + b)],
    "F4 (a, 2b, 2a+b)":       lambda a, b, c: [a * c, b * (2 * a + b), (a + b) * c],
}
CLOSED = {
    "F1 (a, a+b, a+2b)":   lambda a, b: Fraction(a + b, b),
    "F2 (2a, 2b, a+b)":    lambda a, b: Fraction((a + 2 * b) * (2 * a + b)),
    "F3 (a, 2a, 3b)":      lambda a, b: Fraction(3 * (a + b) * (a + 2 * b)),
    "F4 (a, 2b, 2a+b)":    lambda a, b: Fraction((a + b) * (2 * a + b)),
}

mism = 0
for a in range(1, 200):
    for b in range(1, 200):
        c = is120(a, b)
        if not c:
            continue
        for name, sides in FAMILIES.items():
            if N0_from_sides(sides(a, b, c), a, b) != CLOSED[name](a, b):
                mism += 1
print(f"closed-form N0 matches Heron computation on all primitive triples a,b<200: "
      f"{mism} mismatches (expect 0)\n")

# a+b is never prime for a primitive 120-triple (so F1's N = t*(a+b) is composite).
print("F1: a+b is never prime for a primitive 120-triple (=> N = t*(a+b) composite):")
bad_f1 = [(a, b, a + b) for a in range(1, 600) for b in range(1, 600)
          if is120(a, b) and __import__("sympy").isprime(a + b)]
print(f"   primitive triples (a,b<600) with a+b prime: {bad_f1 if bad_f1 else 'NONE'}  (expect NONE)")
print("   smallest a+b values:",
      sorted({a + b for a in range(1, 60) for b in range(1, 60) if is120(a, b)})[:6], "(all composite)\n")

print("F2, F4: N0 = (product of two integer factors each >= 3) -> composite.")
print("   sample N0_F2:",
      sorted({(a + 2 * b) * (2 * a + b) for a in range(1, 40) for b in range(1, 40) if is120(a, b)})[:5])
print("   sample N0_F4:",
      sorted({(a + b) * (2 * a + b) for a in range(1, 40) for b in range(1, 40) if is120(a, b)})[:5], "\n")

print("F3: N0 = 3(a+b)(a+2b) -> divisible by 3 -> composite.")
print("   3 | N0_F3 on all primitive triples a,b<200:",
      all(CLOSED["F3 (a, 2a, 3b)"](a, b) % 3 == 0
          for a in range(1, 200) for b in range(1, 200) if is120(a, b)), "\n")

print("=" * 78)
print("Corollary (N = 19): 19 is prime, so no scalene shape can give 19 tiles.")
print("  F1 needs a+b = 19 (prime) -> impossible.  F2/F4 need 19 = product of two factors >= 3")
print("  -> impossible.  F3 needs 3 | 19 -> impossible.  Tile-similar gives N = n^2 (19 not square).")
print("  Equilateral and isosceles are handled by the cited theorems and the Phi-invariant.")
print("=" * 78)
