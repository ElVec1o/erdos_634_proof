#!/usr/bin/env python3
"""
Completeness of the scalene-ABC shape list for a 2pi/3 tile, derived from the VERIFIED
vertex-type enumeration (no dependence on the withdrawn Triangle Tiling V Theorem 1).

A corner of ABC is filled by tiles; its angle is  theta = P*alpha + Q*beta + R*gamma
with gamma=2pi/3, beta=pi/3-alpha  =>  theta = m*alpha + k*(pi/3),  m=P-Q, k=Q+2R,
feasible iff exists P,Q,R>=0 (>=1 tile) with those values.  ABC's three corners satisfy
sum of angles = pi  =>  sum(m_i)=0 and sum(k_i)=3.

We enumerate every feasible corner triple, keep those that are valid triangles for an
irrational alpha in (0, pi/3), and classify equilateral / isosceles / scalene.
"""
from itertools import product
from fractions import Fraction

def corner_feasible(m, k):
    """exists P,Q,R>=0, P+Q+R>=1, with P-Q=m, Q+2R=k?"""
    if k < 0:
        return False
    for Q in range(0, k+1):
        if (k - Q) % 2 != 0:
            continue
        R = (k - Q)//2
        P = Q + m
        if P >= 0 and (P+Q+R) >= 1:
            return True
    return False

# angle(theta) = m*alpha + k*pi/3.  Represent as (m, k): value = m*alpha + k/3 (in units of pi).
# For a valid triangle corner we need 0 < m*alpha + k*pi/3 < pi for the tile's actual alpha,
# but alpha varies per tile; we keep corners that are in (0,pi) for ALL alpha in (0,pi/3)
# OR depend on alpha (these are the "alpha-bearing" corners).  We enumerate structural shapes.

# Enumerate corner triples with sum(m)=0, sum(k)=3, each feasible, angle strictly in (0,pi)
# at a generic alpha in (0,pi/3).
def angle_val(m, k, alpha):
    import math
    return m*alpha + k*math.pi/3

shapes = set()
M = range(-3, 4)
for (m1,m2,m3) in product(M, repeat=3):
    if m1+m2+m3 != 0:
        continue
    for (k1,k2,k3) in product(range(0,4), repeat=3):
        if k1+k2+k3 != 3:
            continue
        corners = [(m1,k1),(m2,k2),(m3,k3)]
        if not all(corner_feasible(m,k) for (m,k) in corners):
            continue
        # check validity for a generic irrational alpha, say alpha=pi/3 * 0.31415...
        import math
        alpha = (math.pi/3)*0.3141592653589793
        angs = [angle_val(m,k,alpha) for (m,k) in corners]
        if any(a <= 1e-9 or a >= math.pi-1e-9 for a in angs):
            continue
        # canonical key: sort corner (m,k)
        key = tuple(sorted(corners))
        shapes.add(key)

def classify(corners, alpha=0.31415):
    import math
    al = (math.pi/3)*alpha
    angs = sorted(round(angle_val(m,k,al),6) for (m,k) in corners)
    # equilateral: all pi/3 ; isosceles: two equal
    n_eq = sum(1 for i in range(3) for j in range(i+1,3) if abs(angs[i]-angs[j])<1e-6)
    if all(abs(a-math.pi/3)<1e-6 for a in angs):
        return "EQUILATERAL"
    if n_eq >= 1:
        return "isosceles"
    return "SCALENE"

print("All structurally-valid ABC corner triples (m,k per corner), classified:")
scalene = []
for key in sorted(shapes):
    cls = classify(list(key))
    # describe angles symbolically: m*alpha + k*(pi/3)
    desc = ", ".join(f"{m}a+{k}p/3" for (m,k) in key)
    print(f"  [{cls:11s}]  corners (m,k)={key}   angles: {desc}")
    if cls == "SCALENE":
        scalene.append(key)

print(f"\nDistinct scalene shapes: {len(scalene)}")
# Map each scalene shape to readable angle form (alpha, and combos), using beta=pi/3-alpha:
# angle m*alpha + k*pi/3 = m*alpha + k*(alpha+beta) = (m+k)alpha + k*beta
print("\nScalene shapes in (alpha,beta) form  [m*a+k*(pi/3) = (m+k)*alpha + k*beta]:")
for key in scalene:
    parts = []
    for (m,k) in key:
        ca, cb = m+k, k
        parts.append(f"{ca}a+{cb}b")
    print(f"  {key}  ->  ({', '.join(parts)})")

print("""
Expected (Beeson TT-V Thm 8 (iii)-(vi), the genuinely scalene cases):
  F1 (alpha, alpha+beta, alpha+2beta) = (1a+0b, 1a+1b, 1a+2b)
  F2 (2alpha, 2beta, alpha+beta)      = (2a+0b, 0a+2b, 1a+1b)
  F3 (alpha, 2alpha, 3beta)           = (1a+0b, 2a+0b, 0a+3b)
  F4 (alpha, 2beta, 2alpha+beta)      = (1a+0b, 0a+2b, 2a+1b)
""")

# --- Rigorous N=19 exclusion for F1 and F2 (closed form) ---
from math import isqrt, gcd
print("="*70)
print("RIGOROUS N=19 exclusion, closed form:")
print("="*70)
print("""F1: ABC sides prop to (a, c, a+b); the two sides at the pi/3 vertex are
    a and a+b; area eqn => N0 = (a+b)/b, and integrality forces scale k in Z, so
    N = k^2*(a+b)/b with (a+b)|N (since gcd(b,a+b)=1).  N=19 prime => a+b=19 and
    b a perfect square.  Candidates b in {1,4,9,16}, a=19-b:""")
for b in [1,4,9,16]:
    a = 19-b
    s = a*a+a*b+b*b
    c = isqrt(s)
    print(f"    (a,b)=({a},{b}): gcd={gcd(a,b)}, c^2={s}, perfect square? {c*c==s}")
print("    mirror (swap a,b): a in {1,4,9,16}, b=19-a:")
for a in [1,4,9,16]:
    b = 19-a
    s = a*a+a*b+b*b
    c = isqrt(s)
    print(f"    (a,b)=({a},{b}): gcd={gcd(a,b)}, c^2={s}, perfect square? {c*c==s}")
print("    => NO valid 120-tile. F1 cannot tile N=19.  [RIGOROUS]\n")

print("""F2: ABC sides prop to (a(a+2b), b(2a+b), c^2); the two sides at the pi/3 vertex
    are a(a+2b), b(2a+b); area eqn => N0 = (a+2b)(2a+b).  So N = k^2*(a+2b)(2a+b).
    Both factors are integers >= 3 (a,b>=1), so N0 >= 9 and N0 is composite-or-prime>=11;
    19 = k^2 (a+2b)(2a+b) is impossible (k=1 needs (a+2b)(2a+b)=19 prime, but it is a
    product of two factors each >=3).  => F2 cannot tile N=19.  [RIGOROUS]""")
print("    spot check N0=(a+2b)(2a+b):",
      [( (a,b), (a+2*b)*(2*a+b)) for (a,b) in [(3,5),(5,16),(7,8)]],
      "(matches Beeson floors 143,962,506)")
