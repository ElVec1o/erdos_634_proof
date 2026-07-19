#!/usr/bin/env python3
"""
Symbolic verification of the vertex-type enumeration and area equation for the
(alpha, alpha+beta, alpha+2beta) target triangle of Erdos #634, Section 4 of the
handover.

Setup: tile angles (alpha, beta, gamma) with gamma = 2*pi/3, hence alpha + beta
       = pi/3.  alpha is NOT a rational multiple of pi (the interesting case).
       ABC has corner angles alpha (P1), pi/3 = alpha+beta (P2), 2pi/3 - alpha =
       alpha+2beta (P3).

A vertex where tiles meet contributes some number of alpha-, beta-, gamma-corners.
Write the type as (P, Q, R).  The angle sum is

    P*alpha + Q*beta + R*gamma
  = P*alpha + Q*(pi/3 - alpha) + R*(2pi/3)
  = (P - Q)*alpha + (Q + 2R)*pi/3.

Because alpha is irrational over pi, for the sum to equal a target of the form
m*alpha + (k/3)*pi we need  P - Q = m  AND  Q + 2R = k.

We brute-force all non-negative integer (P,Q,R) up to a generous bound and
collect the feasible types for each target, then compare against the handover's
hand-derived tables.
"""

from sympy import Rational, pi, symbols, sin, simplify, nsimplify
from itertools import product

BOUND = 12  # generous; real vertices have small valence

def feasible(m, k):
    """All (P,Q,R) >= 0 with P-Q = m and Q+2R = k, P+Q+R >= 1."""
    out = []
    for P, Q, R in product(range(BOUND + 1), repeat=3):
        if P + Q + R == 0:
            continue
        if (P - Q) == m and (Q + 2 * R) == k:
            out.append((P, Q, R))
    return out

# Targets.  Each is (name, alpha-coeff m, pi/3-coeff k, expected set).
# Corner angles, expressed as m*alpha + (k/3)*pi:
#   P1 = alpha                 -> m=1, k=0
#   P2 = pi/3 = alpha+beta     -> m=0, k=1
#   P3 = 2pi/3 - alpha         -> m=-1, k=2
#   boundary (pi)              -> m=0, k=3
#   interior (2pi)             -> m=0, k=6
TARGETS = [
    ("P1 corner (angle alpha)",        1,  0, {(1, 0, 0)}),
    ("P2 corner (angle pi/3)",         0,  1, {(1, 1, 0)}),
    ("P3 corner (angle 2pi/3-alpha)", -1,  2, {(1, 2, 0)}),
    ("boundary point (angle pi)",      0,  3, {(3, 3, 0), (1, 1, 1)}),
    ("interior point (angle 2pi)",     0,  6, {(6, 6, 0), (4, 4, 1), (2, 2, 2), (0, 0, 3)}),
]

print("=" * 72)
print("VERTEX-TYPE ENUMERATION  (alpha, alpha+beta, alpha+2beta), gamma=2pi/3")
print("=" * 72)
all_ok = True
for name, m, k, expected in TARGETS:
    got = set(feasible(m, k))
    ok = got == expected
    all_ok &= ok
    print(f"\n{name}:  alpha-coeff={m}, (pi/3)-coeff={k}")
    print(f"  computed : {sorted(got)}")
    print(f"  handover : {sorted(expected)}")
    print(f"  MATCH    : {ok}")

print("\n" + "=" * 72)
print(f"ALL VERTEX TYPES MATCH HANDOVER: {all_ok}")
print("=" * 72)

# ---------------------------------------------------------------------------
# Area equation:  N * a * b = X * Z
# ABC angle at P2 is pi/3, between sides X and Z.
# tile angle gamma = 2pi/3, between sides a and b.
# Area(ABC) = 1/2 X Z sin(pi/3);  Area(tile) = 1/2 a b sin(2pi/3).
# N * Area(tile) = Area(ABC).
# ---------------------------------------------------------------------------
print("\nAREA EQUATION CHECK")
s_pi3 = sin(pi / 3)
s_2pi3 = sin(2 * pi / 3)
print(f"  sin(pi/3)  = {s_pi3}")
print(f"  sin(2pi/3) = {s_2pi3}")
print(f"  sin(pi/3) == sin(2pi/3) : {simplify(s_pi3 - s_2pi3) == 0}")
# Symbolic: N*(1/2 a b sin2pi3) = 1/2 X Z sinpi3  ->  N a b = X Z
N, a, b, X, Z = symbols("N a b X Z", positive=True)
lhs = N * (Rational(1, 2) * a * b * s_2pi3)
rhs = Rational(1, 2) * X * Z * s_pi3
# divide out the common 1/2 sin(pi/3):
reduced = simplify(lhs / (Rational(1, 2) * s_pi3) - rhs / (Rational(1, 2) * s_pi3))
print(f"  N*a*b - X*Z  (after dividing common factor) = {simplify(N*a*b - X*Z)}  (should reduce to the identity N a b = X Z)")
print(f"  derivation consistent: {simplify(lhs - rhs) == simplify((N*a*b - X*Z) * Rational(1,2) * s_pi3)}")

# ---------------------------------------------------------------------------
# The "stall": N | X*Z does NOT force N|X and N|Z when N is prime.
# (Contrast equilateral case X = Z: then N | X^2, and N prime => N | X.)
# Show a concrete counterexample to "N prime and N|XZ => N|X and N|Z".
# ---------------------------------------------------------------------------
print("\nSTALL CHECK: does N prime, N | X*Z force N|X AND N|Z?")
Np = 19
# pick X*Z divisible by 19 but split: X=19, Z=1 -> 19|X not Z ; or X=38,Z=... trivial.
# The real point: N a b = X Z with X != Z gives no symmetric square, so the
# equilateral closing step does not transfer.  Demonstrate that 19 | XZ has
# solutions with 19 dividing exactly one factor:
examples = [(19, 7), (7, 19), (38, 5)]
for Xv, Zv in examples:
    prod = Xv * Zv
    print(f"  X={Xv}, Z={Zv}: XZ={prod}, 19|XZ={prod % 19 == 0}, 19|X={Xv % 19 == 0}, 19|Z={Zv % 19 == 0}")
print("  => N|XZ alone does not pin a side; equilateral X=Z square-trick does NOT transfer. Confirmed.")
