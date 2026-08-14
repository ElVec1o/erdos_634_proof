#!/usr/bin/env python3
"""Exact-rational verification of V1, V2 and the T-vertex forcing.

Setting (Erdős #634, base-β): tile (a,b,c) = (ef, f²−e², f²), chart (x, ŷ) with
y = ŷ·√D, D = 4f²−e².  Δ_k: A = α-corner at origin, B-side (length kb) along
w = (1,0), c-side (length kc) along u = ((2f²−e²)/(2f²), e/(2f²)) (unit).
Vertices A = 0, C = kb·w, B = kc·u.  Slot Y_i = (i+1)b·w; rogue c-edge from Y_i
along the ray toward X_i = ib·w + c·u.

V1: the chord direction (c·u − b·w)/a is parallel to the a-side BC, and the
    barycentric sum s+t is constant (= (i+1)/k) along the whole ray from Y_i.
V2: the maximal length available inside Δ_k from Y_i along the ray is exactly
    L_max = (i+1)·a, with exit through the c-side AB at s = 0.
    Consistency: c ≤ (i+1)a ⟺ (i+1)e ≥ f.
T:  Δ = c−a = f(f−e) satisfies b−Δ = e(f−e) > 0, c−Δ = a > 0, and
    n·a = Δ has a solution n ∈ ℕ iff e = 1.

Everything is exact (fractions.Fraction); a length² in the chart is p² + q²·D.
Also verified: which side of the chord is which (row side contains A and the
−w base direction; rogue side contains B and +w), needed for the boundary-case
angle rule at the chord's exit through AB.
"""
from fractions import Fraction as Fr
from math import gcd
import sys

def chart(e, f, k):
    a, b, c = e*f, f*f - e*e, f*f
    D = 4*f*f - e*e
    w = (Fr(1), Fr(0))
    u = (Fr(2*f*f - e*e, 2*f*f), Fr(e, 2*f*f))
    A = (Fr(0), Fr(0))
    C = (Fr(k*b), Fr(0))
    B = (Fr(k*c) * u[0], Fr(k*c) * u[1])
    return a, b, c, D, w, u, A, B, C

def len2(v, D):
    return v[0]*v[0] + v[1]*v[1]*D

def cross(v1, v2):
    # Euclidean cross = sqrt(D) * chart cross; sign identical (D>0)
    return v1[0]*v2[1] - v1[1]*v2[0]

def bary(P, B, C):
    # P = s*C + t*B (A at origin); solve the 2x2 rational system
    det = C[0]*B[1] - C[1]*B[0]
    assert det != 0
    s = (P[0]*B[1] - P[1]*B[0]) / det
    t = (C[0]*P[1] - C[1]*P[0]) / det
    return s, t

def coprime_pairs(fmax):
    for f in range(2, fmax + 1):
        for e in range(1, f):
            if gcd(e, f) == 1:
                yield e, f

checks = 0
fails = []

for e, f in coprime_pairs(12):
    for k in range(2, f + 1):
        a, b, c, D, w, u, A, B, C = chart(e, f, k)
        # unit check on u
        assert len2(u, D) == 1
        v = (Fr(c)*u[0] - Fr(b), Fr(c)*u[1])          # c·u − b·w, the chord vector
        # |v| = a
        assert len2(v, D) == a*a, (e, f)
        # V1 part 1: v parallel (antiparallel) to BC = C − B, exactly BC = −k·v
        BC = (C[0]-B[0], C[1]-B[1])
        assert cross(v, BC) == 0
        assert BC[0] == -k*v[0] and BC[1] == -k*v[1]
        checks += 1
        for i in range(0, k - 1):                      # slots i = 0..k−2
            Y = (Fr((i+1)*b), Fr(0))
            X = (Fr(i*b) + Fr(c)*u[0], Fr(c)*u[1])
            # X − Y = v
            assert (X[0]-Y[0], X[1]-Y[1]) == v
            # V1 part 2: s+t constant along the ray, = (i+1)/k;  s(L), t(L) formulas
            for L in [Fr(1), Fr(a), Fr(c), Fr(a+c), Fr(3*c, 2), Fr((i+1)*a), Fr(7, 3)]:
                P = (Y[0] + (L/a)*v[0], Y[1] + (L/a)*v[1])
                s, t = bary(P, B, C)
                if s + t != Fr(i+1, k): fails.append(("V1 s+t", e, f, k, i, L))
                if s != (Fr(i+1) - L/a)/k: fails.append(("V1 s", e, f, k, i, L))
                if t != L/(Fr(a)*k): fails.append(("V1 t", e, f, k, i, L))
                checks += 1
            # at L = c: the RogueContainment formulas
            s, t = bary((Y[0] + Fr(c,a)*v[0], Y[1] + Fr(c,a)*v[1]), B, C)
            assert s == Fr((i+1)*e - f, e*k) and t == Fr(f, e*k)
            # V2: containment along the ray ⟺ 0 ≤ L ≤ (i+1)a  (t ≥ 0 and s+t < 1 automatic)
            assert Fr(i+1, k) < 1
            Lmax = Fr((i+1)*a)
            sM, tM = bary((Y[0] + (Lmax/a)*v[0], Y[1] + (Lmax/a)*v[1]), B, C)
            if sM != 0: fails.append(("V2 exit s", e, f, k, i))
            # exit point on segment AB: P = t·B with 0 < t < 1
            if not (0 < tM < 1): fails.append(("V2 exit on AB", e, f, k, i))
            # strictly inside for L < Lmax, strictly outside for L > Lmax
            for Ltest, inside in [(Lmax - Fr(1,7), True), (Lmax + Fr(1,7), False)]:
                P = (Y[0] + (Ltest/a)*v[0], Y[1] + (Ltest/a)*v[1])
                s2, t2 = bary(P, B, C)
                ok = (s2 >= 0 and t2 >= 0 and s2 + t2 <= 1)
                if ok != inside: fails.append(("V2 side", e, f, k, i, Ltest))
            # V2 consistency: c ≤ (i+1)a ⟺ (i+1)e ≥ f
            assert (c <= (i+1)*a) == ((i+1)*e >= f)
            checks += 2
            # side bookkeeping: row side (sign of cross(v, ·) > 0) contains A − Y;
            # rogue side (< 0) contains B − Y and +w
            AmY = (A[0]-Y[0], A[1]-Y[1]); BmY = (B[0]-Y[0], B[1]-Y[1])
            if not (cross(v, AmY) > 0): fails.append(("side A", e, f, k, i))
            if not (cross(v, BmY) < 0): fails.append(("side B", e, f, k, i))
            if not (cross(v, w) < 0): fails.append(("side w", e, f, k, i))
            checks += 1

# T-vertex forcing
for e, f in coprime_pairs(12):
    a, b, c = e*f, f*f - e*e, f*f
    Delta = c - a
    assert Delta == f*(f-e)
    assert b - Delta == e*(f-e) and b - Delta > 0
    assert c - Delta == a
    flush = [n for n in range(0, Delta // a + 2) if n * a == Delta]
    if e == 1:
        if flush != [f - 1]: fails.append(("T e=1", e, f, flush))
    else:
        if flush: fails.append(("T flush", e, f, flush))
    # and Δ < b < c so any b- or c-edge overshoots [X_i, Z_i]
    assert Delta < b < c or (Delta < b and b < c)
    checks += 1

print(f"phase 1 (V1, V2, T-forcing, sides): {checks} exact checks; {len(fails)} failures")
for x in fails[:20]:
    print("FAIL", x)


# ---- Phase 2: chord-2 geometry (C2a-C2d) and the K2 boundary kill ----


fails2 = 0
checks2 = 0


for f in range(3, 13):
    for e in range(2, f):
        if gcd(e, f) != 1:
            continue
        a, b, c = e*f, f*f - e*e, f*f
        u = (Fr(2*f*f - e*e, 2*f*f), Fr(e, 2*f*f))
        for k in range(3, f + 1):
            C = (Fr(k*b), Fr(0))
            B = (Fr(k*c)*u[0], Fr(k*c)*u[1])
            for i in range(0, k - 1):
                Y = (Fr((i+1)*b), Fr(0))
                # (C2a): V_{i+1} = Y_i
                assert Fr((i+1)*b) == Y[0]
                # (C2c): u-ray containment up to (k-i-1)c
                Lmax = Fr((k - i - 1)*c)
                for ell, inside in [(Lmax - Fr(1, 3), True), (Lmax, True),
                                    (Lmax + Fr(1, 3), False)]:
                    P = (Y[0] + ell*u[0], Y[1] + ell*u[1])
                    s, t = bary(P, B, C)
                    ok = (s >= 0 and t >= 0 and s + t <= 1)
                    if ok != inside:
                        print("FAIL C2c", e, f, k, i, ell); fails2 += 1
                # exit point interior to BC: s+t = 1 with 0 < s < 1
                P = (Y[0] + Lmax*u[0], Y[1] + Lmax*u[1])
                s, t = bary(P, B, C)
                if not (s + t == 1 and 0 < s < 1):
                    print("FAIL C2c exit", e, f, k, i); fails2 += 1
                checks2 += 2

        # (C2d): no x·a + y·b + z·c = c with x ≥ 1  (e ≥ 2)
        for x in range(0, c // a + 1):
            for y in range(0, c // b + 1):
                r = c - x*a - y*b
                if r < 0:
                    continue
                if r % c == 0:
                    z = r // c
                    if x >= 1:
                        print("FAIL C2d", e, f, (x, y, z)); fails2 += 1
        checks2 += 1

        # (Bdy): no ma·a + mb·b + mc·c = M·a with mc ≥ 1, M ≤ f−1
        for M in range(1, f):
            T = M*a
            for mc in range(1, T // c + 1):
                for mb in range(0, (T - mc*c) // b + 1):
                    r = T - mc*c - mb*b
                    if r >= 0 and r % a == 0:
                        print("FAIL Bdy", e, f, M, (r // a, mb, mc)); fails2 += 1
            checks2 += 1

print(f"phase 2 (chord-2 geometry, K2/K3 cores): {checks2} checks; {fails2} failures")
sys.exit(1 if (fails or fails2) else 0)
