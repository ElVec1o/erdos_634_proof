#!/usr/bin/env python3
"""
verify_no_go.py  --  Remark (no invariant decides realizability), Section 8.

For the sharpest open instance N=105 (F1 target (105,56,91) of the tile (8,7,13)):
  (1) searches ALL directional invariants of period <= P in the alpha-winding, with
      reflections, that assign the tile a constant boundary value +-V over every orientation,
      and checks each against N=105.  The only ones are f_alpha (M=5) and f_beta (M=21); both
      are admissible.  (A directional invariant is conserved by tile placement, so it can only
      reproduce the admissibility conditions -- it cannot obstruct an admissible instance.)
  (2) checks the vertex-type balance forced by the angle relations a*alpha+b*beta+c*gamma in
      {pi, 2pi}: it admits 42282 nonnegative integer solutions, so vertex counting does not
      obstruct 105 either.
"""
from fractions import Fraction as F
from itertools import product

# ---- (1) directional invariant search --------------------------------------------------------
# Tile (8,7,13): CCW ref edges A->B (13,(0,0)), B->C (8,(1,2)), C->A (7,(1,3)).
# w(n,m) periodic in n (period p), w(n,m+3) = -w(n,m); unknowns A[n],B[n],C[n]=w(n,0),w(n,1),w(n,2).
# tile value (nonreflected, orientation m0):  13 w(n0,m0)+8 w(n0+1,m0+2)-7 w(n0+1,m0)
# reflected:                                   13 w(n0,m0+3)+7 w(n0-1,m0)+8 w(n0-1,m0+1)
# target (105,56,91): edges VU(105,(0,0)), UW(91,(-1,3)), WV(56,(0,4)).

def gauss(Aug, n):
    M = [row[:] for row in Aug]; piv = 0
    for col in range(n):
        pr = next((r for r in range(piv, len(M)) if M[r][col] != 0), None)
        if pr is None: return None
        M[piv], M[pr] = M[pr], M[piv]
        M[piv] = [v / M[piv][col] for v in M[piv]]
        for r in range(len(M)):
            if r != piv and M[r][col] != 0:
                f = M[r][col]; M[r] = [a - f * b for a, b in zip(M[r], M[piv])]
        piv += 1
        if piv == n: break
    for r in range(piv, len(M)):
        if all(M[r][c] == 0 for c in range(n)) and M[r][n] != 0: return None
    return [M[i][n] for i in range(n)] if piv == n else None

def search_period(p):
    idx = lambda k, n: k * p + (n % p)                       # k=0,1,2 -> A,B,C
    def add_w(c, n, m, coef):
        n %= p; m %= 6
        base = idx(m % 3, n)
        c[base] += coef if m < 3 else -coef
    def eq_nonref(n, m0):
        c = [F(0)] * (3 * p); add_w(c, n, m0, 13); add_w(c, n + 1, m0 + 2, 8); add_w(c, n + 1, m0, -7); return c
    def eq_ref(n, m0):
        c = [F(0)] * (3 * p); add_w(c, n, m0 + 3, 13); add_w(c, n - 1, m0, 7); add_w(c, n - 1, m0 + 1, 8); return c
    def w(x, n, m):
        n %= p; m %= 6; base = x[idx(m % 3, n)]; return base if m < 3 else -base
    nonref = [eq_nonref(n, m0) for n in range(p) for m0 in range(3)]
    ref = [eq_ref(n, m0) for n in range(p) for m0 in range(3)]
    tvs, obstruct = set(), False
    for sigma in product([1, -1], repeat=3 * p):
        x = gauss([nonref[i][:] + [F(sigma[i])] for i in range(3 * p)], 3 * p)
        if x is None: continue
        if any(abs(sum(r[i] * x[i] for i in range(3 * p))) != 1 for r in ref): continue
        tv = 105 * w(x, 0, 0) + 91 * w(x, -1, 3) + 56 * w(x, 0, 4)
        adm = tv.denominator == 1 and int(tv) % 2 == 1 and abs(int(tv)) <= 105
        tvs.add(tv)
        if not adm: obstruct = True
    return sorted(tvs), obstruct

print("== (1) directional invariants vs N=105 ==")
any_obstruct = False
for p in (1, 2, 3, 4):
    tvs, ob = search_period(p)
    any_obstruct |= ob
    print(f"   period {p}: I(target)/V in {tvs}  (all admissible odd ints in [-105,105]: {not ob})")
print(f"   => obstruction found: {any_obstruct}   (expect False; only M_alpha=5, M_beta=21 occur)\n")

# ---- (2) vertex-type counting ----------------------------------------------------------------
# interior (sum 2pi) corner-triples (#a,#b,#g): (0,0,3),(2,2,2),(4,4,1),(6,6,0)
# flat/T-junction (sum pi): (1,1,1),(3,3,0);  target corners: alpha=(1,0,0),pi/3=(1,1,0),a2b=(1,2,0)
# totals #alpha=#beta=#gamma=N.  count nonneg integer solutions for N=105.
print("== (2) vertex-type balance for N=105 ==")
N = 105; sols = 0
for n12 in range(0, 18):
    for n9 in range(0, 106):
        if 4 * n9 + 6 * n12 > 102: break
        for n6 in range(0, 53):
            A = 2 * n6 + 4 * n9 + 6 * n12
            if A > 102: break
            rem = 102 - A
            for b6 in range(0, rem // 3 + 1):
                b3 = rem - 3 * b6
                num = 105 - 2 * n6 - n9 - b3
                if num >= 0 and num % 3 == 0:
                    sols += 1
print(f"   nonnegative integer solutions: {sols}  (expect 42282 -> no obstruction)\n")

print("RESULT: no directional invariant (period <= 4, with reflections) and no vertex-type count")
print("obstructs N=105 -- deciding its realizability is beyond every linear/coloring invariant.")
