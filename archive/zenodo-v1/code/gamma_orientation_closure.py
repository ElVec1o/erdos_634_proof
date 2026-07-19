#!/usr/bin/env python3
"""
gamma-orientation closure test for the open isosceles prime cases of Erdos #634.

A prime N is achievable by a 2pi/3 tile only via an isosceles ABC (uniform-conjecture-reduction).
For iso-alpha: N=a+2b, b=k^2, tile (a,b,c) primitive (c^2=a^2+ab+b^2), ABC=k*(c,c,2b+a).
Each side of ABC is a disjoint union of full tile edges {a,b,c}.

CLOSURE (this file): N is impossible if
  (1) the equal side k*c has a UNIQUE decomposition = k copies of c (pure-c), AND
  (2) every base (k*N) decomposition with >=2 b-edges (one per corner) is c-free.
Then every base edge is an a- or b-edge, each with exactly one gamma-endpoint; the corner
b-edges force the first edge's gamma to its right end and the last edge's gamma to its left end;
two gammas cannot share a straight boundary point (2*120>180); so 'R then L' is forbidden, and
the propagation from x_1=R to x_m=R contradicts x_m=L.  No tiling exists.
"""
from math import isqrt
from itertools import product

def decs(L, a, b, c):
    out = []
    for r in range(L//c + 1):
        for q in range((L - c*r)//b + 1):
            rem = L - c*r - b*q
            if rem >= 0 and rem % a == 0:
                out.append((rem//a, q, r))   # (#a, #b, #c)
    return out

def cfree_base_forced(a, b, c, N, k):
    base = [d for d in decs(k*N, a, b, c) if d[1] >= 2]   # need b at both corners
    return len(base) > 0 and all(d[2] == 0 for d in base), base

def pure_c_equal_side(a, b, c, k):
    return decs(k*c, a, b, c) == [(0, 0, k)]

def closed(a, b, c, N):
    k = isqrt(b)
    pc = pure_c_equal_side(a, b, c, k)
    cf, base = cfree_base_forced(a, b, c, N, k)
    return pc and cf, pc, base

def no_valid_assignment(m):
    """brute force: c-free base, x in {L,R}^m, x_1=R, x_m=L, no R->L adjacency -> none exists."""
    return not any(
        x[0] == 'R' and x[-1] == 'L' and all(not (x[i] == 'R' and x[i+1] == 'L') for i in range(m-1))
        for x in product('LR', repeat=m)
    )

# the open prime ≡3 mod4 candidates up to 10^4 (from tiling_search.rs)
CANDS = [(39,16,49,71),(155,144,259,443),(735,64,769,863),(1659,400,1891,2459),
         (819,1600,2131,4019),(6795,784,7219,8363),(1463,3600,4513,8663)]

print("orientation lemma sanity (c-free base => no valid gamma-assignment):",
      all(no_valid_assignment(m) for m in range(2, 25)))
print()
closed_list, open_list = [], []
for a, b, c, N in CANDS:
    ok, pc, base = closed(a, b, c, N)
    (closed_list if ok else open_list).append(N)
    print(f"N={N:5d}  tile({a},{b},{c})  pure-c equal side={pc}  base(>=2b)={base}  CLOSED={ok}")
print()
print("CLOSED by gamma-orientation:", sorted(closed_list))
print("still OPEN (base admits c-edges):", sorted(open_list))
print("=> smallest open prime ≡3 (mod 4):", min(open_list))
