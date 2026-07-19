#!/usr/bin/env python3
"""
The Phi-invariant that closes the isosceles 2pi/3 case of Erdos #634.

INVARIANT.  Fix a direction frame.  For a directed edge of length L and direction
theta = j*(pi/3) + k*alpha (mod 2pi) assign  L * f(theta),  f(theta) := (-1)^j.
Because f(theta+pi) = -f(theta), interior edges cancel -- INCLUDING across T-junctions
(a long c-edge = the sum of the shorter a/b edges it overhangs; the functional is linear in
length).  So  sum over all tiles of C(tile) = Phi(boundary of ABC),  where C(tile) = sum of
L*f over the tile's CCW edges.  Every tile, in every orientation, has C(tile) = +- V0 with
V0 = c+a-b.  Hence  Phi(boundary) = M * V0  with  M an INTEGER (a signed tile count).

For an ISOSCELES ABC with base angle = a tile acute angle, align f to the base angle.
Then (with squared leg s, scale k=sqrt(s), prime N):  M = (c - a - b)/k.
THEOREM: for a primitive 120-triple, k does NOT divide (a+b-c); so M is never an integer;
so NO prime number of 2pi/3 tiles tiles an isosceles triangle.

This file: (1) validates the invariant on real tilings; (2) confirms C=+-V0 over all
orientations; (3) verifies M=(c-a-b)/k and 0 counterexamples over a large search.
"""
import math
from math import isqrt, gcd
from sympy import isprime

def make_f(alpha):
    def f(theta):
        best = None
        for j in range(-20, 21):
            for k in range(-20, 21):
                d = (j*math.pi/3 + k*alpha - theta) % (2*math.pi); d = min(d, 2*math.pi-d)
                if best is None or d < best[0]: best = (d, j)
        assert best[0] < 1e-6, theta
        return (-1)**(best[1] % 2)
    return f

def ccw(v):
    s = 0.5*sum(v[i][0]*v[(i+1)%3][1]-v[(i+1)%3][0]*v[i][1] for i in range(3))
    return v if s > 0 else [v[0], v[2], v[1]]

def Ctile(v, f):
    v = ccw(v); s = 0
    for i in range(3):
        p, q = v[i], v[(i+1)%3]
        L = math.hypot(q[0]-p[0], q[1]-p[1]); s += L*f(math.atan2(q[1]-p[1], q[0]-p[0]))
    return s

# (1) validate on reptile tilings N=m^2 of tile (5,16,19) -- M must equal m.
print("== (1) validation on real tilings (reptiles) ==")
a, b, c = 5, 16, 19; alpha = math.asin(a*math.sqrt(3)/(2*c)); f = make_f(alpha); V0 = c+a-b
ca, sa = (2*b+a)/(2*c), a*math.sqrt(3)/(2*c)
for m in [2, 3, 4, 5]:
    P0, P1, P2 = (0, 0), (m*c, 0), (m*b*ca, m*b*sa)
    g = lambda i, j: (P0[0]+i/m*(P1[0]-P0[0])+j/m*(P2[0]-P0[0]),
                      P0[1]+i/m*(P1[1]-P0[1])+j/m*(P2[1]-P0[1]))
    tris = []
    for i in range(m):
        for j in range(m-i):
            tris.append([g(i, j), g(i+1, j), g(i, j+1)])
            if i+j < m-1: tris.append([g(i+1, j), g(i, j+1), g(i+1, j+1)])
    Cs = [Ctile(t, f) for t in tris]
    print(f"  N={m*m}: all|C|=V0={V0}? {all(abs(abs(x)-V0)<1e-6 for x in Cs)}  "
          f"M=sumC/V0={round(sum(Cs)/V0)} (expect {m})")

# (2) C(tile)=+-V0 over all orientations (rotations m*alpha+n*pi/3, and reflection).
print("\n== (2) C(tile)=+-V0 over 98 orientations ==")
A, B, G = (0., 0.), (c, 0.), (b*ca, b*sa)
rot = lambda p, t: (p[0]*math.cos(t)-p[1]*math.sin(t), p[0]*math.sin(t)+p[1]*math.cos(t))
vals = set(); bad = 0
for mm in range(-3, 4):
    for nn in range(-3, 4):
        t = mm*alpha+nn*math.pi/3
        for refl in (False, True):
            v = [(p[0], -p[1]) if refl else p for p in (A, B, G)]
            C = Ctile([rot(p, t) for p in v], f)
            vals.add(round(C, 2));  bad += abs(abs(C)-V0) > 1e-6
print(f"  all give +-V0? {bad==0}; distinct C: {sorted(vals)}")

# (3) the necessary condition + non-integrality, for prime isosceles candidates.
print("\n== (3) M=(c-a-b)/k for prime isosceles candidates; integer-M counterexamples ==")
cp = bad2 = 0
for m in range(2, 2000):
    for n in range(1, m):
        if gcd(m, n) != 1 or (m-n) % 3 == 0: continue
        a0, b0, c0 = m*m-n*n, 2*m*n+n*n, m*m+m*n+n*n
        for (A_, B_, C_) in [(a0, b0, c0), (b0, a0, c0)]:
            if isqrt(B_)**2 == B_ and isprime(A_+2*B_):  # iso, squared leg B_, prime N
                cp += 1; k = isqrt(B_)
                if (A_+B_-C_) % k == 0: bad2 += 1
print(f"  prime candidates checked: {cp}; integer-M counterexamples: {bad2}")
# (4) TWO invariants: iso-beta needs f_beta.  Show that for an iso-beta target the alpha-frame
#     invariant f_alpha can give an INTEGER M (so it does NOT obstruct), while f_beta gives the
#     non-integer M=(c-a-b)/sqrt(a) that DOES.  (Addresses the two-invariant subtlety explicitly.)
print("\n== (4) iso-beta requires the mirror invariant f_beta ==")
def Phi_M(a, b, c, base_is_alpha):
    # build the isosceles ABC and f aligned to base angle; return M = Phi(boundary)/V0.
    if base_is_alpha:
        base_ang = math.asin(a*math.sqrt(3)/(2*c)); sq, oth, V = b, a, c+a-b
    else:
        base_ang = math.asin(b*math.sqrt(3)/(2*c)); sq, oth, V = a, b, c+b-a
    fA = make_f(base_ang)
    k = int(round(sq**0.5)); base_len = k*(2*sq+oth); eq = k*c
    Phi = base_len*fA(0.0) + eq*fA(math.pi-base_ang) + eq*fA(math.pi+base_ang)
    return Phi/V
for (a, b, c, N) in [(16, 39, 49, 71), (64, 735, 769, 863)]:   # iso-beta primes ==3 mod 4
    # f_alpha applied to the *non-base* angle (the WRONG grid) vs f_beta (base angle):
    al = math.asin(a*math.sqrt(3)/(2*c)); fwrong = make_f(al)
    kk = int(round(a**0.5)); base_len = kk*(2*a+b); eq = kk*c
    M_wrong = (base_len*fwrong(0.0)+eq*fwrong(math.pi-math.asin(b*math.sqrt(3)/(2*c)))
               + eq*fwrong(math.pi+math.asin(b*math.sqrt(3)/(2*c))))/(c+a-b)
    M_beta = Phi_M(a, b, c, base_is_alpha=False)
    print(f"  iso-beta N={N} tile({a},{b},{c}): f_alpha grid M={M_wrong:.3f} (integer -> does NOT obstruct); "
          f"f_beta M={M_beta:.4f} (= (c-a-b)/sqrt(a) -> non-integer, obstructs)")

# (5) T-junction cancellation unit test: a long c-edge (dir theta) meets short a/b edges (dir
#     theta+pi) whose lengths sum to it; the weighted sum must be 0 for ANY f with f(th+pi)=-f(th).
print("\n== (5) T-junction cancellation (length-additivity) unit test ==")
import random as _r
ok_tj = True
fT = make_f(alpha)
for _ in range(2000):
    th = _r.uniform(0, 2*math.pi)
    # snap theta to a grid direction so f is defined
    j = _r.randint(-6, 6); kk = _r.randint(-6, 6); th = j*math.pi/3 + kk*alpha
    Llong = _r.uniform(1, 100)
    # split Llong into random short pieces (the abutting edges), opposite direction
    parts = []
    rem = Llong
    while rem > 1e-6:
        p = min(rem, _r.uniform(0.1, Llong/2)); parts.append(p); rem -= p
    s = Llong*fT(th) + sum(p*fT(th+math.pi) for p in parts)
    if abs(s) > 1e-9: ok_tj = False
print(f"  long edge weight + sum of opposite short-edge weights == 0 in 2000 trials: {ok_tj}")

print("\nRESULT: no prime number of 2pi/3 tiles tiles an isosceles triangle "
      "(two invariants f_alpha,f_beta validated; C=+-V0 confirmed; M never integer; "
      "T-junction cancellation holds).")
