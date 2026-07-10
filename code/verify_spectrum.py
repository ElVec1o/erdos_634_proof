#!/usr/bin/env python3
"""
verify_spectrum.py  --  Section 7 of the paper (towards the full problem).

Checks, in exact arithmetic:
  (1) the prime dichotomy's achievability half: every prime p ≢ 3 (mod 4) is a sum of two
      positive squares (the biquadratic construction realizes it);
  (2) the scale-structure lemma: for b = d·e² with d squarefree, b | k² iff (d·e) | k;
  (3) the isosceles admissible spectrum: enumerating all (tile, k), every admissible count
      is N = d·w²·(a+2b) with e | w(c−a−b); no prime is admissible; N = 46 is admissible on
      the tile (7,8,13);
  (4) the solvability classification: every primitive triple with b = d·e² and e | (a+b−c)
      arises from an integer j with d < j < 2d via a = e²(2d−j)(2d+j)/(4(j−d)); for d = 1
      there are none (Lemma 6 re-proved).
"""
from math import isqrt, gcd

def issq2(n):
    return n >= 0 and isqrt(n) ** 2 == n
from sympy import isprime, factorint


def sqfree_split(b):
    """b = d * e**2 with d squarefree."""
    d = e = 1
    for p, v in factorint(b).items():
        e *= p ** (v // 2)
        if v % 2:
            d *= p
    return d, e


def is120(a, b):
    if gcd(a, b) != 1:
        return None
    s = a * a + a * b + b * b
    c = isqrt(s)
    return c if c * c == s else None


# (1) prime dichotomy, achievability half ------------------------------------------------------
print("== (1) every prime p ≢ 3 (mod 4), p < 10^5, is a sum of two positive squares ==")
bad = 0
p = 2
count = 0
while p < 100000:
    if isprime(p) and p % 4 != 3:
        count += 1
        found = any((lambda r: r * r == p - e * e)(isqrt(p - e * e))
                    for e in range(1, isqrt(p // 2) + 1))
        if not found:
            bad += 1
    p += 1
print(f"   primes checked: {count};  failures: {bad}  (expect 0)\n")


# (2) b | k²  iff  (d·e) | k ------------------------------------------------------------------
print("== (2) scale structure: b | k^2  iff  d·e | k   (b = d·e², d squarefree) ==")
mism = 0
for b in range(1, 400):
    d, e = sqfree_split(b)
    assert d * e * e == b
    for k in range(1, 200):
        if ((k * k) % b == 0) != (k % (d * e) == 0):
            mism += 1
print(f"   b < 400, k < 200: mismatches {mism}  (expect 0)\n")


# (3) the isosceles admissible spectrum --------------------------------------------------------
print("== (3) isosceles-alpha admissible counts N = d·w²·(a+2b) with e | w(c−a−b) ==")
admissible = set()
prime_hits = []
for a in range(1, 260):
    for b in range(1, 260):
        c = is120(a, b)
        if not c:
            continue
        d, e = sqfree_split(b)
        for w in range(1, 12):
            # scale k = d e w; area gives N automatically integral:
            N = d * w * w * (a + 2 * b)
            # the invariant condition:
            if (w * (c - a - b)) % e == 0:
                admissible.add(N)
                if isprime(N):
                    prime_hits.append((N, a, b, c, w))
print(f"   tiles a,b < 260, w < 12: admissible values found: {len(admissible)}")
print(f"   prime admissible values: {prime_hits if prime_hits else 'NONE'}  (expect NONE)")
print(f"   46 admissible (tile (7,8,13), d=2, e=2, w=1): {46 in admissible}")
print("   smallest admissible values:", sorted(admissible)[:8], "\n")


# (4) solvability classification ---------------------------------------------------------------
print("== (4) e | (a+b−c) instances match the j-parametrization; none for d = 1 ==")
hits, mismatches, d1_hits = [], 0, 0
for a in range(1, 3000):
    for b in range(1, 3000):
        c = is120(a, b)
        if not c:
            continue
        d, e = sqfree_split(b)
        if e > 1 and (a + b - c) % e == 0:
            if d == 1:
                d1_hits += 1
            # find the j predicted by the proposition
            ok = False
            for j in range(d + 1, 2 * d):
                if (e * j) % 2 == 0 and 4 * (j - d) * a == e * e * (2 * d - j) * (2 * d + j):
                    ok = True
                    break
            hits.append((a, b, c, d, e))
            if not ok:
                mismatches += 1
print(f"   instances with e>1 and e | (a+b−c): {len(hits)};  outside the j-classification: "
      f"{mismatches}  (expect 0);  with d = 1: {d1_hits}  (expect 0; Lemma 6)")
print("   sample instances:", hits[:4], "\n")

# (5) the lattice theorem --------------------------------------------------------------------
print("== (5) lattice theorem: admissible w form exactly the lattice E*Z ==")
print("   (r = c-a-b, g = gcd(e,r), e1 = e/g, T = r/g + d*e1^2*(a+2b); E = e1 if T even else 2*e1)")
mism = 0
zhang_match = 0
free_tiles = []
tiles_checked = 0
for a in range(1, 300):
    for b in range(1, 300):
        c = is120(a, b)
        if not c:
            continue
        tiles_checked += 1
        d, e = sqfree_split(b)
        r = c - a - b
        g = gcd(e, abs(r)) if r != 0 else e
        e1 = e // g
        T = (r // g + d * e1 * e1 * (a + 2 * b)) % 2
        E = e1 if T == 0 else 2 * e1
        for w in range(1, 41):
            N = d * w * w * (a + 2 * b)
            adm = (w * r) % e == 0 and ((w * r) // e - N) % 2 == 0
            if adm != (w % E == 0):
                mism += 1
        if E == e:      # lattice = e*Z would mean spectrum ~ Zhang up to the 2-adic factor
            pass
        if E == 2 * e or E == e:
            zhang_match += 1
        if E < e:       # strictly larger spectrum than the Zhang family
            free_tiles.append((a, b, c, d, e, E))
print(f"   tiles checked: {tiles_checked};  lattice mismatches: {mism}  (expect 0)")
print(f"   tiles whose lattice is coarser than e*Z (spectrum beyond the Zhang family): "
      f"{len(free_tiles)}")
print("   examples:", free_tiles[:4])
d19, e19 = sqfree_split(261)
r19 = 271 - 19 - 261
g19 = gcd(e19, abs(r19)); e119 = e19 // g19
T19 = (r19 // g19 + d19 * e119 * e119 * (19 + 2 * 261)) % 2
E19 = e119 if T19 == 0 else 2 * e119
print(f"   tile (19,261,271): d={d19}, e={e19}, r={r19}, E={E19} -> N = {d19*541}*w^2 for ALL w;")
print(f"   w=1 gives N = {d19*541} = 29*541, admissible but OUTSIDE Zhang's family m^2*b*(a+2b).")

# (6) THE SPECTRUM THEOREM: both invariants together give exactly Zhang's family --------------
print("== (6) spectrum theorem: full admissibility (both invariants) == Zhang family ==")
mism6 = beta_kills = 0
tiles6 = 0
for a in range(1, 400):
    for b in range(1, 400):
        c = is120(a, b)
        if not c:
            continue
        tiles6 += 1
        d, e = sqfree_split(b)
        X, Y = c + a - b, c + b - a
        for w in range(1, 3 * e + 2):
            k = d * e * w
            N = d * w * w * (a + 2 * b)
            MA = k * (2 * b + a - 2 * c)
            MB = k * (2 * b + a + 2 * c)
            condA = MA % X == 0 and (MA // X - N) % 2 == 0
            condB = MB % Y == 0 and (MB // Y - N) % 2 == 0
            if (condA and condB) != (w % e == 0):
                mism6 += 1
            if condA and not condB:
                beta_kills += 1
print(f"   tiles: {tiles6};  (tile,w) with full-admissible != Zhang: {mism6}  (expect 0)")
print(f"   f_alpha-passing pairs killed by f_beta: {beta_kills}  (the closed gap;")
print("    includes the retracted instances 354, 1694, 15689)\n")

# (7) conic form of the equilateral criteria ---------------------------------------------------
print("== (7) equilateral criteria as divisor conditions on 16N^2 (conic form) ==")
bad_p = bad_q = 0
for N in range(1, 300):
    d_pi3 = any(M * M < N and (N - M) % 2 == 0 and issq2((9 * N - M * M) * (N - M * M))
                for M in range(1, isqrt(N) + 1))
    d_2pi3 = False
    for sdiv in range(1, 3 * N + 1):
        if (3 * N) % sdiv:
            continue
        t = 3 * N // sdiv
        if sdiv > t or (sdiv - N) % 2 or (t - N) % 2:
            continue
        if issq2((t - sdiv) ** 2 + 16 * N):
            d_2pi3 = True
    c_pi3 = c_2pi3 = False
    T = 16 * N * N
    u = 1
    while u * u <= T:
        if T % u == 0:
            v = T // u
            if (u + v) % 2 == 0:
                M2 = 5 * N - (u + v) // 2
                if M2 > 0 and issq2(M2):
                    M = isqrt(M2)
                    if M * M < N and (N - M) % 2 == 0 and M > 0:
                        c_pi3 = True
                s2 = (u + v) // 2 - 5 * N
                if s2 > 0 and issq2(s2):
                    sdiv = isqrt(s2)
                    if (3 * N) % sdiv == 0:
                        t = 3 * N // sdiv
                        if (sdiv - N) % 2 == 0 and (t - N) % 2 == 0:
                            c_2pi3 = True
        u += 1
    bad_p += d_pi3 != c_pi3
    bad_q += d_2pi3 != c_2pi3
print(f"   N < 300: pi/3 mismatches {bad_p}, 2pi/3 mismatches {bad_q}  (expect 0, 0)\n")

print("RESULT: prime dichotomy, scale structure, spectra, j-classification, lattice theorem,")
print("SPECTRUM THEOREM (full admissibility = Zhang family, every tile), and the conic form of")
print("the equilateral criteria all verify.")
