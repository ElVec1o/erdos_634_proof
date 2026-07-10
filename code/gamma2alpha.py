#!/usr/bin/env python3
"""
gamma2alpha.py -- Beeson's boundary-tiling algorithm for the gamma = 2*alpha branch
(Tilings of an isosceles triangle, Lemmas 11.2, 11.11-11.14, 11.17, Theorem 11.18).

An isosceles ABC with base angles alpha, N-tiled by a tile with angles (alpha, beta, 2alpha)
(alpha not a rational multiple of pi), forces:
  - tile (a,b,c) = (k^2, m^2-k^2, mk), gcd(k,m)=1, 2k > m > k          [Lemma 11.2]
  - m < N + (N+1)^2/16                                                  [Lemma 11.12]
  - squarefree(b) = squarefree(N)  (since X^2 = N a b = N k^2 b)        [Lemma 11.14]
  - X = sqrt(N a b), Y = (m/k) X integers                               [area equations]
  - X = p a + q b + r c with q >= 1, r >= 1, p+q+r < (N+1)/4            [11.11 + 11.13]
  - Y = u a + v b + w c for some nonnegative (u,v,w)                    [Lemma 11.14]
  - NOT (r = 1 and every Y-representation has w in {1,2})               [Lemma 11.17]
A value N is EXCLUDED in this branch iff no tile admits a surviving boundary representation.
This reproduces Beeson's published eliminations (20, 28, 36, 44 die; 45 survives via (4,5,6)).
"""
import sys
from math import gcd, isqrt


def sqfree(n):
    d = 1
    m = n
    p = 2
    while p * p <= m:
        while m % (p * p) == 0:
            m //= p * p
        if m % p == 0:
            d *= p
            m //= p
        p += 1
    return d * m


def reps(X, a, b, c, cap=None, need_qr=False):
    """all (p,q,r) >= 0 with pa+qb+rc = X, optionally q,r >= 1 and p+q+r < cap"""
    out = []
    for r in range(0, X // c + 1):
        for q in range(0, (X - r * c) // b + 1):
            rem = X - r * c - q * b
            if rem % a:
                continue
            p = rem // a
            if need_qr and (q < 1 or r < 1):
                continue
            if cap is not None and p + q + r >= cap:
                continue
            out.append((p, q, r))
    return out


def gamma2alpha_status(N, verbose=False):
    """returns (excluded: bool, surviving: list of (tile, X-rep sample, Y-rep sample))"""
    mbound = N + (N + 1) * (N + 1) // 16 + 1
    sN = sqfree(N)
    survivors = []
    for m in range(2, mbound + 1):
        for k in range(m // 2 + 1, m):
            if gcd(k, m) != 1:
                continue
            a, b, c = k * k, m * m - k * k, m * k
            if b <= 0:
                continue
            if sqfree(b) != sN:
                continue
            X2 = N * a * b
            X = isqrt(X2)
            if X * X != X2:
                continue
            if (m * X) % k:
                continue
            Y = (m * X) // k
            cap = (N + 1) / 4
            xreps = [t for t in reps(X, a, b, c) if t[1] >= 1 and t[2] >= 1
                     and t[0] + t[1] + t[2] < cap]
            if not xreps:
                continue
            # Lemma 11.13 (base version, pigeonhole on b- and c-edges of AC): v>=1, w>=1
            yreps = [t for t in reps(Y, a, b, c) if t[1] >= 1 and t[2] >= 1]
            if not yreps:
                continue
            # Lemma 11.17: if every X-rep has r=1 and every Y-rep has w in {1,2}: dead
            if all(t[2] == 1 for t in xreps) and all(t[2] in (1, 2) for t in yreps):
                if verbose:
                    print(f"   N={N}: tile ({a},{b},{c}) killed by Lemma 11.17 "
                          f"(X-reps all r=1, Y-reps all w in {{1,2}})")
                continue
            survivors.append(((a, b, c), xreps[0], yreps[0], X, Y))
    return (len(survivors) == 0), survivors


if __name__ == '__main__':
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    print("Beeson gamma=2alpha boundary algorithm (Lemmas 11.2/11.11-11.14/11.17):")
    print("  calibration: 20,28,36,44 must be EXCLUDED; 45 must SURVIVE via (4,5,6)")
    for N in range(lo, hi + 1):
        exc, surv = gamma2alpha_status(N)
        if exc:
            print(f"  N={N:3d}: EXCLUDED (no possible boundary tiling)")
        else:
            s = surv[0]
            print(f"  N={N:3d}: survives  e.g. tile {s[0]}, X={s[3]}={s[1]}, Y={s[4]}={s[2]}"
                  f"  [{len(surv)} tile(s)]")
