#!/usr/bin/env python3
"""Where the prime residue actually lives, by geometric regime.

Each prime = 11 mod 12 has exactly one representation p = 3f^2 - e^2 (ThinHole.rep_unique), so the
residue partitions cleanly.  The regimes matter because the machinery's hypotheses change:

  e = 1                 the hole; reduced to CRUX-1
  separated             f^2 > 2ef + e^2; the determined base walk applies
  wedge condition       e^4 - 4e^2f^2 + 2f^4 > 0, i.e. alpha < pi/4, i.e. 2*beta > alpha

The wedge condition, NOT beta-minimality, is what the corner-chain steps need: they fill a wedge of
angle exactly alpha with one alpha-tile, and what that requires is that no two smaller angles fit.
Frontier records that beta-minimality is not the load-bearing fact, and the two disagree at (3,4),
where beta is minimal yet the step survives.
"""
import sympy, math
LIM = 200000
SEP = 1 + 2 ** 0.5

def wedge_ok(e, f):
    """alpha < pi/4, exactly, in integers"""
    return e ** 4 - 4 * e * e * f * f + 2 * f ** 4 > 0

def rep(p):
    lo = sympy.integer_nthroot(p // 3, 2)[0]
    hi = sympy.integer_nthroot(p // 2, 2)[0] + 2
    for f in range(max(lo - 1, 2), hi + 1):
        d = 3 * f * f - p
        if d <= 0: continue
        e, ok = sympy.integer_nthroot(d, 2)
        if ok and 1 <= e < f and math.gcd(e, f) == 1:
            return (e, f)
    return None

buckets = {'e=1 (hole)': [], 'separated, wedge ok': [], 'close, wedge ok': [],
           'WEDGE FAILS': []}
for p in sympy.primerange(5, LIM):
    if p % 12 != 11: continue
    e, f = rep(p)
    if not wedge_ok(e, f): buckets['WEDGE FAILS'].append((p, e, f))
    elif e == 1: buckets['e=1 (hole)'].append((p, e, f))
    elif f > SEP * e: buckets['separated, wedge ok'].append((p, e, f))
    else: buckets['close, wedge ok'].append((p, e, f))
tot = sum(len(v) for v in buckets.values())
print(f"primes = 11 mod 12 below {LIM:,}: {tot}\n")
for k in ['e=1 (hole)', 'separated, wedge ok', 'close, wedge ok', 'WEDGE FAILS']:
    v = buckets[k]
    print(f"  {k:20} {len(v):>5}  ({100*len(v)/tot:4.1f}%)   smallest: "
          + ", ".join(f"{p}=({e},{f})" for p, e, f in sorted(v)[:4]))
