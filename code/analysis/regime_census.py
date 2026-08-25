#!/usr/bin/env python3
"""Where the prime residue actually lives, by geometric regime.

Each prime = 11 mod 12 has exactly one representation p = 3f^2 - e^2 (ThinHole.rep_unique), so the
residue partitions cleanly.  The regimes matter because the machinery's hypotheses change:

  e = 1                 the hole; reduced to CRUX-1
  separated   f > (1+sqrt2) e     the determined base walk applies
  close, f >= e*phi     b <= 2a but alpha still minimal
  close, f <  e*phi     b < a, and BETA is the minimal angle: lem:wallclimb's alpha-minimality
                        hypothesis FAILS, so the geometry itself changes
"""
import sympy, math
LIM = 200000
PHI = (1 + 5 ** 0.5) / 2
SEP = 1 + 2 ** 0.5

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

buckets = {'e=1 (hole)': [], 'separated': [], 'close, alpha min': [], 'close, BETA min': []}
for p in sympy.primerange(5, LIM):
    if p % 12 != 11: continue
    e, f = rep(p)
    if e == 1: buckets['e=1 (hole)'].append((p, e, f))
    elif f > SEP * e: buckets['separated'].append((p, e, f))
    elif f >= PHI * e: buckets['close, alpha min'].append((p, e, f))
    else: buckets['close, BETA min'].append((p, e, f))
tot = sum(len(v) for v in buckets.values())
print(f"primes = 11 mod 12 below {LIM:,}: {tot}\n")
for k in ['e=1 (hole)', 'separated', 'close, alpha min', 'close, BETA min']:
    v = buckets[k]
    print(f"  {k:20} {len(v):>5}  ({100*len(v)/tot:4.1f}%)   smallest: "
          + ", ".join(f"{p}=({e},{f})" for p, e, f in sorted(v)[:4]))
