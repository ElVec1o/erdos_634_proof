#!/usr/bin/env python3
"""How much of the e>=2 prime residue does the 'separated' hypothesis actually cover?

The main paper: "The walk of a separated member, meaning one with f^2 > 2ef + e^2, admits
exactly three edge decompositions ... Hence at a separated thick member the base walk is the
walls form."  Separated <=> f/e > 1 + sqrt(2) ~ 2.4142.

By ThinHole.rep_unique each prime has exactly ONE representation, so each prime is either
separated or not -- no ambiguity.
"""
import sympy

LIM = 200000
def rep(p):
    """The unique (e,f) with p = 3f^2 - e^2, 1 <= e < f, gcd(e,f)=1.

    p = 3f^2 - e^2 with 0 < e < f forces sqrt(p/3) < f < sqrt(p/2); sweeping only up to
    sqrt(p/3) is the truncation that made an earlier census report 4000 primes below
    200000 instead of 4489.
    """
    import math
    lo = sympy.integer_nthroot(p // 3, 2)[0]
    hi = sympy.integer_nthroot(p // 2, 2)[0] + 2
    for f in range(max(lo - 1, 2), hi + 1):
        d = 3 * f * f - p
        if d <= 0:
            continue
        e, ok = sympy.integer_nthroot(d, 2)
        if ok and 1 <= e < f and math.gcd(e, f) == 1:
            return (e, f)
    return None

prims = [p for p in sympy.primerange(5, LIM) if p % 12 == 11]
reps = {p: rep(p) for p in prims}
missing = [p for p, r in reps.items() if r is None]
e1 = [p for p, r in reps.items() if r and r[0] == 1]
e2 = [p for p, r in reps.items() if r and r[0] >= 2]
sep = [p for p in e2 if reps[p][1] ** 2 > 2 * reps[p][0] * reps[p][1] + reps[p][0] ** 2]
uns = [p for p in e2 if p not in set(sep)]

print(f"primes = 11 mod 12 below {LIM:,}: {len(prims)}")
print(f"  no representation found : {len(missing)}")
print(f"  e = 1 (the hole)        : {len(e1)}")
print(f"  e >= 2 (the residue)    : {len(e2)}")
print(f"      separated  (covered): {len(sep):>6}  ({100*len(sep)/len(e2):.1f}%)")
print(f"      NOT separated       : {len(uns):>6}  ({100*len(uns)/len(e2):.1f}%)")
print()
print("smallest e>=2 primes and whether the determined-walk result reaches them:")
for p in sorted(e2)[:16]:
    e, f = reps[p]
    s = "separated" if f*f > 2*e*f + e*e else "NOT separated"
    print(f"  p={p:<6} (e,f)=({e},{f})  f/e={f/e:.3f}  {s}")
