#!/usr/bin/env python3
"""The e=1 hole of thm:fullprime is exactly the primes of the form 3f^2 - 1.

A prime p is "in the hole" when every base-beta representation p = 3f^2 - e^2
(gcd(e,f)=1, 1 <= e < f) has e = 1, so the unconditional e >= 2 half of
thm:fullprime gives it no content.

This enumerates both sets and checks they coincide.  Reproduces the numbers in
Erdos634/ThinHole.lean: 51 each below 200000, 82 each below 600000.

Usage:  python3 code/analysis/hole_characterisation.py [bound]
"""
import sys
from math import gcd
from sympy import isprime

def main(LIM):
    reps = {}
    f = 2
    while 3*f*f - 1 <= LIM:
        for e in range(1, f):
            if gcd(e, f) != 1:
                continue
            p = 3*f*f - e*e
            if 2 <= p <= LIM and isprime(p):
                reps.setdefault(p, []).append((e, f))
        f += 1
    hole = {p for p, r in reps.items() if all(e == 1 for e, _ in r)}

    form = set()
    f = 2
    while 3*f*f - 1 <= LIM:
        p = 3*f*f - 1
        if isprime(p):
            form.add(p)
        f += 1

    print(f"bound {LIM:,}")
    print(f"  representable primes : {len(reps)}")
    print(f"  hole (all reps e=1)  : {len(hole)}")
    print(f"  primes of form 3f^2-1: {len(form)}")
    print(f"  sets equal           : {hole == form}")
    print(f"  in form not hole     : {len(form - hole)}")
    print(f"  in hole not form     : {len(hole - form)}")
    return hole == form

if __name__ == "__main__":
    ok = main(int(sys.argv[1]) if len(sys.argv) > 1 else 200000)
    sys.exit(0 if ok else 1)
