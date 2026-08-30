#!/usr/bin/env python3
"""The count in obstructions prop:norm: primes of the form 3f^2 - e^2 with gcd(e,f)=1, e<f<40."""
import math
import sympy

pairs = [(e, f) for f in range(2, 40) for e in range(1, f)
         if math.gcd(e, f) == 1 and sympy.isprime(3 * f * f - e * e)]
print(f"pairs (e,f): {len(pairs)}")
print(f"distinct prime values: {len({3 * f * f - e * e for e, f in pairs})}")
