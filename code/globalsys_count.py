#!/usr/bin/env python3
"""Enumerate solutions of prop:globalsys's angle-Euler system over the nonnegative integers.

Unknowns: n1,n2 (boundary non-corner figures (1,1,1),(3,2,0)),
          v1..v4 (interior figures (0,1,3),(2,2,2),(4,3,1),(6,4,0)).
Corner fills fixed: one apex (3,0,0), two base corners (0,1,0).
Constraints: each of the three corner types sums to N, plus Euler N = 2I + B + 1.
Usage: python3 code/globalsys_count.py [N ...]      (default 11 23 47)
"""
import sys

def solutions(N):
    out = []
    for n1 in range(N + 1):
        for n2 in range(N + 1):
            if 3 + n1 + 3 * n2 > N: break
            for v4 in range(N + 1):
                if 3 + n1 + 3 * n2 + 6 * v4 > N: break
                for v3 in range(N + 1):
                    if 3 + n1 + 3 * n2 + 6 * v4 + 4 * v3 > N: break
                    for v2 in range(N + 1):
                        a = 3 + n1 + 3 * n2 + 6 * v4 + 4 * v3 + 2 * v2
                        if a > N: break
                        if a != N: continue
                        for v1 in range(N + 1):
                            b = 2 + n1 + 2 * n2 + 4 * v4 + 3 * v3 + 2 * v2 + v1
                            if b > N: break
                            if b != N: continue
                            if n1 + v3 + 2 * v2 + 3 * v1 != N: continue
                            if N != 2 * (v1 + v2 + v3 + v4) + (n1 + n2) + 1: continue
                            out.append((n1, n2, v1, v2, v3, v4))
    return out

for N in (int(x) for x in (sys.argv[1:] or ["11", "23", "47"])):
    print(f"N={N}: {len(solutions(N))} solutions")
