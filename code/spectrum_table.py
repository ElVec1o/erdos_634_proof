#!/usr/bin/env python3
"""The Erdos-634 spectrum below N = 200: realizable / excluded / open, with reasons.

Exact integer arithmetic only.  The status of each N in [1, 200]:

REALIZABLE families (constructions in the literature and in this project):
  square     N = k^2            subdivision of any triangle;
  twosq      N = x^2 + y^2      (x, y >= 1) right triangle with legs x, y split by the
                                altitude, the two parts subdivided x^2- and y^2-fold
                                (covers 2k^2, all primes p = 2 and p == 1 mod 4);
  3sq        N = 3k^2           equilateral joined to its center, then subdivided;
  6sq        N = 6k^2           equilateral cut into six 30-60-90 triangles, subdivided;
  cert       N in {28,44,63,77,99}  kernel-certified tilings of this project
                                (lean/Tiling28,44,77,99.lean, lean/CevianTiling28/63.lean);
  ladder     N = k^2 * N'       for any realizable N' (Theorem thm:ladder;
                                lean/Primitives.lean, ladder_cells) -- closed to a fixpoint.

EXCLUDED:
  mod12      N prime, N == 7 mod 12: unconditional (thm:main + thm:mod12; the forward
             direction of thm:mod12 is lean/Mod12.lean);
  exhausted  N prime, N == 11 mod 12, N in {11, 23, 47, 59, 71, 107}: every base-beta
             member of N is settled EXHAUSTED_NO_TILING by the certified engine, and no
             other branch admits a prime == 3 mod 4 (main paper).

Everything else is OPEN.  Notable open subclasses annotated in the output:
  - primes == 11 mod 12 not yet exhausted: 83, 131, 167, 179, 191;
  - the base-beta member values 66 = (3,5), 138 = (3,7) (branch-dead there, open as counts);
  - Zhang-admissible sporadic values below 200 with no construction: 105, 120, 132, 154, 184.

Usage: python3 code/spectrum_table.py [--tex]
"""
import sys
from math import isqrt

LIMIT = 200
CERT = {28: "Tiling28/CevianTiling28", 44: "Tiling44", 63: "CevianTiling63",
        77: "Tiling77", 99: "Tiling99"}
EXHAUSTED = {11, 23, 47, 59, 71, 107}
OPEN_MOD12 = {83, 131, 167, 179, 191}
ZHANG_OPEN = {105, 120, 132, 154, 184}
# composite exclusions of the main paper's frontier theorems (thm:frontier..frontier5,
# rem:seventy); each combines a branch sweep with per-instance engine exhaustions.  After the
# N=63 correction (thm:63, rem:63correction) the sweep's scalene 3a+2b step is under re-audit;
# the per-instance exhaustions themselves are unaffected.
FRONTIER = {14: "thm:frontier", 15: "thm:frontier",
            21: "thm:frontier2", 22: "thm:frontier2", 30: "thm:frontier2",
            33: "thm:frontier2", 35: "thm:frontier2", 38: "thm:frontier2",
            39: "thm:frontier2", 42: "thm:frontier2", 46: "thm:frontier2",
            51: "thm:frontier3", 55: "thm:frontier3", 56: "thm:frontier3",
            57: "thm:frontier3", 60: "thm:frontier3", 62: "thm:frontier3",
            66: "thm:frontier3 proof (7.2M-node exhaustion)", 69: "thm:frontier3",
            70: "rem:seventy (134.6M-node exhaustion)", 76: "thm:frontier4",
            78: "thm:frontier3", 86: "thm:frontier5", 87: "thm:frontier5"}


def is_prime(n):
    if n < 2: return False
    for p in range(2, isqrt(n) + 1):
        if n % p == 0: return False
    return True


def base_reason(n):
    r = isqrt(n)
    if r * r == n:
        return f"{r}^2"
    for x in range(1, isqrt(n) + 1):
        y2 = n - x * x
        y = isqrt(y2)
        if y >= 1 and y * y == y2:
            return f"{x}^2+{y}^2"
    if n % 3 == 0:
        k = isqrt(n // 3)
        if 3 * k * k == n:
            return f"3*{k}^2"
    if n % 6 == 0:
        k = isqrt(n // 6)
        if 6 * k * k == n:
            return f"6*{k}^2"
    if n in CERT:
        return f"certified ({CERT[n]})"
    if n % 7 == 0:
        m = isqrt(n // 7)
        if 7 * m * m == n and m >= 2:
            return f"7*{m}^2 (W-family, thm:wfamily)"
    return None


def main():
    status = {}
    for n in range(1, LIMIT + 1):
        b = base_reason(n)
        if b:
            status[n] = ("REALIZABLE", b)
    # ladder fixpoint
    changed = True
    while changed:
        changed = False
        for n in range(1, LIMIT + 1):
            if n in status: continue
            for k in range(2, isqrt(n) + 1):
                if n % (k * k) == 0 and n // (k * k) in status and status[n // (k * k)][0] == "REALIZABLE":
                    status[n] = ("REALIZABLE", f"{k}^2*{n // (k * k)} (ladder)")
                    changed = True
                    break
    for n in range(1, LIMIT + 1):
        if n in status: continue
        if n in FRONTIER:
            status[n] = ("EXCLUDED", f"composite, {FRONTIER[n]} (scalene step under re-audit)")
        elif is_prime(n):
            if n % 12 == 7:
                status[n] = ("EXCLUDED", "prime == 7 mod 12 (thm:main + thm:mod12)")
            elif n % 12 == 11 and n in EXHAUSTED:
                status[n] = ("EXCLUDED", "prime == 11 mod 12, all members exhausted")
            elif n % 12 == 11:
                status[n] = ("OPEN", "prime == 11 mod 12, members unresolved")
            else:
                status[n] = ("OPEN", "prime, unclassified")  # should not occur
        else:
            note = []
            if n in ZHANG_OPEN: note.append("Zhang-admissible, no construction")
            if n in (66, 138): note.append("base-beta member exhausted; other branches open")
            status[n] = ("OPEN", "; ".join(note) if note else "no construction, no exclusion")

    R = [n for n in range(1, LIMIT + 1) if status[n][0] == "REALIZABLE"]
    E = [n for n in range(1, LIMIT + 1) if status[n][0] == "EXCLUDED"]
    O = [n for n in range(1, LIMIT + 1) if status[n][0] == "OPEN"]

    if "--tex" in sys.argv:
        print("% generated by code/spectrum_table.py -- do not edit by hand")
        print(f"% realizable {len(R)}, excluded {len(E)}, open {len(O)} of {LIMIT}")
        print("\\newcommand{\\SpecRealizable}{" + ", ".join(map(str, R)) + "}")
        print("\\newcommand{\\SpecExcluded}{" + ", ".join(map(str, E)) + "}")
        print("\\newcommand{\\SpecOpen}{" + ", ".join(map(str, O)) + "}")
        return

    print(f"N <= {LIMIT}: {len(R)} realizable, {len(E)} excluded, {len(O)} open\n")
    for n in range(1, LIMIT + 1):
        s, why = status[n]
        print(f"{n:4d}  {s:10s}  {why}")
    print("\nREALIZABLE:", ", ".join(map(str, R)))
    print("\nEXCLUDED:  ", ", ".join(map(str, E)))
    print("\nOPEN:      ", ", ".join(map(str, O)))


if __name__ == "__main__":
    main()
