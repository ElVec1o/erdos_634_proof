#!/usr/bin/env python3
"""Extra base columns at close pairs (Erdos #634).

Reproduces every count quoted in Proposition~\\ref{prop:sharpcolumn} and
Remark~\\ref{rem:sharpcolumnscope} of the companion, and checks the sharp
criterion against brute enumeration of the base equation.

Setting.  For coprime 1 <= e < f the tile is (a,b,c) = (ef, f^2-e^2, f^2) and the
target base has length e(3f^2-e^2).  A base column is a solution (x,y,z) of
    x*a + y*b + z*c = e(3f^2-e^2)
with x,z >= 1 and x+z >= 4.  The standard column has y = e; the extra ones have
y = e + k*f with k >= 1.

Criterion (Proposition sharpcolumn).  Let x_k be the least positive integer with
x_k = k*e (mod f), written x_k = k*e - m_k*f, and set
    g(k) = (m_k + 2)*e - 1 - k*f,     z_k = (2ef - k*b - x_k*e) / f.
A column with parameter k exists iff g(k) >= 0 and x_k + z_k >= 4.  g drops by at
least f-e per step, so the admissible k form an initial segment 1..K, and
g(1) = 2e-1-f, so f >= 2e leaves no column at all.

Usage:  python3 code/close_pair_columns.py [EMAX]      (default 200)
"""

import sys
from math import gcd


def brute(e, f):
    """All k >= 1 carrying an extra base column, by direct enumeration."""
    a, b, c = e * f, f * f - e * e, f * f
    target = e * (3 * f * f - e * e)
    out, k = [], 1
    while True:
        y = e + k * f
        if y * b > target:
            return out
        rem = target - y * b
        for z in range(1, rem // c + 1):
            r = rem - z * c
            if r > 0 and r % a == 0 and r // a >= 1 and r // a + z >= 4:
                out.append(k)
                break
        k += 1


def criterion(e, f):
    """The same set, via the sharp criterion."""
    b = f * f - e * e
    out, k = [], 1
    while k * b < 2 * e * f:
        m = (k * e - 1) // f
        if (m + 2) * e - 1 - k * f >= 0:                      # g(k) >= 0
            x = k * e - m * f
            z = (2 * e * f - k * b - x * e) // f
            if x + z >= 4:
                out.append(k)
        k += 1
    return out


def close_pairs(emax):
    for e in range(1, emax + 1):
        for f in range(e + 1, int((1 + 2 ** 0.5) * e) + 1):
            if gcd(e, f) == 1 and f * f - e * e <= 2 * e * f:
                yield e, f


def main(emax):
    pairs = disagree = columns = cleared = seg_fail = kbound_fail = 0
    for e, f in close_pairs(emax):
        pairs += 1
        B, C = brute(e, f), criterion(e, f)
        if B != C:
            disagree += 1
            print(f"  DISAGREEMENT at (e,f)=({e},{f}): brute={B} criterion={C}")
        columns += len(B)
        if f >= 2 * e:
            if B:
                print(f"  f >= 2e yet a column exists at ({e},{f}): {B}")
            else:
                cleared += 1
        if B != list(range(1, len(B) + 1)):
            seg_fail += 1
        if B and max(B) > 1 + (2 * e - 1 - f) // (f - e):
            kbound_fail += 1

    print(f"close pairs with e <= {emax}: {pairs}")
    print(f"  extra base columns found:                      {columns}")
    print(f"  criterion disagreements with brute force:      {disagree}")
    print(f"  pairs with f >= 2e, hence no column at all:    {cleared}"
          f"  ({100 * cleared / pairs:.1f}%)")
    print(f"  surviving set not an initial segment:          {seg_fail}")
    print(f"  violations of K <= 1 + floor((2e-1-f)/(f-e)):  {kbound_fail}")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 200)
