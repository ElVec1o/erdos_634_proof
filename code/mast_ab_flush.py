#!/usr/bin/env python3
"""The mast's AB exit: exact solvability of  x·a + y·b + z·c = M·a, z ≥ 1.

The mast is the two-sided wall on the rogue's c-edge line (s = 0 in chord
coordinates); its right side starts with the rogue's c-edge, so a flush
termination at AB (height M·a) needs a word x·a + y·b + z·c = M·a with
z ≥ 1.  This script decides that equation exactly for every residual
(M,k) pair of code/patch_results.txt (parsed via zfan_residual's layers)
and for the two SURVIVES controls, and prints the closed-form predicate
it observes.  Exact integer arithmetic only.
"""
from math import gcd
import re
import sys


def residual_pairs(recert_path, fmax=12):
    """Parses the authoritative '== the exact residual ==' block of
    code/patch_results.txt -> [(e,f,M,k)]."""
    out = []
    in_block = False
    for line in open(recert_path):
        if line.startswith("== the exact residual"):
            in_block = True
            continue
        if in_block and line.startswith("=="):
            break
        if not in_block:
            continue
        m = re.match(r"\((\d+),(\d+)\): residual \(M,k\) pairs \[\d+\]: (.*)",
                     line)
        if not m:
            continue
        e, f = int(m.group(1)), int(m.group(2))
        for mk in re.findall(r"\((\d+),(\d+)\)\*?", m.group(3)):
            out.append((e, f, int(mk[0]), int(mk[1])))
    return out


def ab_flush_solvable(e, f, M):
    """x·a + y·b + z·c = M·a with x,y,z ≥ 0, z ≥ 1?  Returns witness or None."""
    a, b, c = e * f, f * f - e * e, f * f
    T = M * a
    for z in range(1, T // c + 1):
        r1 = T - z * c
        for y in range(0, r1 // b + 1):
            r2 = r1 - y * b
            if r2 % a == 0:
                return (r2 // a, y, z)
    return None


def main():
    recert = sys.argv[1] if len(sys.argv) > 1 else "code/patch_results.txt"
    pairs = residual_pairs(recert)
    assert len(pairs) == 178, len(pairs)
    controls = [(3, 10, 7, 10), (3, 11, 7, 10)]
    mism = 0
    print("# (e,f)  (M,k)  r  r>=e  fb<=Ma  AB-flush(x,y,z)|None   predicate-check")
    for tag, lst in (("residual", pairs), ("CONTROL", controls)):
        for (e, f, M, k) in lst:
            a, b = e * f, f * f - e * e
            w = ab_flush_solvable(e, f, M)
            pred = f * b <= M * a          # observed closed form: solvable iff fb <= Ma
            ok = (w is not None) == pred
            if not ok:
                mism += 1
            print(f"{tag} ({e},{f}) ({M},{k}) r={k-M} r>=e:{k-M>=e} "
                  f"fb<=Ma:{pred} flush:{w} pred-ok:{ok}")
    print(f"\npredicate 'solvable iff f·b <= M·a' mismatches: {mism}")
    # summary: how many residual pairs have NO AB flush (mast cannot exit AB)
    noexit = [(e, f, M, k) for (e, f, M, k) in pairs
              if ab_flush_solvable(e, f, M) is None]
    print(f"residual pairs with NO right-side AB flush: {len(noexit)} / 178")
    for q in noexit:
        print("   ", q)


if __name__ == "__main__":
    main()
