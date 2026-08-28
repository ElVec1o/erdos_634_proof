#!/usr/bin/env python3
"""Exact verification of the ladder invariant (Rule 9 reproduction).

Claim: along the mirrored-branch march of a (bp,2)-seeded refutation, each block's c-edge carries
the previous block's apex as a T-vertex at parameter EXACTLY b/c, in Q(sqrt(D)) arithmetic, no
floats.  Requires trace files produced by:
    CENGINE_TRACE=2 CENGINE_THREADS=1 <engine> FILE:uni_f{f}_b4c2.txt 200000 2> /tmp/tree_f{f}g.txt
"""
import re, sys
from fractions import Fraction as F

CASES = {6: ('2.3.1.2.4.0.2.2', '2.3.1.2.4.0.2.2.0.2.0'),
         7: ('2.3.1.2.4.0.2.2.1.2', '2.3.1.2.4.0.2.2.1.2.0.2.0')}

def parse(f):
    T = {}
    for l in open(f'/tmp/tree_f{f}g.txt'):
        if not l.startswith('T '):
            continue
        parts = l.split(None, 2)
        c = re.findall(r'\(([-\d]+) ([-\d]+) ([-\d]+) \| ([-\d]+) ([-\d]+) ([-\d]+)\)', l)
        T[parts[1]] = [((F(int(a), int(cc)), F(int(b), int(cc))),
                        (F(int(d), int(ff)), F(int(e), int(ff)))) for a, b, cc, d, e, ff in c]
    return T

ok = True
for f, (atile, p2) in CASES.items():
    try:
        T = parse(f)
    except FileNotFoundError:
        print(f"f={f}: trace missing, run the engine with CENGINE_TRACE=2 first"); ok = False
        continue
    b, c = f * f - 1, f * f
    V, pin, tip = T[atile][2], T[p2][0], T[p2][2]
    lhs = tuple((V[i][j] - pin[i][j]) for i in range(2) for j in range(2))
    rhs = tuple(F(b, c) * (tip[i][j] - pin[i][j]) for i in range(2) for j in range(2))
    good = lhs == rhs
    ok &= good
    print(f"f={f}: apex == pin + ({b}/{c})*(ctip - pin)  ->  {'EXACT' if good else 'FAIL'}")
sys.exit(0 if ok else 1)
