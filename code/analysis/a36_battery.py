#!/usr/bin/env python3
"""Examples battery (I7) and negative control (I13) for the wall b-count tool.

The tool (WallStraddle.b_on_both_sides_or_neither, and the sharper
b_counts_equal_horizontal) predicts: on a straight wall of length L inside the target, the two
sides' b-counts agree mod f, so an asymmetry forces the heavy side to carry >= f b-edges and hence
L >= f*b = f^3 - f.

interface_census.py already computes the two-sided edge words of every maximal interface in the
eight certificates. This checks the prediction against all of them. A violation would be a fatal
negative-control failure (I13); the bound being ATTAINED is the interesting outcome, since a bound
that is never tight is usually the wrong bound.
"""
import re, subprocess, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
out = subprocess.run([sys.executable, os.path.join(ROOT, 'code', 'interface_census.py')],
                     capture_output=True, text=True).stdout
f, a, b, c = 2, 2, 3, 4          # the certificates are the (1,2) family: f=2, tile (2,3,4)
thr = f ** 3 - f
cur, rows = None, []
for line in out.splitlines():
    line = line.strip()
    if line.startswith('=='):
        cur = line.split(':')[0].replace('== ', '').strip(); continue
    m = re.match(r'equation ([abc]+) = ([abc]+)\s+\(x(\d+)\)', line)
    if m:
        rows.append((cur, m.group(1), m.group(2)))
bad = tight = asym = 0
for cert, L, Rt in rows:
    nl, nr = L.count('b'), Rt.count('b')
    ln = L.count('a') * a + L.count('b') * b + L.count('c') * c
    rn = Rt.count('a') * a + Rt.count('b') * b + Rt.count('c') * c
    assert ln == rn, (cert, L, Rt)
    if (nl - nr) % f != 0:
        print(f"  MOD-f VIOLATION {cert} {L}={Rt}"); bad += 1
    if nl != nr:
        asym += 1
        if ln < thr: print(f"  BOUND VIOLATION {cert} {L}={Rt} len {ln} < {thr}"); bad += 1
        elif ln == thr: tight += 1
print(f"{len(rows)} interface equations, {asym} asymmetric, {bad} violations, "
      f"{tight} attaining the bound exactly")
sys.exit(1 if bad else 0)
