#!/usr/bin/env python3
"""T-vertex census on b-edge endpoints (Rule 3 falsification of rung S4').

S4' asked: does a b-edge's endpoints lie on the junction set of BOTH sides of its wall?  If so the
b-edges pair exactly (WallStraddle.b_pairs_at_common_junctions) and the crux's blocking
configuration would be pinned.  This checks the question against every interface of the eight
certificates.  Result: 58 of 60 fail, so S4' is FALSE and the locating approach dies with it.
"""
import re, subprocess, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
out = subprocess.run([sys.executable, os.path.join(ROOT, 'code', 'interface_census.py')],
                     capture_output=True, text=True).stdout
a, b, c = 2, 3, 4                      # the certificates are the (1,2) family
LEN = {'a': a, 'b': b, 'c': c}

def junctions(word):
    s, out = 0, {0}
    for ch in word:
        s += LEN[ch]; out.add(s)
    return out

cur, tot, bad = None, 0, 0
for line in out.splitlines():
    line = line.strip()
    if line.startswith('=='):
        cur = line.split(':')[0].replace('== ', '').strip(); continue
    m = re.match(r'equation ([abc]+) = ([abc]+)\s+\(x(\d+)\)', line)
    if not m:
        continue
    W1, W2 = m.group(1), m.group(2)
    J1, J2 = junctions(W1), junctions(W2)
    for word, far in ((W1, J2), (W2, J1)):
        s = 0
        for ch in word:
            if ch == 'b':
                tot += 1
                if s not in far or s + b not in far:
                    bad += 1
            s += LEN[ch]
print(f"b-edges examined: {tot}")
print(f"endpoints NOT both junctions on the far side: {bad}  ({100*bad/tot:.0f}%)")
print("S4' is FALSE" if bad else "S4' survives")
