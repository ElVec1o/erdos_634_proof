#!/usr/bin/env python3
"""Coverage certificate for an e=1 sweep: every escaping base word is exhausted, or its mirror is.

    verify_sweep.py f log [log ...]

Parses `f=<f> (bp,cp): RESULT EXHAUSTED...` lines, and `=== (bp,cp) started ===` blocks followed by
a RESULT line, and bare `(bp,cp): RESULT ...` lines.  Prints PASS only if the exhausted set together
with its mirror images covers every escape at the proved reach.

This exists because three of the four completed sweeps had silently dropped exactly one orbit: the
drivers fed their instance list to `while read`, which discards a final line with no newline.
"""
import re
import sys

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from sweep_configs import escapes, mirror, transversal


def parse(f, paths):
    ok = set()
    for p in paths:
        s = open(p, errors='ignore').read()
        for m in re.finditer(r'f=%d \((\d+),(\d+)\)[^\n]*RESULT EXHAUSTED' % f, s):
            ok.add((int(m.group(1)), int(m.group(2))))
        cur = None
        for line in s.splitlines():
            m = re.match(r'=== \((\d+),(\d+)\) started', line)
            if m:
                cur = (int(m.group(1)), int(m.group(2)))
            m = re.match(r'\((\d+),(\d+)\):[^\n]*RESULT EXHAUSTED', line)
            if m:
                ok.add((int(m.group(1)), int(m.group(2))))
            elif 'RESULT EXHAUSTED' in line and cur:
                ok.add(cur)
    return ok


if __name__ == '__main__':
    f = int(sys.argv[1])
    ok = parse(f, sys.argv[2:])
    for R in (4, 5):
        E = escapes(f, R)
        cov = ok | {mirror(f, w) for w in ok}
        miss = sorted(E - cov)
        print(f"f={f} N={3*f*f-1} reach={R-1} (R={R})  escapes={len(E)} orbits={len(transversal(f, R))}"
              f"  exhausted={len(ok)}  {'PASS' if not miss else 'FAIL missing ' + str(miss)}")
