#!/usr/bin/env python3
"""Orientation census of the a-tiles a refutation lays on the run line (Erdos #634, e=1).

Runs the engine under CENGINE_TRACE=2, which prints one line per *recursed* placement as exact
(p + q*sqrt(D))/d coordinate pairs, and classifies every tile that lays an a-edge on the run line
by its apex's horizontal offset from the edge's left end:

    dBG = (3f^2 - 1) / 2f     beta at the left end
    dGB = (1 - f^2) / 2f      gamma at the left end   (negative: the apex overhangs left)

Usage:  run_orientation.py <f> <bp> <cp> [engine] [cap]

Regenerates from scratch, so the reported table is reproducible (Rule 9).
"""
import os, re, subprocess, sys
from fractions import Fraction as F

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def parse_vertex(tok):
    n = [int(x) for x in re.findall(r'-?\d+', tok)]
    return (F(n[0], n[2]), F(n[1], n[2]), F(n[3], n[5]), F(n[4], n[5]))


def census(trace_path, f):
    dBG, dGB = F(3 * f * f - 1, 2 * f), F(1 - f * f, 2 * f)
    rows = []
    for line in open(trace_path):
        if not line.startswith('T '):
            continue
        parts = line.split(None, 2)
        verts = [parse_vertex(v) for v in re.findall(r'\([^)]*\)', parts[2])]
        # a-tile laid on the run line: two vertices at y = 0, exactly f apart in x
        base = [v for v in verts if v[2] == 0 and v[3] == 0 and v[1] == 0]
        if len(base) != 2:
            continue
        xs = sorted(v[0] for v in base)
        if xs[1] - xs[0] != f:
            continue
        apex = [v for v in verts if not (v[2] == 0 and v[3] == 0)]
        if len(apex) != 1:
            continue
        off = apex[0][0] - xs[0]
        rows.append((parts[1], xs[0],
                     'BG' if off == dBG else ('GB' if off == dGB else 'other(%s)' % off)))
    return rows, dBG, dGB


def main():
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    f, bp, cp = (int(x) for x in sys.argv[1:4])
    engine = sys.argv[4] if len(sys.argv) > 4 else os.path.join(ROOT, 'private/bin/cengine_rx2')
    cap = sys.argv[5] if len(sys.argv) > 5 else '50000000'
    work = os.path.join(ROOT, 'private/inst')
    inst = os.path.join(work, 'uni_f%d_b%dc%d.txt' % (f, bp, cp))
    if not os.path.exists(inst):
        with open(inst, 'w') as fh:
            subprocess.run([sys.executable, os.path.join(ROOT, 'code/engine/gen_basebeta.py'),
                            '1', str(f), str(bp), str(cp)], stdout=fh, check=True)
    trace = os.path.join(work, '.orient_f%d_b%dc%d.trace' % (f, bp, cp))
    env = dict(os.environ, CENGINE_TRACE='2', CENGINE_GEN='1', CENGINE_THREADS='1')
    with open(trace, 'w') as th:
        out = subprocess.run([engine, 'FILE:' + inst, cap], env=env, cwd=work,
                             stdout=subprocess.PIPE, stderr=th).stdout.decode()
    verdict = re.search(r'RESULT [A-Z_]+ nodes=\d+', out)
    rows, dBG, dGB = census(trace, f)
    counts = {}
    for _, _, o in rows:
        counts[o] = counts.get(o, 0) + 1
    print('f=%d (%d,%d): %s' % (f, bp, cp, verdict.group(0) if verdict else 'NO RESULT'))
    print('  dBG=%s  dGB=%s' % (dBG, dGB))
    print('  a-tiles laid on the run line: %d   orientations: %s' % (len(rows), counts))
    for p, t, o in rows[:12]:
        print('     %-26s left=%-6s %s' % (p, t, o))


if __name__ == '__main__':
    main()
