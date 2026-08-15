#!/usr/bin/env python3
"""A2-grid engine sweep over the exact residual (M,k) pairs.

For every residual pair (e,f,M,k) of code/patch_results.txt (the
authoritative '== the exact residual ==' block, 178 cells), run the fixed
engine (code/swap_patch_search.py) in mode r{k-M}, chord=free, with the
theorem-backed A2 grid layer enabled:

  * base b-grid: sound at every scale (Inflation.b_side_rigid for k < f,
    RogueMirror.wall_base_reading for k = f);
  * BC a-grid: sound for k < f (a_side_rigid); at k = f only where the
    member's transverse branch is DEAD (engine A2 table) — gate
    A2_BCGRID_WALL, members (5,7) (6,7) (7,8) (8,9) among the residual.

Resumable: one result file per cell in code/a2_sweep/; cells with a
RESULT line are skipped, so the sweep can be re-launched at any time.
Parallel via multiprocessing, workers niced; PID 4842 untouched.
"""
import multiprocessing as mp
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(ROOT, "a2_sweep")
ENGINE = os.path.join(ROOT, "swap_patch_search.py")

# members whose transverse branch is DEAD with the A2 base grid
# (code/patch_results.txt, '== transverse, A2 base grid =='):
TRANSVERSE_DEAD = {(2, 3), (3, 4), (2, 5), (3, 5), (4, 5), (5, 6), (2, 7),
                   (3, 7), (5, 7), (6, 7), (7, 8), (2, 9), (8, 9)}


def residual_pairs(path):
    out = []
    in_block = False
    for line in open(path):
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


def run_cell(job):
    e, f, M, k, tcap, ncap = job
    os.nice(10)
    tag = f"{e}_{f}_M{M}_k{k}"
    path = os.path.join(OUT, tag + ".txt")
    if os.path.exists(path) and "RESULT" in open(path).read():
        return (tag, "skip")
    env = dict(os.environ, A2_GRIDS="1")
    if k == f and (e, f) in TRANSVERSE_DEAD:
        env["A2_BCGRID_WALL"] = "1"
    cmd = [sys.executable, ENGINE, "--fmax", str(f), "--mode", f"r{k - M}",
           "--chord", "free", "--only", f"{e},{f},{M}",
           "--time-cap", str(tcap), "--node-cap", str(ncap)]
    try:
        cp = subprocess.run(cmd, env=env, capture_output=True, text=True,
                            timeout=tcap * 3 + 120)
        body = cp.stdout + cp.stderr
    except subprocess.TimeoutExpired:
        body = "HARD-TIMEOUT"
    verdict = "?"
    m = re.search(r"M=\d+: (\w[\w-]*)", body)
    if m:
        verdict = m.group(1)
    with open(path, "w") as fh:
        fh.write(f"# cell ({e},{f}) M={M} k={k} r={k-M} tcap={tcap} "
                 f"bcwall={'A2_BCGRID_WALL' in env}\n")
        fh.write(body)
        fh.write(f"\nRESULT {verdict}\n")
    return (tag, verdict)


def main():
    tcap = float(sys.argv[1]) if len(sys.argv) > 1 else 240.0
    ncap = int(sys.argv[2]) if len(sys.argv) > 2 else 400000
    nw = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    os.makedirs(OUT, exist_ok=True)
    pairs = residual_pairs(os.path.join(ROOT, "patch_results.txt"))
    assert len(pairs) == 178, len(pairs)
    # cheap cells first (small f, small r)
    jobs = [(e, f, M, k, tcap, ncap)
            for (e, f, M, k) in sorted(pairs, key=lambda p: (p[1], p[3] - p[2]))]
    with mp.Pool(nw) as pool:
        for tag, v in pool.imap_unordered(run_cell, jobs):
            print(tag, v, flush=True)


if __name__ == "__main__":
    main()
