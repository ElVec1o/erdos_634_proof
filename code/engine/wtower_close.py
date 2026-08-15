#!/usr/bin/env python3
"""wtower_close.py -- close residual W-tower steps by the enum recipe.

For each target (e, f, k) the recipe of the (6,7) closure (patch_results.txt,
'DEFINITIVELY CLOSED' block) is run mechanically:

  1. every deviant c-side word (qf, 0, k-qe), q >= 1, is exhausted
     (cengine_lifo; base and a-side words are theorems at every scale);
  2. at k = f, the transverse a-side word c^e is exhausted too, unless the
     member is already on the transverse-dead list;
  3. the standard-boundary instance is enumerated to exhaustion with
     cengine_enum (env ENUM_ALL): the verdict must be EXHAUSTED_ENUM found=1
     and the unique tiling must equal the standard subdivision exactly
     (rational set comparison against the lattice built from the instance's
     own corners).

A target is CLOSED when all three hold; any other outcome is recorded and the
target is left OPEN.  Resumable: verdict files in private/wtower/; a target
with a VERDICT line is skipped.  Workers are niced; the long-running N=83
search (separate binary, separate instance) is not touched.
"""
import multiprocessing as mp
import os
import re
import subprocess
import sys
from fractions import Fraction as F

ROOT = os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))))   # repo root
ENG_DIR = os.path.join(ROOT, "code", "engine")
OUT = os.path.join(ROOT, "private", "wtower")
SCRATCH = ("/private/tmp/claude-501/-Users-vico-Documents-elvec1o-ERDOS-634/"
           "57444d33-c266-44bb-9eea-8ade695f4bf7/scratchpad")
LIFO = os.path.join(SCRATCH, "cengine_lifo")
ENUM = os.path.join(SCRATCH, "cengine_enum")

TRANSVERSE_DEAD = {(2, 3), (3, 4), (2, 5), (3, 5), (4, 5), (5, 6), (2, 7),
                   (3, 7), (5, 7), (6, 7), (7, 8), (2, 9), (8, 9)}


def gen(e, f, k, cw, aw, bw, path):
    r = subprocess.run([sys.executable, os.path.join(ENG_DIR, "gen_scale.py"),
                        str(e), str(f), str(k),
                        ",".join(map(str, cw)), ",".join(map(str, aw)),
                        ",".join(map(str, bw))],
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"gen_scale failed: {r.stderr[:200]}")
    open(path, "w").write(r.stdout)


def run_engine(binary, inst, tag, enum=False, timeout=14400):
    env = dict(os.environ)
    if enum:
        env["ENUM_ALL"] = "1"
    base = os.path.basename(inst)
    r = subprocess.run(["nice", "-n", "12", binary, f"FILE:{base}",
                        "1000000000000", f"{base}.ck"],
                       capture_output=True, text=True, timeout=timeout,
                       cwd=os.path.dirname(inst), env=env)
    m = re.search(r"RESULT (\S+)(.*)", r.stdout)
    return (m.group(1), m.group(0).strip()) if m else ("NO-RESULT", r.stdout[-200:])


def load_tiling(path):
    toks = open(path).read().split()
    N = int(toks[1])
    rest = toks[3:]
    tris, i = set(), 0
    for _ in range(N):
        vs = []
        for _v in range(3):
            p, q, r, s, t, u = (int(rest[i + j]) for j in range(6))
            i += 6
            vs.append((F(p, r), F(t, u)))
        tris.add(frozenset(vs))
    return N, tris


def standard_subdivision(inst_path, k):
    lines = [l.split() for l in open(inst_path).read().splitlines()]
    # vertices are the three lines after the N line: p q r  s t u
    nidx = next(i for i, l in enumerate(lines) if len(l) == 1 and l[0].isdigit()
                and i >= 6)
    vs = []
    for l in lines[nidx + 1:nidx + 4]:
        p, q, r, s, t, u = (int(x) for x in l)
        vs.append((F(p, r), F(t, u)))
    A, B, C = vs
    v1 = ((B[0] - A[0]) / k, (B[1] - A[1]) / k)
    v2 = ((C[0] - A[0]) / k, (C[1] - A[1]) / k)
    P = lambda i, j: (A[0] + i * v1[0] + j * v2[0], A[1] + i * v1[1] + j * v2[1])
    std = set()
    for j in range(k):
        for i in range(k - j):
            std.add(frozenset([P(i, j), P(i + 1, j), P(i, j + 1)]))
            if i + j <= k - 2:
                std.add(frozenset([P(i + 1, j), P(i, j + 1), P(i + 1, j + 1)]))
    return std


def close_target(job):
    e, f, k = job
    os.nice(5)
    tag = f"{e}_{f}_k{k}"
    vfile = os.path.join(OUT, f"{tag}.txt")
    if os.path.exists(vfile) and "VERDICT" in open(vfile).read():
        return tag, "SKIP"
    lines = []
    ok = True
    # 1. c-side deviants
    q = 1
    while k - q * e >= 0:
        cw = (q * f, 0, k - q * e)
        inst = os.path.join(OUT, f"inst_{tag}_q{q}.txt")
        gen(e, f, k, cw, (k, 0, 0) if k < f else (f, 0, 0), (0, k, 0), inst)
        v, full = run_engine(LIFO, inst, tag)
        lines.append(f"cside q={q} {cw}: {full}")
        if v != "EXHAUSTED_NO_TILING":
            ok = False
        q += 1
    # 2. transverse at wall scale
    if k == f and (e, f) not in TRANSVERSE_DEAD:
        inst = os.path.join(OUT, f"inst_{tag}_trans.txt")
        gen(e, f, k, (0, 0, f), (0, 0, e), (0, f, 0), inst)
        v, full = run_engine(LIFO, inst, tag)
        lines.append(f"transverse a-side c^e: {full}")
        if v != "EXHAUSTED_NO_TILING":
            ok = False
    # 3. enum the standard instance
    inst = os.path.join(OUT, f"inst_{tag}_std.txt")
    gen(e, f, k, (0, 0, k), (k, 0, 0), (0, k, 0), inst)
    v, full = run_engine(ENUM, inst, tag, enum=True)
    lines.append(f"standard enum: {full}")
    unique_std = False
    if v == "EXHAUSTED_ENUM":
        n = int(re.search(r"found=(\d+)", full).group(1))
        if n == 1:
            dump = os.path.join(OUT, f"tiling_FILE_inst_{tag}_std.txt_enum1.txt")
            if os.path.exists(dump):
                _, tris = load_tiling(dump)
                unique_std = tris == standard_subdivision(inst, k)
                lines.append(f"unique tiling == standard subdivision: {unique_std}")
        else:
            lines.append(f"found={n} != 1")
    ok = ok and unique_std
    verdict = "CLOSED" if ok else "OPEN"
    with open(vfile, "w") as fh:
        fh.write(f"# W-tower target ({e},{f}) k={k}\n")
        for l in lines:
            fh.write(l + "\n")
        fh.write(f"VERDICT {verdict}\n")
    return tag, verdict


def main():
    os.makedirs(OUT, exist_ok=True)
    work = [tuple(int(x) for x in l.split())
            for l in open(sys.argv[1]).read().splitlines() if l.strip()]
    # smallest instances first: cheap wins early, heavy k=11,12 last
    work.sort(key=lambda t: (t[2], t[1]))
    with mp.Pool(int(os.environ.get("WORKERS", "6"))) as pool:
        for tag, verdict in pool.imap_unordered(close_target, work):
            print(f"{tag}: {verdict}", flush=True)


if __name__ == "__main__":
    main()
