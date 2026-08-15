#!/usr/bin/env python3
"""A2: the wall-scale base family of the scale-f inflation, engine campaign.

At k = f the base (B-side) equation n_a*a + n_b*b + n_c*c = f*b admits, besides
b^f, exactly the family n_a = (j+1)f - e, n_b = 0, n_c = f - (j+1)e for
0 <= j <= f/e - 1 (RogueMirror.base_side_wall_family).  The geometric kill
(RogueMirror.wall_base_reading, 2026-08-15) is: the region's c-side has length
f*c = f^3, the same walk equation as the m = 1 equal side, so the gamma-trap
plus SideNoB.side_no_b_uncond make it b-free; the single alpha-corner tile must
then lay its b-flank on the base; and one b on the base forces b^f
(wall_base_dichotomy).

This driver verifies the kill member by member with the inflation engine: for
every coprime (e,f), f in [FLO, FHI], and every family word q = j+1, it builds
the scale-f instance with

  * the B-side pinned to the family word (the hypothesis under test),
  * the c-side FREE over ALL length-admissible words -- the b-carrying word
    (e, f, 0) included, so the gamma-trap is NOT assumed,
  * the a-side FREE over both its words a^f and c^e -- the transverse branch
    is NOT excluded,

and expects EXHAUSTED_NO_TILING; q = 0 is the positive control (B-side free
over ALL its words) and must return FOUND_TILING.  A FOUND at any q >= 1
would REFUTE wall_base_reading's geometric steps.

Usage: a2_wall_family.py [FLO FHI [CAP]]     (default 2 9 2e9)
Requires a built cengine_lifo; set CENGINE to its path.

2026-08-15 campaign (f <= 9, 55 family instances + 20 controls): every family
instance EXHAUSTED, every control FOUND; kill is local (<= 3000 nodes at every
member except the (2,7)/(2,9) controls).  Results: code/a2_results.txt.
"""
import os, subprocess, sys, tempfile
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "engine"))
import importlib.util
_spec = importlib.util.spec_from_file_location(
    "gen_inflation", os.path.join(HERE, "engine", "gen_inflation.py"))
_gi = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(_gi)
qd, squarefree = _gi.qd, _gi.squarefree

CENGINE = os.environ.get("CENGINE", os.path.join(HERE, "engine", "cengine"))


def words(a, b, c, L):
    out = []
    for nb in range(L // b + 1):
        for nc in range((L - nb * b) // c + 1):
            r = L - nb * b - nc * c
            if r % a == 0:
                out.append((r // a, nb, nc))
    return out


def instance(e, f, q):
    a, b, c = e * f, f * f - e * e, f * f
    D, S = squarefree(4 * f * f - e * e)
    L = [f"{D}", f"{a} {b} {c}"]
    L.append(f"{qd(2*f*f - e*e, 0, 2*f*f)}  {qd(0, e*S, 2*f*f)}")
    L.append(f"{qd(e*(3*f*f - e*e), 0, 2*f**3)}  {qd(0, (f*f - e*e)*S, 2*f**3)}")
    L.append(f"{qd(-e, 0, 2*f)}  {qd(0, S, 2*f)}")
    L.append(qd(0, e * (f * f - e * e) * S, 2))
    L.append(f"{f*f}")
    L.append(f"{qd(0,0,1)}  {qd(0,0,1)}")
    L.append(f"{qd(f*c,0,1)}  {qd(0,0,1)}")
    L.append(f"{qd(f*(c*c + b*b - a*a), 0, 2*c)}  {qd(0, f*f*e*(f*f - e*e)*S, 2*f*c)}")
    cwords = words(a, b, c, f * c)
    awords = words(a, b, c, f * a)
    if q == 0:
        bwords = words(a, b, c, f * b)
    else:
        assert 1 <= q <= f // e and f - q * e >= 0
        bwords = [(q * f - e, 0, f - q * e)]
    swords = bwords + awords
    L.append(f"WALKS 0 {len(cwords)}")
    for w in cwords:
        L.append("  %d %d %d" % w)
    L.append(f"{len(swords)}")
    for w in swords:
        L.append("  %d %d %d" % w)
    return "\n".join(L) + "\n"


def main():
    flo = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    fhi = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    cap = int(float(sys.argv[3])) if len(sys.argv) > 3 else 2000000000
    bad = 0
    for f in range(flo, fhi + 1):
        for e in range(1, f):
            if gcd(e, f) != 1:
                continue
            for q in range(0, f // e + 1):
                if q >= 1 and f - q * e < 0:
                    continue
                with tempfile.NamedTemporaryFile("w", suffix=".txt",
                                                 delete=False) as fh:
                    fh.write(instance(e, f, q))
                    path = fh.name
                out = subprocess.run(
                    ["nice", "-n", "19", CENGINE, f"FILE:{path}", str(cap)],
                    capture_output=True, text=True).stdout
                res = [l for l in out.splitlines() if l.startswith("RESULT")]
                res = res[0] if res else "RESULT ???"
                want = "FOUND_TILING" if q == 0 else "EXHAUSTED_NO_TILING"
                ok = want in res
                bad += 0 if ok else 1
                print(f"({e},{f}) q={q}  {res}  "
                      f"[{'ok' if ok else 'UNEXPECTED'}]")
                sys.stdout.flush()
                os.unlink(path)
    print(f"unexpected verdicts: {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
