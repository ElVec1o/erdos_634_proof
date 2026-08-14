#!/usr/bin/env python3
"""Instance for the tile at (e,f) inflated by an ARBITRARY scale k, tiled by k^2 copies.

gen_inflation.py is the k = f special case and additionally hard-codes the a-side word to a^f.
Both restrictions are removed here: the scale is a parameter, and all three side words are given
explicitly.  Two things this is needed for.

  * The sub-scale crux.  For k < f the c-side is not forced either: its words are (p*f, 0, k - p*e)
    for p = 0 .. floor((k-2)/e), so the p=0/p>=1 dichotomy that thm:inflrigid decides at k=f exists
    at every scale k >= e+2.  The cheapest instance of the crux is therefore k = e+2, on (e+2)^2
    tiles rather than f^2 -- at (3,7) that is 25 tiles and 16 nodes against 49 tiles and 57824.

  * The transverse beta-corner branch.  Inflation.a_side_all_c shows the a-side of a scale-k
    inflation may be c^{k e / f} instead of a^k, which in the range k <= f happens only at k = f.
    gen_inflation.py cannot express that word.

Usage:  gen_scale.py e f k  <c-word> <a-word> <b-word>      (words as na,nb,nc)
        gen_scale.py --selftest

Self-test: at k = f with the standard a- and b-words it must reproduce gen_inflation.py exactly,
which in turn reproduces the hand-built (3,7) instances byte for byte.
"""
import sys, os, importlib.util

_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("gen_inflation", os.path.join(_here, "gen_inflation.py"))
_gi = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(_gi)
qd, squarefree = _gi.qd, _gi.squarefree


def instance(e, f, k, cword, aword, bword):
    a, b, c = e*f, f*f - e*e, f*f
    D, S = squarefree(4*f*f - e*e)
    L = [f"{D}", f"{a} {b} {c}"]
    L.append(f"{qd(2*f*f - e*e, 0, 2*f*f)}  {qd(0, e*S, 2*f*f)}")
    L.append(f"{qd(e*(3*f*f - e*e), 0, 2*f**3)}  {qd(0, (f*f - e*e)*S, 2*f**3)}")
    L.append(f"{qd(-e, 0, 2*f)}  {qd(0, S, 2*f)}")
    L.append(qd(0, e*(f*f - e*e)*S, 2))            # doubled area of the UNIT tile
    L.append(f"{k*k}")
    L.append(f"{qd(0,0,1)}  {qd(0,0,1)}")
    L.append(f"{qd(k*c,0,1)}  {qd(0,0,1)}")
    # x = ((kc)^2 + (kb)^2 - (ka)^2)/(2kc);  y = 2*Area(T_k)/(kc)
    L.append(f"{qd(k*(c*c + b*b - a*a), 0, 2*c)}  {qd(0, k*k*e*(f*f - e*e)*S, 2*k*c)}")
    L.append("WALKS 0 1")
    L.append("  %d %d %d" % tuple(cword))
    L.append("2")
    L.append("  %d %d %d" % tuple(bword))
    L.append("  %d %d %d" % tuple(aword))
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        ok = True
        for (e, f, p) in [(3,7,1), (3,7,0), (2,5,1), (2,5,0), (1,3,1), (4,9,1)]:
            w = (f, 0, f - e) if p == 1 else (0, 0, f)
            got = instance(e, f, f, w, (f, 0, 0), (0, f, 0))
            ref = _gi.instance(e, f, w)
            same = got.split() == ref.split()
            print(f"  ({e},{f}) p={p}: {'MATCH' if same else 'MISMATCH'} vs gen_inflation")
            ok &= same
        sys.exit(0 if ok else 1)
    e, f, k = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    W = [tuple(int(x) for x in s.split(',')) for s in sys.argv[4:7]]
    sys.stdout.write(instance(e, f, k, W[0], W[1], W[2]))
