"""Emit an exact instance file from run_all.make_instance, so cengine and engine.py
run bit-identical instances (no re-implementation of the number theory in C++)."""
import sys, os
sys.path.insert(0,'/Users/vico/Documents/elvec1o/MATH_PAPER_3/634/engine')
from engine import QD
import run_all

def qd_triple(x):
    return f"{x.pn} {x.qn} {x.den}"

nm = sys.argv[1]; out = sys.argv[2]
tile, target, N = run_all.make_instance(nm)
L=[]
L.append(str(QD.D))
L.append(f"{tile.a} {tile.b} {tile.c}")
for (cs, sn, pairs) in tile.corners:
    L.append(qd_triple(cs) + "  " + qd_triple(sn))
L.append(qd_triple(tile.area2))
L.append(str(N))
for (x,y) in target:
    L.append(qd_triple(x) + "  " + qd_triple(y))
open(out,'w').write("\n".join(L)+"\n")
print(f"wrote {out}: {nm} D={QD.D} tile=({tile.a},{tile.b},{tile.c}) N={N}")
