#!/usr/bin/env python3
"""Per-pair closure: for a slot (e,f,M) at scale k = M+r, run the patch engine
once per 1D-surviving chord-word pair, with the chord discipline pinned to that
pair. The slot is closed at that scale iff every pair is KILLED.
Usage: per_pair.py e f M r [time_cap]"""
from fractions import Fraction as Fr
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from swap_patch_search import (Geo, Patch, Search, place_tile, addm, sub,
                               cross, neg, canon_dir, line_key, dot)
import rogue_chord_survivors as rcs

def run_pair(e, f, M, r, wr, ws, tcap):
    G = Geo(e, f)
    a, b, c = G.a, G.b, G.c
    S = Search(G, M, f"r{r}", "pair", 1500000, 100, tcap)
    P0 = S.seed()          # seeds with chord=None (chordmode 'pair' != 'swap')
    # build the pair discipline
    lens = {"a": a, "b": b, "c": c}
    pq = canon_dir(G.vh)
    dd = (Fr(pq[0]), Fr(pq[1]))
    Y = (Fr(M * b), Fr(0))
    scale = dot(G, G.vh, dd)
    tY = dot(G, Y, dd)
    arc = lambda P: (dot(G, P, dd) - tY) / scale
    rowside = 1 if cross(dd, sub((Fr(0), Fr(0)), Y)) > 0 else -1
    def cuts(word):
        out, s = [], 0
        for x in word:
            out.append((Fr(s), Fr(s + lens[x])))
            s += lens[x]
        return out
    L = sum(lens[x] for x in wr)
    allowed = {rowside: set(cuts(wr)), -rowside: set(cuts(ws))}
    P0.chord = {"lk": line_key(Y, G.vh), "dd": dd, "arc": arc,
                "L": Fr(L), "allowed": allowed}
    S.t0 = time.time()
    return S.dfs(P0, 0), S.nodes

if __name__ == "__main__":
    e, f, M, r = map(int, sys.argv[1:5])
    tcap = float(sys.argv[5]) if len(sys.argv) > 5 else 240.0
    a, b, c = e * f, f * f - e * e, f * f
    n1, a1, b1, kept, Lv = rcs.enumerate_pairs(a, b, c, M * a, keep=100000)
    print(f"({e},{f}) M={M} r={r}: {a1} 1D pairs to test")
    verdicts = {}
    for (L, wr, ws) in kept:
        v, nodes = run_pair(e, f, M, r, wr, ws, tcap)
        verdicts[v] = verdicts.get(v, 0) + 1
        tag = "" if v == "KILLED" else f"   <-- {v}: R={'.'.join(wr)} S={'.'.join(ws)} L={L}"
        if v != "KILLED":
            print(f"  {v} [n={nodes}]{tag}")
    print(f"({e},{f}) M={M} r={r} per-pair: {verdicts}")
    print("SLOT CLOSED" if set(verdicts) == {"KILLED"} else "SLOT NOT CLOSED")
