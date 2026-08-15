#!/usr/bin/env python3
"""Trace the transverse-branch forcing tree of swap_patch_search exactly.

Prints every DFS node: the pivot found, the options, each placement (tile
described by corner labels at points written in the frame P = B + x(-u) + y(-vh),
x = depth along AB from B, y = arc along BC direction), and each kill with its
site.  Landmarks: J_j = B + jc(-vh)  (BC grid), and points are shown as
(x, y) pairs in units of the tile sides where clean.
"""
import sys, os, importlib.util
from fractions import Fraction as Fr

HERE = "/Users/vico/Documents/elvec1o/ERDOS/634/code"
spec = importlib.util.spec_from_file_location("sps", os.path.join(HERE, "swap_patch_search.py"))
sps = importlib.util.module_from_spec(spec)
sys.modules["sps"] = sps
spec.loader.exec_module(sps)

def make_frame(G):
    f = G.f
    B = (Fr(f * G.c) * G.u[0], Fr(f * G.c) * G.u[1])
    mu = sps.neg(G.u)     # -u
    mv = sps.neg(G.vh)    # -vh
    # solve P - B = x*mu + y*mv  (2x2 over Q, chart coords)
    det = mu[0] * mv[1] - mu[1] * mv[0]
    def coords(P):
        rx, ry = P[0] - B[0], P[1] - B[1]
        x = (rx * mv[1] - ry * mv[0]) / det
        y = (mu[0] * ry - mu[1] * rx) / det
        return x, y
    return coords

def fmt_len(G, val):
    """Express val as combination shorthand of a,b,c if clean."""
    a, b, c = G.a, G.b, G.c
    names = {0: "0", a: "a", b: "b", c: "c", a + b: "a+b", a + c: "a+c",
             b + c: "b+c", 2 * a: "2a", 2 * b: "2b", 2 * c: "2c",
             c - b: "c-b", a - b: "a-b", c - a: "c-a", 2*c - b: "2c-b",
             3 * c: "3c", 2*a+b: "2a+b", a+2*b:"a+2b", c+b: "c+b",
             2*c+b:"2c+b", 3*b:"3b", a-2*b:"a-2b", c-2*b:"c-2b"}
    if val.denominator == 1 and int(val) in names:
        return names[int(val)]
    return str(val)

def describe_tile(G, coords, T):
    parts = []
    lab = {"A": "α", "B": "β", "G": "γ"}
    for P, L in zip(T.pts, T.labels):
        x, y = coords(P)
        parts.append(f"{lab[L]}@({fmt_len(G,x)},{fmt_len(G,y)})")
    return " ".join(parts)

def run(e, f, deep=True, maxnodes=100000):
    if deep:
        os.environ["TR_DEEP"] = "1"
    G = sps.Geo(e, f)
    coords = make_frame(G)
    S = sps.Search(G, 0, "tri", "grid", maxnodes, 80, 600.0)
    orig_dfs = sps.Search.dfs
    lines = []
    def dfs(self, P, depth):
        self.nodes += 1
        import time
        if self.nodes > self.node_cap or depth > self.depth_cap or \
           time.time() - self.t0 > self.time_cap:
            lines.append("  " * depth + "OPEN(caps)")
            return "OPEN"
        piv = self.find_pivot(P)
        ind = "  " * depth
        if piv is None:
            lines.append(ind + "SURVIVES")
            self.survivor = P
            return "SURVIVES"
        if piv[0] == "dead":
            kind, V = piv[1]
            x, y = coords(V)
            lines.append(ind + f"DEAD {kind} at ({fmt_len(G,x)},{fmt_len(G,y)})")
            key = str(piv[1])
            self.kill_reasons[key] = self.kill_reasons.get(key, 0) + 1
            return "KILLED"
        if piv[0] == "defer":
            lines.append(ind + "DEFER")
            return "OPEN"
        res = "KILLED"
        opts = list(piv[1])
        for i, T in enumerate(opts):
            lines.append(ind + f"[{i+1}/{len(opts)}] place {describe_tile(G, coords, T)}")
            P2 = P.clone()
            P2.add(T)
            r = dfs(self, P2, depth + 1)
            if r == "SURVIVES":
                return "SURVIVES"
            if r == "OPEN":
                res = "OPEN"
        return res
    sps.Search.dfs = dfs
    try:
        import time
        S.t0 = time.time()
        P0 = S.seed_transverse()
        lines.append(f"SEED {describe_tile(G, coords, P0.tiles[0])}")
        verdict = dfs(S, P0, 0)
    finally:
        sps.Search.dfs = orig_dfs
    print(f"=== ({e},{f}) transverse trace: {verdict} nodes={S.nodes} "
          f"a={G.a} b={G.b} c={G.c} ===")
    print("\n".join(lines))

if __name__ == "__main__":
    for arg in sys.argv[1:]:
        e, f = map(int, arg.split(","))
        run(e, f)
