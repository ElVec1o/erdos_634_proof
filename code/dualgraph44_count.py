"""Reproducible check of `rem:spectral`'s dual-graph claim about the certified 44-tiling.

Reads Tiling44.lean's `def tiles` list literal directly (exact Z[sqrt15] integer coordinates,
no floating point for the edge computation) and computes, under the strict "shares a full edge"
adjacency (both endpoints of one tile's edge equal both endpoints of another's):
  - vertex count (= tile count, 44)
  - number of shared full edges
  - degree distribution
  - connected components

Usage: python3 code/dualgraph44_count.py
"""
import re
from collections import defaultdict, Counter

def load_tiles(path='lean/Erdos634/Tiling44.lean'):
    src = open(path).read()
    m = re.search(r'def tiles : List Tri := \[(.*?)\]\n', src, re.S)
    body = m.group(1)
    tuples = re.findall(r'\(([^()]*)\)', body)
    pts = [tuple(int(x) for x in t.split(',')) for t in tuples]
    assert len(pts) % 3 == 0
    return [tuple(pts[i:i+3]) for i in range(0, len(pts), 3)]

def edges(tri):
    a, b, c = tri
    return [frozenset([a, b]), frozenset([b, c]), frozenset([a, c])]

def main():
    tris = load_tiles()
    n = len(tris)
    edge_owner = defaultdict(list)
    for i, t in enumerate(tris):
        for e in edges(t):
            edge_owner[e].append(i)
    mult = Counter(len(v) for v in edge_owner.values())
    assert mult[2] and all(k in (1, 2) for k in mult), f"unexpected multiplicity {mult}"
    shared = {e: v for e, v in edge_owner.items() if len(v) == 2}
    adj = defaultdict(set)
    for (i, j) in shared.values():
        adj[i].add(j); adj[j].add(i)
    deg = [len(adj[i]) for i in range(n)]
    seen, comps = set(), []
    for i in range(n):
        if i in seen: continue
        stack, comp = [i], set()
        while stack:
            x = stack.pop()
            if x in comp: continue
            comp.add(x)
            stack.extend(adj[x] - comp)
        seen |= comp
        comps.append(sorted(comp))
    print(f"tiles (dual-graph vertices): {n}")
    print(f"shared full edges: {len(shared)}")
    print(f"degree distribution: {sorted(Counter(deg).items())}")
    print(f"components: {len(comps)}, sizes {sorted(len(c) for c in comps)}")

if __name__ == '__main__':
    main()
