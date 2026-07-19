#!/usr/bin/env python3
"""
Apex obstruction (Erdos #634, isosceles 2pi/3 tile).

The apex of iso-alpha=(alpha,alpha,alpha+3beta) has angle alpha+3beta = pi-2alpha, vertex type
(1,3,0): exactly 4 tiles with apex-angles {alpha,beta,beta,beta}.  The two equal sides meeting at
the apex are forced pure-c, so the two OUTER spokes are c-edges.

At a tile's apex-vertex the two incident sides are the FLANKS of that angle:
   alpha-vertex -> {b,c};   beta-vertex -> {a,c}.
So EVERY apex tile has exactly one c-edge at the apex.  In an EDGE-TO-EDGE fan the 5 spokes
s0..s4 are single shared lengths with s0=s4=c, and each tile Ti has {s_{i-1},s_i} = its flank set.

THEOREM: there are 0 such edge-to-edge configurations -> no isosceles 2pi/3 tiling is edge-to-edge
at the apex.  (Not prime-specific; evaded by a T-junction since c>a,b.)
"""
from itertools import product

def flanks(angle):           # sides incident to the apex-vertex angle
    return {'b','c'} if angle=='alpha' else {'a','c'}

def count_e2e_apex(apex_alpha_count):
    """edge-to-edge apex configs with exactly `apex_alpha_count` alpha-tiles among 4."""
    n=0; examples=[]
    for angles in product(['alpha','beta'], repeat=4):
        if angles.count('alpha')!=apex_alpha_count: continue
        for s in product(['a','b','c'], repeat=5):
            if s[0]!='c' or s[4]!='c': continue
            if all({s[i],s[i+1]}==flanks(angles[i]) for i in range(4)):
                n+=1; examples.append((angles,s))
    return n, examples

# iso-alpha apex = type (1,3,0): one alpha
na,_=count_e2e_apex(1)
print(f"iso-alpha apex (type 1,3,0): edge-to-edge configurations = {na}")
# iso-beta apex = type (3,1,0): one beta  (mirror: swap roles of a<->b in flanks)
def flanks_b(angle):
    return {'a','c'} if angle=='alpha' else {'b','c'}
nb=0
for angles in product(['alpha','beta'],repeat=4):
    if angles.count('beta')!=1: continue
    for s in product(['a','b','c'],repeat=5):
        if s[0]!='c' or s[4]!='c': continue
        if all({s[i],s[i+1]}==flanks_b(angles[i]) for i in range(4)):
            nb+=1; break
print(f"iso-beta  apex (type 3,1,0): edge-to-edge configurations = {nb}")
print()
print("THEOREM (verified): no isosceles 2pi/3 tiling is edge-to-edge at the apex.")
print("Caveat: NOT prime-specific (shape-only); evaded by a T-junction (c=259 > a=155,b=144),")
print("so it forces non-edge-to-edge at the apex but does not forbid a tiling.")
