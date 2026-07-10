"""Parse a cengine tiling dump and reverify it with engine.py's independent checker."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from engine import QD, qd, reverify
from fractions import Fraction as F
import run_all

fn = sys.argv[1]
lines = open(fn).read().strip().split('\n')
name, N, D = lines[0].split()
N = int(N)
# map cengine instance names to run_all names/targets
def target_for(name):
    m = {'V1A': ('A', 2), 'V1B': ('B', 2), 'V1E': ('E', 2), 'V2B': ('B', 1), 'V2E': ('E', 1),
         'A': ('A', None), 'B': ('B', None), 'M56': ('M', None), 'M60': ('M60', None),
         'L105': ('L', None), 'N44A': ('N44A', None), 'I2': ('G', None)}
    rn, scale = m[name]
    tile, target, Nfull = run_all.make_instance(rn)
    if scale:
        cosA, sinA = tile.corners[0][0], tile.corners[0][1]
        target = run_all.tile_triangle(tile, cosA, sinA, scale)
    return tile, target
tile, target = target_for(name)
tiles = []
for ln in lines[1:]:
    v = ln.split()
    assert len(v) == 18
    pts = []
    for k in range(3):
        xp, xq, xd, yp, yq, yd = (int(t) for t in v[6*k:6*k+6])
        pts.append((qd(F(xp, xd), F(xq, xd)), qd(F(yp, yd), F(yq, yd))))
    tiles.append(pts)
assert len(tiles) == N, f"tile count {len(tiles)} != {N}"
ok, msg = reverify(tiles, target, tile)
print(f"cross-language reverify of {fn}: {ok} ({msg})")
