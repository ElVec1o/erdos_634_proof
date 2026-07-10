#!/usr/bin/env python3
"""
Validation battery + the four frontier instances.
Usage:
  python3 run_all.py validate          # V1-V4 (must all pass)
  python3 run_all.py A|B|D|E           # run one instance to exhaustion
"""
import sys, time, json
from fractions import Fraction
import engine
from engine import QD, qd, Tile, Search, poly_area2, reverify


def make_instance(name):
    F = Fraction
    if name in ('A', 'B'):
        QD.D = 3
        if name == 'A':
            a, b, c, N, S = 7, 8, 13, 14, 28
        else:
            a, b, c, N, S = 3, 5, 7, 15, 15
        cosA, sinA = qd(F(2 * b + a, 2 * c)), qd(0, F(a, 2 * c))
        cosB, sinB = qd(F(2 * a + b, 2 * c)), qd(0, F(b, 2 * c))
        cosC, sinC = qd(F(-1, 2)), qd(0, F(1, 2))
        tile = Tile(a, b, c, cosA, sinA, cosB, sinB, cosC, sinC)
        tile.area2 = qd(0, F(a * b, 2))              # a*b*sin(2pi/3) = ab*(1/2)*sqrt3
        target = [(qd(0), qd(0)), (qd(S), qd(0)), (qd(F(S, 2)), qd(0, F(S, 2)))]
        return tile, target, N
    if name == 'D':
        QD.D = 23
        a, b, c, N = 56, 15, 64, 15
        tile = Tile(a, b, c,
                    qd(F(79, 128)), qd(0, F(21, 128)),
                    qd(F(1001, 1024)), qd(0, F(45, 1024)),
                    qd(F(-7, 16)), qd(0, F(3, 16)))
        tile.area2 = qd(0, F(315, 2))                # 56*15*(3/16) = 315/2  (x sqrt23)
        target = [(qd(0), qd(0)), (qd(105), qd(0)), (qd(F(105, 2)), qd(0, F(45, 2)))]
        return tile, target, N
    if name == 'F':
        QD.D = 6
        a, b, c, N = 110, 21, 121, 21
        tile = Tile(a, b, c,
                    qd(F(71, 121)), qd(0, F(40, 121)),
                    qd(F(1315, 1331)), qd(0, F(84, 1331)),
                    qd(F(-5, 11)), qd(0, F(4, 11)))
        tile.area2 = qd(0, 840)                      # 110*21*(4/11) = 840  (x sqrt6)
        target = [(qd(0), qd(0)), (qd(210), qd(0)), (qd(105), qd(0, 84))]
        return tile, target, N
    if name == 'G':
        QD.D = 6
        a, b, c, N = 10, 21, 25, 21
        tile = Tile(a, b, c,
                    qd(F(23, 25)), qd(0, F(4, 25)),
                    qd(F(71, 125)), qd(0, F(42, 125)),
                    qd(F(-1, 5)), qd(0, F(2, 5)))
        tile.area2 = qd(0, 84)                       # 10*21*(2/5) = 84  (x sqrt6)
        target = [(qd(0), qd(0)), (qd(42), qd(0)), (qd(21), qd(0, 42))]
        return tile, target, N
    if name == 'E':
        QD.D = 7
        a, b, c, N = 4, 15, 16, 15
        tile = Tile(a, b, c,
                    qd(F(31, 32)), qd(0, F(3, 32)),
                    qd(F(47, 128)), qd(0, F(45, 128)),
                    qd(F(-1, 8)), qd(0, F(3, 8)))
        tile.area2 = qd(0, F(45, 2))                 # 4*15*(3/8) = 45/2  (x sqrt7)
        target = [(qd(0), qd(0)), (qd(15), qd(0)), (qd(F(15, 2)), qd(0, F(45, 2)))]
        return tile, target, N
    raise SystemExit(f"unknown instance {name}")


def tile_triangle(tile, cosA, sinA, scale=1):
    """the tile itself as a triangle: (0,0), (c*scale,0), (b*scale*cosA, b*scale*sinA)"""
    c = tile.c * scale
    b = tile.b * scale
    return [(qd(0), qd(0)), (qd(c), qd(0)),
            ((cosA * b), (sinA * b))]


def validate():
    F = Fraction
    print("== V2: N = 1, target = tile itself (both families) ==", flush=True)
    for name in ('B', 'E'):
        tile, _, _ = make_instance(name)
        cosA, sinA = tile.corners[0][0], tile.corners[0][1]
        tri = tile_triangle(tile, cosA, sinA, 1)
        s = Search(tile, tri, 1, f"V2-{name}", log_every=10 ** 9)
        r = s.run()
        print(f"   {name}: {r} nodes={s.nodes}")
        assert r == 'FOUND_TILING', "V2 failed"

    print("== V1: N = 4 reptile, target = tile scaled by 2 (both families) ==", flush=True)
    for name in ('B', 'E', 'A'):
        tile, _, _ = make_instance(name)
        cosA, sinA = tile.corners[0][0], tile.corners[0][1]
        tri = tile_triangle(tile, cosA, sinA, 2)
        s = Search(tile, tri, 4, f"V1-{name}", log_every=10 ** 9)
        t0 = time.time()
        r = s.run()
        print(f"   {name}: {r} nodes={s.nodes} t={time.time()-t0:.1f}s")
        assert r == 'FOUND_TILING', "V1 failed"
        ok, msg = reverify(s.found, tri, tile)
        assert ok, f"V1 reverify failed: {msg}"
        print(f"   {name}: reverified ok")

    print("== V3: wrong N rejected at the root ==", flush=True)
    tile, _, _ = make_instance('B')
    cosA, sinA = tile.corners[0][0], tile.corners[0][1]
    tri = tile_triangle(tile, cosA, sinA, 2)
    try:
        Search(tile, tri, 3, "V3", log_every=10 ** 9)
        raise SystemExit("V3 FAILED: root accepted wrong N")
    except AssertionError:
        print("   root area assertion fired correctly")

    print("== V4: determinism ==", flush=True)
    s = Search(tile, tri, 4, "V4", log_every=10 ** 9)
    r = s.run()
    assert r == 'FOUND_TILING'
    print("   determinism ok")

    print("== V5: non-edge-to-edge positive control (hand-built T-junction 2-tiling) ==",
          flush=True)
    tile, _, _ = make_instance('B')
    cosA, sinA = tile.corners[0][0], tile.corners[0][1]
    Capex = (cosA * tile.b, sinA * tile.b)
    T2apex = (qd(1) + Capex[0], qd(0) - Capex[1])
    hexagon = [(qd(0), qd(0)), (qd(1), qd(0)), T2apex, (qd(8), qd(0)), (qd(7), qd(0)), Capex]
    s = Search(tile, hexagon, 2, "V5", log_every=10 ** 9)
    r = s.run()
    assert r == 'FOUND_TILING', "V5 failed: T-junction tiling not found"
    ok, msg = reverify(s.found, hexagon, tile)
    assert ok, f"V5 reverify: {msg}"
    print(f"   found and reverified (nodes={s.nodes})")
    print("ALL VALIDATIONS PASSED", flush=True)


def run_instance(name):
    tile, target, N = make_instance(name)
    s = Search(tile, target, N, name, log_every=100000)
    t0 = time.time()
    r = s.run()
    dt = time.time() - t0
    line = (f"RESULT {name}: {r} nodes={s.nodes} maxdepth={s.maxdepth} "
            f"placements={s.placements_tried} pruneA={s.prune_area} pruneR={s.prune_run} "
            f"time={dt:.0f}s")
    print(line, flush=True)
    if r == 'FOUND_TILING':
        ok, msg = reverify(s.found, target, tile)
        print(f"REVERIFY {name}: {'OK' if ok else 'FAILED'} ({msg})", flush=True)
        with open(f"found_{name}.json", "w") as f:
            json.dump([[[str(x.p), str(x.q)] for x in pt] for tri in s.found
                       for pt in tri], f)
    return line


def run_noP2(name):
    """robustness: rerun with the P2 run-prune disabled; verdict must be unchanged"""
    engine.Search.runs_ok = lambda self, poly: True
    return run_instance(name)


if __name__ == '__main__':
    arg = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if arg == 'validate':
        validate()
    elif arg.startswith('noP2-'):
        run_noP2(arg[5:])
    else:
        run_instance(arg)
