#!/usr/bin/env python3
"""Append the P5 walk section (gamma-trap + corner-parallelogram rule) to an exact instance file.

A side of the target is partitioned into whole tile edges, so its edge multiset (#a,#b,#c) is a
"walk" solving P*a + Q*b + R*c = |side|.  The gamma-injection lemma (paper; BaseBetaWalks.lean)
forces R >= 1 on EVERY side, at every scale m: each a-edge tile and each b-edge tile puts a gamma at
a junction of that side (a joins beta to gamma, b joins alpha to gamma, c joins alpha to beta), no
gamma sits at a base corner (exactly one tile there, angle beta) or at the apex (exactly three tiles,
all alpha), and every other node of a side is a pi-vertex carrying at most one gamma.  So
edge -> its gamma junction is injective: #a + #b <= #edges - 1, i.e. R >= 1.

We emit the walks with R >= 1 and nothing else.  At m = 1 that ALREADY encodes the two stronger
theorems, which are corollaries of it:
  side_no_b     -- no equal side carries a b-edge          (Q = 0 on every surviving side walk)
  base_b_bound  -- the base's b-count Q = e+f*j has j(f-e) <= e-1
Both are asserted below against the emitted lists, so a bug in either direction is caught here.

Usage:  add_walks.py <in.txt> <out.txt> <Ybase> <Xside> <a> <b> <c> [e f m]
"""
import sys


def walks(target, a, b, c):
    """every (P,Q,R) >= 0 with P*a + Q*b + R*c == target"""
    out = []
    for Q in range(target // b + 1):
        for R in range((target - Q * b) // c + 1):
            rem = target - Q * b - R * c
            if rem % a == 0:
                out.append((rem // a, Q, R))
    return out


def main():
    if len(sys.argv) not in (8, 11):
        print(__doc__)
        sys.exit(1)
    src, dst = sys.argv[1], sys.argv[2]
    Y, X, a, b, c = (int(v) for v in sys.argv[3:8])
    efm = tuple(int(v) for v in sys.argv[8:11]) if len(sys.argv) == 11 else None

    # the corner-parallelogram rule needs the b-edge unsplittable: no n_a*a + n_c*c == b
    def b_unsplittable():
        for na in range(b // a + 1):
            rem = b - na * a
            if rem >= 0 and rem % c == 0:
                return False
        return True
    assert b_unsplittable(), "b splits into a/c edges -- corner rule invalid, do not use"

    def corner_base(w):
        """first two AND last two base edges lie in {a,c}  =>  Q <= k-4 (k>=4); k==3 => Q==0"""
        P, Q, R = w
        k = P + Q + R
        return Q <= k - 4 if k >= 4 else Q == 0

    def corner_side(w):
        """first two side edges (from the base corner) lie in {a,c}  =>  Q <= k-2"""
        P, Q, R = w
        return Q <= (P + Q + R) - 2

    allb, alls = walks(Y, a, b, c), walks(X, a, b, c)
    base = [w for w in allb if w[2] >= 1 and corner_base(w)]   # gamma-trap + corner rule
    side = [w for w in alls if w[2] >= 1 and corner_side(w)]   # gamma-trap + corner rule

    if efm:
        e, f, m = efm
        assert (a, b, c) == (e * f, f * f - e * e, f * f), "tile is not the primitive 3a+2b tile"
        assert Y == e * m * (3 * f * f - e * e) and X == f ** 3 * m, "target is not the base-beta one"
        if m == 1:
            # side_no_b: every surviving side walk is b-free
            bad = [w for w in side if w[1] != 0]
            assert not bad, "side_no_b VIOLATED by %r -- do not use this prune" % (bad,)
            # base_b_bound: j*(f-e) <= e-1 where Q = e + f*j
            for (P, Q, R) in base:
                assert (Q - e) % f == 0 and Q >= e, "base b-count %d is not e+f*j" % Q
                j = (Q - e) // f
                assert j * (f - e) <= e - 1, "base_b_bound VIOLATED: j=%d" % j
            print("  m=1 corollaries verified: side_no_b OK, base_b_bound OK (jmax=%d)"
                  % ((e - 1) // (f - e)))

    with open(src) as fh:
        body = fh.read().rstrip()
    with open(dst, "w") as fh:
        fh.write(body + "\nWALKS\n")
        fh.write("%d\n" % len(base))
        for w in base:
            fh.write("%d %d %d\n" % w)
        fh.write("%d\n" % len(side))
        for w in side:
            fh.write("%d %d %d\n" % w)
    print("  base walks %d -> %d kept   side walks %d -> %d kept"
          % (len(allb), len(base), len(alls), len(side)))
    print("  base kept: %s" % (base,))
    print("  side kept: %s" % (side,))


if __name__ == "__main__":
    main()
