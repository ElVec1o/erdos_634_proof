#!/usr/bin/env python3
"""
gen_walks.py -- emit the P5 (gamma-trap) WALKS section for a cengine instance file.

P5 is the gamma-injection lemma: each side of the target is partitioned into whole tile edges, and
every side must carry at least one c-edge.  Each a-edge tile and each b-edge tile puts a gamma at a
junction; no gamma sits at a base corner or the apex; a pi-vertex carries at most one gamma.  The
map (a/b-edge -> its gamma junction) is therefore injective, so #a + #b <= k - 1, i.e. #c >= 1.
This holds for EVERY e and EVERY scale m -- it carries no side condition (companion, gamma-trap).

A "walk" is the edge multiset (#a, #b, #c) of one side.  For a side of length L this enumerates
every (x, y, z) with x*a + y*b + z*c = L and z >= 1.  The engine prunes a partial walk as soon as
it is not a componentwise sub-multiset of any listed walk.

Usage:  gen_walks.py <instance.txt>          # print the WALKS section
        gen_walks.py <instance.txt> --write   # append it to the file in place
"""
import sys
from fractions import Fraction
from math import isqrt


def read_tokens(path):
    with open(path) as f:
        return f.read().split()


class Inst:
    """Just enough of the instance format to get the tile edges and the target side lengths."""

    def __init__(self, path):
        t = read_tokens(path)
        # the optional trailing WALKS/CORNERS section is not part of the numeric prefix
        for stop in ("WALKS", "CORNERS"):
            if stop in t:
                t = t[: t.index(stop)]
        self.tok = t
        self.i = 0
        self.D = self._long()
        self.a, self.b, self.c = self._long(), self._long(), self._long()
        self.corners = [(self._qd(), self._qd()) for _ in range(3)]  # (cos, sin)
        self.area2 = self._qd()
        self.N = self._long()
        self.target = [(self._qd(), self._qd()) for _ in range(3)]   # (x, y)
        if self.i != len(self.tok):
            raise SystemExit(f"{path}: {len(self.tok) - self.i} unconsumed tokens -- format mismatch")

    def _qd(self):
        """(p + q*sqrt(D)) / d  ->  (Fraction p/d, Fraction q/d), i.e. rational + rational*sqrt(D)."""
        p, q, d = int(self.tok[self.i]), int(self.tok[self.i + 1]), int(self.tok[self.i + 2])
        self.i += 3
        return (Fraction(p, d), Fraction(q, d))

    def _long(self):
        """A bare integer: rd_long() reads a single mpz, unlike rd_qd() which reads p, q, d."""
        v = int(self.tok[self.i])
        self.i += 1
        return v

    def side_len2(self, s):
        """Squared length of side s (from target[s] to target[s+1]) as u + v*sqrt(D)."""
        (x0, y0), (x1, y1) = self.target[s], self.target[(s + 1) % 3]
        dx = (x1[0] - x0[0], x1[1] - x0[1])
        dy = (y1[0] - y0[0], y1[1] - y0[1])
        # (p + q sqrt D)^2 = p^2 + q^2 D + 2pq sqrt D
        u = dx[0] ** 2 + dx[1] ** 2 * self.D + dy[0] ** 2 + dy[1] ** 2 * self.D
        v = 2 * dx[0] * dx[1] + 2 * dy[0] * dy[1]
        return u, v

    def side_len(self, s):
        """Exact side length; must be rational (it is, for every base-beta / 120 target here)."""
        u, v = self.side_len2(s)
        if v != 0:
            raise SystemExit(f"side {s}: length^2 = {u} + {v}*sqrt({self.D}) is irrational -- unsupported")
        if u.denominator != 1:
            raise SystemExit(f"side {s}: length^2 = {u} is not an integer")
        r = isqrt(int(u))
        if r * r != int(u):
            raise SystemExit(f"side {s}: length^2 = {u} is not a perfect square")
        return r


def walks(L, a, b, c, min_c=1):
    """All (#a, #b, #c) with x*a + y*b + z*c == L and z >= min_c."""
    out = []
    for z in range(min_c, L // c + 1):
        rem_z = L - z * c
        for y in range(0, rem_z // b + 1):
            rem = rem_z - y * b
            if rem % a == 0:
                out.append((rem // a, y, z))
    return out


def e1m1_walks(inst, lens, base, others):
    """Theorem thm:e1reduce (companion): e=1, m=1, f>=3.

    Target (f^3, f^3, 3f^2-1), tile (f, f^2-1, f^2), N = 3f^2-1.  In ANY tiling:
      (i)  no equal side carries a b-edge; each begins and ends with a c-edge, so n_c >= 2.
           With n_b = 0, n_a + n_c*f = f^2 forces f | n_a: n_a = f*k, n_c = f - k.
      (ii) the base carries exactly one b-edge and exactly one c-edge, and its first and last
           edges are a-edges -- so the base walk is the single multiset (f, 1, 1).

    Strictly stronger than the gamma-trap alone, which leaves the base at two walks.  Returns
    (base_walks, side_walks, corner_types) or None when the instance is not in this family.
    """
    f = inst.a
    if (inst.b, inst.c) != (f * f - 1, f * f):
        return None
    if f < 3:
        return None                                   # the theorem is stated for f >= 3
    if lens[base] != 3 * f * f - 1 or lens[others[0]] != f ** 3 or inst.N != 3 * f * f - 1:
        return None
    base_walks = [(f, 1, 1)]                          # (ii)
    side_walks = [(f * k, 0, f - k) for k in range(0, f - 1)]   # (i), n_c = f-k >= 2
    corner = [None, None, None]
    corner[base] = 0                                  # base begins and ends with an a-edge
    for s in others:
        corner[s] = 2                                 # each equal side begins and ends with a c-edge
    return base_walks, side_walks, corner


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    path = sys.argv[1]
    inst = Inst(path)
    a, b, c = inst.a, inst.b, inst.c
    lens = [inst.side_len(s) for s in range(3)]

    # the BASE is the side that differs; the other two are the equal sides.  (For an equilateral
    # target all three agree and side 0 is taken as the base -- the walk sets coincide anyway.)
    if lens[0] == lens[1] == lens[2]:
        base = 0
    else:
        base = next(s for s in range(3) if lens.count(lens[s]) == 1)
    others = [s for s in range(3) if s != base]
    if lens[others[0]] != lens[others[1]]:
        raise SystemExit(f"target is scalene (sides {lens}) -- P5 needs an isosceles target")

    # --min-c 0 lists EVERY edge partition of the side: that is pure arithmetic (a side of length L
    # cut into whole tile edges must satisfy x*a + y*b + z*c = L) and is valid with no theorem
    # behind it.  --min-c 1 (the default) adds the gamma-trap.  Keeping the two separable lets the
    # arithmetic layer be validated on its own before the proved layer is switched on.
    min_c = 1
    if "--min-c" in sys.argv:
        min_c = int(sys.argv[sys.argv.index("--min-c") + 1])
    corner = None
    if "--e1m1" in sys.argv:
        got = e1m1_walks(inst, lens, base, others)
        if got is None:
            raise SystemExit(f"{path}: not an e=1, m=1, f>=3 instance -- thm:e1reduce does not apply")
        wb, ws, corner = got
    else:
        wb = walks(lens[base], a, b, c, min_c)
        ws = walks(lens[others[0]], a, b, c, min_c)

    sys.stderr.write(
        f"{path}: tile=({a},{b},{c}) N={inst.N} D={inst.D}  sides={lens}  "
        f"base=side{base} (len {lens[base]}), equal sides len {lens[others[0]]}\n"
        f"  base walks with #c>=1: {len(wb)}   (unrestricted: {len(walks(lens[base], a, b, c, 0))})\n"
        f"  side walks with #c>=1: {len(ws)}   (unrestricted: {len(walks(lens[others[0]], a, b, c, 0))})\n")

    out = [f"WALKS {base} {len(wb)}"]
    out += [f"  {x} {y} {z}" for (x, y, z) in wb]
    out += [f"{len(ws)}"]
    out += [f"  {x} {y} {z}" for (x, y, z) in ws]
    if corner is not None:
        out += ["CORNERS " + " ".join(str(t) for t in corner)]
    text = "\n".join(out) + "\n"

    if "--write" in sys.argv:
        with open(path, "a") as f:
            f.write(text)
        sys.stderr.write(f"  appended to {path}\n")
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
