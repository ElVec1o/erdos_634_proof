#!/usr/bin/env python3
"""The Z-fan corridor criterion: exact kill test for the high slots.

Setting (verified from scratch in code/verify_zfan_scratch.py): at a rogue
slot M of the step W(k−1) ⟹ W(k), the second chord runs from Y = M·b·w along
u and exits Δ_k through the a-side BC at E = Y + (k−M)c·u = C + (k−M)a·v̂
(the subdivision vertex at distance M·a from B — the mirror of the X-fan's
X − (M−1)b·w = B/k ∈ AB).  Both sides of the chord-2 line are edge-unions
from Y up to their first common breakpoint: the row side starts with
P_{M+1}'s c-edge, the rogue side with the rogue's a-edge.  Since u ∥ AB and
v̂ ∥ BC, a unit step along d = p·u + q·v̂ costs exactly p of the BC-room and
q of the AB-room (Z2/Z3 of the verifier), with p = sin(β−θ)/sin β,
q = sin θ/sin β for d = rot_θ(u) — all exact rationals in the chart.

This module walks the two word systems with every forced constraint and
nothing else:

  * both sides start with their forced letters (a and c);
  * at a breakpoint s interior to the other side's covering, the side must
    complete the straight angle: the residue π − X (X the forward corner of
    the arriving edge) is filled by a ccw (row: cw) sequence of tile corners
    in the (α,β)-calculus — faithful because α/π is irrational — whose
    chord-adjacent corner lays the next letter on the line;
  * every edge of every fill tile is room-checked: length ℓ at ray angle θ
    from +u obeys ℓ·p(θ) ≤ (k−M)c − s (BC), ℓ·q(θ) ≤ M·a (AB), and on the
    row side ℓ·|q| ≤ s·a/c (the base);
  * the first rogue-side junction carries the forced parallelogram: the
    rogue's b-edge is covered by a single b-edge (b unsplittable, e ≥ 2), the
    reflected partner dies on 2γ = π + α, and the direct partner is not
    chord-adjacent — so the fill at Y+a·u is F_Y (a β-tile laying a or c)
    then the partner;
  * a side stops only at the exit (flush, s = (k−M)c) or at a common
    breakpoint with the other side; a common interior stop must close its
    2π-vertex, a common flush its π-vertex on BC, both room-checked.

Everything that is not forced is allowed (no overlap tests, no off-line
propagation), so KILLED here is a sound kill for the slot at that scale —
strictly weaker than the 2D engine, but in closed reach of Lean.

Verdict per (e, f, M, r):  KILLED iff no pair of walks shares a stopping
point.  Cross-checks: engine r-mode results (KILLED here ⟹ engine KILLED
wherever the engine decided; engine SURVIVES ⟹ alive here).
"""
from fractions import Fraction as Fr
from math import gcd
import sys

# ---------------------------------------------------------------- angles

class Mem:
    def __init__(self, e, f):
        self.e, self.f = e, f
        self.a, self.b, self.c = e * f, f * f - e * e, f * f
        self.D = 4 * f * f - e * e
        self.A = (Fr(2 * f * f - e * e, 2 * f * f), Fr(e, 2 * f * f))
        self.B = (Fr(e * (3 * f * f - e * e), 2 * f ** 3),
                  Fr(f * f - e * e, 2 * f ** 3))
        self.G = (Fr(-e, 2 * f), Fr(1, 2 * f))
        self.corner = {"A": self.A, "B": self.B, "G": self.G}
        self.edges_of = {"A": ("b", "c"), "B": ("a", "c"), "G": ("a", "b")}
        self.len_of = {"a": self.a, "b": self.b, "c": self.c}
        # far-end corner of edge x approached from corner X:
        # ends of a are {B, G}, of b {A, G}, of c {A, B}
        self.ends = {"a": ("B", "G"), "b": ("A", "G"), "c": ("A", "B")}

    def ang_add(self, t1, t2):
        return (t1[0] * t2[0] - self.D * t1[1] * t2[1],
                t1[1] * t2[0] + t1[0] * t2[1])

    def ang_sub(self, t1, t2):
        return (t1[0] * t2[0] + self.D * t1[1] * t2[1],
                t1[1] * t2[0] - t1[0] * t2[1])

    def pq(self, th):
        """(p, q) of d = rot_th(u): p = sin(β−θ)/sinβ, q = sinθ/sinβ."""
        sb = self.B[1]
        return (self.ang_sub(self.B, th)[1] / sb, th[1] / sb)

ONE = (Fr(1), Fr(0))

def far_end(mem, edge, near):
    x, y = mem.ends[edge]
    return y if near == x else x


def staircase_ok(mem, P0, P1):
    """The forced row P_{M+1}, P_{M+2}, … occupies, in (u, v̂)-coordinates
    based at Y, the region below the staircase V = −a·⌊U/c⌋ (row tile
    P_{M+j+1} is the triangle with top edge V = −ja, U ∈ [jc, (j+1)c] and
    riser U = (j+1)c).  A corridor edge from P0 to P1 must stay in the closed
    region V ≥ −a·⌊U/c⌋: checked piecewise (the segment is linear in U)."""
    (U0, V0), (U1, V1) = P0, P1
    if V0 > V1:
        (U0, V0), (U1, V1) = (U1, V1), (U0, V0)
    if V0 >= 0:
        return True
    a, c = mem.a, mem.c
    if U0 == U1:
        # vertical (−v̂) edge: allowed down to the riser floor −a·(U/c) when
        # U is a multiple of c, else to −a·⌊U/c⌋
        j = U0 // c if U0 % c == 0 else U0 // c
        return min(V0, V1) >= -a * (U0 // c)
    lo, hi = (U0, U1) if U0 < U1 else (U1, U0)
    jlo, jhi = int(lo // c), int(hi // c)
    for j in range(jlo, jhi + 1):
        # sub-interval of [jc, (j+1)c) ∩ [lo, hi]; at U = jc exactly the
        # floor is −ja (risers may be glued)
        A = max(lo, Fr(j * c))
        Bb = min(hi, Fr((j + 1) * c))
        if A > Bb:
            continue
        for U in (A, Bb):
            if U == Fr((j + 1) * c) and U != hi:
                continue
            V = V0 + (V1 - V0) * (U - U0) / (U1 - U0)
            if V < -a * j:
                return False
    return True

# ---------------------------------------------------------------- fills

def fill_sequences(X):
    """Orders of the residue π − X as corner sequences (chord-adjacent
    first).  π = 3α + 2β; γ = 2α + β; fills solved in the calculus:
      π − γ = α + β        → {α,β}
      π − β = 2α + β + ... = {3α? no: 3α+β} | {α,γ}
      π − α = 2α + 2β      → {2α,2β} | {β,γ}
    """
    from itertools import permutations
    if X == "G":
        mults = [("A", "B")]
    elif X == "B":
        mults = [("A", "A", "A", "B"), ("A", "G")]
    elif X == "A":
        mults = [("A", "A", "B", "B"), ("B", "G")]
    else:
        raise ValueError(X)
    seqs = set()
    for m in mults:
        for p in permutations(m):
            seqs.add(p)
    return sorted(seqs)


def junction_moves(mem, M, r, s, X, side, first=False):
    """All (letter, new_state) landable from a junction at s with forward
    corner X.  side = +1 (rogue, ccw fills) or −1 (row, cw fills).
    Room checks: BC ℓ·p ≤ rc − s; AB ℓ·q ≤ M·a; base (row side) ℓ·|q| ≤ s·a/c.
    """
    rc = r * mem.c
    out = set()
    from itertools import product
    for seq in fill_sequences(X):
        if first and side == +1:
            # forced parallelogram at Y+a·u: fill is (β then α = partner);
            # the α is the partner: not chord-adjacent, c-edge on the v̂-ray.
            if seq != ("B", "A"):
                continue
        # rays r_0 = u, r_j = rot of the prefix sum (ccw for the rogue side,
        # cw for the row side).  A cw ray at positive angle θ has
        # p = sin(β+θ)/sinβ and q = −sinθ/sinβ; both drop out of mem.pq
        # applied to the signed pair (cosθ, −sin_qθ).
        rays = [ONE]
        th = ONE
        for Ycor in seq:
            th = mem.ang_add(th, mem.corner[Ycor])
            rays.append(th)
        if side == -1:
            rays = [(t[0], -t[1]) for t in rays]

        def room_ok(ell, th):
            p, q = mem.pq(th)
            if p > 0 and ell * p > rc - s:
                return False
            if q > 0 and ell * q > M * mem.a:
                return False
            if q < 0 and not staircase_ok(mem, (Fr(s), Fr(0)),
                                          (s + ell * p, ell * q)):
                return False
            return True
        for assign in product((0, 1), repeat=len(seq)):
            good = True
            lay = None
            newX = None
            for i, (Ycor, sw) in enumerate(zip(seq, assign)):
                e1, e2 = mem.edges_of[Ycor]
                if sw:
                    e1, e2 = e2, e1
                # e1 on rays[i], e2 on rays[i+1]
                l1, l2 = mem.len_of[e1], mem.len_of[e2]
                if i == 0:
                    # chord-adjacent: e1 is the next line letter
                    if s + l1 > rc:
                        good = False
                        break
                    lay = e1
                    newX = far_end(mem, e1, seq[0])
                else:
                    if not room_ok(l1, rays[i]):
                        good = False
                        break
                if not room_ok(l2, rays[i + 1]):
                    good = False
                    break
                if first and side == +1 and i == 1:
                    # the partner lays c on the v̂-ray (rays[1]), b on rays[2]
                    if e1 != "c":
                        good = False
                        break
            if good and lay is not None:
                out.add((lay, newX))
    return sorted(out)


# ---------------------------------------------------------------- walks

def reachable(mem, M, r, side):
    """All (s, X) landable by the side's walk.  Returns dict s -> set(X)."""
    rc = r * mem.c
    if side == +1:
        start = [(mem.a, "G", True)]
    else:
        start = [(mem.c, "B", False)]
    seen = {}
    stack = list(start)
    first_done = set()
    while stack:
        s, X, first = stack.pop()
        if s in seen and X in seen[s] and not first:
            continue
        seen.setdefault(s, set()).add(X)
        if s == rc:
            continue
        for (lay, newX) in junction_moves(mem, M, r, s, X, side, first=first):
            s2 = s + mem.len_of[lay]
            if s2 > rc:
                continue
            if s2 not in seen or newX not in seen[s2]:
                stack.append((s2, newX, False))
    return seen


def closure_ok(mem, M, r, s, Xup, Xlo):
    """Can the common breakpoint at s close?  Flush (s = rc): the boundary
    vertex needs π − X_up − X_lo representable in the calculus.  Interior:
    the 2π-vertex needs a fill of 2π − X_up − X_lo whose tiles pass the
    BC room at s (rays tracked exactly, wrapping the +u direction)."""
    rc = r * mem.c
    val = {"A": (1, 0), "B": (0, 1), "G": (2, 1)}
    if s == rc:
        # residue π − X_up − X_lo = (3,2) − val(Xup) − val(Xlo) in (α,β)
        rx = 3 - val[Xup][0] - val[Xlo][0]
        ry = 2 - val[Xup][1] - val[Xlo][1]
        if rx < 0 or ry < 0:
            return False
        # representable as x·(1,0) + y·(0,1) + z·(2,1), all ℕ?
        for z in range(0, rx // 2 + 1):
            if ry - z >= 0 and rx - 2 * z >= 0:
                return True
        return False
    # interior: fill 2π − X_up − X_lo from the row backward ray (cw side)
    # around +u to the rogue backward ray.  Rays from θ0 = −(π − X_lo)
    # accumulating ccw; edges room-checked against BC (p > 0 rays only;
    # AB and base checks are slack here and skipped only when provably
    # weaker: AB room M·a ≥ c holds on every containment-surviving slot).
    rx = 6 - val[Xup][0] - val[Xlo][0]
    ry = 4 - val[Xup][1] - val[Xlo][1]
    from itertools import permutations, product
    combos = set()
    for z in range(0, min(rx // 2, ry) + 1):
        x, y = rx - 2 * z, ry - z
        combos.add(("A",) * x + ("B",) * y + ("G",) * z)
    # θ0: the row backward tile's down-edge ray: cw angle (π − X_lo) from u,
    # i.e. rotation by −(π − X_lo): as exact pair: π − X = sum to π
    pi_pair = (Fr(-1), Fr(0))
    for base in combos:
        for seq in set(permutations(base)):
            th = mem.ang_sub(pi_pair, mem.corner[Xlo])   # π − X_lo
            th = (th[0], -th[1])                          # −(π − X_lo)
            rays = [th]
            for Ycor in seq:
                th = mem.ang_add(th, mem.corner[Ycor])
                rays.append(th)
            for assign in product((0, 1), repeat=len(seq)):
                good = True
                for i, (Ycor, sw) in enumerate(zip(seq, assign)):
                    e1, e2 = mem.edges_of[Ycor]
                    if sw:
                        e1, e2 = e2, e1
                    for ell, ray in ((mem.len_of[e1], rays[i]),
                                     (mem.len_of[e2], rays[i + 1])):
                        p, q = mem.pq(ray)
                        if p > 0 and ell * p > rc - s:
                            good = False
                            break
                        if q > 0 and ell * q > M * mem.a:
                            good = False
                            break
                        if q < 0 and not staircase_ok(
                                mem, (Fr(s), Fr(0)),
                                (s + ell * p, ell * q)):
                            good = False
                            break
                    if not good:
                        break
                if good:
                    return True
    return False


def slot_verdict(mem, M, r):
    """KILLED iff no common stopping point closes."""
    up = reachable(mem, M, r, +1)
    lo = reachable(mem, M, r, -1)
    rc = r * mem.c
    for s in sorted(set(up) & set(lo)):
        for Xu in up[s]:
            for Xl in lo[s]:
                if closure_ok(mem, M, r, s, Xu, Xl):
                    return "alive", s, Xu, Xl
    return ("KILLED",)


def members(fmax, emin=2):
    for f in range(3, fmax + 1):
        for e in range(emin, f):
            if gcd(e, f) == 1:
                yield e, f


def main():
    fmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    print("# Z-fan corridor criterion: slot (e,f,M) at scale k = M+r")
    grand = {}
    for e, f in members(fmax):
        mem = Mem(e, f)
        Mlo, Mhi = f // e + 2, f - 2
        rows = []
        for M in range(Mlo, Mhi + 1):
            rs = []
            for r in range(2, f - M + 1):
                v = slot_verdict(mem, M, r)
                if v[0] == "KILLED":
                    rs.append(r)
                grand[(e, f, M, r)] = v
            allr = list(range(2, f - M + 1))
            tag = "ALL" if rs == allr and allr else \
                ("none" if not rs else str(rs))
            rows.append(f"M={M}: killed r={tag}" +
                        ("" if rs == allr else f" of {allr}"))
        if rows:
            print(f"({e},{f}): " + "; ".join(rows))
    # summary of the alive set
    alive = sorted(k for k, v in grand.items() if v[0] != "KILLED")
    print(f"\nalive (e,f,M,r) [{len(alive)}]:")
    for k in alive:
        v = grand[k]
        print("   ", k, "stops at s =", v[1], f"({v[2]},{v[3]})")
    return grand


if __name__ == "__main__":
    main()
