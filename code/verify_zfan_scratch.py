#!/usr/bin/env python3
"""FROM-SCRATCH verification of the Z-side (mirror) structure at a rogue slot.

Independent of the engine (no project imports).  Points live in the chart
(x, ŷ) with y = ŷ·√D, D = 4f²−e²; everything is exact rational arithmetic.
Triangle Δ_k placed from side lengths alone: A = (0,0), C = (kb, 0),
B = apex with |AB| = kc, |CB| = ka.  Slot Y = M·b·w, rogue β-tile at Y with
c-edge along v̂ = (B−C)/(ka) and a-edge along u = B/(kc).

The X-fan (RogueFan.lean) lives on the AB side of the slot: the row side of
chord 1 completes π at X = Y + a·v̂, and the fan's room is measured by
X − (M−1)b·w = B/k ∈ AB.  This file verifies the MIRROR: the Z-side
propagation of the rogue collides with the a-side BC through the second
chord, and the collision is governed by exact linear identities.

Verified claims:

  Z1  (chart generator)  c·u − a·v̂ = b·w exactly; hence the three jump
      identities  X = Y + a·v̂ = Y_{M-1} + c·u,  Xc := Y + c·u = Y_{M+1} + a·v̂,
      and generally  Y + (t+c)·u = Y_{M+1} + t·u + a·v̂ for all t.
  Z2  (the mirror identity)  the chord-2 ray Y + t·u stays in Δ_k exactly for
      t ≤ (k−M)·c, and the exit point is the BC-subdivision vertex
          E := Y + (k−M)c·u = C + (k−M)a·v̂ ∈ BC,  |E − B| = M·a :
      the mirror of X − (M−1)b·w = B/k ∈ AB.  Moreover s_AB is constant along
      u (u ∥ AB), and σ := s+t is constant along v̂ (v̂ ∥ BC): the two chords'
      room coordinates decouple, and a unit step along d = p·u + q·v̂ costs
      exactly p of the BC-room and q of the AB-room.
  Z3  (room ratios)  for d = rot_θ(u), θ ∈ ℕα + ℕβ, the decomposition
      d = p·u + q·v̂ has  p = sin(β−θ)/sin β and q = sin θ/sin β, both exact
      rationals in the chart; table verified against barycentric rates.
      In particular p(u) = 1, p(v̂) = 0, p(w) = c/b, q(w) = −a/b,
      q(−w) = a/b, q(v̂) = 1.
  Z4  (forced parallelogram)  the rogue's b-edge [Z, Yau] is covered on its
      far side by a single b-edge (b = x·a + y·b + z·c forces (0,1,0) for
      e ≥ 2), so a partner tile shares it, with corners at Z and Yau exactly;
      the reflected partner repeats γ at Yau where the residue is α + β, and
      2γ − π = α > 0 kills it; the direct partner fits with the exact vertex
      identity  Papex = Yau + c·v̂ = Z + a·u.
  Z5  (the two forced fans)  at Z the residue between the partner's γ and the
      chord-1 forward ray is exactly β (rot_α(−v̂ reversed) bookkeeping via
      exact rotations); at Yau the residue between the partner's α and the
      chord-2 forward ray is exactly β; fills of β are {β} alone (α/π
      irrational ⟹ the (α,β)-calculus is faithful), so each fan is a single
      β-tile with edge pairs {a,c} on the two rays: 2 × 2 assignments.
  Z6  (chord-2 T-forcing)  the rogue side of chord 2 cannot break at Xc:
      a + (word) = c needs x·a + y·b + z·c = Δ = c − a, impossible for e ≥ 2
      (same arithmetic as chord 1's T-vertex forcing).  Hence the row side
      completes π at Xc: with P_{M+1}'s β and Q_{M+1}'s γ the residue is α;
      with P_{M+1}'s β alone it is α + γ = {α,γ} | {3α,β}.
  Z7  (the r = 2 chain)  at k = M+2 the α-fill at Xc laying c on +w dies by
      the BC-room  c·p(w) = c²/b > (k−M−1)·c  ⟺  c > (k−M−1)·b, which at
      k−M = 2 is c > b, true always; so the second-row tile P'_{M+1} is
      forced whenever Q_{M+1} is standard.

Any discrepancy prints REFUTED and exits 1.
"""
from fractions import Fraction as Fr
from math import gcd, isqrt
import sys

checks = 0
fails = []


def chk(cond, *info):
    global checks
    checks += 1
    if not cond:
        fails.append(info)
        print("REFUTED:", info)


def sub(P, Q): return (P[0] - Q[0], P[1] - Q[1])
def add(P, Q): return (P[0] + Q[0], P[1] + Q[1])
def smul(s, P): return (s * P[0], s * P[1])
def dot(D, P, Q): return P[0] * Q[0] + D * P[1] * Q[1]
def len2(D, P): return dot(D, P, P)
def cross_q(P, Q): return P[0] * Q[1] - P[1] * Q[0]


def rot(D, cs, P, sign=+1):
    c, s = cs
    s = s * sign
    return (c * P[0] - s * D * P[1], s * P[0] + c * P[1])


def ang_add(D, t1, t2):
    """(cos, sin_q) of the sum of two angles given as (cos, sin_q) pairs."""
    return (t1[0] * t2[0] - D * t1[1] * t2[1], t1[1] * t2[0] + t1[0] * t2[1])


def ang_sub(D, t1, t2):
    return (t1[0] * t2[0] + D * t1[1] * t2[1], t1[1] * t2[0] - t1[0] * t2[1])


def sqrt_fr(x):
    n, d = x.numerator, x.denominator
    rn, rd = isqrt(n), isqrt(d)
    if rn * rn != n or rd * rd != d:
        return None
    return Fr(rn, rd)


def members(fmax, emin=2):
    for f in range(3, fmax + 1):
        for e in range(emin, f):
            if gcd(e, f) == 1:
                yield e, f


def bary(P, B, C):
    det = C[0] * B[1] - C[1] * B[0]
    s = (P[0] * B[1] - P[1] * B[0]) / det
    t = (C[0] * P[1] - C[1] * P[0]) / det
    return s, t


FMAX = 12

for e, f in members(FMAX):
    a, b, c = e * f, f * f - e * e, f * f
    D = 4 * f * f - e * e
    cos_a, sin_a = Fr(2 * f * f - e * e, 2 * f * f), Fr(e, 2 * f * f)
    cos_b, sin_b = Fr(e * (3 * f * f - e * e), 2 * f ** 3), \
        Fr(f * f - e * e, 2 * f ** 3)
    cos_g, sin_g = Fr(-e, 2 * f), Fr(1, 2 * f)
    A_, B_, G_ = (cos_a, sin_a), (cos_b, sin_b), (cos_g, sin_g)
    for cs in (A_, B_, G_):
        chk(cs[0] ** 2 + D * cs[1] ** 2 == 1, "unit angle", e, f)
    # α + β + γ = π as exact rotation arithmetic
    s3 = ang_add(D, ang_add(D, A_, B_), G_)
    chk(s3 == (Fr(-1), Fr(0)), "angle sum", e, f)
    w = (Fr(1), Fr(0))
    u = (cos_a, sin_a)                     # u = rot_α(w), |u| = 1
    chk(len2(D, u) == 1, "u unit", e, f)
    vraw = sub(smul(Fr(c), u), smul(Fr(b), w))
    chk(len2(D, vraw) == a * a, "|c·u − b·w| = a", e, f)
    vh = smul(Fr(1, a), vraw)
    # Z1: the chart generator c·u − a·v̂ = b·w
    chk(sub(smul(Fr(c), u), smul(Fr(a), vh)) == (Fr(b), Fr(0)),
        "Z1 generator", e, f)
    # v̂ = rot_β(u): the chord and the flank rays differ by exactly β
    chk(rot(D, B_, u) == vh, "Z1 vh = rot_beta(u)", e, f)
    # rot_γ(v̂) = −w: the third rotation closes the base
    chk(rot(D, G_, vh) == (Fr(-1), Fr(0)), "Z1 rot_gamma(vh) = -w", e, f)

    # Z3: room ratios.  d = p·u + q·v̂ solved exactly; check the table.
    def uv_decomp(d):
        det = cross_q(u, vh)
        p = cross_q(d, vh) / det
        q = cross_q(u, d) / det
        return p, q
    chk(uv_decomp(u) == (1, 0), "Z3 p(u)", e, f)
    chk(uv_decomp(vh) == (0, 1), "Z3 p(vh)", e, f)
    chk(uv_decomp(w) == (Fr(c, b), Fr(-a, b)), "Z3 w = (c/b)u − (a/b)v̂", e, f)
    # rot_θ(u) for θ = x·α + y·β, small x, y: p = sin(β−θ)/sinβ, q = sinθ/sinβ
    for x in range(0, 4):
        for y in range(0, 3):
            th = (Fr(1), Fr(0))
            for _ in range(x):
                th = ang_add(D, th, A_)
            for _ in range(y):
                th = ang_add(D, th, B_)
            d = rot(D, th, u)
            p, q = uv_decomp(d)
            bmth = ang_sub(D, B_, th)
            chk(p == bmth[1] / sin_b, "Z3 p formula", e, f, x, y)
            chk(q == th[1] / sin_b, "Z3 q formula", e, f, x, y)

    # Z4: b is unsplittable over {a,b,c} for e ≥ 2
    reps = [(x, y, z) for z in range(0, b // c + 1)
            for y in range(0, b // b + 1)
            for x in range(0, b // a + 1) if x * a + y * b + z * c == b]
    chk(reps == [(0, 1, 0)], "Z4 b unsplittable", e, f, reps)
    # 2γ − π = α > 0: the reflected partner dies at Yau
    two_g = ang_add(D, G_, G_)
    pi_a = ang_add(D, (Fr(-1), Fr(0)), A_)   # π + α
    chk(two_g == pi_a, "Z4 2γ = π + α", e, f)

    # Z6: Δ = c − a is not representable (x·a + y·b + z·c = Δ) for e ≥ 2
    Dl = c - a
    reps = [(x, y, z) for z in range(0, Dl // c + 1)
            for y in range(0, Dl // b + 1)
            for x in range(0, Dl // a + 1) if x * a + y * b + z * c == Dl]
    chk(reps == [], "Z6 Delta unrepresentable", e, f, reps)

    # per-scale geometry
    for k in range(4, f + 1):
        Ck = (Fr(k * b), Fr(0))
        Bk = smul(Fr(k * c), u)
        chk(len2(D, sub(Bk, Ck)) == (k * a) ** 2, "S1 |CB|", e, f, k)
        chk(len2(D, Bk) == (k * c) ** 2, "S1 |AB|", e, f, k)
        chk(sub(Bk, Ck) == smul(Fr(k * a), vh), "S1 B−C = ka·v̂", e, f, k)
        for M in range(f // e + 2, k - 1):
            Y = (Fr(M * b), Fr(0))
            X = add(Y, smul(Fr(a), vh))
            Z = add(Y, smul(Fr(c), vh))
            Yau = add(Y, smul(Fr(a), u))
            Xc = add(Y, smul(Fr(c), u))
            YM1 = (Fr((M + 1) * b), Fr(0))
            # Z1 jumps
            chk(X == add((Fr((M - 1) * b), Fr(0)), smul(Fr(c), u)),
                "Z1 X jump", e, f, k, M)
            chk(Xc == add(YM1, smul(Fr(a), vh)), "Z1 Xc jump", e, f, k, M)
            # Z2: the mirror identity
            E = add(Y, smul(Fr((k - M) * c), u))
            E2 = add(Ck, smul(Fr((k - M) * a), vh))
            chk(E == E2, "Z2 exit identity", e, f, k, M)
            sE, tE = bary(E, Bk, Ck)
            chk(sE + tE == 1 and 0 < sE < 1, "Z2 exit interior to BC",
                e, f, k, M)
            chk(len2(D, sub(Bk, E)) == (M * a) ** 2, "Z2 |E−B| = Ma",
                e, f, k, M)
            # containment along u: strictly inside below (k−M)c, outside above
            for t, inside in [(Fr((k - M) * c) - Fr(1, 3), True),
                              (Fr((k - M) * c), True),
                              (Fr((k - M) * c) + Fr(1, 3), False)]:
                P = add(Y, smul(t, u))
                s2, t2 = bary(P, Bk, Ck)
                ok = s2 >= 0 and t2 >= 0 and s2 + t2 <= 1
                chk(ok == inside, "Z2 containment", e, f, k, M, t)
            # s_AB constant along u; σ = s+t constant along v̂
            P1 = add(Y, smul(Fr(7, 3), u))
            s1, t1 = bary(P1, Bk, Ck)
            sY, tY = bary(Y, Bk, Ck)
            chk(s1 == sY == Fr(M, k), "Z2 s const along u", e, f, k, M)
            P2 = add(Y, smul(Fr(7, 3), vh))
            s2, t2 = bary(P2, Bk, Ck)
            chk(s2 + t2 == sY + tY == Fr(M, k), "Z2 σ const along v̂",
                e, f, k, M)
            # AB-room along v̂ from any chord-2 point: exactly M·a
            P3 = add(add(Y, smul(Fr(5, 7), u)), smul(Fr(M * a), vh))
            s3, _ = bary(P3, Bk, Ck)
            chk(s3 == 0, "Z2 AB-room = Ma", e, f, k, M)

            # Z4: the direct partner's apex
            Papex = add(Yau, smul(Fr(c), vh))
            chk(Papex == add(Z, smul(Fr(a), u)), "Z4 Papex identity",
                e, f, k, M)
            # partner congruence: sides (a, b, c) from {Papex, Yau, Z}
            chk(len2(D, sub(Papex, Z)) == a * a, "Z4 partner a", e, f, k, M)
            chk(len2(D, sub(Yau, Z)) == b * b, "Z4 partner b", e, f, k, M)
            chk(len2(D, sub(Papex, Yau)) == c * c, "Z4 partner c", e, f, k, M)

            # Z5: the residues at Z and Yau are exactly β.
            # At Yau (ccw from the chord-2 forward ray u): the F_Y tile spans
            # (u, rot_β u = v̂); then the partner's α spans (v̂, rot_α v̂);
            # then the rogue's γ closes to −u: α+β+γ = π.
            dz = rot(D, A_, vh)          # rot_α(v̂): the b-edge ray to Z
            chk(smul(Fr(b), dz) == sub(Z, Yau), "Z5 rogue b-edge ray",
                e, f, k, M)
            chk(rot(D, G_, dz) == (Fr(-u[0]), Fr(-u[1])),
                "Z5 gamma closes at Yau", e, f, k, M)
            # At Z (ccw from the chord-1 forward ray v̂, going clockwise
            # instead: the fan tile spans (u, v̂) at Z): rot_β(u) = v̂ again,
            # the partner's γ spans (d_bz, u) with d_bz = (Yau−Z)/b, and the
            # rogue's α closes to −v̂.
            d_bz = smul(Fr(1, b), sub(Yau, Z))
            chk(rot(D, G_, d_bz) == u, "Z5 partner gamma at Z", e, f, k, M)
            chk(rot(D, A_, (Fr(-vh[0]), Fr(-vh[1]))) == d_bz,
                "Z5 rogue alpha at Z", e, f, k, M)

            # Z6: at Xc the row side carries P_{M+1}'s β between −u and −v̂
            chk(sub(Y, Xc) == smul(Fr(-c), u), "Z6 c-edge ray", e, f, k, M)
            chk(sub(YM1, Xc) == smul(Fr(-a), vh), "Z6 a-edge ray", e, f, k, M)
            # residue α + γ: rot_α(rot_γ(−v̂)) = u  (fill {γ then α})
            mvh = (Fr(-vh[0]), Fr(-vh[1]))
            chk(rot(D, A_, rot(D, G_, mvh)) == u, "Z6 residue closes",
                e, f, k, M)

            # Z7: the +w edge at Xc has BC-cost p(w) = c/b: an edge of
            # length ℓ from Xc along +w stays inside iff ℓ·c ≤ (k−M−1)·c·b,
            # i.e. ℓ ≤ (k−M−1)b.  Verified by direct barycentric test.
            for ell, expect in [(Fr((k - M - 1) * b), True),
                                (Fr((k - M - 1) * b) + Fr(1, 5), False)]:
                P = add(Xc, smul(ell, w))
                s4, t4 = bary(P, Bk, Ck)
                chk((s4 + t4 <= 1) == expect, "Z7 w-room at Xc",
                    e, f, k, M, ell)

# ---- Z8: the r = 2 row-side head kills (the top-2 criterion's geometry) ----
#
# At the row-side junction Xc (arc c, forward corner β) with k = M + 2, the
# fill's chord-adjacent tile lays the next row letter on +u with its other
# edge on the first clockwise ray.  The four non-flush heads die:
#   L1 α laying b (c-edge on the cw-α ray = w):   BC-cost c·(c/b) > room c.
#   L2 β laying a (c-edge on the cw-β ray):       BC-cost c·2cosβ > c when
#      e(3f²−e²) > f³; otherwise the c-edge's far vertex (c+2c·cosβ, −c) in
#      (u,v̂)-coordinates lies below the forced-row staircase V ≥ −a·⌊U/c⌋.
#      Equality e(3f²−e²) = f³ never holds (f ∤ e³).
#   L3 γ laying a (b-edge on the cw-γ ray):       far vertex (c+a, −c),
#      floor 1, and −c < −a.
#   L4 γ laying b (a-edge on the cw-γ ray):       far vertex at U/c = c/b
#      exactly (the identity c² = a² + bc), and b ∤ c, so V = −(c/b)a lies
#      strictly below −⌊c/b⌋·a.
# The flush heads (α or β laying c) land exactly at 2c.
for e, f in members(FMAX):
    a, b, c = e * f, f * f - e * e, f * f
    D = 4 * f * f - e * e
    cos_a, sin_a = Fr(2 * f * f - e * e, 2 * f * f), Fr(e, 2 * f * f)
    cos_b, sin_b = Fr(e * (3 * f * f - e * e), 2 * f ** 3), \
        Fr(f * f - e * e, 2 * f ** 3)
    cos_g, sin_g = Fr(-e, 2 * f), Fr(1, 2 * f)
    A_, B_, G_ = (cos_a, sin_a), (cos_b, sin_b), (cos_g, sin_g)
    w = (Fr(1), Fr(0))
    u = A_
    vh = rot(D, B_, u)

    def pq(d):
        det = cross_q(u, vh)
        return (cross_q(d, vh) / det, cross_q(u, d) / det)

    # cw rays from u: rot by the NEGATIVE of the corner angle
    neg_ = lambda t: (t[0], -t[1])
    ray_cw_a = rot(D, neg_(A_), u)
    ray_cw_b = rot(D, neg_(B_), u)
    ray_cw_g = rot(D, neg_(G_), u)
    chk(ray_cw_a == w, "Z8 cw-alpha ray is w", e, f)
    pA, qA = pq(ray_cw_a)
    pB, qB = pq(ray_cw_b)
    pG, qG = pq(ray_cw_g)
    chk((pA, qA) == (Fr(c, b), Fr(-a, b)), "Z8 p,q at cw-alpha", e, f)
    chk(pB == Fr(e * (3 * f * f - e * e), f ** 3) and qB == -1,
        "Z8 p,q at cw-beta = (2cosβ, −1)", e, f)
    chk((pG, qG) == (Fr(a, b), Fr(-c, b)), "Z8 p,q at cw-gamma", e, f)
    # L1: BC-cost of the c-edge on w exceeds the r=2 room
    chk(c * pA > c, "Z8 L1", e, f)
    # L2: the dichotomy, exclusive
    lhs = e * (3 * f * f - e * e)
    chk(lhs != f ** 3, "Z8 L2 no equality", e, f)
    if lhs < f ** 3:
        U, V = Fr(c) + c * pB, Fr(c) * qB
        chk(U < 2 * c and V == -c and -c < -a, "Z8 L2 staircase", e, f)
    else:
        chk(c * pB > c, "Z8 L2 BC", e, f)
    # L3: γ laying a puts its b-edge far vertex at (c+a, −c)
    U3, V3 = Fr(c) + b * pG, Fr(b) * qG
    chk((U3, V3) == (Fr(c + a), Fr(-c)), "Z8 L3 far vertex", e, f)
    chk(c < U3 < 2 * c and V3 < -a, "Z8 L3 kill", e, f)
    # L4: U/c = c/b exactly (the identity c² = a² + bc), and b ∤ c
    U4, V4 = Fr(c) + a * pG, Fr(a) * qG
    chk(U4 / c == Fr(c, b), "Z8 L4 identity c^2 = a^2 + bc", e, f)
    chk(c * c == a * a + b * c, "Z8 L4 ring identity", e, f)
    chk(c % b != 0, "Z8 L4 b does not divide c", e, f)
    j4 = U4 // c
    chk(V4 < -a * j4, "Z8 L4 staircase kill", e, f)
    # flush heads land exactly at 2c
    chk(c + c == 2 * c, "Z8 flush", e, f)
    # the mirror flush emptiness at r = 2 (e >= 3): (x+1)a + yb + zc = 2c
    if e >= 3:
        sols = [(x, y, z) for x in range(0, 2 * c // a + 1)
                for y in range(0, 2 * c // b + 1)
                for z in range(0, 3)
                if (x + 1) * a + y * b + z * c == 2 * c]
        chk(sols == [], "Z8 no upper flush at r=2", e, f, sols)

# fills of β and of α+γ in the (α,β)-calculus: solved once (pure integers)
sols_b = [(x, y, z) for x in range(0, 3) for y in range(0, 3)
          for z in range(0, 2) if x + 2 * z == 0 and y + z == 1]
chk(sols_b == [(0, 1, 0)], "Z5 fills of beta")
sols_ag = [(x, y, z) for x in range(0, 4) for y in range(0, 3)
           for z in range(0, 2) if x + 2 * z == 3 and y + z == 1]
chk(sorted(sols_ag) == [(1, 0, 1), (3, 1, 0)], "Z6 fills of alpha+gamma")
sols_ab = [(x, y, z) for x in range(0, 3) for y in range(0, 3)
           for z in range(0, 2) if x + 2 * z == 1 and y + z == 1]
chk(sols_ab == [(1, 1, 0)], "Z4 fills of alpha+beta")

print(f"from-scratch Z-fan verification: {checks} checks, "
      f"{len(fails)} failures over coprime (e,f), f <= {FMAX}, e >= 2, "
      f"all scales 4 <= k <= f, slots floor(f/e)+2 <= M <= k-2")
sys.exit(1 if fails else 0)
