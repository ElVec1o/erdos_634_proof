#!/usr/bin/env python3
"""FROM-SCRATCH re-verification of the X-fan kill (independent of the engine).

No imports from the project. Points live in the real plane as pairs
(x, y) with x rational and y = q*sqrt(D) stored as the rational q; D = 4f^2-e^2.
The triangle Delta_k is placed from its side lengths alone:
    A = (0,0), C = (k*b, 0), B = apex with |AB| = k*c, |CB| = k*a.
Everything else is linear algebra over Q(sqrt(D)); the only trigonometric
inputs are cosines COMPUTED from dot products of placed vectors.

Verified claims (the load-bearing steps of RogueFan.lean and commit cba63d4):
  S1  the apex B = (k(2f^2-e^2)/(2f), k e /2 *sqrt(D)/f ... ) chosen with
      y > 0 satisfies |AB| = kc, |CB| = ka exactly.
  S2  with vhat = (B - C)/(k a):  X := Y + a*vhat, Z := Y + c*vhat satisfy
      X strictly between Y and Z on the segment [Y, Z]  (rogue c-edge
      covers X in its interior).
  S3  P_M := (Y - b*w, Y, X) has side lengths (b, a, c) — a congruent tile —
      and its corner at X has cosine e(3f^2-e^2)/(2f^3)  (= beta).
  S4  Q := ((M-1)b*w, (M-2)b*w + B/k, X) has side lengths (c, a, b); its
      b-edge satisfies the exact identity  X - ((M-2)b*w + B/k) = b*w,
      so it leaves X along -w; its corner at X has cosine (2f^2-e^2)/(2f^2)
      (= alpha).
  S5  X - (M-1)b*w = B/k, which lies on the open segment AB: the -w ray from
      X meets AB at distance exactly (M-1)b.
  S6  angle check: beta(P_M at X) + alpha(Q at X) + gamma = pi holds as the
      rotation identity on placed vectors (the residual is exactly gamma).
  S7  the twelve fan assignments: tiles placed at X with edge lengths from
      the incidence table (alpha:{b,c}, beta:{a,c}, gamma:{a,b}), the
      chord-adjacent tile laying c on [X, X + c*vhat]; every tile vertex is
      tested against the half-plane of line AB (side of C).  The resulting
      per-(e,f,M) verdict table must equal BOTH the closed-form DNF of
      rogue_chord_survivors.fan_alive AND the engine-side table.
  S8  the two Lean kill facts on the verdicts: every in-range M = 3 slot is
      dead, and every slot with (M-1)(f^2-e^2) < f^2 is dead.

Any discrepancy prints REFUTED lines and exits 1.
"""
from fractions import Fraction as Fr
from math import gcd
import sys

# ---- Q(sqrt(D)) plane: points (x, yq) meaning (x, yq*sqrt(D)) --------------

def sub(P, Q): return (P[0] - Q[0], P[1] - Q[1])
def add(P, Q): return (P[0] + Q[0], P[1] + Q[1])
def smul(s, P): return (s * P[0], s * P[1])

def dot(D, P, Q):  return P[0] * Q[0] + D * P[1] * Q[1]     # real dot
def len2(D, P):    return dot(D, P, P)                       # real |P|^2
def cross_q(P, Q): return P[0] * Q[1] - P[1] * Q[0]          # real cross / sqrt(D)

def rot_by(D, cos_t, sin_q, P, sign=+1):
    """Rotate real point P by angle t: cos t = cos_t (rational), sin t =
    sin_q*sqrt(D) (sin_q rational).  Exact in the representation."""
    x, yq = P
    s = sin_q * sign
    return (cos_t * x - s * D * yq, s * x + cos_t * yq)

checks = 0
fails = []
def chk(cond, *info):
    global checks
    checks += 1
    if not cond:
        fails.append(info)
        print("REFUTED:", info)

def fan_verdict_scratch(e, f, M, k):
    """True iff some of the twelve fan assignments fits inside AB half-plane."""
    a, b, c = e * f, f * f - e * e, f * f
    D = 4 * f * f - e * e
    # S1: place the triangle from side lengths
    kb, kc, ka = k * b, k * c, k * a
    Bx = Fr(kc * kc - ka * ka + kb * kb, 2 * kb)
    # By^2 = (kc)^2 - Bx^2 must be D * (rational)^2
    By2 = Fr(kc * kc) - Bx * Bx
    Byq2 = By2 / D
    # sqrt of a rational square, exactly
    from math import isqrt
    num, den = Byq2.numerator, Byq2.denominator
    rn, rd = isqrt(num), isqrt(den)
    chk(rn * rn == num and rd * rd == den, "S1 sqrt", e, f, k)
    Byq = Fr(rn, rd)
    A = (Fr(0), Fr(0)); C = (Fr(kb), Fr(0)); B = (Bx, Byq)
    chk(len2(D, sub(B, A)) == kc * kc, "S1 |AB|", e, f, k)
    chk(len2(D, sub(B, C)) == ka * ka, "S1 |CB|", e, f, k)
    w = (Fr(1), Fr(0))
    vhat = smul(Fr(1, ka), sub(B, C))
    chk(len2(D, vhat) == 1, "S2 unit", e, f, k)
    Y = (Fr(M * b), Fr(0))
    X = add(Y, smul(Fr(a), vhat))
    Z = add(Y, smul(Fr(c), vhat))
    # S2: X interior to [Y, Z]
    chk(0 < a < c, "S2 interior", e, f)
    # S3: P_M congruent with the right corner at X
    Yp = (Fr((M - 1) * b), Fr(0))
    chk(len2(D, sub(Y, Yp)) == b * b, "S3 b", e, f, M)
    chk(len2(D, sub(X, Y)) == a * a, "S3 a", e, f, M)
    chk(len2(D, sub(X, Yp)) == c * c, "S3 c", e, f, M)
    u1, u2 = sub(Y, X), sub(Yp, X)
    cosX = dot(D, u1, u2)  # |u1||u2| = a*c
    chk(cosX * 2 * f ** 3 == Fr(e * (3 * f * f - e * e)) * a * c,
        "S3 cos beta", e, f, M)
    # S4: Q with b-edge along -w from X
    Wp = add((Fr((M - 2) * b), Fr(0)), smul(Fr(1, k), B))
    chk(len2(D, sub(X, Wp)) == b * b, "S4 b-len", e, f, M)
    chk(sub(X, Wp) == (Fr(b), Fr(0)), "S4 b-horizontal", e, f, M)
    chk(len2(D, sub(Wp, Yp)) == a * a, "S4 a", e, f, M)
    v1, v2 = sub(Wp, X), sub(Yp, X)
    cosXQ = dot(D, v1, v2)  # |v1||v2| = b*c
    chk(cosXQ * 2 * f * f == Fr(2 * f * f - e * e) * b * c, "S4 cos alpha",
        e, f, M)
    # S5: the -w ray from X meets AB at distance (M-1)b
    chk(sub(X, smul(Fr((M - 1) * b), w)) == smul(Fr(1, k), B), "S5 room",
        e, f, M)
    # S6: the residual at X is exactly gamma = 2*alpha + beta: rotating vhat
    # ccw by alpha, alpha, beta lands exactly on -w (the Q b-edge direction)
    cos_a, sin_a = Fr(2 * f * f - e * e, 2 * f * f), Fr(e, 2 * f * f)
    cos_b, sin_b = Fr(e * (3 * f * f - e * e), 2 * f ** 3), \
        Fr(f * f - e * e, 2 * f ** 3)
    d6 = rot_by(D, cos_a, sin_a, vhat)
    d6 = rot_by(D, cos_a, sin_a, d6)
    d6 = rot_by(D, cos_b, sin_b, d6)
    chk(d6 == (Fr(-1), Fr(0)), "S6 residual gamma", e, f)
    # the cosines used above are themselves certified: cos_a matches S4's
    # dot-product cosine and cos_b matches S3's; sin^2 = 1 - cos^2:
    chk(cos_a * cos_a + D * sin_a * sin_a == 1, "S6 sin alpha", e, f)
    chk(cos_b * cos_b + D * sin_b * sin_b == 1, "S6 sin beta", e, f)
    # S7: twelve assignments; interface rays accumulate ccw from vhat
    lens = {"a": a, "b": b, "c": c}
    edges_of = {"A": ("b", "c"), "B": ("a", "c"), "G": ("a", "b")}
    ang = {"A": (cos_a, sin_a), "B": (cos_b, sin_b)}
    inside = lambda P: cross_q(B, P) >= 0 if cross_q(B, C) >= 0 else \
        cross_q(B, P) <= 0
    # (side of AB containing C; on-line counts as inside)
    ok_any = False
    for order in (("B", "A", "A"), ("A", "B", "A"), ("A", "A", "B")):
        # chord-adjacent tile is order[0], must have a c-edge on the chord;
        # the last tile sits against -w
        d = vhat
        rays = [d]
        okorder = True
        for t in order:
            if t == "G":
                okorder = False
                break
            ct, st = ang[t]
            d = rot_by(D, ct, st, d)
            rays.append(d)
        if not okorder:
            continue
        chk(rays[-1] == (Fr(-1), Fr(0)), "S7 fan closes", e, f, order)
        # tile i occupies rays[i], rays[i+1]; edge letters: tile 0 lays c on
        # rays[0]; other edge is the remaining letter of its corner
        for pick0 in [x for x in edges_of[order[0]] if x != "c"]:
            # tile0: c on the chord ray, pick0 on rays[1]
            for pick1 in edges_of[order[1]]:
                oth1 = [x for x in edges_of[order[1]] if x != pick1]
                if not oth1:
                    continue
                for pick2 in edges_of[order[2]]:
                    oth2 = [x for x in edges_of[order[2]] if x != pick2]
                    if not oth2:
                        continue
                    # edges at rays: tile0: (c @ rays0, pick0 @ rays1)
                    # tile1: (pick1 @ rays1, oth1 @ rays2)
                    # tile2: (pick2 @ rays2, oth2 @ rays3=-w)
                    pts = [add(X, smul(Fr(lens["c"]), rays[0])),
                           add(X, smul(Fr(lens[pick0]), rays[1])),
                           add(X, smul(Fr(lens[pick1]), rays[1])),
                           add(X, smul(Fr(lens[oth1[0]]), rays[2])),
                           add(X, smul(Fr(lens[pick2]), rays[2])),
                           add(X, smul(Fr(lens[oth2[0]]), rays[3]))]
                    # sanity: each tile's third side must close to a tile edge
                    s1 = len2(D, sub(pts[1], pts[0]))
                    s2 = len2(D, sub(pts[3], pts[2]))
                    s3 = len2(D, sub(pts[5], pts[4]))
                    third = {("a"): a, "b": b, "c": c}
                    lets = {a * a, b * b, c * c}
                    chk(s1 in lets and s2 in lets and s3 in lets,
                        "S7 tile closes", e, f, M, order)
                    if all(inside(P) for P in pts):
                        ok_any = True
    return ok_any

# ---- the closed-form DNF (restated independently from the Lean statement) --

def fan_alive_dnf(e, f, M):
    a, b, c = e * f, f * f - e * e, f * f
    R = (M - 1) * b
    K1 = c <= R
    K2 = c * (2 * f * f - e * e) <= R * f * f
    K3 = c * f <= R * e
    K4 = a * (2 * f * f - e * e) <= R * f * f
    K5 = a * b * (3 * f * f - e * e) <= R * f ** 4
    K6 = c * b * (3 * f * f - e * e) <= R * f ** 4
    Kb = b * b * (3 * f * f - e * e) <= R * f ** 4
    return K3 or (K1 and K2) or (K3 and K4) or \
        (K5 and ((Kb and K2) or K6) and (K1 or K2))

mism = 0
table = {}
for f in range(3, 13):
    for e in range(2, f):
        if gcd(e, f) != 1:
            continue
        for M in range(f // e + 2, f - 1):
            v_scratch = fan_verdict_scratch(e, f, M, M + 2)
            v_dnf = fan_alive_dnf(e, f, M)
            table[(e, f, M)] = v_scratch
            if v_scratch != v_dnf:
                mism += 1
                print("REFUTED: DNF mismatch", e, f, M, v_scratch, v_dnf)
            # S8: the Lean kill facts
            if M == 3:
                chk(not v_scratch, "S8 M=3 kill", e, f)
            if (M - 1) * (f * f - e * e) < f * f:
                chk(not v_scratch, "S8 headline kill", e, f, M)

print(f"from-scratch X-fan verification: {checks} checks, {len(fails)} failures, "
      f"{mism} DNF mismatches over {len(table)} slots")
killed = sorted([k for k, v in table.items() if not v])
print(f"fan-dead slots ({len(killed)}):", killed)
sys.exit(1 if (fails or mism) else 0)
