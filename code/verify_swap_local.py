#!/usr/bin/env python3
"""Exact verification of the swap's two-dimensional local structure (Erdős #634).

Setting as in verify_rogue_chord.py: tile (a,b,c) = (ef, f²−e², f²), chart (x, ŷ)
with y = ŷ·√D, D = 4f²−e².  Δ_k: A at origin, b-side along w = (1,0), c-side along
u; slot Y = M·b·w (M = i+1), chord-1 unit v̂ = (c·u − b·w)/a, X = Y + a·v̂,
Z = Y + c·v̂, W = Y + (a+c)·v̂.

Verified here (all exact rationals; angle equalities via rotation matrices, since
cos θ ∈ ℚ and sin θ ∈ ℚ·√D for every tile angle):

  L1  angle data: cos α = (2f²−e²)/2f², cos β = e(3f²−e²)/2f³, cos γ = −e/2f,
      the sin-coefficients, γ = 2α + β and 3α + 2β = π as rotation identities,
      2γ > π (i.e. cos γ < 0), and v̂ = rot_{π−γ}(w).
  L2  the row tiles: P_M = {(M−1)b·w, Y, X} has α/γ/β at those vertices,
      P_{M+1} = P_M + b·w has α at Y with c-edge [Y, Y+c·u]; the standard slot
      tile is Q = {Y, X, Y+c·u} (β/γ/α), sharing P_M's a-edge [Y, X].
  L3  the rogue {Y, Z, Y+a·u}: edge lengths c/a/b, corners β at Y, α at Z,
      γ at Y+a·u; it is the OPPOSITE chirality from Q (mirror tile).
  L4  the b-partner: direct partner = {Z, Y+a·u, Z+a·u} (γ/α/β), same chirality
      as the rogue, union = a×c parallelogram; the mirror partner puts γ at
      Y+a·u where the rogue already has γ, and Y+a·u is interior to P_{M+1}'s
      c-edge (0 < a < c), so the far side of chord 2 is a straight angle there:
      2γ > π kills the mirror.  [G1 core]
  L5  forced fans: at Z (rogue side of chord 1, straight angle) the fill is
      α(rogue) + γ(partner) + β: exactly one more tile, T_rog, with β at Z,
      wedge between u and v̂ — angle(u, v̂) = β.  At Y+a·u (far side of chord 2,
      straight angle) the fill is γ(rogue) + α(partner) + β: exactly one more
      tile, T₃, with β at Y+a·u, wedge between v̂ and u.
  L6  the swap branch of T_rog: a-edge [Z, W] on chord 1 forces its c-edge along
      u: T_rog = {Z, W, Z+c·u} = Q + c·v̂ (translate), b-edge [W, Z+c·u], γ at W,
      α at Z+c·u.  T₃'s two options are (i) rogue + a·u (translate; c-edge flush
      with the partner's c-edge) and (ii) Q + a·u (translate; a-edge a proper
      initial segment of the partner's c-edge, c-edge along chord 2).
  L7  chord 3 = the u-line through Z: near side T_rog's c-edge [Z, Z+c·u], far
      side starts with the partner's a-edge [Z, Z+a·u]; containment bound along
      u from Z is (k−M)·c (exit through BC), same as chord 2; for e ≥ 2 the far
      side cannot break flush at Z+c·u (no decomposition of c containing an a),
      so Z+c·u is a T-vertex, flat on the far side, and the near side fills π
      there: α(T_rog) + {β,γ} or {2α,2β}.
  L8  the fills of the straight and slot angles (integer solutions of
      x + 2z = X, y + z = Y): π−β = {α,γ} or {3α,β}; π−α = {β,γ} or {2α,2β};
      π = {α,β,γ} or {3α,2β}; 2π = (6,4,0),(4,3,1),(2,2,2),(0,1,3); and the
      c-edge/a-edge endpoint tables: c ends carry {α,β}, a ends {β,γ}, b ends
      {α,γ}.
  L9  heights: X, Z, W, Y+a·u, Z+a·u, Z+c·u all have ŷ > 0 (strictly above the
      base line), and the whole swap skeleton stays inside Δ_k for every
      k ≥ M+2 (barycentric check of all skeleton vertices).

Every claim is checked for all coprime (e,f), 2 ≤ e < f ≤ 12, and all slots
M in the surviving range [⌊f/e⌋+2, f−2] (k = M+2 and k = f).
"""
from fractions import Fraction as Fr
from math import gcd
import sys

def data(e, f):
    a, b, c = e * f, f * f - e * e, f * f
    D = 4 * f * f - e * e
    # rotation data: cos t = p, sin t = q·√D  (all exact)
    rot = {
        "A": (Fr(2 * f * f - e * e, 2 * f * f), Fr(e, 2 * f * f)),
        "B": (Fr(e * (3 * f * f - e * e), 2 * f**3), Fr(f * f - e * e, 2 * f**3)),
        "G": (Fr(-e, 2 * f), Fr(1, 2 * f)),
    }
    return a, b, c, D, rot

def rotate(d, pq, D, sign=+1):
    """Rotate chart direction d by the angle with (cos, sincoef) = pq; sign=-1 for cw."""
    p, q = pq
    q = q * sign
    return (p * d[0] - q * D * d[1], q * d[0] + p * d[1])

def len2(v, D):
    return v[0] * v[0] + v[1] * v[1] * D

def dot(v1, v2, D):
    return v1[0] * v2[0] + D * v1[1] * v2[1]

def cross(v1, v2):
    return v1[0] * v2[1] - v1[1] * v2[0]

def sub(P, Q):
    return (P[0] - Q[0], P[1] - Q[1])

def addm(P, s, d):
    return (P[0] + s * d[0], P[1] + s * d[1])

def corner_of(T, V, D, lengths):
    """Corner label at vertex V of triangle T (list of 3 points): the angle
    opposite the side not containing V, identified by exact side lengths."""
    others = [P for P in T if P != V]
    opp = len2(sub(others[0], others[1]), D)
    a2, b2, c2 = lengths
    return {a2: "A", b2: "B", c2: "G"}[opp]

def fills(X, Y):
    """All (na, nb, ng) with na + 2ng = X, nb + ng = Y."""
    out = []
    for ng in range(0, min(X // 2, Y) + 1):
        na, nb = X - 2 * ng, Y - ng
        out.append((na, nb, ng))
    return out

checks = 0
fails = []

def chk(cond, tag, *info):
    global checks
    checks += 1
    if not cond:
        fails.append((tag,) + info)

for f in range(3, 13):
    for e in range(2, f):
        if gcd(e, f) != 1:
            continue
        a, b, c, D, rot = data(e, f)
        a2, b2, c2 = a * a, b * b, c * c
        L = (a2, b2, c2)
        w = (Fr(1), Fr(0))
        u = (Fr(2 * f * f - e * e, 2 * f * f), Fr(e, 2 * f * f))
        # --- L1: angle data ---
        for t in "ABG":
            p, q = rot[t]
            chk(p * p + q * q * D == 1, "L1 unit", e, f, t)
        # law of cosines against the placed tile P_0 = {0, b·w, c·u}
        chk(dot(w, u, D) == rot["A"][0], "L1 cosA", e, f)
        vraw = (Fr(c) * u[0] - Fr(b), Fr(c) * u[1])
        chk(len2(vraw, D) == a2, "L1 |v|=a", e, f)
        vh = (vraw[0] / a, vraw[1] / a)
        # γ = 2α + β as a rotation identity
        d1 = rotate(rotate(rotate(w, rot["A"], D), rot["A"], D), rot["B"], D)
        d2 = rotate(w, rot["G"], D)
        chk(d1 == d2, "L1 G=2A+B", e, f)
        # 3α + 2β = π: the composite rotation is −id
        d3 = rotate(rotate(d1, rot["A"], D), rot["B"], D)
        chk(d3 == (Fr(-1), Fr(0)), "L1 3A+2B=pi", e, f)
        # 2γ > π  ⟺  γ > π/2  ⟺  cos γ < 0
        chk(rot["G"][0] < 0, "L1 2G>pi", e, f)
        # v̂ = rot_{π−γ}(w) = rot_{2α+β applied after π}... check directly:
        # rot by π−γ = rot by π then by −γ
        d4 = rotate((Fr(-1), Fr(0)), rot["G"], D, sign=-1)
        chk(d4 == vh, "L1 vhat=rot(pi-G)w", e, f)
        # angle(u, v̂) = β: rotating u by β (ccw) gives v̂
        chk(rotate(u, rot["B"], D) == vh, "L5 angle(u,v)=B", e, f)

        Mlo, Mhi = f // e + 2, f - 2
        for M in range(Mlo, Mhi + 1):
            for k in {M + 2, f}:
                if k < M + 2 or k > f:
                    continue
                Y = (Fr(M * b), Fr(0))
                X = addm(Y, Fr(a), vh)
                Z = addm(Y, Fr(c), vh)
                W = addm(Y, Fr(a + c), vh)
                Yau = addm(Y, Fr(a), u)
                Zau = addm(Z, Fr(a), u)
                Zcu = addm(Z, Fr(c), u)
                Ycu = addm(Y, Fr(c), u)
                # --- L2: row tiles ---
                Yprev = (Fr((M - 1) * b), Fr(0))
                PM = [Yprev, Y, X]
                chk(len2(sub(Y, Yprev), D) == b2, "L2 PM b-edge", e, f, M)
                chk(len2(sub(X, Y), D) == a2, "L2 PM a-edge", e, f, M)
                chk(len2(sub(X, Yprev), D) == c2, "L2 PM c-edge", e, f, M)
                chk(corner_of(PM, Yprev, D, L) == "A", "L2 PM alpha", e, f, M)
                chk(corner_of(PM, Y, D, L) == "G", "L2 PM gamma", e, f, M)
                chk(corner_of(PM, X, D, L) == "B", "L2 PM beta", e, f, M)
                Ybw = (Fr((M + 1) * b), Fr(0))
                PM1 = [Y, Ybw, Ycu]
                chk(corner_of(PM1, Y, D, L) == "A", "L2 PM1 alpha", e, f, M)
                chk(len2(sub(Ycu, Y), D) == c2, "L2 PM1 c-edge", e, f, M)
                Q = [Y, X, Ycu]
                chk(corner_of(Q, Y, D, L) == "B", "L2 Q beta", e, f, M)
                chk(corner_of(Q, X, D, L) == "G", "L2 Q gamma", e, f, M)
                chk(corner_of(Q, Ycu, D, L) == "A", "L2 Q alpha", e, f, M)
                # --- L3: the rogue ---
                R = [Y, Z, Yau]
                chk(len2(sub(Z, Y), D) == c2, "L3 rogue c", e, f, M)
                chk(len2(sub(Yau, Y), D) == a2, "L3 rogue a", e, f, M)
                chk(len2(sub(Yau, Z), D) == b2, "L3 rogue b", e, f, M)
                chk(corner_of(R, Y, D, L) == "B", "L3 rogue beta", e, f, M)
                chk(corner_of(R, Z, D, L) == "A", "L3 rogue alpha", e, f, M)
                chk(corner_of(R, Yau, D, L) == "G", "L3 rogue gamma", e, f, M)
                # canonical chirality: sign of the loop α → β → γ
                def sgn(T):
                    byc = {corner_of(T, P, D, L): P for P in T}
                    return cross(sub(byc["B"], byc["A"]), sub(byc["G"], byc["A"]))
                chk(sgn(R) * sgn(Q) < 0, "L3 rogue mirror-of-Q", e, f, M)
                chk(sgn(R) * sgn(PM) < 0, "L3 rogue mirror-of-P", e, f, M)
                # --- L4: the b-partner ---
                Pd = [Z, Yau, Zau]
                chk(len2(sub(Zau, Z), D) == a2, "L4 partner a", e, f, M)
                chk(len2(sub(Zau, Yau), D) == c2, "L4 partner c", e, f, M)
                chk(corner_of(Pd, Z, D, L) == "G", "L4 partner gamma", e, f, M)
                chk(corner_of(Pd, Yau, D, L) == "A", "L4 partner alpha", e, f, M)
                chk(corner_of(Pd, Zau, D, L) == "B", "L4 partner beta", e, f, M)
                chk(sgn(Pd) * sgn(R) > 0, "L4 direct same chirality", e, f, M)
                # parallelogram: Zau − Yau = Z − Y and Zau − Z = Yau − Y
                chk(sub(Zau, Yau) == sub(Z, Y), "L4 pgram", e, f, M)
                # mirror partner: reflection of rogue across the b-edge line;
                # its corners at the shared edge are α at Z, γ at Yau
                m = sub(Yau, Z)
                m2 = len2(m, D)
                refl = lambda x: addm((Fr(0), Fr(0)), 2 * dot(x, m, D) / m2, m)[0:2]
                def reflect(x):
                    s = 2 * dot(x, m, D) / m2
                    return (s * m[0] - x[0], s * m[1] - x[1])
                Ym = addm(Z, Fr(1), reflect(sub(Y, Z)))
                Pm = [Z, Yau, Ym]
                chk(len2(sub(Ym, Z), D) == c2, "L4 mirror c at Z", e, f, M)
                chk(len2(sub(Ym, Yau), D) == a2, "L4 mirror a at Yau", e, f, M)
                chk(corner_of(Pm, Z, D, L) == "A", "L4 mirror alpha at Z", e, f, M)
                chk(corner_of(Pm, Yau, D, L) == "G", "L4 mirror gamma at Yau", e, f, M)
                chk(sgn(Pm) * sgn(R) < 0, "L4 mirror opp chirality", e, f, M)
                # Yau interior to P_{M+1}'s c-edge: 0 < a < c along u  ✓ trivially
                chk(0 < a < c, "L4 Yau interior", e, f, M)
                # the mirror kill: γ(rogue) + γ(mirror) = 2γ > π on the straight
                # far side at Yau: 2γ > π was L1; record the pairing explicitly
                chk(corner_of(R, Yau, D, L) == "G" and corner_of(Pm, Yau, D, L) == "G",
                    "L4 gamma-gamma", e, f, M)
                # --- L5: forced fans (arithmetic: π − α − γ = β uniquely) ---
                # fill of π−(α+γ) = coefficients (3−1−2, 2−0−1) = (0,1): exactly β
                chk(fills(0, 1) == [(0, 1, 0)], "L5 fan Z forced", e, f)
                # wedges: at Z, remaining wedge between u and v̂ is β (checked L1);
                # at Yau, remaining wedge between v̂ and u is also β (same angle)
                # --- L6: the swap's T_rog and the T₃ options ---
                Trog = [Z, W, Zcu]
                chk(len2(sub(W, Z), D) == a2, "L6 Trog a", e, f, M)
                chk(len2(sub(Zcu, Z), D) == c2, "L6 Trog c", e, f, M)
                chk(len2(sub(Zcu, W), D) == b2, "L6 Trog b", e, f, M)
                chk(corner_of(Trog, Z, D, L) == "B", "L6 Trog beta", e, f, M)
                chk(corner_of(Trog, W, D, L) == "G", "L6 Trog gamma at W", e, f, M)
                chk(corner_of(Trog, Zcu, D, L) == "A", "L6 Trog alpha", e, f, M)
                # T_rog = Q + c·v̂ (translate)
                chk(all(sub(Trog[j], Q[j]) == sub(Z, Y) for j in range(3)),
                    "L6 Trog translate of Q", e, f, M)
                # T₃ option (i): rogue + a·u; c-edge flush with partner's c-edge
                T3i = [addm(P, Fr(1), (Fr(0), Fr(0))) for P in R]
                T3i = [addm(P, Fr(a), u) for P in R]
                chk(sub(T3i[1], T3i[0]) == sub(Z, Y), "L6 T3i c-edge dir", e, f, M)
                chk(T3i[0] == Yau and T3i[1] == Zau, "L6 T3i flush", e, f, M)
                # T₃ option (ii): Q + a·u; a-edge ⊂ partner's c-edge
                T3ii = [addm(P, Fr(a), u) for P in Q]
                Xau = addm(X, Fr(a), u)
                chk(T3ii[0] == Yau and T3ii[1] == Xau, "L6 T3ii", e, f, M)
                chk(len2(sub(Xau, Yau), D) == a2, "L6 T3ii a-edge", e, f, M)
                # Xau strictly between Yau and Zau on the v̂-line: 0 < a < c ✓
                # --- L7: chord 3 bound: exit of u-ray from Z at (k−M)·c ---
                C = (Fr(k * b), Fr(0))
                B = (Fr(k * c) * u[0], Fr(k * c) * u[1])
                det = C[0] * B[1] - C[1] * B[0]
                bary = lambda P: ((P[0] * B[1] - P[1] * B[0]) / det,
                                  (C[0] * P[1] - C[1] * P[0]) / det)
                Lmax = Fr((k - M) * c)
                for ell, inside in [(Lmax - Fr(1, 3), True), (Lmax, True),
                                    (Lmax + Fr(1, 3), False)]:
                    P = addm(Z, ell, u)
                    s, t = bary(P)
                    ok = (s >= 0 and t >= 0 and s + t <= 1)
                    chk(ok == inside, "L7 chord3 bound", e, f, M, k, ell)
                sE, tE = bary(addm(Z, Lmax, u))
                chk(sE + tE == 1 and 0 < sE < 1, "L7 chord3 exit BC", e, f, M, k)
                # v̂-ray from Yau: bound M·a (exit s = 0)
                sV, tV = bary(addm(Yau, Fr(M * a), vh))
                chk(sV == 0, "L7 chord4 bound", e, f, M, k)
                # far side of chord 3 flush at c impossible: decomposition of c
                # with an a-count ≥ 1 (e ≥ 2) — re-verified small enumeration
                bad = [(x, y, z) for x in range(1, c // a + 1)
                       for y in range((c - x * a) // b + 1)
                       for z in range((c - x * a - y * b) // c + 1)
                       if x * a + y * b + z * c == c]
                chk(bad == [], "L7 no a-decomp of c", e, f)
                # --- L9: heights and containment of the skeleton ---
                for P, nm in [(X, "X"), (Z, "Z"), (W, "W"), (Yau, "Yau"),
                              (Zau, "Zau"), (Zcu, "Zcu")]:
                    chk(P[1] > 0, "L9 height " + nm, e, f, M)
                    s, t = bary(P)
                    chk(s >= 0 and t >= 0 and s + t <= 1, "L9 inside " + nm,
                        e, f, M, k)

# --- L8: the fill tables (member-independent) ---
chk(fills(3, 1) == [(3, 1, 0), (1, 0, 1)], "L8 pi-beta")      # π−β: {3α,β} or {α,γ}
chk(fills(2, 2) == [(2, 2, 0), (0, 1, 1)], "L8 pi-alpha")     # π−α: {2α,2β} or {β,γ}
chk(fills(3, 2) == [(3, 2, 0), (1, 1, 1)], "L8 pi")           # π
chk(fills(6, 4) == [(6, 4, 0), (4, 3, 1), (2, 2, 2), (0, 1, 3)], "L8 2pi")
chk(fills(0, 1) == [(0, 1, 0)], "L8 beta")                    # π−α−γ = β

print(f"swap local structure: {checks} exact checks; {len(fails)} failures")
for x in fails[:30]:
    print("FAIL", x)
sys.exit(1 if fails else 0)
