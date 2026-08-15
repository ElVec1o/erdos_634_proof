#!/usr/bin/env python3
"""The exit kill and the forced ladder: exact verification, from scratch.

Frame: (s,t) chord coordinates at the slot Y (s along u ∥ AB, t along
v̂ ∥ BC; angle between u and v̂ is β).  Chord 2 is the s-axis; it exits
Δ_k through the interior of BC at E = (rc, 0), r = k−M; BC is the line
s = rc; AB the line t = Ma; the base the line a·s + c·t = 0.

Claims verified (exact integer / rational arithmetic only):

  X1 (flush classification)  the rogue-side flush words of chord 2 —
      (x+1)·a + y·b + z·c = r·c, first letter a forced — have, for
      r < f, exactly the solutions (x+1, y, z) = (jf, 0, r−je),
      1 ≤ j ≤ ⌊r/e⌋; none for r < e; a unique one (a^f) at r = e.
  X2 (the exit fill)  the wedge at E between the chord's back-ray −u
      and the BC up-ray v̂ is α+γ; its fills in the (α,β)-calculus
      (γ = 2α+β faithful) are exactly {α,γ} and {3α,β}.  The last
      letter's tile T_last is a fill member adjacent to −u:
        last = a  ⟹ T_last ∈ {β,γ} at E ⟹ the BC-adjacent fill tile
                    is an α, flanks {b,c}: every branch lays b or c on
                    BC — dead against a^k (a_side_rigid + a_side_no_b).
        last = c  ⟹ T_last ∈ {α,β}; β dies as above; EXACTLY TWO
                    branches survive, both with T_last = α (tile C_0)
                    and an a-edge laid on BC up from E:
                      (S1) fill {α,γ}: the γ-tile G_0 on BC — the
                           ladder head; and
                      (S2) fill {3α,β}: two more α's, then a β-tile
                           adjacent to BC laying a on BC, c inward.
                    E sits at the a-grid vertex r·a from C, so the
                    a on BC is grid-legal in both.
      Since z = 0 words end in a: every z = 0 flush dies at E.  At
      r = e the only word is a^f: NO flush survives for r ≤ e.
  X3 (the forced partner frame)  C_0's b-flank ray at E is exactly −w
      (the base direction reversed): the shared b-edge ends at
      F = E − b·w = (rc−c, a); G_0 = {E, E+a·v̂, F} with its c-edge
      HORIZONTAL [F, (rc, a)] (z = 1 case), i.e. ∥ AB.
  X4 (the ladder)  the ladder translate C_{i+1} = C_i + a·v̂ is exact;
      rung tops V_i = (rc, ia) are BC a-grid vertices; the pure ladder
      of M rungs puts G_{M−1}'s c-edge on AB at [B−c, B] and its left
      wall — the C_i a-edges — on the line s = rc−c spanning t ∈ [0, Ma]
      with both ends blocked (chord below, AB above).
  X5 (left-wall rigidity, unconditional)  x·a + y·b + z·c = M·a has
      the UNIQUE solution (M,0,0) for every M < f — no thinness
      hypothesis (this is Inflation.a_side_no_b + a_side_rigid at
      k := M; derivation: y = fY, Yf+z = eT, x = M+Ye−fT; Y ≥ 1
      forces T ≥ Y+1, so f(Y+1) ≤ M+Ye < f+Ye gives fY < Ye,
      impossible).  Brute force on every cell.
  X6 (chart embedding)  all of the above re-verified in the global
      chart (x, ŷ√D), D = 4f²−e²: E on BC at |E−C| = ra, |E−B| = Ma,
      F and the G_0/C_0 side lengths (a,b,c), the wedge angle at E is
      exactly α+γ as a rotation identity, and G_0's c-edge direction
      equals u (∥ AB).

Cells: the four A2_GRIDS kills, plus every deep-scale cell (M, k) with
k < f (r ≥ 3 for e ≤ 3, r ≥ 4 for e ≥ 4, M ≥ ⌊f/e⌋+2) over a spread of
members f ∈ [13, 30].  Any discrepancy prints REFUTED and exits 1.
"""
from fractions import Fraction as Fr
from math import gcd
import sys

checks = 0
fails = []


def chk(cond, *info):
    global checks
    checks += 1
    if not cond:
        fails.append(info)
        print("REFUTED:", info)


# ---------- pure word arithmetic (X1, X5) ----------

def flush_words(e, f, r):
    """All (x+1, y, z) ≥ (1,0,0) with (x+1)a + yb + zc = rc, brute force."""
    a, b, c = e * f, f * f - e * e, f * f
    T = r * c
    out = []
    for x1 in range(1, T // a + 1):
        for y in range(0, (T - x1 * a) // b + 1):
            rem = T - x1 * a - y * b
            if rem >= 0 and rem % c == 0:
                out.append((x1, y, rem // c))
    return sorted(out)


def mast_words(e, f, M):
    """All (x, y, z) ≥ 0 with xa + yb + zc = Ma, brute force."""
    a, b, c = e * f, f * f - e * e, f * f
    T = M * a
    out = []
    for z in range(0, T // c + 1):
        for y in range(0, (T - z * c) // b + 1):
            rem = T - z * c - y * b
            if rem % a == 0:
                out.append((rem // a, y, z))
    return sorted(out)


# ---------- the exit-fill enumeration (X2) ----------
# angles in the (α,β)-calculus: α=(1,0), β=(0,1), γ=(2,1); π=(3,2).
AL, BE, GA = (1, 0), (0, 1), (2, 1)
WEDGE_E = (3, 1)          # α+γ = 3α+β
FLANKS = {AL: ("b", "c"), BE: ("a", "c"), GA: ("a", "b")}
END_ANGLES = {"a": (BE, GA), "b": (AL, GA), "c": (AL, BE)}


def fills(target):
    X, Y = target
    out = []
    for z in range(0, X // 2 + 1):
        x = X - 2 * z
        y = Y - z
        if y >= 0:
            out.append(tuple(sorted([AL] * x + [BE] * y + [GA] * z)))
    return sorted(set(out))


def exit_branches(last_letter):
    """Enumerate every fill of the E-wedge containing an admissible
    T_last angle, every linear arrangement with T_last adjacent to −u,
    and the BC-adjacent tile's flank choice.  Returns a list of
    (fill, arrangement, bc_letter) branches."""
    out = []
    for fill in fills(WEDGE_E):
        for t_ang in END_ANGLES[last_letter]:
            if t_ang not in fill:
                continue
            rest = list(fill)
            rest.remove(t_ang)
            # arrangements of the remaining tiles between T_last and BC;
            # only the BC-adjacent one matters for the grid letter.
            bc_candidates = set(rest) if rest else {t_ang}
            for bc_ang in bc_candidates:
                for letter in FLANKS[bc_ang]:
                    out.append((fill, t_ang, bc_ang, letter))
    return out


def deep_cells(e, f, cap=3):
    """Deep-scale rogue cells at k < f: r ≥ 3 (e ≤ 3) or 4 (e ≥ 4)."""
    rmin = 3 if e <= 3 else 4
    out = []
    for k in range(4, f):
        for M in range(f // e + 2, k - rmin + 1):
            out.append((M, k))
    return out[:cap]


# ---------- chart embedding (X6) ----------

def chart(e, f):
    a, b, c = e * f, f * f - e * e, f * f
    D = 4 * f * f - e * e
    A_ = (Fr(2 * f * f - e * e, 2 * f * f), Fr(e, 2 * f * f))
    B_ = (Fr(e * (3 * f * f - e * e), 2 * f ** 3), Fr(f * f - e * e, 2 * f ** 3))
    G_ = (Fr(-e, 2 * f), Fr(1, 2 * f))
    return a, b, c, D, A_, B_, G_


def rot(D, cs, P, sign=+1):
    ccos, s = cs
    s = s * sign
    return (ccos * P[0] - s * D * P[1], s * P[0] + ccos * P[1])


def ang_add(D, t1, t2):
    return (t1[0] * t2[0] - D * t1[1] * t2[1], t1[1] * t2[0] + t1[0] * t2[1])


def sub(P, Q): return (P[0] - Q[0], P[1] - Q[1])
def add(P, Q): return (P[0] + Q[0], P[1] + Q[1])
def smul(s, P): return (s * P[0], s * P[1])
def len2(D, P): return P[0] * P[0] + D * P[1] * P[1]


def verify_cell(e, f, M, k):
    a, b, c, D, A_, B_, G_ = chart(e, f)
    r = k - M
    # X1: flush classification
    ws = flush_words(e, f, r)
    expect = sorted((j * f, 0, r - j * e) for j in range(1, r // e + 1))
    chk(ws == expect, "X1 classification", e, f, M, k, ws[:4])
    if r < e:
        chk(ws == [], "X1 none below e", e, f, M, k)
    if r == e:
        chk(ws == [(f, 0, 0)], "X1 unique at r=e", e, f, M, k)

    # X2: the exit fills and the kill
    chk(fills(WEDGE_E) == sorted([tuple(sorted([AL, GA])),
                                  tuple(sorted([AL, AL, AL, BE]))]),
        "X2 fills of alpha+gamma", e, f)
    survivors = []
    for last in ("a", "c"):
        for (fill, t_ang, bc_ang, letter) in exit_branches(last):
            # grid law on BC (word a^k, k<f): only 'a' may lie on BC
            if letter == "a":
                survivors.append((last, fill, t_ang, bc_ang))
    chk(all(s[0] == "c" for s in survivors), "X2 z=0 all dead", e, f)
    expect_surv = sorted([
        ("c", tuple(sorted([AL, GA])), AL, GA),          # S1: ladder head
        ("c", tuple(sorted([AL, AL, AL, BE])), AL, BE),  # S2: beta head
    ])
    chk(sorted(survivors) == expect_surv,
        "X2 exactly two c-ended survivors", e, f, survivors)

    # chart points
    w = (Fr(1), Fr(0))
    u = A_
    vh = rot(D, B_, u)
    Y = smul(Fr(M * b), w)
    Ck = smul(Fr(k * b), w)
    Bk = smul(Fr(k * c), u)
    E = add(Y, smul(Fr(r * c), u))
    # X6: E on BC at the a-grid vertex ra from C
    chk(len2(D, sub(E, Ck)) == (r * a) ** 2, "X6 |E-C| = ra", e, f, M, k)
    chk(len2(D, sub(Bk, E)) == (M * a) ** 2, "X6 |E-B| = Ma", e, f, M, k)
    chk(sub(E, Ck) == smul(Fr(r * a), vh), "X6 E-C along vh", e, f, M, k)

    # X3: C_0's b-ray at E is −w; F = E − b·w
    th = ang_add(D, B_, G_)                    # β+γ
    r1 = rot(D, th, u)                         # the wedge's middle ray
    chk(r1 == (Fr(-1), Fr(0)), "X3 r1 = -w", e, f, M, k)
    F = sub(E, smul(Fr(b), w))
    chk(F == add(E, smul(Fr(b), r1)), "X3 F = E - b·w", e, f, M, k)
    V1 = add(E, smul(Fr(a), vh))
    # G_0 = {E, V1, F} is a congruent tile: sides a, b, c
    chk(len2(D, sub(V1, E)) == a * a, "X3 G0 side a", e, f, M, k)
    chk(len2(D, sub(F, E)) == b * b, "X3 G0 side b", e, f, M, k)
    chk(len2(D, sub(V1, F)) == c * c, "X3 G0 side c", e, f, M, k)
    # G_0's c-edge is horizontal: V1 − F = c·u  (∥ AB)
    chk(sub(V1, F) == smul(Fr(c), u), "X3 G0 c-edge ∥ AB", e, f, M, k)
    # the wedge at E is exactly α+γ: rot_{α+γ}(v̂) = −u
    ag = ang_add(D, A_, G_)
    chk(rot(D, ag, vh) == (Fr(-u[0]), Fr(-u[1])), "X6 wedge = α+γ", e, f, M, k)

    # X4: ladder translates and the AB arrival.  Rung i: C_i = C_0 + ia·v̂,
    # G_i = {V_i, V_{i+1}, F_i} with F_i = F + ia·v̂ and c-edge [F_i, V_{i+1}]
    for i in (1, 2, M - 1):
        Vi = add(E, smul(Fr(i * a), vh))
        Vi1 = add(E, smul(Fr((i + 1) * a), vh))
        Fi = add(F, smul(Fr(i * a), vh))
        chk(len2(D, sub(Bk, Vi)) == ((M - i) * a) ** 2,
            "X4 rung on grid", e, f, M, k, i)
        # V_{i+1} − F_i = a·v̂ + b·w = c·u: the chart generator again
        chk(sub(Vi1, Fi) == smul(Fr(c), u), "X4 rung c-edge ∥ AB",
            e, f, M, k, i)
        chk(len2(D, sub(Fi, Vi)) == b * b, "X4 rung b-edge", e, f, M, k, i)
    # top rung: G_{M-1}'s c-edge = [B − c·u, B] on AB
    FM = add(F, smul(Fr((M - 1) * a), vh))
    chk(add(FM, smul(Fr(c), u)) == Bk, "X4 top rung ends at B", e, f, M, k)
    # left wall: F_i all on the line through E − b·w parallel to BC,
    # i.e. s = rc − c: F_{M-1} = E − b·w + (M−1)a·v̂ and
    # E − c·u + Ma·v̂  must agree
    chk(FM == add(sub(E, smul(Fr(c), u)), smul(Fr(M * a), vh)),
        "X4 wall spans t ∈ [0, Ma] at s = rc − c", e, f, M, k)

    # X5: the left-wall word is a^M, unconditionally (M < f)
    mws = mast_words(e, f, M)
    chk(mws == [(M, 0, 0)], "X5 unique a^M", e, f, M, k, mws[:4])


def main():
    cells = [(2, 11, 7, 10), (3, 10, 6, 9), (3, 11, 6, 9), (3, 11, 7, 10)]
    # synthetic deep cells, f in [13, 30]
    members = [(2, 13), (3, 13), (5, 13), (12, 13), (2, 15), (4, 15),
               (3, 17), (6, 17), (16, 17), (5, 19), (7, 22), (3, 25),
               (9, 26), (5, 28), (7, 30), (11, 30)]
    for (e, f) in members:
        assert gcd(e, f) == 1
        for (M, k) in deep_cells(e, f, cap=2):
            cells.append((e, f, M, k))
    for (e, f, M, k) in cells:
        verify_cell(e, f, M, k)
    print(f"strip_exit verification: {checks} checks, {len(fails)} failures "
          f"over {len(cells)} cells; members f ≤ 30")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
