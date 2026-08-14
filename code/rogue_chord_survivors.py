#!/usr/bin/env python3
"""Final tabulation: the two-sided chord system with all four kills.

Kills (all exact-arithmetic, verified separately):
  K0 containment       — slot M = i+1 rogue-free unless M·e > f  (RogueContainment)
  K1 first-slot        — M = ⌊f/e⌋+1 dies: separated by L ≥ a+c > M·a;
                         close (M=2) by the b-run/Δ argument
  K2 boundary exit     — L = M·a impossible (no c in a decomposition of M·a, M < f)
  K3 top slot          — M = k−1 dies via chord 2 (bound c; far side has an a)

Surviving slots of the step W(k−1) ⟹ W(k):  ⌊f/e⌋+2 ≤ M ≤ k−2.
For the wall scale k = f:                    ⌊f/e⌋+2 ≤ M ≤ f−2.
W(k) closes outright for k ≤ ⌊f/e⌋+3; the member closes if ⌊f/e⌋ ≥ f−3.

For each survivor slot: chord-1 survivors (words R = a·…, S = c·…, equal sums,
disjoint proper partial sums, L < M·a — K2 makes the bound strict) and the
chord-2 system (R2 = a·…, S2 = c·…, bound (f−M)·c at k = f).
"""
from math import gcd
from functools import lru_cache
import sys

ALPHA, BETA, GAMMA = "α", "β", "γ"

def orientations(letter):
    return {"a": [(BETA, GAMMA), (GAMMA, BETA)],
            "b": [(ALPHA, GAMMA), (GAMMA, ALPHA)],
            "c": [(ALPHA, BETA), (BETA, ALPHA)]}[letter]

def angle_feasible(word, first_orient):
    rights = {first_orient[1]}
    for letter in word[1:]:
        new = set()
        for pr in rights:
            for (l, r) in orientations(letter):
                if (pr, l) != (GAMMA, GAMMA):
                    new.add(r)
        rights = new
        if not rights:
            return False
    return True

def enumerate_pairs(a, b, c, bound, keep=200):
    """Staggered word pairs R = a·…, S = c·…, equal totals ≤ bound.
    Returns (n_length, n_angle, n_boundary, kept_records, L_values)."""
    letters = [a, b, c]
    names = {a: "a", b: "b", c: "c"}

    @lru_cache(maxsize=None)
    def reach(lo, hi):
        for x in letters:
            n = lo + x
            if n > bound:
                continue
            if n == hi:
                return True
            p, q = (n, hi) if n < hi else (hi, n)
            if reach(p, q):
                return True
        return False

    stats = {"len": 0, "ang": 0, "bdy": 0}
    kept = []
    Lvals = {}

    def finish(R, S, L):
        stats["len"] += 1
        wr = [names[x] for x in R]
        ws = [names[x] for x in S]
        okR = angle_feasible(wr, (GAMMA, BETA))
        okS = angle_feasible(ws, (BETA, ALPHA))
        if L == bound:
            stats["bdy"] += 1
        if okR and okS:
            stats["ang"] += 1
            Lvals[L] = Lvals.get(L, 0) + 1
            if len(kept) < keep:
                kept.append((L, wr, ws))

    def dfs(sR, sS, R, S):
        if sR < sS:
            cur, other, word = sR, sS, R
            for x in letters:
                n = cur + x
                if n > bound:
                    continue
                if n == other:
                    finish(R + [x], S, n)
                else:
                    p, q = (n, other) if n < other else (other, n)
                    if reach(p, q):
                        dfs(n, sS, R + [x], S)
        else:
            for x in letters:
                n = sS + x
                if n > bound:
                    continue
                if n == sR:
                    finish(R, S + [x], n)
                else:
                    p, q = (n, sR) if n < sR else (sR, n)
                    if reach(p, q):
                        dfs(sR, n, R, S + [x])

    dfs(a, c, [a], [c])
    return stats["len"], stats["ang"], stats["bdy"], kept, Lvals

def counts(word):
    return (word.count("a"), word.count("b"), word.count("c"))

def fan_alive(e, f, M):
    """Closed-form 2D fan criterion at the row breakpoint X (swap words).

    Under the leftmost-rogue reduction the row side of the chord at X carries
    P_M's β and Q_{M−1}'s α; the residual is exactly γ, filled by {γ} (no
    c-edge: dead for the swap) or {2α,β} in one of twelve snug placements.
    Each edge at X must stay inside the AB half-plane: room (M−1)·b at ray
    ratio ρ ∈ {1, f/e, (2f²−e²)/f², (f²−e²)(3f²−e²)/f⁴}.  Cross-checked
    against exact tile placement on all 142 slots f ≤ 12 (0 mismatches) and
    against the 2D patch engine (code/swap_patch_search.py).
    Returns True iff the swap's fan at X survives (slot NOT killed here)."""
    a, b, c = e*f, f*f - e*e, f*f
    R = (M - 1) * b
    K1 = c <= R
    K2 = c*(2*f*f - e*e) <= R*f*f
    K3 = c*f <= R*e
    K4 = a*(2*f*f - e*e) <= R*f*f
    K5 = a*b*(3*f*f - e*e) <= R*f**4
    K6 = c*b*(3*f*f - e*e) <= R*f**4
    Kb = b*b*(3*f*f - e*e) <= R*f**4
    return K3 or (K1 and K2) or (K3 and K4) or \
        (K5 and ((Kb and K2) or K6) and (K1 or K2))

def analyze_member(e, f, keep=200, verbose_words=6):
    a, b, c = e*f, f*f - e*e, f*f
    close = b < a
    M0 = f // e + 1
    Mlo, Mhi = M0 + 1, f - 2
    print(f"\n== ({e},{f})  a={a} b={b} c={c}  Δ={c-a}  "
          f"{'close' if close else 'separated'};  slots for W(f): "
          f"[{Mlo},{Mhi}]" + ("  — MEMBER CLOSES" if Mlo > Mhi else ""))
    member_rows = []
    for M in range(Mlo, Mhi + 1):
        n1, a1, b1, kept, Lv = enumerate_pairs(a, b, c, M*a, keep=keep)
        assert b1 == 0, f"boundary survivor at ({e},{f}) M={M}!"  # K2 cross-check
        # invariant checks on kept records
        for (L, wr, ws) in kept:
            (na_, nb_, nc_), (ma_, mb_, mc_) = counts(wr), counts(ws)
            assert (nb_ - mb_) % f == 0
            assert ((nb_ + nc_) - (mb_ + mc_)) % e == 0
            assert L < M*a
        minL = min(Lv) if Lv else None
        # chord 2 at k = f: bound (f−M)·c
        n2, a2, b2, kept2, Lv2 = enumerate_pairs(a, b, c, (f - M)*c, keep=0)
        fan = fan_alive(e, f, M)
        member_rows.append((M, a1, minL, a2, fan))
        print(f"  M={M}: chord1 {a1} survivors (min L={minL}, "
              f"{len(Lv)} distinct L); chord2 (bound {(f-M)*c}) {a2} survivors"
              + ("  [chord2 DEAD ⇒ slot dies]" if a2 == 0 else "")
              + ("  [swap: fan-KILLED at X, all k]" if not fan else
                 "  [swap: fan fits; killed per-scale by the 2D engine]"))
        shown = 0
        for (L, wr, ws) in sorted(kept, key=lambda r: (r[0], r[1]))[:verbose_words]:
            print(f"      L={L:>4}  R={'·'.join(wr)}  S={'·'.join(ws)}")
            shown += 1
        if a1 > shown:
            print(f"      … ({a1 - shown} more)")
    return member_rows

if __name__ == "__main__":
    members = [(2,3),(3,4),(2,5),(3,5),(4,5),(5,6),(2,7),(3,7),(4,7),(5,7),
               (6,7),(3,8),(5,8),(7,8),(2,9),(4,9),(5,9),(7,9),(8,9)]
    summary = {}
    for e, f in members:
        summary[(e, f)] = analyze_member(e, f)
    print("\n==== FINAL SUMMARY: surviving slots of W(f) after K0–K3 ====")
    for (e, f), rows in summary.items():
        if not rows:
            print(f"({e},{f}): CLOSED (no surviving slot)")
        else:
            print(f"({e},{f}): " + "; ".join(
                f"M={M}: {a1} chord1 / {a2} chord2"
                + ("" if fan else " / swap fan-dead")
                for (M, a1, mL, a2, fan) in rows))
    print("\n==== SWAP STATUS (2D layer) ====")
    print("fan-KILLED slots die for EVERY scale k ≥ M+2 (RogueFan.lean:")
    print("slot_three_dies for M = 3, headline_dies for (M−1)b < c, and the")
    print("full DNF above, all under the leftmost-rogue reduction).  The")
    print("remaining swap slots were killed per-scale by the exact 2D patch")
    print("engine (code/swap_patch_search.py: open mode = all k; rN mode =")
    print("k = M+N): at f ≤ 9 every slot of every member is engine-KILLED")
    print("except the capped-OPEN pairs listed in the session log.")
    for (e, f), rows in summary.items():
        dead = [M for (M, a1, mL, a2, fan) in rows if not fan]
        alive = [M for (M, a1, mL, a2, fan) in rows if fan]
        if rows:
            print(f"({e},{f}): fan-dead M={dead}; engine-per-scale M={alive}")
