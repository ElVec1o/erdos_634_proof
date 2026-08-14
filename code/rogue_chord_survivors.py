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
        member_rows.append((M, a1, minL, a2))
        print(f"  M={M}: chord1 {a1} survivors (min L={minL}, "
              f"{len(Lv)} distinct L); chord2 (bound {(f-M)*c}) {a2} survivors"
              + ("  [chord2 DEAD ⇒ slot dies]" if a2 == 0 else ""))
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
                f"M={M}: {a1} chord1 / {a2} chord2" for (M, a1, mL, a2) in rows))
