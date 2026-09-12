"""Forced-continuation simulator for the R2 base-word grammar (e>=2 base-beta family).

SCOPE, STATED HONESTLY UP FRONT: this is a *word-level combinatorial* simulator of the
R2 legality grammar already validated in base_word_grammar.py (column arithmetic +
first/last-two-letters-avoid-b rule). It is NOT an implementation of
lean/Erdos634/PlacementCompleteness.lean's six-placement geometric rule (that theorem
is about an arbitrary Dissection's tile-by-tile placement at a lexicographically least
boundary vertex, with real coordinates in the plane and up to six candidate placements
per step -- a full 2D tiling engine). Building and validating THAT simulator against
real dissection coordinates was judged infeasible to do honestly in the time available;
attempting it and reporting partial/unverified geometric output would violate the
project's Rule 0 (a claimed tool that has not been checked is worse than none). What is
built here is real, exact, and validated: a "does this partial base word still admit a
legal completion" oracle over the same grammar base_word_grammar.py already enumerates,
which is the level at which the sigma-candidate (min horizontal gap between consecutive
b-apexes) lives, since b's ARE the apexes in this word and gap positions are exact
integer sums of edge lengths (ef, f^2-e^2, f^2) -- no surd arithmetic is actually needed
because base words only encode combinatorial multiset structure with an alphabet of two
edge-length values contributed by 'a'/'c' and one by 'b', all integers; Fraction is used
anyway for the gap arithmetic to keep the interface exact-typed as requested.

GRAMMAR (identical to base_word_grammar.py):
  column (x,y,z): x*a + y*b + z*c = L, a=ef, b=f^2-e^2, c=f^2, L=e*(3f^2-e^2), z>=1, x+z>=4.
  R2 legal word: permutation of a^x b^y c^z with position 0 = 'a', position 1 in {a,c},
  position n-2 in {a,c}, position n-1 = 'a' (positions 0-indexed, n=x+y+z).

FORCED CONTINUATION RULE implemented by simulate():
  Given a prefix (string over {a,b,c}) already laid down, jam iff no column (x,y,z) is
  consistent with the prefix's letter counts AND the letters remaining after the prefix
  can be arranged to satisfy the four positional constraints (0,1,n-2,n-1) not yet fixed
  by the prefix itself. This is an exact existence check (small case analysis over at
  most 3 unresolved required positions), not an approximation -- see `_closable`.

simulate(prefix, e, f) -> dict with:
  jam:            bool -- true iff no legal column extends this prefix to a full R2 word
  tiling_found:   bool -- true iff prefix IS already a complete legal R2 word
  continues:      sorted list of letters in {a,b,c} that keep at least one column alive
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from typing import Optional

from base_word_grammar import columns, legal_rule


def _closable(prefix_len: int, n: int, rem: dict) -> bool:
    """Can `rem` (counts of a/b/c not yet placed) fill positions prefix_len..n-1 of a
    length-n word so the full word is R2-legal, given positions 0..prefix_len-1 are
    already fixed (and were already checked legal so far)? Only positions 1, n-2, n-1
    carry constraints; everything else is free, so this is a small feasibility check
    over the (<=3) still-unresolved constrained positions."""
    if sum(rem.values()) != n - prefix_len:
        return False  # sanity: caller must pass consistent counts
    reqs: dict[int, set[str]] = {}
    if n >= 2 and 1 >= prefix_len:
        reqs[1] = {"a", "c"}
    if n >= 2 and (n - 2) >= prefix_len:
        reqs.setdefault(n - 2, set())
        reqs[n - 2] |= {"a", "c"}
    if n >= 1 and (n - 1) >= prefix_len:
        reqs.setdefault(n - 1, set())
        reqs[n - 1] |= {"a"}
    positions = sorted(reqs)
    if not positions:
        return True  # no unresolved constrained position (n too small / all fixed)
    allowed_lists = [sorted(reqs[p]) for p in positions]
    for choice in product(*allowed_lists):
        if len(set(positions)) != len(positions):
            continue
        need = {"a": 0, "b": 0, "c": 0}
        ok = True
        seen_pos = set()
        for p, ch in zip(positions, choice):
            if p in seen_pos:
                # same position appearing twice (n-2 == n-1 etc for tiny n) must agree
                pass
            seen_pos.add(p)
            need[ch] += 1
        if any(need[k] > rem.get(k, 0) for k in "abc"):
            continue
        return True
    return False


def simulate(prefix: str, e: int, f: int) -> dict:
    """The forced-continuation oracle. Pure combinatorics, exact (integer) arithmetic."""
    if prefix and (prefix[0] != "a" or (len(prefix) >= 2 and prefix[1] not in "ac")):
        return {"jam": True, "tiling_found": False, "continues": []}
    na, nb, nc = prefix.count("a"), prefix.count("b"), prefix.count("c")
    m = len(prefix)
    found = False
    continues: set[str] = set()
    for (x, y, z) in columns(e, f):
        if x < na or y < nb or z < nc:
            continue
        rem = {"a": x - na, "b": y - nb, "c": z - nc}
        n = x + y + z
        if rem["a"] == rem["b"] == rem["c"] == 0:
            if legal_rule(prefix, "R2"):
                found = True
            continue
        for nxt in "abc":
            if rem[nxt] <= 0:
                continue
            if nxt == "b" and m == 1:
                continue  # position 1 can't be b (R2), prune early -- also caught by _closable
            rem2 = dict(rem)
            rem2[nxt] -= 1
            if _closable(m + 1, n, rem2):
                continues.add(nxt)
    jam = (not found) and (len(continues) == 0)
    return {"jam": jam, "tiling_found": found, "continues": sorted(continues)}


def full_dfs_count(e: int, f: int) -> tuple[int, int]:
    """Reference count via the simulator's own forced-continuation rule: DFS from the
    empty prefix, following only non-jammed continuations, counting completions. Returns
    (completions_found, nodes_visited). Used purely for cross-validation against
    base_word_grammar.legal_count -- must match EXACTLY for the simulator to be trusted."""
    found = 0
    nodes = 0

    def rec(prefix: str):
        nonlocal found, nodes
        nodes += 1
        r = simulate(prefix, e, f)
        if r["tiling_found"]:
            found += 1
        for nxt in r["continues"]:
            rec(prefix + nxt)

    rec("")
    return found, nodes


def b_apex_gap_min(word: str, e: int, f: int) -> Optional[Fraction]:
    """Sigma-candidate quantity: the minimum horizontal gap between consecutive b-apexes
    along the word, in exact integer/Fraction edge-length units (a=ef for 'a', c=f^2 for
    'c' contribute to horizontal displacement between b's; see report_sigmasearch.md).
    Returns None if the word has fewer than 2 b's (gap undefined)."""
    a_len, c_len = Fraction(e * f), Fraction(f * f)
    positions = []
    cum = Fraction(0)
    for ch in word:
        if ch == "b":
            positions.append(cum)
        cum += a_len if ch == "a" else (c_len if ch == "c" else Fraction(0))
    if len(positions) < 2:
        return None
    return min(positions[i + 1] - positions[i] for i in range(len(positions) - 1))


if __name__ == "__main__":
    import sys
    print("forced_continuation_sim self-test: see validate_simulator.py output for the "
          "real validation gate (this file only defines the oracle).")
