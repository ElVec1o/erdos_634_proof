"""Faithful generator/counter for the e>=2 base-beta legal base-word grammar.

Pure combinatorics, no tiling engine invoked (this script never touches guard_run.sh,
cengine binaries, or any protected path). Safe to run directly.

GRAMMAR (family-wide, derived from the base-beta target's edge-length identity and
prop:cornerpara; not e=1-specific):

For base-beta parameters (e,f), tile (ef, f^2-e^2, f^2), base length L = e*(3f^2-e^2) = N*e.
A "column" is a triple (x,y,z) of non-negative integers with

    x*(ef) + y*(f^2-e^2) + z*(f^2) = L                      (edge-length identity)

restricted to z>=1, x+z>=4 (columns that can carry a legal word at all -- this is the
R1 "columns" filter reproduced from report_prefixlift.md / the Erdos seat's original count).
A base word is a word over {a,b,c} that is a permutation of the multiset a^x b^y c^z for
some column (x,y,z). Two nested legality rules apply on top of the column filter:

  R1 (weak):  first letter = last letter = 'a'.
  R2 (strong, = R1 + prop:cornerpara): first two letters and last two letters each lie
              in {a,c} (i.e. positions 0,1,n-2,n-1 avoid 'b' -- no b-block touches a corner).

R2 is the one used everywhere downstream (ThickPrefixACB.lean, report_prefixlift.md);
R1 is kept only as the historical/weaker check that reproduces the very first count (30
words at N=23 over all 1,637,232 permutations of a^3 b^2 c^2).

Validated counts (see validate() / __main__):
  (e,f)=(2,3), N=23:  R1 -> 30 legal words (out of 1,637,232 permutations of aaabbcc);
                       R2 -> 9 legal words.
  (e,f)=(5,6), N=83:  R1 -> 1,637,232 legal words; R2 -> 264,144 legal words.
  (5,6) R2 words surviving the two proven prefix/mirror-suffix local kills
        {acb, aab, aacb, accb} (ThickPrefixACB.lean's family-wide kill + the two
        (5,6)-specific local kills from report_prefixlift.md Q1/Q2): exactly 19,596,
        split aaa:4079 aac:3395 aca:8244 acc:3878 -- matching report_prefixlift.md's
        residue table exactly.

This module does NOT decide whether a legal word actually tiles -- that is the tiling
engine's job (via guard_run.sh only). It only enumerates the combinatorial candidate
set; the multiplicity-only representation (x,y,z,ends) supports the ~10^6-word regime
at N=83 without ever materializing all permutations.
"""
from __future__ import annotations
from math import factorial
from itertools import product, permutations
from typing import Iterator, Sequence


def columns(e: int, f: int) -> list[tuple[int, int, int]]:
    """All (x,y,z) with x*a+y*b+z*c=L, z>=1, x+z>=4, a=ef,b=f^2-e^2,c=f^2, L=e*(3f^2-e^2)."""
    a, b, c = e * f, f * f - e * e, f * f
    L = e * (3 * f * f - e * e)
    out = []
    for z in range(1, L // c + 1):
        for y in range(0, (L - z * c) // b + 1):
            r = L - z * c - y * b
            if r >= 0 and r % a == 0:
                x = r // a
                if x + z >= 4:
                    out.append((x, y, z))
    return out


def multinom(x: int, y: int, z: int) -> int:
    return factorial(x + y + z) // (factorial(x) * factorial(y) * factorial(z))


def legal_rule(w: str, rule: str) -> bool:
    """R1: first/last letter 'a'.  R2: R1 + first-two/last-two in {a,c}."""
    if w[0] != "a" or w[-1] != "a":
        return False
    if rule == "R2":
        n = len(w)
        if n >= 2 and (w[1] not in "ac" or w[-2] not in "ac"):
            return False
    return True


def gen_words(e: int, f: int, rule: str = "R2") -> Iterator[str]:
    """Yield every legal base word (as an explicit string) for (e,f) under `rule`.

    Warning: materializes every permutation -- fine up to N~a few hundred thousand
    words (validated at N=83, 264,144 R2 words), NOT recommended beyond that without
    switching to the multiplicity-only counting path (see legal_count/count_with_kills).
    """
    for (x, y, z) in columns(e, f):
        multiset = list("a" * x + "b" * y + "c" * z)
        for perm in set(permutations(multiset)):
            w = "".join(perm)
            if legal_rule(w, rule):
                yield w


def legal_count(e: int, f: int, rule: str = "R2") -> int:
    """Exact count of legal words without ever enumerating them (multiplicity-only)."""
    tot = 0
    for (x, y, z) in columns(e, f):
        for ends in product("ac", repeat=4) if rule == "R2" else product("abc", repeat=2):
            if rule == "R2":
                w0, w1, wm2, wm1 = ends
                if w0 != "a" or wm1 != "a":
                    continue
                cnt = {"a": x, "b": y, "c": z}
                ok = True
                for ch in (w0, w1, wm2, wm1):
                    cnt[ch] -= 1
                    if cnt[ch] < 0:
                        ok = False
                        break
                if ok:
                    tot += multinom(cnt["a"], cnt["b"], cnt["c"])
            else:
                w0, wm1 = ends
                if w0 != "a" or wm1 != "a":
                    continue
                cnt = {"a": x, "b": y, "c": z}
                cnt["a"] -= 2
                if cnt["a"] >= 0:
                    tot += multinom(cnt["a"], y, z)
    return tot


def count_with_kills(e: int, f: int, rule: str, dead_prefixes: Sequence[str]) -> dict:
    """Exact residue after removing every legal word that starts with a dead prefix or
    whose *reverse* starts with one (mirror-suffix kill, sound because sigma:x->N-x is a
    proven symmetry of the base-beta target). Returns dict with tot/killed/residue/by_prefix3.
    """
    dead = set(dead_prefixes)
    maxlen = max((len(p) for p in dead), default=0)
    k = max(maxlen - 1, 1)
    tot = 0
    killed = 0
    residue_by_first3: dict[str, int] = {}
    for (x, y, z) in columns(e, f):
        if x < 2:
            continue
        mid_count = {"a": x - 2, "b": y, "c": z}
        n = x - 2 + y + z
        if n < 2 * k:
            multiset = list("a" * (x - 2) + "b" * y + "c" * z)
            for perm in set(permutations(multiset)):
                w = "a" + "".join(perm) + "a"
                if not legal_rule(w, rule):
                    continue
                tot += 1
                kp = any(w.startswith(p) for p in dead)
                ks = any(w.endswith(p[::-1]) for p in dead)
                if kp or ks:
                    killed += 1
                else:
                    residue_by_first3[w[:3]] = residue_by_first3.get(w[:3], 0) + 1
            continue
        for pre in product("abc", repeat=k):
            for suf in product("abc", repeat=k):
                cnt = dict(mid_count)
                ok = True
                for ch in pre + suf:
                    cnt[ch] -= 1
                    if cnt[ch] < 0:
                        ok = False
                        break
                if not ok:
                    continue
                w_head = "a" + "".join(pre)
                w_tail = "".join(suf) + "a"
                stub = w_head + "?" * (n - 2 * k) + w_tail
                if not legal_rule(stub, rule):
                    continue
                m = multinom(cnt["a"], cnt["b"], cnt["c"])
                tot += m
                kp = any(w_head.startswith(p) for p in dead)
                ks = any(w_tail.endswith(p[::-1]) for p in dead)
                if kp or ks:
                    killed += m
                else:
                    residue_by_first3[w_head[:3]] = residue_by_first3.get(w_head[:3], 0) + m
    return {"total": tot, "killed": killed, "residue": tot - killed, "by_first3": residue_by_first3}


def validate() -> None:
    assert legal_count(2, 3, "R1") == 30, legal_count(2, 3, "R1")
    assert legal_count(2, 3, "R2") == 9, legal_count(2, 3, "R2")
    assert legal_count(5, 6, "R1") == 1637232, legal_count(5, 6, "R1")
    assert legal_count(5, 6, "R2") == 264144, legal_count(5, 6, "R2")
    r = count_with_kills(5, 6, "R2", ["acb", "aab", "aacb", "accb"])
    assert r["residue"] == 19596, r
    assert r["by_first3"] == {"aaa": 4079, "aac": 3395, "aca": 8244, "acc": 3878}, r["by_first3"]
    print("All checkpoints reproduced exactly: (2,3) R1=30 R2=9; (5,6) R1=1637232 "
          "R2=264144; (5,6) residue after {acb,aab,aacb,accb} = 19596 "
          f"({r['by_first3']}).")


if __name__ == "__main__":
    validate()
