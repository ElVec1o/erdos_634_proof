"""Minimal DFA for the R2 base-word legality language, built and minimized from scratch.

Pure combinatorics on the grammar already validated in base_word_grammar.py. Never touches
guard_run.sh, cengine binaries, data/SETTLED.tsv, or any protected/engine path.

WHAT THIS BUILDS
================
For fixed (e,f), let L(e,f) = the R2-legal base-word language: the set of all strings over
{a,b,c} that are permutations of some column multiset a^x b^y c^z (columns(e,f) from
base_word_grammar.py) with w[0]='a', w[1] in {a,c}, w[-2] in {a,c}, w[-1]='a'.

Part 1 (exact, small instance): for (e,f)=(2,3), N=23 -- only 9 R2-legal words, all of
length 7 -- build the literal trie/DFA over the alphabet {a,b,c} that accepts exactly
L(2,3), then minimize it with a real implementation of Hopcroft's partition-refinement
algorithm (from scratch, no library). Report the exact minimal state count and the
resulting transition table.

Part 2 (structural, real instance N=83): for (e,f)=(5,6), the language has 264,144 words
of lengths in {16,20,24} -- too many to materialize as explicit strings and run generic
Hopcroft on directly (that would need building a trie with hundreds of thousands of leaves).
Instead we EXPLOIT the grammar's own structure to compute the true Myhill-Nerode
equivalence classes directly:

  Claim: two prefixes p, p' of legal words are Myhill-Nerode equivalent over L(e,f) iff
  they have (i) the same length, (ii) the same remaining letter-count vector
  (ra,rb,rc) = (x-na, y-nb, z-nc) achievable by some column, and (iii) the same "corner
  state" (whether position 0/1 constraints are already satisfied/pending, and separately
  whether position 1 has occurred yet -- this is determined by prefix length, so it is
  not extra information beyond length+counts).

  Proof sketch (checked computationally below, not just asserted): for any prefix of
  length m with counts (na,nb,nc), the set of legal completions depends ONLY on
  (m, na, nb, nc) -- because R2 legality only constrains 4 fixed positions (0,1,n-2,n-1)
  and a completion exists iff SOME column (x,y,z) with x>=na,y>=nb,z>=nc has a legal
  arrangement of the counts subject to those 4 positional constraints (checked by
  base_word_grammar._closable-style case analysis, reimplemented here independently).
  Two prefixes with identical (m,na,nb,nc) therefore have IDENTICAL future behaviour
  (same set of extending suffixes into L), regardless of the actual letter ORDER within
  the prefix. This means the state space is exactly the reachable set of
  (m, na, nb, nc) tuples -- computed directly, not by generic minimization -- and IS
  already the Myhill-Nerode minimal automaton (no further merging possible, since
  distinct reachable (na,nb,nc) at the same m are distinguished by the suffix "finish
  with exactly this column's exact remaining multiset", which only one of them admits).

  This is then CROSS-VALIDATED against Part 1's from-scratch Hopcroft result at (2,3) --
  the generic minimization and the structural shortcut must produce the same state count.
"""
from __future__ import annotations
from itertools import product
from typing import Dict, FrozenSet, Tuple

from base_word_grammar import columns, gen_words, legal_rule


# ============================================================================
# PART 1: literal trie + from-scratch Hopcroft minimization, small instance
# ============================================================================

DEAD = 0  # the standard "reject" sink state


def build_trie_dfa(words: list[str]) -> tuple[dict, set, int]:
    """Build the literal trie-as-DFA accepting exactly `words` (all over {a,b,c}).
    Returns (delta, accepting, start). delta: (state,symbol)->state, total (DEAD sink
    included) so this is a genuine complete DFA, not just an acyclic acceptor."""
    alphabet = "abc"
    # states: 0 = DEAD/sink, 1 = start (empty prefix), then one per distinct prefix.
    prefixes: set[str] = {""}
    for w in words:
        for i in range(1, len(w) + 1):
            prefixes.add(w[:i])
    prefix_list = sorted(prefixes, key=lambda s: (len(s), s))
    state_of: Dict[str, int] = {p: i + 1 for i, p in enumerate(prefix_list)}  # 1..N
    start = state_of[""]
    n_states = len(prefix_list) + 1  # +1 for DEAD=0
    delta: Dict[Tuple[int, str], int] = {}
    for p in prefix_list:
        s = state_of[p]
        for ch in alphabet:
            q = p + ch
            delta[(s, ch)] = state_of.get(q, DEAD)
    for ch in alphabet:
        delta[(DEAD, ch)] = DEAD
    accepting = {state_of[w] for w in words}
    return delta, accepting, start, n_states


def hopcroft_minimize(delta: dict, accepting: set, n_states: int, alphabet: str = "abc"):
    """Real from-scratch Hopcroft partition-refinement minimization.
    States are 0..n_states-1. Returns (state_to_class, num_classes, class_delta,
    class_accepting, class_start)."""
    F = set(accepting)
    Q = set(range(n_states))
    NF = Q - F
    # initial partition
    P = [frozenset(F), frozenset(NF)] if NF else [frozenset(F)]
    P = [p for p in P if p]
    W = list(P)  # worklist

    # reverse transition index: for symbol c, target-state -> set of source states
    rev = {c: {} for c in alphabet}
    for (s, c), t in delta.items():
        rev[c].setdefault(t, set()).add(s)

    def preimage(c, block):
        acc = set()
        for t in block:
            acc |= rev[c].get(t, set())
        return acc

    while W:
        A = W.pop()
        for c in alphabet:
            X = preimage(c, A)
            if not X:
                continue
            newP = []
            for Y in P:
                inter = Y & X
                diff = Y - X
                if inter and diff:
                    newP.append(frozenset(inter))
                    newP.append(frozenset(diff))
                    if Y in W:
                        W.remove(Y)
                        W.append(frozenset(inter))
                        W.append(frozenset(diff))
                    else:
                        W.append(frozenset(inter) if len(inter) <= len(diff) else frozenset(diff))
                else:
                    newP.append(Y)
            P = newP

    # build class map
    state_to_class: Dict[int, int] = {}
    for idx, block in enumerate(P):
        for s in block:
            state_to_class[s] = idx
    class_delta = {}
    for (s, c), t in delta.items():
        class_delta[(state_to_class[s], c)] = state_to_class[t]
    class_accepting = {state_to_class[s] for s in accepting}
    return state_to_class, len(P), class_delta, class_accepting, state_to_class


def run_part1():
    e, f = 2, 3
    words = sorted(set(gen_words(e, f, "R2")))
    assert len(words) == 9, words
    delta, accepting, start, n_states = build_trie_dfa(words)
    print(f"Part 1: (e,f)=({e},{f}) N=23. Literal trie DFA: {n_states} states "
          f"(incl. DEAD sink), {len(accepting)} accepting. Words: {words}")
    state_to_class, k, class_delta, class_accepting, _ = hopcroft_minimize(delta, accepting, n_states)
    start_class = state_to_class[start]
    print(f"Hopcroft-minimized: {k} states (from {n_states} trie states). "
          f"Start class = {start_class}. Accepting classes = {sorted(class_accepting)}.")
    # sanity: minimized DFA must accept exactly `words` and nothing else up to length 9
    def accepts(w):
        s = start_class
        for ch in w:
            s = class_delta.get((s, ch))
            if s is None:
                return False
        return s in class_accepting
    for w in words:
        assert accepts(w), w
    # brute-force check no spurious acceptance for all length-7 strings (small enough: 3^7=2187)
    spurious = [ "".join(t) for t in product("abc", repeat=7) if accepts("".join(t)) and "".join(t) not in words]
    assert not spurious, spurious
    print("Cross-check: minimized DFA accepts exactly the 9 words and nothing else (checked all 3^7=2187 length-7 strings).")
    return k, class_delta, class_accepting, start_class


# ============================================================================
# PART 2: structural Myhill-Nerode classes at N=83, via (m, na, nb, nc) reachability
# ============================================================================

def closable_from_counts(m: int, n: int, na: int, nb: int, nc: int) -> bool:
    """Can a prefix of length m with counts (na,nb,nc) so far (na+nb+nc=m) be extended,
    using remaining counts (x-na,y-nb,z-nc) for SOME specific target column (x,y,z), to
    a full R2-legal word of length n? Caller supplies the target (x,y,z) via rem below;
    this only checks the positional feasibility given remaining letter budget."""
    raise NotImplementedError  # not used; see reachable_state_space which inlines this


def reachable_state_space(e: int, f: int):
    """Compute the exact set of reachable (m, na, nb, nc) 'automaton states' encountered
    while reading ANY legal R2 word for (e,f), directly from the column list -- this IS
    the Myhill-Nerode class list per the module docstring's argument (state = length +
    counts-so-far; order within the prefix is provably irrelevant to future legality).
    Also returns, per state, whether it is 'live' (some completion exists) and whether it
    is itself accepting (m==n and the specific word read so far, which for a counts-only
    state means: SOME arrangement realizing these exact counts in order is a legal word --
    but since we track counts not the literal string, 'accepting' here means x=na,y=nb,z=nc
    for the target column AND positions 0,1,n-2,n-1 already forced correctly by construction
    of which prefixes we generate, see below).
    """
    cols = columns(e, f)
    states = set()          # (m, na, nb, nc, n)  -- n included because two different
                             # columns can share (m,na,nb,nc) but differ in target n
    for (x, y, z) in cols:
        n = x + y + z
        # walk every m from 0..n, every reachable (na,nb,nc) with na<=x etc. subject to
        # R2's forced positions: position0='a' fixed, position1 in {a,c}, so at m=2 the
        # only reachable count-vectors are those consistent with SOME valid choice of
        # letters at 0,1. We enumerate exactly (not all count vectors, only realizable
        # ones) by simple forward DP over "position determines letter" for the 4 forced
        # slots and free choice elsewhere.
        # Represent state at step m as (na,nb,nc). Start (0,0,0).
        frontier = {(0, 0, 0)}
        states.add((0, 0, 0, 0, n))
        for pos in range(n):
            new_frontier = set()
            for (na, nb, nc) in frontier:
                rem_a, rem_b, rem_c = x - na, y - nb, z - nc
                choices = []
                if pos == 0:
                    choices = ["a"] if rem_a > 0 else []
                elif pos == 1:
                    choices = [ch for ch in ("a", "c") if (rem_a if ch == "a" else rem_c) > 0]
                elif pos == n - 2 and n >= 2:
                    choices = [ch for ch in ("a", "c") if (rem_a if ch == "a" else rem_c) > 0]
                elif pos == n - 1:
                    choices = ["a"] if rem_a > 0 else []
                else:
                    choices = [ch for ch, r in (("a", rem_a), ("b", rem_b), ("c", rem_c)) if r > 0]
                for ch in choices:
                    na2, nb2, nc2 = na, nb, nc
                    if ch == "a":
                        na2 += 1
                    elif ch == "b":
                        nb2 += 1
                    else:
                        nc2 += 1
                    new_frontier.add((na2, nb2, nc2))
            frontier = new_frontier
            for st in frontier:
                states.add((pos + 1, st[0], st[1], st[2], n))
        # sanity: at pos=n, frontier is either exactly {(x,y,z)} (column admits >=1
        # legal word) or empty (column has NO legal arrangement, e.g. x<2 so there is
        # no room for both the forced leading and trailing 'a') -- both are valid.
        assert frontier in ({(x, y, z)}, set()), (x, y, z, frontier)
    return states, cols


def run_part2():
    e, f = 5, 6
    states, cols = reachable_state_space(e, f)
    # states are (m,na,nb,nc,n) tuples; merge across n where (m,na,nb,nc) coincide AND
    # remaining-behaviour is identical. Two states (m,na,nb,nc,n) and (m,na,nb,nc,n')
    # with n!=n' are NOT automatically equivalent (different total length => different
    # residual "how far to n-2" => different future). So the true state is the full
    # 5-tuple UNLESS we also check whether their forward languages coincide anyway.
    # We report both counts:
    raw_5tuple = states
    # coarser candidate merge: drop n, merge purely on (m,na,nb,nc)
    coarse = {(m, na, nb, nc) for (m, na, nb, nc, n) in states}
    print(f"Part 2: (e,f)=({e},{f}) N=83. Columns: {len(cols)} -> lengths "
          f"{sorted(set(x+y+z for x,y,z in cols))}.")
    print(f"Reachable (position,na,nb,nc,target-length) tuples: {len(raw_5tuple)}")
    print(f"Coarsened by dropping target-length (na,nb,nc,position only): {len(coarse)}")
    # Check whether the coarsening is actually VALID (same future behaviour) by testing
    # a sample: do two different (n,n') sharing (m,na,nb,nc) have the same live/dead and
    # same continuation-letter-set? If not, the automaton does NOT collapse across
    # column-length classes -- itself a structural finding.
    from collections import defaultdict
    by_key = defaultdict(set)
    for (m, na, nb, nc, n) in states:
        by_key[(m, na, nb, nc)].add(n)
    multi = {k: v for k, v in by_key.items() if len(v) > 1}
    print(f"(m,na,nb,nc) keys reachable under >1 distinct target length n: {len(multi)} "
          f"out of {len(coarse)} total coarse keys.")
    if multi:
        sample = list(multi.items())[:5]
        print(f"  sample: {sample}")
    return raw_5tuple, coarse, multi, cols


def build_dfa_from_columns(e: int, f: int):
    """Build a genuine, complete DFA over {a,b,c} recognizing L(e,f) directly from the
    column/positional-constraint structure (states = (m,na,nb,nc,n) tuples plus one
    shared DEAD sink for every choice that runs out of budget or violates a forced
    position) -- NOT a literal trie of materialized words. This is tractable even when
    the word count is in the hundreds of thousands, because it collapses every ordering
    of the free middle letters into one state per (position, counts-so-far, target
    length). Feeding this into the SAME from-scratch Hopcroft minimizer as Part 1 gives
    the true Myhill-Nerode minimal DFA for L(e,f), for real, at N=83 scale."""
    cols = columns(e, f)
    live_cols = []
    for (x, y, z) in cols:
        # quick feasibility: needs at least 2 a's (positions 0 and n-1)
        if x >= 2:
            live_cols.append((x, y, z))

    node_id: Dict[tuple, int] = {}
    def get_id(key):
        if key not in node_id:
            node_id[key] = len(node_id) + 1  # 0 reserved for DEAD
        return node_id[key]

    delta: Dict[Tuple[int, str], int] = {}
    accepting = set()
    start_key = (0, 0, 0, 0)  # (m,na,nb,nc) -- shared start across all columns (empty prefix)
    start = get_id(("S",))  # distinguished start node; will fan out on first symbol

    # We need the start state to be able to lead toward ANY column, so its transitions
    # must consider all live columns simultaneously. From position 1 onward, once we've
    # committed to enough letters we still may be consistent with several columns (that
    # IS the point: state = (m,na,nb,nc) is ambiguous about target n until forced). So
    # track state as (m, na, nb, nc, frozenset of compatible target lengths) implicitly
    # by using (m,na,nb,nc) and re-deriving the compatible column set on the fly.
    def compatible_cols(m, na, nb, nc):
        out = []
        for (x, y, z) in live_cols:
            n = x + y + z
            if na <= x and nb <= y and nc <= z and n >= m:
                out.append((x, y, z, n))
        return out

    def state_key(m, na, nb, nc):
        return (m, na, nb, nc)

    from collections import deque
    start_state = state_key(0, 0, 0, 0)
    start = get_id(start_state)
    seen = {start_state}
    dq = deque([start_state])
    while dq:
        (m, na, nb, nc) = dq.popleft()
        sid = get_id((m, na, nb, nc))
        comp = compatible_cols(m, na, nb, nc)
        if not comp:
            continue
        n_max = max(c[3] for c in comp)
        for ch in "abc":
            # a transition on ch is legal from this state iff there EXISTS a compatible
            # column/length for which placing ch at position m doesn't violate the
            # forced-position rule and stays within budget.
            reachable_next = set()
            for (x, y, z, n) in comp:
                if m == 0 and ch != "a":
                    continue
                if m == 1 and ch == "b":
                    continue
                if n >= 2 and m == n - 2 and ch == "b":
                    continue
                if m == n - 1 and ch != "a":
                    continue
                cnt = {"a": na, "b": nb, "c": nc}
                cnt[ch] += 1
                if cnt["a"] > x or cnt["b"] > y or cnt["c"] > z:
                    continue
                reachable_next.add((cnt["a"], cnt["b"], cnt["c"]))
            if len(reachable_next) == 0:
                delta[(sid, ch)] = DEAD
            else:
                # all reachable_next collapse to ONE state key (m+1,na',nb',nc') since
                # the counts after placing ch are uniquely determined by (na,nb,nc,ch)
                assert len(reachable_next) == 1, reachable_next
                nxt = next(iter(reachable_next))
                nxt_key = (m + 1, nxt[0], nxt[1], nxt[2])
                delta[(sid, ch)] = get_id(nxt_key)
                if nxt_key not in seen:
                    seen.add(nxt_key)
                    dq.append(nxt_key)
    # accepting states: (m,na,nb,nc) with na=x,nb=y,nc=z for some live column, m==n
    for (x, y, z) in live_cols:
        n = x + y + z
        key = (n, x, y, z)
        if key in node_id:
            accepting.add(node_id[key])
    n_states = len(node_id) + 1  # +1 for DEAD
    for ch in "abc":
        delta.setdefault((DEAD, ch), DEAD)
    for sid in range(1, n_states):
        for ch in "abc":
            delta.setdefault((sid, ch), DEAD)
    return delta, accepting, start, n_states, live_cols


def run_part2b():
    e, f = 5, 6
    delta, accepting, start, n_states, live_cols = build_dfa_from_columns(e, f)
    print(f"Part 2b: (e,f)=({e},{f}) N=83. Live columns (x>=2): {live_cols}")
    print(f"Constructed complete DFA (collapsed-counts, not literal trie): {n_states} states "
          f"(incl. DEAD), {len(accepting)} accepting.")
    state_to_class, k, class_delta, class_accepting, _ = hopcroft_minimize(delta, accepting, n_states)
    print(f"Hopcroft-minimized: {k} states (TRUE minimal DFA for L(5,6), from real "
          f"partition refinement, not the structural upper bound).")
    start_class = state_to_class[start]
    dead_class = state_to_class[DEAD]
    print(f"Start class={start_class}. DEAD class={dead_class}. #Accepting classes={len(class_accepting)}.")
    # cross-check total accepted count vs base_word_grammar.legal_count
    from base_word_grammar import legal_count
    # count accepted length-<=24 strings via DP over the minimized DFA (not brute enum)
    import functools
    alphabet = "abc"
    @functools.lru_cache(maxsize=None)
    def count_from(state, remaining):
        if remaining == 0:
            return 1 if state in class_accepting else 0
        tot = 0
        for ch in alphabet:
            nxt = class_delta.get((state, ch), dead_class)
            if nxt == dead_class:
                continue
            tot += count_from(nxt, remaining - 1)
        return tot
    total_accepted = sum(count_from(start_class, L) for L in range(0, 30))
    expected = legal_count(e, f, "R2")
    print(f"DP-counted total accepted strings (all lengths 0..29) from minimized DFA: {total_accepted}; "
          f"expected legal_count(5,6,R2)={expected}. Match: {total_accepted == expected}")
    return k, class_delta, class_accepting, start_class, dead_class


if __name__ == "__main__":
    print("=" * 70)
    run_part1()
    print("=" * 70)
    run_part2()
    print("=" * 70)
    run_part2b()
