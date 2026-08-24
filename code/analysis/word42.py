#!/usr/bin/env python3
"""The (bp,cp)=(4,2) base word: a c a b a^(f-3).  Which runs have length f^2?

A run of whole base letters of total length f^2 is, by the length arithmetic
(A2BranchRow3.span_all_a), either f consecutive a-letters or a single c-edge --
those being the only ways to make f^2 out of {f, f^2-1, f^2}.
"""
def word42(f):
    return ['a', 'c', 'a', 'b'] + ['a'] * (f - 2)   # f+2 letters, exactly f of them 'a'

def lengths(f):
    return {'a': f, 'b': f * f - 1, 'c': f * f}

print(f"{'f':>3} {'len':>4} {'#a':>3} {'runs of length f^2 (start,letters)':<44} {'max a-run':>9}")
for f in range(5, 13):
    w = word42(f); L = lengths(f)
    assert len(w) == f + 2 and w.count('a') == f and w[0] == 'a' and w[-1] == 'a'
    assert sum(L[ch] for ch in w) == 3 * f * f - 1
    runs = []
    for i in range(len(w)):
        s = 0
        for j in range(i, len(w)):
            s += L[w[j]]
            if s == f * f:
                runs.append((i, w[i:j + 1]))
            if s > f * f:
                break
    # longest run of consecutive 'a'
    best = cur = 0
    for ch in w:
        cur = cur + 1 if ch == 'a' else 0
        best = max(best, cur)
    desc = "; ".join(f"@{i}:{''.join(r)}" for i, r in runs)
    print(f"{f:>3} {len(w):>4} {w.count('a'):>3} {desc:<44} {best:>9}  (need {f})")
