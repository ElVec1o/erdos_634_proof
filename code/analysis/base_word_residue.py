#!/usr/bin/env python3
"""Admissible e=1 base words per f, and how many the proved reach step already kills.

Base word (thm:e1reduce): a permutation of (a^f, b, c), f+2 letters, first and last `a`.
prop:cornerpara: the `b` avoids the first two and last two positions, so bp in [3, f];
the first two and last two letters lie in {a,c}, which for the single `c` means cp != 1, f+2.

PincerLadder.pincer_ladder: if the four kills cover depth <= R, no (bp, cp) escapes for
f <= R+1.  For f > R+1 the escapes are those satisfying none of the four disjuncts.
Reach r gives R = r+1; the best proved reach is 4, i.e. R = 5.
"""
def admissible(f):
    """1-indexed positions 1..f+2; position 1 and f+2 are `a`."""
    out = []
    for bp in range(3, f + 1):                       # cornerpara
        for cp in range(2, f + 2):                   # c not at 1 or f+2
            if cp != bp:
                out.append((bp, cp))
    return out

def killed(f, bp, cp, R):
    return ((bp < cp and bp <= R) or
            (cp < bp and f + 3 - bp <= R) or
            (cp == bp + 1 and f + 3 - cp <= R) or
            (bp == cp + 1 and cp <= R))

print(f"{'f':>3} {'N=3f^2-1':>9} {'words':>6} {'killed R=5':>11} {'escape':>7}  escapes")
for f in range(3, 13):
    words = admissible(f)
    esc = [w for w in words if not killed(f, w[0], w[1], 5)]
    N = 3 * f * f - 1
    tag = "" if len(esc) else "  <- all dead"
    print(f"{f:>3} {N:>9} {len(words):>6} {len(words)-len(esc):>11} {len(esc):>7}  {esc[:6]}{tag}")

print()
print("reach needed for a clean sweep at each f (smallest R killing every word):")
for f in range(3, 13):
    words = admissible(f)
    R = next(R for R in range(1, 60) if all(killed(f, b, c, R) for b, c in words))
    print(f"  f={f:<3} N={3*f*f-1:<5} needs R={R} (reach {R-1})")
