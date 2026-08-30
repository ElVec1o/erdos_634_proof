#!/usr/bin/env python3
"""The instance list of an e=1 exhaustive sweep at a given f, and its coverage certificate.

The admissible base words are the (bp, cp) of `base_word_residue.admissible`; the pincer window at
the proved reach 3 (R = 5) kills those satisfying `base_word_residue.killed`.  What survives is
closed under the word reversal (bp, cp) -> (f+3-bp, f+3-cp), which is a mirror image of the tiling
(`MirrorKill.kill_mirror`), so one representative per orbit suffices.

Usage:  sweep_configs.py f          emits "f bp cp" lines, one per orbit representative
        sweep_configs.py f --check  prints the coverage certificate instead
"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from base_word_residue import admissible, killed


def escapes(f, R=5):
    return {w for w in admissible(f) if not killed(f, w[0], w[1], R)}


def mirror(f, w):
    return (f + 3 - w[0], f + 3 - w[1])


def transversal(f, R=5):
    """One representative per mirror orbit: the member with the smaller bp."""
    out, seen = [], set()
    for w in sorted(escapes(f, R)):
        if w in seen:
            continue
        seen.add(w)
        seen.add(mirror(f, w))
        out.append(w)
    return out


if __name__ == '__main__':
    f = int(sys.argv[1])
    T = transversal(f)
    if len(sys.argv) > 2 and sys.argv[2] == '--check':
        E = escapes(f)
        covered = set(T) | {mirror(f, w) for w in T}
        print(f"f={f}  N={3*f*f-1}  words={len(admissible(f))}  escapes={len(E)}  orbits={len(T)}")
        print(f"  every escape covered by the transversal or its mirror: {E <= covered}")
    else:
        for bp, cp in T:
            print(f, bp, cp)
