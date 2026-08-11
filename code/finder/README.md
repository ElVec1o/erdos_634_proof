# finder — randomized tiling FINDER (Erdos #634)

Sound but **incomplete**: it may miss tilings, and finding nothing proves nothing. Every tiling it
reports is re-verified from scratch (congruence of all N tiles, exact area identity, and coverage
with disjoint interiors via the boundary algebra), so a bug yields a rejected candidate, never a
false theorem. **Exhaustion claims must come from `code/engine/cengine`, never from this program.**

    cargo build --release
    ./target/release/finder <instance.txt> [threads] [seed]
    FINDER_SHUFFLE=0 ./target/release/finder <instance.txt> 1     # deterministic control

Instance files are the same format the C++ engine reads.

## Status

Validated on N=44 (the (16,16,22) target, tile (2,3,4)): FOUND_TILING, 44 congruent tiles, verified
by this program and independently.

Measured on that instance:

| configuration | nodes | outcome |
|---|---|---|
| C++ cengine, deterministic | 858 163 | FOUND |
| finder, `FINDER_SHUFFLE=0` | 1 071 411 | FOUND |
| finder, randomized + Luby restarts | >1 420 000 | not found |

Randomizing the candidate order made the search **worse**. The corner-anchored order is not
arbitrary -- it is most-constrained-corner-first -- and that is precisely the assumption the
heavy-tailed/restart argument (Gomes, Selman & Crato 1997; Luby, Sinclair & Zuckerman 1993) does not
make. Uniform shuffling destroys real geometric information. Useful diversification here would have
to keep the deterministic order and vary something else (first move only, or a portfolio of distinct
principled orderings).
