# What it takes to prove the prime case of Erdős #634

A dependency map, with each node's current Rule 0 label. Built from the papers on 2026-09-01, not
from memory. The purpose is to replace batch-of-four working with a target that terminates.

**GOAL.** No prime `N > 3` is a number of congruent triangles into which some triangle can be cut,
except `N ≡ 1 (mod 4)` (and `N = 2, 3`).

---

## A. Primes `N ≢ 11 (mod 12)` — DONE

`thm:mod12` (VERIFIED forward): a prime `p > 3` with `p = 3f² − e²`, `gcd(e,f)=1`, satisfies
`p ≡ 11 (mod 12)`. So every prime outside that class is not a base-β candidate, and `thm:main`
(PROVED) excludes it. `thm:primefull` (PROVED) states the resulting equivalence.

*Residual debt, not blocking:* the **converse** of `thm:mod12` (every prime `≡ 11` is of that form)
uses quadratic reciprocity and the class group of discriminant 12 and is **not formalized**. It is
not needed for A — only the forward direction is — but it is needed to say the exceptional set is
*exactly* the class.

## B. Primes `N ≡ 11 (mod 12)` — OPEN. This is the whole problem.

Such `N` are exactly the base-β candidates: `N = 3f² − e²`, `gcd(e,f) = 1`. Since `N = m²N₀` and
`N` is prime, `m = 1`. So **the prime case is the `m = 1` case of the base-β family**, and splits:

### B1. `e = 1`: `N = 3f² − 1`
### B2. `e ≥ 2`

Both reduce to one question (`prop:threecostumes`, PROVED):

> **The crossing question.** At the end `V` of a maximal run of forced tiles along a segment `L`,
> must the next tile lay a whole edge on `L` without overrunning `V`, or can it cross at `V`?

`prop:ninetools` (PROVED) closes nine tool classes against it, for one reason: each computes a
quantity invariant under *relocating* edges, while the question asks *where* an edge lies. **Any new
attack must be location-sensitive.** This is the admission test.

---

## B1. The `e = 1` branch — two routes

### Route 1: word-by-word exclusion (the sweep made into a proof)

`thm:e1reduce` constrains the base word (`n_b = 1`, `n_c ≥ 1`). The words surviving the pincer
window at the proved reach are the *escapes*; a proof needs every escape family excluded **for every
`f`**, not per member. Orbit counts grow: 24, 41, 87, 149, 186 at `f = 12, 14, 18, 22, 24`, so this
is a proof about **families**, never an enumeration.

Families and their status:

| Family | share at `f=24` | status |
|---|---|---|
| `cp = bp − 1` (the march) | 7 | `rem:marchobl` OPEN — see below |
| `cp = f − 1` (the ceiling band) | 8 | mechanism measured, no proof |
| `cp = 2` | 10 | noted golden in `f`, no mechanism |
| `cp < bp`, other | 45 | unclassified |
| `cp > bp`, other | 116 | unclassified |

**The dominant families are unclassified.** The march covers 7 of 186 orbits at `f = 24`. Closing it
does *not* close `e = 1`.

#### `rem:marchobl` (the march family), OPEN
- (i) steps land on `γ`-carrying straight-edge junctions — **VERIFIED on a side of the target**
  (`presents_beta_or_gamma` → `junction_cases` → `MarchMonotone` → `all_but_one_is_march_junction`),
  with two hypotheses open in `MarchRunObject`: run contiguity, and the orientation word being the
  one read off the tiles.
- (ii) the two chiralities advance by one and two positions — **HEURISTIC** (traced, pre-registered
  hit at `bp = 6, 7`).
- (iii) both advances reduce to the same problem at smaller `bp` — **HEURISTIC** (same traces).
- Base cases: **VERIFIED** (`offset_terminal_dies`, residue 1 is a gap).

### Route 2: `conj:advance` — CONJECTURE, proved at `f = 2, 3, 4`

If proved, gives `p = 0`, hence `hyp:walls` for every `(1,f)`, which closes `e = 1` **entirely** —
all families at once. The conjecture names exactly two gaps and says any proof must close these and
no others:

1. a deviating `a`-run whose new `c`-chord ends beyond the forced region (tile-interior blocking
   fails);
2. an initial side `c`-block of length `≥ 2` (first-run orientation not forced).

Gap 2 is **general except for its enumeration**: its ingredients carry no restriction on `f`
(`first_run_kill`, `through_edge_exclusive`, `chord_two_b`, `double_c_kill`). What is missing is the
walk enumeration — for `f ≥ 5` there are `f − 3` double-`c` walks and the argument as written covers
only an initial block of exactly 2 followed by an `a`-run.

**Route 2 is the shorter path to `e = 1` and it is more precisely scoped than Route 1.**

## B2. The `e ≥ 2` branch

`cor:basewalls`' walk narrowing rests on `thm:n1`, whose induction fails at the interior points
`V_k`; `rem:n1gapexact` shows the missing step **is** the crossing question at `V_k`, verbatim. No
family decomposition exists here. Nothing in the march work touches `e ≥ 2`.

---

## Honest assessment of distance

- **A is done.** **B is not, and B is the problem.**
- Within B1, Route 2 (`conj:advance`, gap 2's enumeration) is the most sharply defined open target
  in the whole programme, and it would close `e = 1` outright.
- B2 has no route that is not the crossing question itself.
- The march work advances one family of one branch. It is real and it is small relative to the goal.
- The nine-tool no-go means no invariant-style argument will work; the admission test for anything
  new is location-sensitivity.

## Ordered target list

1. `conj:advance` gap 2: generalize the double-`c` walk enumeration from `f = 4` to all `f ≥ 5`.
   Closes the second of the two named gaps. **Highest value per unit effort in B1.**
2. `conj:advance` gap 1: the deviating `a`-run whose `c`-chord escapes the forced region.
   With 1, closes `e = 1` entirely.
3. `rem:marchobl` (ii)/(iii): the advance and the reduction, currently HEURISTIC.
4. Classify the 116 + 45 unclassified escape families — needed if Route 1 is ever to work.
5. B2: the crossing question at `V_k`.
6. `thm:mod12`'s converse: formalization debt, not blocking.
