# Inflation instances

The base-beta tile is a rep-tile: expansion by `f` is tiled by `f^2` copies. At `m = 1` the complete
west corner block is that inflation and its far side is the whole equal side, so the inflated tile's
`c`-side word is the equal side's word.

`prop:inflbdy` (companion) proves the inflated boundary has `a`-side `a^f`, `b`-side `b^f`, and
`c`-side either `c^f` (`p = 0`) or one word with `f` `a`-edges (`p = 1`). These instances decide which.

| file | member | N | `c`-side constraint | verdict | nodes |
|---|---|---|---|---|---|
| `inst_infl13.txt`    | (1,3) | 9  | none        | FOUND_TILING          | 30 |
| `inst_infl13_p1.txt` | (1,3) | 9  | `(3,0,2)`   | EXHAUSTED_NO_TILING   | 9 |
| `inst_infl37.txt`    | (3,7) | 49 | none        | (not run to completion) | |
| `inst_infl37_p0.txt` | (3,7) | 49 | `(0,0,7)`   | FOUND_TILING          | 443347 |
| `inst_infl37_p1.txt` | (3,7) | 49 | `(7,0,4)`   | EXHAUSTED_NO_TILING   | 57824 |

So both inflations are rigid: the `p = 1` word is impossible and the standard subdivision is the only
boundary. The two FOUND certificates are `tiling_infl13_standard.txt` and
`tiling_infl37_standard.txt`; their boundary words are `aaa`/`bbb`/`ccc` and
`a^7`/`b^7`/`c^7` respectively.

The `p = 0` runs are the negative controls (Rule I13): a search that exhausted both profiles would
indicate a malformed instance, not a theorem.

Reproduce with `cengine_lifo FILE:<instance> <cap> <checkpoint>`.

## Sub-scale instances, and the transverse branch (`gen_scale.py`)

`gen_inflation.py` fixes two things it need not fix: the scale is `f`, and the `a`-side word is
`a^f`. `gen_scale.py` removes both (it reproduces `gen_inflation.py` byte for byte at `k = f` with
the standard `a`-word; `--selftest` checks six instances). Two consequences.

**The crux exists at every scale `k ≥ e+2`, not only at `k = f`.** `Inflation.a_side_no_b` and
`.a_side_rigid` force the `a`-side of a scale-`k` inflation to `a^k` for `k < f`, and the `b`-side is
unique; the `c`-side words are `(p·f, 0, k − p·e)` with `k − p·e ≥ 2`, so the `p = 0` versus `p ≥ 1`
dichotomy is present as soon as `k ≥ e + 2`. The smallest instance of the crux is therefore
`k = e + 2`, on `(e+2)²` tiles instead of `f²`:

| member | `k` | tiles | `p=1` verdict | nodes | `p=0` control |
|---|---|---|---|---|---|
| (3,7) | 5 | 25 | EXHAUSTED_NO_TILING | 16 | FOUND (2289) |
| (3,7) | 6 | 36 | EXHAUSTED_NO_TILING | 1 162 | FOUND (35658) |
| (3,7) | 7 | 49 | EXHAUSTED_NO_TILING | 57 824 | FOUND (443347, published) |
| (3,8) | 5 | 25 | EXHAUSTED_NO_TILING | 12 | FOUND (2066) |
| (3,8) | 6 | 36 | EXHAUSTED_NO_TILING | 2 159 | |
| (3,8) | 7 | 49 | EXHAUSTED_NO_TILING | 110 037 | |
| (5,7) | 7 | 49 | EXHAUSTED_NO_TILING | 3 219 | |

The `k = 7` row at `(3,7)` reproduces the published 57 824 exactly, which is the cross-check that
`gen_scale.py` agrees with the hand-built instances. Every `p ≥ 1` word at every scale tested was
exhausted: `(1,5)` `k=3,4,5`; `(1,6)` `k=3..6`; `(1,7)` `k=3..7`; `(2,5)` `k=4,5`; `(2,7)` `k=4,5`;
`(3,7)` `k=5,6,7`; `(3,8)` `k=5,6,7`; `(5,7)` `k=7`.

**The transverse `β`-corner branch was never searched.** `Inflation.a_side_all_c` shows the `a`-side
of a scale-`k` inflation may be `c^{ke/f}` rather than `a^k`; in the range `k ≤ f` that happens only
at `k = f`, where the side is `c^e` and the `β`-corner block is the transverse one, of scale `e`.
`prop:inflbdy` excludes this by asserting that both end letters of the `c`-side are `c`, which does
not follow from the flanks of `β` alone. Running the engine with `a`-side `= c^e` over **every**
admissible `c`-side word returns `EXHAUSTED_NO_TILING` at

    (1,3) (2,3) (1,4) (3,4) (1,5) (2,5) (3,5) (4,5) (1,6) (5,6) (1,7) (3,7) (5,7)

— 41 instances, each with the standard boundary returning `FOUND_TILING` as its control. At `e = 1`
the branch also dies by hand: see the discussion in `lean/Inflation.lean`.
