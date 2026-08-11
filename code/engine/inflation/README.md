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
