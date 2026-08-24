import Erdos634.OrderForcing

/-!
# The pincer ladder, uniform in the reach

`OrderForcing` proves the pincer window twice: `pincer_window` (kills covering depth `≤ 4`,
giving `f ≤ 5`) and `pincer_window_four` (depth `≤ 5`, giving `f ≤ 6`).  Both are pure `omega`
statements, and they are instances of one theorem uniform in the depth `R`.

## The ladder

`pincer_ladder`: if the four kills cover depth `≤ R`, the window is empty for every `f ≤ R + 1`.
Since reach `r` makes the kills cover depth `≤ r + 1`, this reads

  **reach `r`  ⟹  `f ≤ r + 2`.**

Checked against the two proved cases: reach `3` gives `R = 4`, `f ≤ 5` — `pincer_window`; reach
`4` gives `R = 5`, `f ≤ 6` — `pincer_window_four`.  Both recovered below as corollaries.

The practical consequence is that the *arithmetic* half of the ladder is now finished for every
level at once.  Extending `cor:walls16` past `f = 6` needs only the geometric reach step; no new
`omega` work is required at any height.

## Sharpness, and why there is no shortcut

The bound is exactly sharp: at `f = R + 2` the configuration `(bp, cp) = (4, 2)` escapes all four
kills (`pincer_sharp`), for every `R ≥ 4`.  Enumerating the escapes at the first failing `f`
shows exactly two families — the constant `(4, 2)` and a growing `(f−1, f+1)`:

```
  R= 4, f= 6: [(4,2), (5,7)]      R= 7, f= 9: [(4,2), (8,10)]
  R= 5, f= 7: [(4,2), (6,8)]      R= 8, f=10: [(4,2), (9,11)]
  R= 6, f= 8: [(4,2), (7,9)]      R= 9, f=11: [(4,2), (10,12)]
```

Killing `(4, 2)` by a separate argument gains **nothing** — the second family still escapes.
Killing *both* families gains exactly `+1` in `f`, after which four new escapes appear
(`(5,2), (5,3)` and the shifted pair).  So the window admits no shortcut: each `f` costs its own
reach step, and picking off individual configurations buys one level each at best.

## What this says about the prime hole

`ThinHole` shows `f` is always **even** on the prime hole (odd `f` makes `3f² − 1` even, hence
composite), and the smallest unsettled case is `191 = 3·8² − 1`, i.e. `f = 8`.  By the ladder
that needs `R = 7`, i.e. **reach 6** — three steps beyond the reach-4 step that is itself still
open at `prop:a2branch` row 3.  This is a measurement of the distance to `N = 191`, not a route
to it.
-/

namespace Erdos634.PincerLadder

/-- **The pincer ladder, uniform in `R`.**  If the four kills cover depth `≤ R`, no admissible
`(bp, cp)` escapes for any `f ≤ R + 1`. -/
theorem pincer_ladder {f bp cp R : ℕ} (hf : 3 ≤ f) (hfR : f ≤ R + 1)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ R) ∨ (cp < bp ∧ f + 3 - bp ≤ R) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ R) ∨ (bp = cp + 1 ∧ cp ≤ R) := by omega

/-- **Reach 3 is the `R = 4` instance** — recovers `OrderForcing.pincer_window`. -/
theorem ladder_reach_three {f bp cp : ℕ} (hf : 3 ≤ f) (hf5 : f ≤ 5)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ 4) ∨ (cp < bp ∧ f + 3 - bp ≤ 4) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ 4) ∨ (bp = cp + 1 ∧ cp ≤ 4) :=
  pincer_ladder hf (by omega) hb3 hbf hc2 hcf hne

/-- **Reach 4 is the `R = 5` instance** — recovers `OrderForcing.pincer_window_four`. -/
theorem ladder_reach_four {f bp cp : ℕ} (hf : 3 ≤ f) (hf6 : f ≤ 6)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ 5) ∨ (cp < bp ∧ f + 3 - bp ≤ 5) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ 5) ∨ (bp = cp + 1 ∧ cp ≤ 5) :=
  pincer_ladder hf (by omega) hb3 hbf hc2 hcf hne

/-- **Sharpness.**  At `f = R + 2` the configuration `(bp, cp) = (4, 2)` escapes all four kills,
so the ladder's bound cannot be improved by arithmetic alone. -/
theorem pincer_sharp {R : ℕ} (hR : 4 ≤ R) :
    ¬ ((4 < 2 ∧ 4 ≤ R) ∨ (2 < 4 ∧ (R + 2) + 3 - 4 ≤ R) ∨
       (2 = 4 + 1 ∧ (R + 2) + 3 - 2 ≤ R) ∨ (4 = 2 + 1 ∧ 2 ≤ R)) := by omega

/-- **The reach needed for the smallest unsettled prime.**  `191 = 3·8² − 1` has `f = 8`, so the
ladder requires `R = 7`, i.e. reach `6`. -/
theorem reach_for_191 : 3 * 8 ^ 2 - 1 = 191 ∧ (8 : ℕ) ≤ 7 + 1 := by norm_num

end Erdos634.PincerLadder
