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

**Corrected below** (`first_failure_escapes`): those two are not two families but one, seen from
the two base corners — `(f-1, f+1)` is the mirror `(f+3-4, f+3-2)` of `(4,2)`.  An earlier version
of this paragraph read "killing `(4,2)` by a separate argument gains nothing — the second family
still escapes"; by `kill_mirror` a kill of `(4,2)` stated generally in `f` transports to its mirror,
so it gains the whole `+1`.  After the gain four new escapes appear (`(5,2), (5,3)` and their
mirrors, again two orbits).  What survives of the sharpness claim is that each `f` costs its own
reach step; what does not is the count — the step is one configuration, not two families.

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

/-! ## The window is mirror-symmetric, so the escapes come in pairs

The target is isosceles, so reflecting it swaps the two base corners and reverses the base word:
position `i` goes to `f + 3 - i`, and a configuration `(bp, cp)` goes to `(f+3-bp, f+3-cp)`.  The
admissible box `3 ≤ bp ≤ f`, `2 ≤ cp ≤ f+1` is carried to itself.

The four kills are stated asymmetrically --- direct-`b` from the `b`-first corner, L2 from the
`c`-first corner --- but the reflection swaps those corners, so it should permute the kills rather
than break them.  It does, in two transpositions: disjuncts 1 and 2 exchange, and so do 3 and 4
(`kill_mirror`).  Hence the escape set is closed under the reflection and its configurations come
in mirror pairs, with only the fixed points unpaired.

**This halves the residue.**  Enumerating the admissible box against the *proved* reach 3 (`R = 4`;
reach 4 remains open at `prop:a2branch` row 3) gives, per member, escapes and escapes-up-to-mirror:

```
   f      N    words   escapes(R=4)   orbits        orbit representatives
   5     74       12        0            0          -- closed, cor:walls15
   6    107       20        2            1
   7    146       30        6            3          (4,2) (5,2) (5,3)
   8    191       42       14            7          (4,2) (5,2) (5,3) (5,6) (5,7) (5,8) (5,9)
```

So `N = 191`, the smallest unsettled prime, stands **seven configurations** from an argument-only
exclusion at the reach available today, and three at reach 4 --- not forty-two.  Generated by
`code/analysis/base_word_residue.py`.

The count is a measurement, not a route: `pincer_sharp` still says each `f` costs its own reach
step. What the mirror buys is a halving of the work at whatever reach is reached, and an explicit,
short list to aim at. -/

/-- The four pincer kills, as a predicate. -/
def Kill (f bp cp R : ℕ) : Prop :=
  (bp < cp ∧ bp ≤ R) ∨ (cp < bp ∧ f + 3 - bp ≤ R) ∨
  (cp = bp + 1 ∧ f + 3 - cp ≤ R) ∨ (bp = cp + 1 ∧ cp ≤ R)

/-- **The kills are invariant under the reflection `i ↦ f + 3 - i`.**  Disjuncts 1 and 2 exchange,
and so do 3 and 4. -/
theorem kill_mirror (f bp cp R : ℕ) (hb3 : 3 ≤ bp) (hbf : bp ≤ f)
    (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) :
    Kill f (f + 3 - bp) (f + 3 - cp) R ↔ Kill f bp cp R := by
  unfold Kill
  omega

/-- The reflection carries the admissible box to itself. -/
theorem mirror_admissible (f bp cp : ℕ) (hb3 : 3 ≤ bp) (hbf : bp ≤ f)
    (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    3 ≤ f + 3 - bp ∧ f + 3 - bp ≤ f ∧ 2 ≤ f + 3 - cp ∧ f + 3 - cp ≤ f + 1 ∧
      f + 3 - bp ≠ f + 3 - cp := by
  omega

/-- The reflection is an involution on the box. -/
theorem mirror_involutive (f bp : ℕ) (hb3 : 3 ≤ bp) (hbf : bp ≤ f) :
    f + 3 - (f + 3 - bp) = bp := by omega

/-! ## Correction: the two escaping families are one, and `(4,2)` is worth a level

The sharpness discussion above reads: "Killing `(4, 2)` by a separate argument gains **nothing** —
the second family still escapes.  Killing *both* families gains exactly `+1` in `f`."

That is wrong, and `kill_mirror` is why.  At the first failing level `f = R + 2` the escapes are
exactly two configurations, `(4,2)` and `(f-1, f+1)`, and these are **mirror images**:
`(f+3-4, f+3-2) = (f-1, f+1)`.  The tabulated pairs are all of this shape —
`R=4, f=6: (4,2),(5,7)`; `R=7, f=9: (4,2),(8,10)` — which the table displays without remarking
on it.  So the "constant family" and the "growing family" are one orbit seen from the two base
corners, and a kill of `(4,2)` stated generally in `f` transports to the other by reflecting the
tiling.  It does not gain nothing; it gains the whole `+1`.

`first_failure_escapes` proves the escape set at `f = R + 2` is exactly that orbit.

The practical reading changes accordingly.  Each level still costs its own step — that much of the
sharpness claim survives, since new escapes appear after the gain — but the step is **one
configuration**, not two families, and it is the same configuration `(4,2)` at every level.  For the
prime hole this is the difference between a vague programme and a single named target: `N = 191`
needs the reach ladder driven from `R = 4` to `R = 7`, and each of those three steps is a proof that
the base word `a\,c\,a\,b\,a^{f-3}` — the word `(bp, cp) = (4, 2)` names — cannot occur. -/

/-- **At the first failing level the escapes are exactly the mirror orbit of `(4,2)`.** -/
theorem first_failure_escapes {R bp cp : ℕ} (hR : 4 ≤ R)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ R + 2) (hc2 : 2 ≤ cp) (hcf : cp ≤ R + 3) (hne : bp ≠ cp)
    (hesc : ¬ Kill (R + 2) bp cp R) :
    (bp = 4 ∧ cp = 2) ∨ (bp = R + 1 ∧ cp = R + 3) := by
  unfold Kill at hesc
  push_neg at hesc
  omega

/-- `(4,2)` really does escape at its own level. -/
theorem four_two_escapes {R : ℕ} (hR : 4 ≤ R) : ¬ Kill (R + 2) 4 2 R := by
  unfold Kill; push_neg; omega

/-- And so does its mirror, necessarily. -/
theorem four_two_mirror_escapes {R : ℕ} (hR : 4 ≤ R) : ¬ Kill (R + 2) (R + 1) (R + 3) R := by
  unfold Kill; push_neg; omega

/-- The two are mirror images: reflecting `(4,2)` at `f = R + 2` gives `(f-1, f+1)`. -/
theorem four_two_mirror {R : ℕ} (hR : 4 ≤ R) :
    (R + 2 + 3 - 4, R + 2 + 3 - 2) = (R + 1, R + 3) := by
  have h1 : R + 2 + 3 - 4 = R + 1 := by omega
  have h2 : R + 2 + 3 - 2 = R + 3 := by omega
  rw [h1, h2]

end Erdos634.PincerLadder
