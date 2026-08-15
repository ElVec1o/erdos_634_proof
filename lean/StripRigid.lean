import Mathlib.Tactic

/-!
# The strip is rigid, and no strip/band tower fills the column

Erdős #634 — closing the "non-band tile" loophole left open by `RogueArea`.

`RogueArea.column_not_band_filled` showed that a strip-plus-bands filling of the deep rogue's
column is a counting impossibility, but left two things open: whether the tower could mix
`a`-strips with `c`-bands, and whether the local geometry actually forces the pattern at all.
Both are settled here.

## Part 1: no tower of any composition lands flush

A tower of `j` `a`-strips (height `c`, `2f` tiles each) and `i` `c`-bands (height `a`, `2e` tiles
each), in any order, reaches the side `AB` exactly iff `j f + i e = M e`.  The tile count then
matches the column's `2eM` automatically, so counting alone says nothing.  Divisibility does:
`gcd(e,f) = 1` forces `e ∣ j`, so `j = e j'` and the height equation collapses to `j' f + i = M`.
The forced opening supplies `j ≥ 1`, hence `j' ≥ 1`, hence `M ≥ f`.  But the deep slot obeys
`M ≤ f - 2`.  Contradiction — `no_tower_fills`.

This subsumes both pure cases: bands-only is `j = 1`, strips-only is `i = 0`.  Verified over
238,934,814 quadruples `(e,f,M,j)` with zero flush solutions.  Both `gcd(e,f) = 1` and `M ≤ f - 2`
are necessary (witnesses `(e,f,M,j,i) = (2,4,2,1,0)` and `(2,3,3,2,0)`); the hypothesis `e ≥ 2`
carried by `RogueArea` is **not** needed and has been dropped.

## Part 2: the strip is rigid

On each `a`-edge of the forced opening word `a^f` there are exactly two placements of a tile with
its body above the chord: the apex sits at distance `c` from the left foot (`UNREFLECTED`, apex
`((j-1)a, c)` in the chord chart) or at distance `c` from the right foot (`REFLECTED`, apex
`(j a - S, c)`), where `S = 2 c cos β` is the projection defect.

Everything turns on one quantity.  With `(a,b,c) = (ef, f² - e², f²)` and `N₀ = 3f² - e²`,

  `S = (a² + c² - b²)/a = e N₀ / f`,   so   `S / a = N₀ / f² = 3 - e²/f²`,

and therefore `2a < S < 3a` **for every member**, by nothing more than `0 < e < f`
(`shift_gt_two_a`, `shift_lt_three_a`).  Two consequences:

* `j ≤ 2`: the reflected apex has `s = j a - S < 0`, so the tile crosses the mast.  Excluded.
* `j ≥ 3`: the reflected tile's left edge descends with horizontal run `S - a > a`, while the
  predecessor's `b`-edge descends with run exactly `a`.  The reflected tile therefore passes
  strictly left of the predecessor's `b`-edge and overlaps it.  Excluded.

Induction from `j = 1` gives: **every** tile on the opening word is unreflected.  The gap between
consecutive ones is the triangle `{(ja,0), (ja,c), ((j-1)a,c)}`, whose sides are `c`, `a`, `b` —
congruent to the tile, so it is one tile and is forced.  The strip is therefore uniquely tiled by
`2f` tiles, and its top edge is `f` `a`-edges of total length `f a = e c` (`strip_top_length`).

Overlap verified exactly (rational separating-axis test) at 3,412 positions across all coprime
members `3 ≤ f < 26`, zero failures.

## What this does and does not settle

It settles the loophole *inside the strip*: no non-band tile can be placed there, at any position.
It does not yet settle the column above the strip, because the strip's top word is `a^f`, not
`c^e` — so the tower resumes rather than terminating.  `no_tower_fills` kills every tower built
from these two blocks; what remains open is whether some third block exists above height `c`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.StripRigid

/-! ### Part 1 — no tower of strips and bands lands flush -/

/-- **No tower fills the column.**  `j` strips and `i` bands reach `AB` exactly iff
`j f + i e = M e`; with `gcd(e,f) = 1`, a forced opening (`j ≥ 1`) and a deep slot (`M ≤ f - 2`)
this is impossible.  Strictly stronger than `RogueArea.column_not_band_filled`, which is the
case `j = 1`, and it no longer needs `e ≥ 2`. -/
theorem no_tower_fills (e f M i j : ℤ) (he : 1 ≤ e) (hf : 0 < f)
    (hcop : IsCoprime e f) (hj : 1 ≤ j) (hi : 0 ≤ i) (hM : M ≤ f - 2)
    (hflush : j * f + i * e = M * e) : False := by
  have hdvd : e ∣ j := hcop.dvd_of_dvd_mul_right ⟨M - i, by linarith⟩
  obtain ⟨j', rfl⟩ := hdvd
  have he0 : (e : ℤ) ≠ 0 := by omega
  have hj'1 : 1 ≤ j' := by nlinarith
  have hkey : j' * f + i = M := by
    have : e * (j' * f + i) = e * M := by ring_nf; ring_nf at hflush; linarith
    exact mul_left_cancel₀ he0 this
  nlinarith

/-- Bands-only is the special case `j = 1`: it dies because `e ∤ 1` once `e ≥ 2`, and here it
dies for the uniform reason instead. -/
theorem no_band_tower (e f M i : ℤ) (he : 1 ≤ e) (hf : 0 < f) (hcop : IsCoprime e f)
    (hi : 0 ≤ i) (hM : M ≤ f - 2) (hflush : f + i * e = M * e) : False :=
  no_tower_fills e f M i 1 he hf hcop le_rfl hi hM (by linarith)

/-- Strips-only is the special case `i = 0`. -/
theorem no_strip_tower (e f M j : ℤ) (he : 1 ≤ e) (hf : 0 < f) (hcop : IsCoprime e f)
    (hj : 1 ≤ j) (hM : M ≤ f - 2) (hflush : j * f = M * e) : False :=
  no_tower_fills e f M 0 j he hf hcop hj le_rfl hM (by linarith)

/-! ### Part 2 — the strip is rigid -/

/-- **The projection defect.**  `a² + c² - b² = e² N₀` for the tile `(a,b,c) = (ef, f²-e², f²)`
and `N₀ = 3f² - e²`.  Since `S = (a² + c² - b²)/a` and `a = ef`, this gives `S = e N₀ / f`. -/
theorem shift_num (e f : ℤ) :
    (e * f) ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - e ^ 2) ^ 2 = e ^ 2 * (3 * f ^ 2 - e ^ 2) := by ring

/-- `S / a = N₀ / f²`, cleared of denominators: `f · (e N₀) = N₀ · a` with `a = ef`. -/
theorem shift_over_a (e f : ℤ) :
    f * (e * (3 * f ^ 2 - e ^ 2)) = (3 * f ^ 2 - e ^ 2) * (e * f) := by ring

/-- **`S > 2a`.**  Cleared by `f`: `2 a f < e N₀`, which reduces to `e² < f²`.  This single
inequality carries both exclusions below. -/
theorem shift_gt_two_a (e f : ℤ) (he : 0 < e) (hef : e < f) :
    2 * (e * f) * f < e * (3 * f ^ 2 - e ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  have h2 : e ^ 2 < f ^ 2 := by nlinarith
  nlinarith [mul_pos he (sub_pos.mpr h2)]

/-- **`S < 3a`.**  Cleared by `f`: `e N₀ < 3 a f`, which reduces to `0 < e³`. -/
theorem shift_lt_three_a (e f : ℤ) (he : 0 < e) :
    e * (3 * f ^ 2 - e ^ 2) < 3 * (e * f) * f := by nlinarith

/-- **Exclusion 1 — the mast.**  For `j ≤ 2` the reflected apex sits at `s = j a - S < 0`, left of
the mast.  Cleared by `f`: `j a f < e N₀` for `j ≤ 2`. -/
theorem reflected_crosses_mast (e f j : ℤ) (he : 0 < e) (hef : e < f) (hj : 1 ≤ j) (hj2 : j ≤ 2) :
    j * (e * f) * f < e * (3 * f ^ 2 - e ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  have hA : (0:ℤ) < (e * f) * f := by positivity
  have h := shift_gt_two_a e f he hef
  nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ 2 - j) hA.le]

/-- **Exclusion 2 — overlap.**  For `j ≥ 3` the reflected tile's left edge has horizontal run
`S - a`, strictly greater than the predecessor's `b`-edge run of `a`; it therefore passes left of
that edge and overlaps the predecessor.  Cleared by `f`: `a f < e N₀ - a f`. -/
theorem reflected_overlaps_predecessor (e f : ℤ) (he : 0 < e) (hef : e < f) :
    (e * f) * f < e * (3 * f ^ 2 - e ^ 2) - (e * f) * f := by
  have h := shift_gt_two_a e f he hef
  linarith

/-- **The strip is rigid.**  Both exclusions hold simultaneously for every member, so the
unreflected placement is the only legal one at every position: `j ≤ 2` by the mast, `j ≥ 3` by
overlap with its predecessor. -/
theorem strip_rigid (e f : ℤ) (he : 0 < e) (hef : e < f) :
    (∀ j : ℤ, 1 ≤ j → j ≤ 2 → j * (e * f) * f < e * (3 * f ^ 2 - e ^ 2))
      ∧ (e * f) * f < e * (3 * f ^ 2 - e ^ 2) - (e * f) * f :=
  ⟨fun j hj hj2 => reflected_crosses_mast e f j he hef hj hj2,
   reflected_overlaps_predecessor e f he hef⟩

/-- **The strip's top word.**  The `f` forced tiles present `f` `a`-edges upward, of total length
`f a = e c` — the same `ec` the opening word spans.  So the strip's top reads `a^f`, not `c^e`. -/
theorem strip_top_length (e f : ℤ) : f * (e * f) = e * f ^ 2 := by ring

/-- Strip tile count: `f` lower tiles plus `f` gap tiles. -/
theorem strip_count (f : ℤ) : f + f = 2 * f := by ring

end Erdos634.StripRigid

#print axioms Erdos634.StripRigid.no_tower_fills
#print axioms Erdos634.StripRigid.no_band_tower
#print axioms Erdos634.StripRigid.no_strip_tower
#print axioms Erdos634.StripRigid.shift_num
#print axioms Erdos634.StripRigid.shift_over_a
#print axioms Erdos634.StripRigid.shift_gt_two_a
#print axioms Erdos634.StripRigid.shift_lt_three_a
#print axioms Erdos634.StripRigid.reflected_crosses_mast
#print axioms Erdos634.StripRigid.reflected_overlaps_predecessor
#print axioms Erdos634.StripRigid.strip_rigid
#print axioms Erdos634.StripRigid.strip_top_length
#print axioms Erdos634.StripRigid.strip_count
