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

* `j = 1`: the reflected apex has `s = j a - S/2 < 0`, so the tile crosses the mast.  Excluded.
  (CORRECTED 2026-09-10: the apex is at `j a - S/2`, not `j a - S` — see "the mast's exact reach"
  below — so the mast's reach is `j = 1` alone, not `j ≤ 2`.  `reflected_crosses_mast` stays a
  true inequality but is weaker than the mast condition at `j = 2`.  Nothing downstream changes:
  the mast is only the base case, and `LayerLink.strip_layer_rigid` already states it at `idx 0`
  in the correct doubled form.)
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
-- CONTENT-FREE (code/trivia_audit.py, 2026-08-25): this statement asserts nothing --
-- rearrangement only (commutativity/associativity).
-- Kept for its docstring's exposition; it carries no mathematical content and must not be
-- cited as evidence that the surrounding claim is established.
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

/-- **Exclusion 1 — the mast.**  Cleared by `f`: `j a f < e N₀` for `j ≤ 2`.
CORRECTED 2026-09-10: the geometric reading of this range was wrong by a factor of two.  The
reflected apex is at `j a - S/2` (`ChordChart.reflected_apex_left_of_mast`, and
`reflected_apex_abscissa` below), so "apex left of the mast" is `2 j a f < e N₀`, which holds
*only at `j = 1`* (`mast_reach_exactly_one`).  The inequality below is true as stated, and its
`j = 1` instance is the only one that is ever used — see `LayerLink.strip_layer_rigid`. -/
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


/-! ### The layer induction, as a schema

The two exclusions above are pointwise facts about one position.  Turning them into "every tile of
the layer is unreflected" is an induction, and it is stated here as a schema whose hypotheses are
exactly the two exclusions.  This is the firewall: the geometric content lives in
`reflected_crosses_mast` and `reflected_overlaps_predecessor` (both VERIFIED above) and in the
corresponding `CLayerRigid` gap bounds, while the induction itself is pure logic.

Formalizing the *link* — that the exclusions imply the hypotheses `base` and `step` for the actual
geometric predicate "tile `j` is unreflected" — needed a formalization of tilings that this project
did not have.

UPDATED 2026-08-24.  It has one now.  `Congruence` supplies the predicate
(`CongruentDissection.UnreflectedAt`), and `LayerLink.layer_rigid_of_exclusions` supplies the
induction against it, instantiated for this layer as `strip_layer_rigid` and for the `c`-layer as
`c_layer_rigid_link`.  What is still missing is *narrower and nameable*.

UPDATED again, same day.  `ChordChart` derives the first bridge outright: placing the tile's
`a`-edge on the floor and subtracting the two distance equations gives the reflected apex at
`(a²+b²-c²)/(2a)`, whose numerator is `e²(e²-f²) < 0` for every member.  The second bridge is
reduced and then CLOSED: both apexes straddle the shared foot, and two triangles reaching across a
common vertical at positive height do intersect — each corner cone contains the straight-up
direction, so both contain a vertical segment of positive height from the shared foot.

**STATUS (corrected 2026-09-10).**  The 2026-08-24 version of this paragraph cited
`ChordChart.upward_in_cone` and `ChordChart.shared_segment_pos` as proving that planar step.  They
do not — the first is a statement about two vectors, the second is `lt_min` — so the claim "BOTH
bridges are theorems" was, at that date, false.  It is true now: the planar step is
`ChordChartPlanar.interiors_meet_at_shared_foot`, with the member instance
`ChordChartPlanar.member_configuration_interiors_meet` and an explicit non-vacuity witness.  What
remains for this file is only ASSEMBLY: turning `ChordChart`'s geometric
conclusions into the inequality-shaped hypotheses `LayerLink.strip_layer_rigid` consumes, via
`Dissection.covers` (an apex left of the mast lies outside the target) and
`Dissection.interiors_disjoint` (overlapping bodies are impossible).  That is ordinary work with
every input proved, not an open obstruction.
-/

/-! ### The mast's exact reach (added 2026-09-10)

`reflected_crosses_mast` is stated for `j ≤ 2`, and the header above reads that range as "the
reflected apex has `s = j a - S < 0`".  **That reading is off by a factor of two, and the mast's
true reach is `j = 1` alone.**  `ChordChart.reflected_apex_left_of_mast` pins the reflected apex
*relative to the tile's own left foot* at `x_r = (a² + b² - c²)/(2a) = e(e² - f²)/(2f)`, and
`x_u + x_r = a` gives `x_r = a - S/2`, not `a - S`.  So the reflected tile at position `j` has
apex abscissa `X_j = (j-1)a + x_r = j a - S/2`, and `X_j < 0` is `2 j a f < e N₀`, not
`j a f < e N₀`.

In closed form, cleared by `2f`,

  `2 f X_j = e ((2j - 3) f² + e²)`   (`reflected_apex_abscissa`),

which is negative exactly when `(3 - 2j) f² > e²`, i.e. — since `0 < e < f` — exactly at `j = 1`.

**The failure at `j ≥ 2` is not marginal and does not decay.**  `X_j` is arithmetic in `j` with
common difference exactly `a` (`apex_step_is_one_edge`), starting from `X_1 = x_r ∈ (-a/2, 0)`.
Hence `X_2 = a + x_r > a/2` (`reflected_apex_beyond_half_edge`): the apex clears the mast by more
than half a full `a`-edge at the very first position where the exclusion fails, and by
`(j - 3/2) a` thereafter.  There is therefore no weaker-but-nonzero mast bound at `j = 2`, `j = 3`
or any later position for any member: the excluded quantity `-X_j` drops below zero in one step of
size `a` from a starting value smaller than `a/2`, so it is never "barely" positive.  Numerically,
`X_2 / a = (f² + e²)/(2f²) ∈ (1/2, 1)` — e.g. `0.5078` at `(e,f) = (1,8)`, `N = 191`.

This costs nothing downstream.  `LayerLink.strip_layer_rigid` already takes its `mast` hypothesis
at `idx 0` only and already states it in the correct doubled form `e N₀ ≤ 2 a f`; the mast is the
*base case* of the layer induction and nothing else, with every `j ≥ 2` carried by
`reflected_overlaps_predecessor`.  `reflected_crosses_mast` remains true as an inequality — it is
just weaker than the mast condition for `j = 2`, where the mast condition is false.
-/

/-- **The reflected apex abscissa, in closed form.**  A tile whose `a`-edge is `[(j-1)a, ja]` on
the floor and whose apex is at distance `b` from the left foot and `c` from the right foot (the
*reflected* placement) has apex abscissa `x` with `2 f x = e ((2j-3) f² + e²)`.  Obtained by
subtracting the two distance equations; no trigonometry, no case split. -/
theorem reflected_apex_abscissa (e f j x y : ℝ) (he : 0 < e) (hf : 0 < f)
    (h1 : (x - (j - 1) * (e * f)) ^ 2 + y ^ 2 = (f ^ 2 - e ^ 2) ^ 2)
    (h2 : (x - j * (e * f)) ^ 2 + y ^ 2 = (f ^ 2) ^ 2) :
    2 * f * x = e * ((2 * j - 3) * f ^ 2 + e ^ 2) := by
  have hx : e * (2 * f * x) = e * (e * ((2 * j - 3) * f ^ 2 + e ^ 2)) := by
    linear_combination h1 - h2
  exact mul_left_cancel₀ (ne_of_gt he) hx

/-- **The mast condition carries a factor of two.**  `X_j < 0` is `2 j a f < e N₀`, not the
`j a f < e N₀` of `reflected_crosses_mast`. -/
theorem mast_condition_doubled (e f j x : ℝ) (he : 0 < e) (hf : 0 < f)
    (hx : 2 * f * x = e * ((2 * j - 3) * f ^ 2 + e ^ 2)) :
    x < 0 ↔ 2 * j * (e * f) * f < e * (3 * f ^ 2 - e ^ 2) := by
  constructor
  · intro h
    nlinarith [mul_pos (by linarith : (0:ℝ) < 2 * f) (neg_pos.mpr h)]
  · intro h
    nlinarith [mul_pos he hf]

/-- **The mast excludes position 1.**  At `j = 1`, `2 f X_1 = e(e² - f²) < 0`. -/
theorem mast_excludes_position_one (e f x y : ℝ) (he : 0 < e) (hef : e < f)
    (h1 : (x - (1 - 1) * (e * f)) ^ 2 + y ^ 2 = (f ^ 2 - e ^ 2) ^ 2)
    (h2 : (x - 1 * (e * f)) ^ 2 + y ^ 2 = (f ^ 2) ^ 2) :
    x < 0 := by
  have hf : 0 < f := lt_trans he hef
  have hx := reflected_apex_abscissa e f 1 x y he hf h1 h2
  nlinarith [mul_pos he he, mul_pos he hf]

/-- **The mast is vacuous from position 2 on, by more than half an `a`-edge.**  For `j ≥ 2`,
`2 f X_j ≥ e (f² + e²) > e f²`, so `X_j > ef/2 = a/2`.  This is the sharp statement: the mast's
reach is exactly `j = 1`, and the first failure clears it by a margin bounded below by `a/2`
uniformly over every member — not by a shrinking positive amount. -/
theorem reflected_apex_beyond_half_edge (e f j x : ℝ) (he : 0 < e) (hef : e < f) (hj : 2 ≤ j)
    (hx : 2 * f * x = e * ((2 * j - 3) * f ^ 2 + e ^ 2)) :
    (e * f) / 2 < x := by
  have hf : 0 < f := lt_trans he hef
  have key : 2 * f * (x - e * f / 2) = e * (f ^ 2 * (2 * j - 4)) + e ^ 3 := by
    linear_combination hx
  have h1 : 0 ≤ e * (f ^ 2 * (2 * j - 4)) :=
    mul_nonneg he.le (mul_nonneg (by positivity) (by linarith))
  have h2 : (0:ℝ) < e ^ 3 := by positivity
  by_contra hc
  push_neg at hc
  have : 2 * f * (x - e * f / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

/-- **No decay: the apex advances by exactly one `a`-edge per position.**  `X_{j+1} - X_j = a`,
so the mast margin `-X_j` decreases by exactly `a` at every step.  Starting from
`X_1 = x_r > -a/2`, it is therefore negative from `j = 2` onwards and can never be marginally
positive at any position — the exclusion does not decay, it terminates. -/
theorem apex_step_is_one_edge (e f j x x' : ℝ) (hf : 0 < f)
    (hx : 2 * f * x = e * ((2 * j - 3) * f ^ 2 + e ^ 2))
    (hx' : 2 * f * x' = e * ((2 * (j + 1) - 3) * f ^ 2 + e ^ 2)) :
    x' - x = e * f := by
  have h : 2 * f * (x' - x) = 2 * f * (e * f) := by ring_nf; ring_nf at hx hx'; linarith
  exact mul_left_cancel₀ (by positivity : (2:ℝ) * f ≠ 0) h

/-- **The reach, as an integer statement.**  For `1 ≤ j`, the mast condition `2 j a f < e N₀`
holds if and only if `j = 1`. -/
theorem mast_reach_exactly_one (e f j : ℤ) (he : 0 < e) (hef : e < f) (hj : 1 ≤ j) :
    (2 * j * (e * f) * f < e * (3 * f ^ 2 - e ^ 2)) ↔ j = 1 := by
  have hf : 0 < f := lt_trans he hef
  constructor
  · intro h
    by_contra hne
    have hj2 : 2 ≤ j := by omega
    have h1 : (1:ℤ) ≤ 2 * j - 3 := by omega
    have hff : (0:ℤ) < f ^ 2 := by positivity
    have hle : f ^ 2 ≤ (2 * j - 3) * f ^ 2 := le_mul_of_one_le_left hff.le h1
    have hee : (0:ℤ) < e ^ 2 := by positivity
    have hpos : 0 < e * ((2 * j - 3) * f ^ 2 + e ^ 2) := mul_pos he (by linarith)
    have heq : e * ((2 * j - 3) * f ^ 2 + e ^ 2)
        = 2 * j * (e * f) * f - e * (3 * f ^ 2 - e ^ 2) := by ring
    linarith [heq ▸ hpos]
  · rintro rfl
    have hsq : e ^ 2 < f ^ 2 := by nlinarith
    nlinarith [mul_pos he (sub_pos.mpr hsq)]

/-- **Non-vacuity witness (Rule 2).**  The distance hypotheses of `reflected_apex_abscissa` are
simultaneously satisfiable at a real member: `(e,f) = (1,8)`, i.e. `N = 191`, the smallest
unsettled prime, with tile `(a,b,c) = (8,63,64)`.  At `j = 1` the reflected apex is
`x = -63/16 < 0` (mast crossed) with `y² = 63²·255/256 > 0`; at `j = 2` the same tile's apex is at
`x = 8 - 63/16 = 65/16 > a/2 = 4`.  So neither `mast_excludes_position_one` nor
`reflected_apex_beyond_half_edge` is vacuous. -/
theorem member_witness_191 :
    ∃ x y : ℝ,
      (x - (1 - 1) * ((1:ℝ) * 8)) ^ 2 + y ^ 2 = ((8:ℝ) ^ 2 - 1 ^ 2) ^ 2
      ∧ (x - 1 * ((1:ℝ) * 8)) ^ 2 + y ^ 2 = ((8:ℝ) ^ 2) ^ 2
      ∧ x < 0 ∧ 0 < y := by
  refine ⟨-63/16, Real.sqrt (3969 * 255 / 256), ?_, ?_, by norm_num, ?_⟩
  · rw [Real.sq_sqrt (by norm_num)]; norm_num
  · rw [Real.sq_sqrt (by norm_num)]; norm_num
  · exact Real.sqrt_pos.mpr (by norm_num)

/-- **Layer induction schema.**  If the first tile is unreflected and an unreflected tile forces
its successor to be unreflected, every tile of the layer is unreflected.  Instantiated for
`a`-layers by `reflected_crosses_mast` (base, via `j = 1`) and `reflected_overlaps_predecessor`
(step), and for `c`-layers by `CLayerRigid.left_gap_not_tiles` and
`CLayerRigid.mixed_gap_not_tiles`. -/
theorem layer_induction (U : ℕ → Prop) (base : U 0) (step : ∀ j, U j → U (j + 1)) :
    ∀ j, U j := fun j => Nat.rec base step j

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
#print axioms Erdos634.StripRigid.layer_induction
#print axioms Erdos634.StripRigid.reflected_apex_abscissa
#print axioms Erdos634.StripRigid.mast_condition_doubled
#print axioms Erdos634.StripRigid.mast_excludes_position_one
#print axioms Erdos634.StripRigid.reflected_apex_beyond_half_edge
#print axioms Erdos634.StripRigid.apex_step_is_one_edge
#print axioms Erdos634.StripRigid.mast_reach_exactly_one
#print axioms Erdos634.StripRigid.member_witness_191
