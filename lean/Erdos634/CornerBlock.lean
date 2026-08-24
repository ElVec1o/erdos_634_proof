import Erdos634.PincerLadder

/-!
# The corner blocks, and the `m = 1` input in general form

`rem:onegap` records that the crossing statement "admits no `m`-independent argument, and must
consume the `m = 1` hypothesis exactly where the corner block is rigid", and backs the
`m`-dependence with data: the five kernel-checked tilings all have `m ≥ 2` and cross
boundary-to-boundary `b`-lines `42, 15, 24, 10, 98` times
(`CrossingHypothesis.crossings_positive`).  So every `m`-independent route is refuted in advance,
and the only admissible shape of a proof is one that uses `m = 1` at the block.

This file states what that input *is*, generally in `(e, f)`.  `MasterLemmas` has the footprint
half per member (`feet_e2f3`, …) and `rem:blockbreaks` has the identification in prose; the
general form, and the spanning fact that isolates `m = 1`, are here.

## The identification

For the tile `(a, b, c) = (ef, f² - e², f²)`:

* the **`a`-block** — the complete block with `f` `a`-feet — is the tile scaled by `f`: footprint
  `f·a = ef²`, far side `f³ = f·c`, and it holds `f²` tiles;
* the **`c`-block** is the tile scaled by `e`: footprint `e·c = ef²` (the same, by `R_c`), far
  side `e²f = e·a`, and it holds `e²` tiles;
* the counts close: `f² + e² + 2(f² - e²) = 3f² - e² = N₀`.

## The `m = 1` input, isolated

An equal side at scale `m` has length `m·f³`.  At `m = 1` that is **exactly** the `a`-block's far
side, so the block spans from the base corner to the apex and is pinned between both ends; its
hypotenuse is the cevian from the apex.  At `m ≥ 2` the side is `m·f³` and the block reaches only
`1/m` of the way, so it can break — which is what `rem:blockbreaks` exhibits.

`block_far_side_eq_side_iff_m_one` is that dichotomy.  It is the asymmetry any proof of the
crossing statement must consume, and it is the reason the routes attempted on 2026-08-24 — strip
iteration, interior rigidity, congruence of fills — could not have worked: all three are
`m`-independent.

**This file proves the identification, not the crossing statement.**  Nothing here closes
`conj:advance`; it states the one input that is known to be necessary.
-/

namespace Erdos634.CornerBlock

/-- **The `a`-block's footprint is `ef²`**: `f` feet of length `a = ef`. -/
theorem block_footprint (e f : ℤ) : f * (e * f) = e * f ^ 2 := by ring

/-- **The `a`-block's far side is `f·c = f³`**, so the block is the tile scaled by `f`. -/
theorem block_far_side (f : ℤ) : f * f ^ 2 = f ^ 3 := by ring

/-- **The `c`-block's footprint is also `ef²`**: `e` feet of length `c = f²`.  This is the `R_c`
identity `e·c = f·a`, which is why the two corner structures span equally. -/
theorem dual_block_footprint (e f : ℤ) : e * f ^ 2 = f * (e * f) := by ring

/-- **The `c`-block's far side is `e·a = e²f`**, so it is the tile scaled by `e`. -/
theorem dual_block_far_side (e f : ℤ) : e * (e * f) = e ^ 2 * f := by ring

/-- **The counts close.**  `f²` tiles in the `a`-block, `e²` in the `c`-block, and `2(f² - e²)` in
the middle, totalling `N₀ = 3f² - e²`. -/
theorem block_counts (e f : ℤ) : f ^ 2 + e ^ 2 + 2 * (f ^ 2 - e ^ 2) = 3 * f ^ 2 - e ^ 2 := by
  ring

/-- **The middle is `e·b`.**  Subtracting the two corner footprints from the base leaves
`e(3f² - e²) - 2ef² = e(f² - e²) = e·b`: the `e` `b`-letters are exactly the middle's base. -/
theorem middle_is_eb (e f : ℤ) :
    e * (3 * f ^ 2 - e ^ 2) - 2 * (e * f ^ 2) = e * (f ^ 2 - e ^ 2) := by ring

/-- **The `m = 1` input, isolated.**  An equal side at scale `m` has length `m·f³`; it equals the
`a`-block's far side `f³` exactly when `m = 1`.  So at `m = 1` the block spans corner to apex, and
at `m ≥ 2` it does not. -/
theorem block_far_side_eq_side_iff_m_one (f m : ℤ) (hf : 0 < f) :
    m * f ^ 3 = f ^ 3 ↔ m = 1 := by
  constructor
  · intro h
    have hf3 : (0 : ℤ) < f ^ 3 := by positivity
    have : (m - 1) * f ^ 3 = 0 := by linarith [h]
    rcases mul_eq_zero.mp this with h1 | h2
    · linarith [h1]
    · exact absurd h2 (ne_of_gt hf3)
  · rintro rfl; ring

/-- **At `m ≥ 2` the block falls strictly short of the side.**  This is the configuration
`rem:blockbreaks` exhibits, and the reason no `m`-independent argument can force a complete
block. -/
theorem block_short_of_side (f m : ℤ) (hf : 0 < f) (hm : 2 ≤ m) : f ^ 3 < m * f ^ 3 := by
  have hf3 : (0 : ℤ) < f ^ 3 := by positivity
  nlinarith [hf3, hm]

/-! ## The `m = 1` invariant is the base `b`-count, and it is already proved

`rem:blockbreaks` names the lever outright: any proof of `hyp:walls` "must use `m = 1` in an
essential way — **the natural candidate being the base `b`-count, which is `e` at `m = 1` but is
`0` for both `44`-tilings and `7` for the `99`-tiling**".

That candidate is **already a theorem**: `BaseBetaWalkArith.base_b_count` proves `n_b = e` from the
walk equation `nₐ·a + n_b·b + n_c·c = e(3f² − e²)`, general in `(e, f)`, under the thin-regime side
condition `2ef + e² < f²`.  The right-hand side is the base length **at `m = 1`**, so the theorem
*is* the `m = 1` statement.  Nothing here re-proves it.

## Negative control (Rule I13)

The theorem must not apply to the three known base-`β` tilings, whose `b`-counts are `0`, `0`, `7`
rather than `e = 1`.  It does not, on two independent counts:

* their base lengths are `m·e·N₀` with `m = 2, 2, 3`, namely `22, 22, 33`, whereas the theorem's
  walk equation demands `e·N₀ = 11` (`known_tilings_wrong_base_length`);
* all three have tile `(2,3,4)`, i.e. `(e,f) = (1,2)`, where the thin condition fails outright:
  `2ef + e² = 5` is not `< f² = 4` (`thin_fails_at_f_two`).

So the machinery does not prove the false statement at `m ≥ 2`.  The control passes. -/

/-- **The known tilings' base lengths are not the `m = 1` one**, so `base_b_count`'s walk equation
is not satisfied there: `22, 22, 33` against `e·N₀ = 11` for the tile `(2,3,4)`. -/
theorem known_tilings_wrong_base_length :
    (22 : ℤ) ≠ 11 ∧ (33 : ℤ) ≠ 11 := by norm_num

/-- **The thin-regime condition fails at `(e,f) = (1,2)`**, the tile of all three known tilings:
`2ef + e² = 5` is not less than `f² = 4`.  A second, independent reason `base_b_count` cannot
reach them. -/
theorem thin_fails_at_f_two : ¬ (2 * 1 * 2 + 1 ^ 2 < 2 ^ 2 : Prop) := by norm_num

/-- **The thin condition holds at `e = 1` for every `f ≥ 3`**, which is the whole prime hole:
`2f + 1 < f²`. -/
theorem thin_holds_e_one (f : ℤ) (hf : 3 ≤ f) : 2 * 1 * f + 1 ^ 2 < f ^ 2 := by nlinarith

/-! ## Why `L_f` is uncrossed and useless, and every needed line is crossed

Two facts already in the corpus, put together, sharpen the gap considerably.

* `CevianSplit`: scanning the certified `44`-tiling for every line no tile crosses returns **six**
  — the three sides, two lines cutting off a single tile each, and **one** interior line.  That
  one is the **apex cevian**, and it splits the tiling `28 | 16` with zero tiles crossed.  So the
  apex cevian resists crossing even at `m ≥ 2`.
* `lem:noapexline` (`OrderForcing.chain_needs_small_lines`): the forcing chain needs `L_k` only for
  `k ≤ bp - 1 ≤ f - 1`, so **the apex line `L_f` is never required**.

The apex cevian *is* `L_f`: dropping it from the apex to the base point at distance `ef²m` gives
length `f·b·m` and cuts off the tile scaled by `fm`, which at `m = 1` is exactly the corner block
of `rem:blockbreaks`, whose hypotenuse the remark identifies as that cevian.

So the picture is:

* `L_f` — uncrossed at every `m`, and the one line the argument does **not** need;
* `L_k`, `k < f` — exactly the lines the argument **does** need, and crossed at `m ≥ 2`
  (`42, 15, 24, 10, 98` incidences, `CrossingHypothesis.crossings_positive`).

**The only interior line that resists crossing is useless to the argument, and every line the
argument uses is crossed at `m ≥ 2`.**  The `m = 1` input must therefore make the `L_k` with
`k < f` behave the way `L_f` already behaves at every `m`.  That is what a proof has to achieve,
stated in terms of objects that already exist, and it is strictly sharper than "consume `m = 1`
somewhere at the corner block".

`needed_lines_are_not_apex` records the disjointness of the two ranges; the geometric statement
about crossings is not proved here and is the gap. -/

/-- **The chain never needs the apex line.**  `k ≤ bp - 1` and `bp ≤ f` give `k < f`, so `k ≠ f`:
the one interior line known to resist crossing is precisely the one the argument cannot use. -/
theorem needed_lines_are_not_apex {f bp k : ℕ} (hf : 3 ≤ f) (hb3 : 3 ≤ bp) (hbf : bp ≤ f)
    (hk : k ≤ bp - 1) : k ≠ f := by omega

/-- **The cevian split's counts**, at the scale where the cut-off piece is the corner block:
`(fm)² + m²(2f² - e²) = m²(3f² - e²) = m²N₀`.  At `m = 1` the first summand is `f²`, the block's
tile count. -/
theorem cevian_split_counts (e f m : ℤ) :
    (f * m) ^ 2 + m ^ 2 * (2 * f ^ 2 - e ^ 2) = m ^ 2 * (3 * f ^ 2 - e ^ 2) := by ring

/-- **The `44`-tiling's split, as reported by `CevianSplit`**: `16 + 28 = 44`, the cut-off piece
being the tile at scale `fm = 4`. -/
theorem cevian_split_44 : ((2 : ℤ) * 2) ^ 2 + 2 ^ 2 * (2 * 2 ^ 2 - 1 ^ 2) = 44 := by norm_num

end Erdos634.CornerBlock
