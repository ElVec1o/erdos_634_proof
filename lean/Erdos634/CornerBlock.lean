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

end Erdos634.CornerBlock
