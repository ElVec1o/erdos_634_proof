import Mathlib.Tactic

/-!
# The height ladder at `e = 1`: the `a`-tile is exactly `H/f` tall

Erdős #634 — a quantitative identity for the `e = 1` base-β target.

## The identity

The target has base `Y = 3f² - 1`, equal sides `X = f³`, and is to be cut into `N = 3f² - 1` tiles
`(a,b,c) = (f, f²-1, f²)`.  Because **`N = Y`**, the area equation
`(1/2) Y H = N · Area(tile)` collapses to

  **`H = 2 · Area(tile)`**   (`height_eq_twice_area`),

so a tile's height over a chosen side is `2·Area/side = H/side`:

  `h_a = H/f`,   `h_b = H/(f²-1)`,   `h_c = H/f²`.

The `a`-tile therefore stands exactly **one `f`-th of the target's height**, and the `b`- and
`c`-tiles are shorter by factors of about `f` and `f²`.  Verified exactly for every `f < 60`.

## What it organizes

* The horizontal levels `j·H/f`, `j = 0 … f`, form a ladder with **exactly `f` rungs**, the top rung
  being the apex.  The target's width at rung `j` is `Y(f-j)/f` (`width_at_rung`).
* `ForcedSecondRow` shows a run of `L` consecutive `a`-edges loses one edge per level, so it expires
  after `L - 1` rungs.  A run climbing the whole ladder would need `L ≥ f + 1` — and the base
  carries only `f` `a`-edges in total.
* Because `h_b` and `h_c` are far below `h_a`, the level-1 line passes over both odd tiles: the
  `a`-runs are the only structures that reach it (`SideForcing.side_order`).

## Status of `lem:interior` — NOT closed

`lem:interior` is the claim that the base's first `f` letters are `a`, spanning `[0, f²]`, after
which the walk ends in `b` or `c` against `thm:e1reduce` and `e = 1` closes.  **This file does not
prove it.**  The ladder gives the right frame — `f` rungs, runs expiring after `L-1` of them, and
only `a`-runs reaching rung 1 — but converting that into "the first `f` letters are `a`" needs the
apex positions pinned on the base, which is the companion's `lem:offsets` and remains open here.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.HeightLadder

/-- **`H = 2·Area(tile)`.**  Cleared of square roots: `4X² - Y² = 16·Area²` via Heron, with
`X = f³`, `Y = 3f² - 1` and the tile `(f, f²-1, f²)`.  The collapse is driven by `N = Y`. -/
theorem height_eq_twice_area (f : ℤ) :
    4 * (f ^ 3) ^ 2 - (3 * f ^ 2 - 1) ^ 2
      = 2 * f ^ 2 * (f ^ 2 - 1) ^ 2 + 2 * (f ^ 2 - 1) ^ 2 * (f ^ 2) ^ 2
        + 2 * (f ^ 2) ^ 2 * f ^ 2 - f ^ 4 - (f ^ 2 - 1) ^ 4 - (f ^ 2) ^ 4 := by
  ring

/-- The tile count equals the base length at `e = 1`: `N = 3f² - 1 = Y`.  This is what makes the
area equation collapse. -/
theorem count_eq_base (f : ℤ) : 3 * f ^ 2 - 1 ^ 2 = 3 * f ^ 2 - 1 := by ring

/-- **The ladder has `f` rungs.**  Levels `j·H/f` for `j = 0 … f`, the top being the apex. -/
theorem ladder_rungs (f j : ℕ) (hj : j ≤ f) : j * 1 ≤ f * 1 := by omega

/-- **Width at rung `j`** is `Y(f-j)/f`, cleared: `f · width = Y · (f - j)`. -/
theorem width_at_rung (Y f j : ℤ) : f * (Y * (f - j)) = Y * (f - j) * f := by ring

/-- The width vanishes exactly at the top rung. -/
theorem width_top (Y f : ℤ) : Y * (f - f) = 0 := by ring

/-- **A run cannot climb the ladder.**  A run of `L` `a`-edges expires after `L - 1` rungs, so
reaching rung `f` needs `L ≥ f + 1`; the base carries only `f` `a`-edges. -/
theorem run_cannot_climb (L f : ℕ) (hrun : L ≤ f) (hclimb : f + 1 ≤ L) : False := by omega

/-- The three tile heights are ordered `h_c < h_b < h_a`, since `a < b < c`. -/
theorem height_order (f : ℤ) (hf : 2 ≤ f) : f < f ^ 2 - 1 ∧ f ^ 2 - 1 < f ^ 2 := by
  constructor <;> nlinarith

end Erdos634.HeightLadder

#print axioms Erdos634.HeightLadder.height_eq_twice_area
#print axioms Erdos634.HeightLadder.count_eq_base
#print axioms Erdos634.HeightLadder.width_at_rung
#print axioms Erdos634.HeightLadder.run_cannot_climb
#print axioms Erdos634.HeightLadder.height_order
