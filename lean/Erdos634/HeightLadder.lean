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
  being the apex.  The target's width at rung `j` is `Y(f-j)/f` (`chord_width`, `width_at_rung_real`).

  **Correction (2026-08-25).**  Until now this bullet cited `width_at_rung`, whose statement was
  `f * (Y * (f - j)) = Y * (f - j) * f` — commutativity, proved by `ring`, asserting nothing about
  any width.  Three further declarations here were of the same kind (`count_eq_base`,
  `ladder_rungs`, `width_top`: respectively `3f² - 1² = 3f² - 1`, `j*1 ≤ f*1` from `j ≤ f`, and
  `Y*(f-f) = 0`).  They have been removed and the width is now derived from the side lines.
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

/-- **Arithmetic shell only.**  `L ≤ f` and `f + 1 ≤ L` contradict.  The intended reading — a run of
`L` `a`-edges expires after `L - 1` rungs, so climbing to rung `f` needs `L ≥ f + 1`, while the base
carries only `f` — needs the per-rung shrinkage, which is **not proved anywhere in the corpus**.  The
name previously suggested otherwise. -/
theorem run_cannot_climb (L f : ℕ) (hrun : L ≤ f) (hclimb : f + 1 ≤ L) : False := by omega

/-- **The chord width at height `h`, with content.**  For the target with base `(0,0)`–`(Y,0)` and
apex `(Y/2, H)`, the side lines put the chord's endpoints at `xL·2H = Y·h` and `xR·2H = 2YH − Y·h`.
Then `(xR − xL)·2H = 2Y(H − h)`: the width is `Y(H-h)/H`.  Cleared of denominators, so this is an
identity about the endpoints rather than about notation. -/
theorem chord_width (Y H h xL xR : ℤ)
    (hL : xL * (2 * H) = Y * h)
    (hR : xR * (2 * H) = 2 * Y * H - Y * h) :
    (xR - xL) * (2 * H) = 2 * Y * (H - h) := by linarith

/-- **Width at rung `j`.**  With `h = j·H/f` the width satisfies `width·f·2H = 2Y(f-j)H`, i.e.
`width = Y(f-j)/f`. -/
theorem width_at_rung_real (Y H f j width : ℤ) (hf : 0 < f)
    (hw : width * (2 * H) = 2 * Y * (H - (j * H) / f))
    (hdvd : (f : ℤ) ∣ j * H) :
    width * f * (2 * H) = 2 * Y * (f - j) * H := by
  obtain ⟨k, hk⟩ := hdvd
  have hjk : (j * H) / f = k := by rw [hk]; exact Int.mul_ediv_cancel_left k (by omega)
  rw [hjk] at hw
  calc width * f * (2 * H) = f * (width * (2 * H)) := by ring
    _ = f * (2 * Y * (H - k)) := by rw [hw]
    _ = 2 * Y * (f * H - f * k) := by ring
    _ = 2 * Y * (f * H - j * H) := by rw [← hk]
    _ = 2 * Y * (f - j) * H := by ring

/-- The three tile heights are ordered `h_c < h_b < h_a`, since `a < b < c`. -/
theorem height_order (f : ℤ) (hf : 2 ≤ f) : f < f ^ 2 - 1 ∧ f ^ 2 - 1 < f ^ 2 := by
  constructor <;> nlinarith

end Erdos634.HeightLadder

#print axioms Erdos634.HeightLadder.height_eq_twice_area
#print axioms Erdos634.HeightLadder.chord_width
#print axioms Erdos634.HeightLadder.width_at_rung_real
#print axioms Erdos634.HeightLadder.run_cannot_climb
#print axioms Erdos634.HeightLadder.height_order
