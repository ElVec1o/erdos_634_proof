import Mathlib.Tactic

/-!
# The base-β target splits as a scaled tile plus a cevian target

Erdős #634 — the construction (sufficiency) side.

The seed-degeneracy theorem says every certified seed complex closes only on `f = 2e`, and with
`gcd(e,f) = 1` that happens **only** at `(e,f) = (1,2)` — which is exactly why nothing transferred.
So instead of a seed complex, read the skeleton off the certificate itself.

Scanning the Lean-certified 44-tiling for every line that no tile crosses returns **eight**: the
three sides of the target, and five interior lines cutting off `1, 1, 4, 9, 16` tiles.  The one
cutting off `16` is an apex cevian, and it splits the tiling `28 | 16` with **zero tiles crossed**.

**CORRECTED 2026-08-24.**  This paragraph read "returns just six … two tiny lines cutting off a
single tile each, and **one** interior line".  Re-running the scan in exact `ℤ[√15]` over all
lines through two of the tiling's 38 vertices gives eight, not six: the two lines cutting off `4`
and `9` tiles were missed.  Splits verified — `43+1`, `43+1`, `40+4`, `35+9`, `28+16`, each
summing to `44`.  The cevian claim itself is unaffected; the count was wrong.
Reproducible: `code/analysis/uncrossed_lines.py lean/Erdos634/Tiling44.lean 15`.

Running the same scan on all four certified **triangle** tilings gives, for the interior
uncrossed lines, the smaller-side counts

```
  28-tiling:  1, 4, 9
  44-tiling:  1, 1, 4, 9, 16
  77-tiling:  1, 4, 9, 16, 29
  99-tiling:  1, 1, 4, 4, 25
```

Seventeen of the eighteen are perfect squares.  The exception is the 77-tiling's `48 | 29` line:
**neither side is a square**, and the refinement "the *triangle* side is a square" fails on it too,
that side holding `48` tiles.  So *"an uncrossed interior line cuts off a perfect square"* is a
regularity and **not a theorem** — falsified on certificates not used to form it.

The `48`-piece is a triangle tiled by 48 congruent copies, similar to neither the tile (`√48` is
not an integer) nor the target (`48/77` is not a square ratio); nothing forces a square there.

Also worth recording: the apex cevian is uncrossed in the 44-tiling but **crossed** in the
99-tiling, whose apex cevian would cut `36 | 63`.  No particular line is guaranteed uncrossed at
`m ≥ 2`.

Both numbers are structural.  Writing `N₀ = 3f² - e²` for the base-β count, the target at
multiplier `m` has sides `(f³m, f³m, e·m·N₀)`.  Drop the cevian from the apex to the base point at
distance `e·f²·m` from a base corner.  It has length `f·b·m`, and it cuts the target into

* the triangle `(e f² m, f b m, f³ m)` — **similar to the tile**, at scale `f m`, hence tiled by
  `(f m)²` copies by the standard subdivision; and
* the triangle `(e m (2f² - e²), f b m, f³ m)` — the **cevian target** of `thm:63`, whose family
  count is `m² (2f² - e²)`.

The counts add exactly, `split_count`: `f² + (2f² - e²) = 3f² - e²`.  At `(1,2,2)` that is
`16 + 28 = 44`, and at `(1,2,3)` it is `36 + 63 = 99` — the two certified cevian tilings
(`CevianTiling28`, `CevianTiling63`) are precisely the complements of the scaled tiles.

**Consequence.**  A cevian tiling at `(e,f,m)` yields a base-β tiling at `(e,f,m)`, because the
other piece is a scaled tile and is always tileable.  So the open seed question for the base-β
family transfers to the cevian family, whose targets are strictly smaller
(`m²(2f² - e²) < m²(3f² - e²)`).

Axiom-clean.  The geometric input is the angle bookkeeping of the cevian, recorded in the
docstrings; everything numeric is proved here.
-/

namespace Erdos634.CevianSplit

/-- **The split identity.**  The scaled tile contributes `f²` and the cevian target `2f² - e²`,
and they sum to the base-β count `N₀ = 3f² - e²`. -/
theorem split_count (e f : ℤ) : f ^ 2 + (2 * f ^ 2 - e ^ 2) = 3 * f ^ 2 - e ^ 2 := by ring

/-- At multiplier `m` the same identity, in tile counts: `(f m)² + m² (2f² - e²) = m² N₀`. -/
theorem split_count_m (e f m : ℤ) :
    (f * m) ^ 2 + m ^ 2 * (2 * f ^ 2 - e ^ 2) = m ^ 2 * (3 * f ^ 2 - e ^ 2) := by ring

/-- **The cevian foot.**  The base of the target has length `e m N₀`; the cevian foot sits at
distance `e f² m` from a base corner, leaving `e m (2f² - e²)` — exactly the cevian target's base
at the same `(e,f,m)`. -/
theorem cevian_foot (e f m : ℤ) :
    e * m * (3 * f ^ 2 - e ^ 2) - e * f ^ 2 * m = e * m * (2 * f ^ 2 - e ^ 2) := by ring

/-- **The scaled piece is the tile at scale `f m`.**  Its sides `(e f² m, f b m, f³ m)` are
`f m · (a, b, c)` for the tile `(a,b,c) = (ef, f² - e², f²)`. -/
theorem scaled_piece_sides (e f m : ℤ) :
    (f * m) * (e * f) = e * f ^ 2 * m
      ∧ (f * m) * (f ^ 2 - e ^ 2) = f * (f ^ 2 - e ^ 2) * m
      ∧ (f * m) * f ^ 2 = f ^ 3 * m := by
  refine ⟨by ring, by ring, by ring⟩

/-- The scaled piece therefore carries `(f m)²` tiles, by the standard subdivision of a triangle
similar to the tile. -/
theorem scaled_piece_count (f m : ℤ) : (f * m) ^ 2 = f ^ 2 * m ^ 2 := by ring

/-- **`(1,2,2)`: the certified 44-tiling is this split.**  `16 + 28 = 44`, and the engine's scan of
that certificate finds the cevian respected with zero tiles crossed. -/
theorem split_44 : (2 * 2 : ℤ) ^ 2 + 2 ^ 2 * (2 * 2 ^ 2 - 1 ^ 2) = 44 := by norm_num

/-- **`(1,2,3)`: `36 + 63 = 99`.**  Here the *certified* 99-tiling does not respect the cevian
(three tiles cross it), but the dissection is still valid — `CevianTiling63` supplies the second
piece, so a 99-tiling of this shape exists independently of the certified one. -/
theorem split_99 : (2 * 3 : ℤ) ^ 2 + 3 ^ 2 * (2 * 2 ^ 2 - 1 ^ 2) = 99 := by norm_num

/-- **The transfer.**  Whenever the cevian target at `(e,f,m)` is tileable, so is the base-β target:
the complementary piece is a scaled tile and always is.  In counts, `m²(2f² - e²)` realizable
forces `m²(3f² - e²)` realizable, the difference being the standard subdivision's `(f m)²`. -/
theorem transfer (e f m X : ℤ) (h : X = m ^ 2 * (2 * f ^ 2 - e ^ 2)) :
    X + (f * m) ^ 2 = m ^ 2 * (3 * f ^ 2 - e ^ 2) := by subst h; ring

/-- The cevian target is strictly smaller than the base-β target it feeds, for every member:
`2f² - e² < 3f² - e²` since `f ≠ 0`. -/
theorem cevian_smaller (e f : ℤ) (hf : 0 < f) :
    2 * f ^ 2 - e ^ 2 < 3 * f ^ 2 - e ^ 2 := by nlinarith

end Erdos634.CevianSplit

#print axioms Erdos634.CevianSplit.split_count
#print axioms Erdos634.CevianSplit.split_count_m
#print axioms Erdos634.CevianSplit.cevian_foot
#print axioms Erdos634.CevianSplit.scaled_piece_sides
#print axioms Erdos634.CevianSplit.transfer
#print axioms Erdos634.CevianSplit.cevian_smaller
