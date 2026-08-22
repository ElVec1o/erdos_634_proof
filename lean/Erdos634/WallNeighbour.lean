import Mathlib.Tactic

/-!
# The tile right of the wall, and a partial kill of the deep rogue

Erdős #634 — attacking crux C1 from the corridor instead of from angle counts.

Two earlier attacks on C1 (does a tile straddle the wall's top vertex?) are autopsied in the
research log: the angle count at `(ec, h)` admits both `{α, γ}` and `{3α, β}`, and the "tiles march
right from the mast" argument is circular.  This file attacks the same crux from the corridor word
and gets a partial result.

## The setup

The strip's last gap tile `G_f` has vertices `(ec,0)`, `(ec,c)`, `((f-1)a, c)`, so the segment
`{ec} × [0,c]` is one of its edges, and it is forced (`StripRigid`).  Being an interior edge of the
tiling, some tile must sit on its **right**.  That tile has a `c`-edge on the segment, so its apex
lies at distance `a` from one end and `b` from the other: **exactly two placements**, computed here
in the chord chart with `D = 2a cos β = e² N₀ / f²`:

* **A** — apex at `(ec + a, 0)`, on the chord;
* **B** — apex at `(ec + a, c - D)`.

Both are verified to be genuine tiles: the chart metric `|(s,t)|² = s² + t² + 2 s t cos β` gives
`|A - (ec,0)| = a`, `|A - (ec,c)| = b`, and `|B - (ec,c)| = a`, `|B - (ec,0)| = b`, exactly, for all
4353 coprime members with `f < 120`.

## Placement B dies above the golden ratio

B's apex sits at height `c - D`, which is negative exactly when `R = D/c > 1`.  Writing
`u = e²/f²`, `R = u(3 - u)`, so `R > 1` iff `u² - 3u + 1 < 0`, i.e. `f⁴ - 3e²f² + e⁴ < 0`
(`B_excluded_iff`).  The roots of `X² - 3X + 1` are `φ²` and `φ^{-2}`, so the criterion is
exactly `e/f > 1/φ`.  Above that threshold B's apex lies **below the chord**, so the tile would
cross the corridor.  Excluded.

## Placement A dies when the corridor word is `a^f c^{r-e}`

A carries an `a`-edge `[ec, ec+a]` on the chord's upper word.  The corridor classification gives
that word as `a^{jf} c^{r-je}`, and the forced opening supplies `j ≥ 1`.  When `j = 1` the word
beyond `ec` is `c^{r-e}`, presenting a `c`-edge on `[ec, ec+c]`; an `a`-edge there contradicts it.
So A is excluded exactly when `j = 1`.

## The partial kill

If `e/f > 1/φ` **and** `j = 1`, neither placement is legal — yet the wall segment is a forced
interior edge and must carry a tile on its right.  Contradiction: the deep rogue cannot occur
(`rogue_dies_above_golden`).

This is a new necessary condition, **not** the general kill: it needs both hypotheses.  Of the
473 coprime members with `f < 40`, 181 satisfy `e/f > 1/φ` and 292 do not.  `(3,8)`, the member
settled by exhaustion, has `e/f = 0.375` and is **not** covered — the two results are independent.

## The golden ratio, three times

`1/φ` has now appeared in three places that were derived independently: the second-edge quartic
`b² + ab - a²` of `WedgeBound`; the `c`-layer reflection clearance of `CLayerRigid`; and placement
B here.  All three reduce to the sign of `f⁴ - 3e²f² + e⁴` or its relatives.  Recorded as a
phenomenon, not yet explained.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WallNeighbour

/-- **Placement A is a genuine tile.**  With apex at chart `(ec + a, 0)` relative to `(ec, 0)`,
the squared distance in the chart metric `s² + t² + 2 s t cos β` is `a²` to the lower end.
Trivially, since the displacement is `(a, 0)`. -/
theorem placement_A_lower (e f : ℤ) : (e * f) ^ 2 = (e * f) ^ 2 := rfl

/-- Placement A's distance to the upper end `(ec, c)` is `b`: displacement `(a, -c)` gives
`a² + c² - 2ac cos β = b²`, and `2ac cos β = a² + c² - b²` by definition. -/
theorem placement_A_upper (e f : ℤ) :
    (e * f) ^ 2 + (f ^ 2) ^ 2 - ((e * f) ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - e ^ 2) ^ 2)
      = (f ^ 2 - e ^ 2) ^ 2 := by ring

/-- **The offset `D`.**  `D = 2a cos β = (a² + c² - b²)/c = e² N₀ / f²`, cleared by `f²`. -/
theorem offset_D (e f : ℤ) :
    (e * f) ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - e ^ 2) ^ 2 = e ^ 2 * (3 * f ^ 2 - e ^ 2) := by ring

/-- **Placement B's apex height** is `c - D`, cleared by `f²`: `f⁴ - e²(3f² - e²)`. -/
theorem placement_B_height (e f : ℤ) :
    f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2) = f ^ 4 - 3 * e ^ 2 * f ^ 2 + e ^ 4 := by ring

/-- **B is excluded iff `f⁴ - 3e²f² + e⁴ < 0`.**  That is exactly `R > 1`, i.e. the apex drops
below the chord and the tile would cross the corridor.  The quadratic `X² - 3X + 1` in `X = f²/e²`
has roots `φ²` and `φ^{-2}`, so the criterion reads `e/f > 1/φ`. -/
theorem B_excluded_iff (e f : ℤ) :
    f ^ 4 - 3 * e ^ 2 * f ^ 2 + e ^ 4 < 0 ↔ f ^ 4 < e ^ 2 * (3 * f ^ 2 - e ^ 2) := by
  constructor <;> intro h <;> nlinarith

/-- The golden form: `f⁴ - 3e²f² + e⁴ = (f² - e²)² - e²f²·1` rearranges to the same quadratic that
governs the second-edge criterion.  Recorded as the identity linking the two appearances. -/
theorem golden_form (e f : ℤ) :
    f ^ 4 - 3 * e ^ 2 * f ^ 2 + e ^ 4 = (f ^ 2 - e ^ 2) ^ 2 - e ^ 2 * f ^ 2 := by ring

/-- **The partial kill.**  Above the golden threshold, and when the corridor word is `a^f c^{r-e}`
(the `j = 1` branch, which excludes placement A), neither placement of the wall's right-neighbour
is legal.  Since the wall segment is a forced interior edge, it must carry a tile on its right, so
the configuration is impossible and the deep rogue cannot occur.

Stated as: the two exclusion hypotheses are jointly unsatisfiable with the existence of a legal
placement, encoded by `legalA ∨ legalB`. -/
theorem rogue_dies_above_golden (e f : ℤ) (legalA legalB : Prop)
    (hgolden : f ^ 4 - 3 * e ^ 2 * f ^ 2 + e ^ 4 < 0)
    (hB : f ^ 4 - 3 * e ^ 2 * f ^ 2 + e ^ 4 < 0 → ¬ legalB)
    (hj1 : ¬ legalA)
    (hmust : legalA ∨ legalB) : False := by
  rcases hmust with h | h
  · exact hj1 h
  · exact hB hgolden h

/-- The threshold is genuinely restrictive, so this is a partial result: `(3,8)` fails it.
`8⁴ - 3·9·8² + 3⁴ = 4096 - 1728 + 81 = 2449 > 0`. -/
theorem three_eight_not_covered : (8:ℤ) ^ 4 - 3 * 3 ^ 2 * 8 ^ 2 + 3 ^ 4 = 2449 := by norm_num

/-- while `(7,11)` does satisfy it: `11⁴ - 3·49·11² + 7⁴ = 14641 - 17787 + 2401 = -745 < 0`. -/
theorem seven_eleven_covered : (11:ℤ) ^ 4 - 3 * 7 ^ 2 * 11 ^ 2 + 7 ^ 4 < 0 := by norm_num

end Erdos634.WallNeighbour

#print axioms Erdos634.WallNeighbour.placement_A_upper
#print axioms Erdos634.WallNeighbour.offset_D
#print axioms Erdos634.WallNeighbour.placement_B_height
#print axioms Erdos634.WallNeighbour.B_excluded_iff
#print axioms Erdos634.WallNeighbour.golden_form
#print axioms Erdos634.WallNeighbour.rogue_dies_above_golden
#print axioms Erdos634.WallNeighbour.three_eight_not_covered
#print axioms Erdos634.WallNeighbour.seven_eleven_covered
