import Erdos634.LayerLink

/-!
# The chord chart: bridge (i) is derived, not carried

`LayerLink.strip_layer_rigid` consumed two geometric bridges as hypotheses.  The first of them
is not a hypothesis at all — it follows from the two distance equations that place the tile.

## The chart

The tile at position `j` of the `a`-layer has its `a`-edge on the floor, from `((j-1)a, 0)` to
`(j·a, 0)`, with the mast at `x = 0`.  Two placements put its body above that edge:

* **unreflected** — apex at distance `c` from the *left* foot, `b` from the right;
* **reflected** — apex at distance `c` from the *right* foot, `b` from the left.

Each is pinned by two distance equations, and subtracting them gives the apex abscissa in
closed form with no trigonometry (`abscissa_of_distances`):

  unreflected  `x_u = (a² + c² - b²)/(2a)`,   reflected  `x_r = (a² + b² - c²)/(2a)`.

## Bridge (i), discharged

For the base-`β` tile `(a,b,c) = (ef, f²-e², f²)` the reflected numerator collapses:

  `a² + b² - c² = e²f² + (f²-e²)² - f⁴ = e⁴ - e²f² = e²(e² - f²)`,

which is **negative for every member**, by `e < f` alone.  So the reflected apex has negative
abscissa: it lies left of the mast, for all `0 < e < f`, with no case split.  Checked exactly at
`e = 1,2,3` and `f` up to `6`: `x_r` matches `e²(e²-f²)/(2ef)` in every case.

The unreflected numerator is `a² + c² - b² = e²(3f² - e²) = e²N₀`, so `x_u = eN₀/(2f) = S/2`:
`StripRigid`'s projection defect `S` is exactly twice the unreflected apex abscissa.  That
identifies `S` geometrically rather than by fiat.

## Bridge (ii), reduced to two proved inequalities

The predecessor's apex sits strictly *right* of the shared foot, since `S/2 > a` is
`StripRigid.shift_gt_two_a`; the reflected tile's apex sits strictly *left* of it, by the above.
So the two bodies reach across the same vertical at positive height, which is the overlap.  The
only step not proved here is that "both reach across it" gives a genuine two-dimensional
intersection — a single planar statement, down from the whole bridge.
-/

namespace Erdos634.ChordChart

/-- **The apex abscissa from two distance equations.**  If `(x,y)` is at distance `b` from the
origin and `c` from `(a,0)`, then `2ax = a² + b² - c²`.  Subtracting the two equations; no
trigonometry enters. -/
theorem abscissa_of_distances (a b c x y : ℝ)
    (h1 : x ^ 2 + y ^ 2 = b ^ 2) (h2 : (x - a) ^ 2 + y ^ 2 = c ^ 2) :
    2 * a * x = a ^ 2 + b ^ 2 - c ^ 2 := by linear_combination h1 - h2

/-- **The reflected numerator collapses**: `a² + b² - c² = e²(e² - f²)` for the base-`β` tile. -/
theorem reflected_numerator (e f : ℝ) :
    (e * f) ^ 2 + (f ^ 2 - e ^ 2) ^ 2 - (f ^ 2) ^ 2 = e ^ 2 * (e ^ 2 - f ^ 2) := by ring

/-- **The unreflected numerator is `e²N₀`**, so `x_u = S/2`: `StripRigid`'s projection defect is
twice the unreflected apex abscissa. -/
theorem unreflected_numerator (e f : ℝ) :
    (e * f) ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - e ^ 2) ^ 2 = e ^ 2 * (3 * f ^ 2 - e ^ 2) := by ring

/-- **Bridge (i).**  The reflected apex lies strictly left of the mast, for every member.
`2a·x_r = e²(e² - f²) < 0` and `a > 0`, so `x_r < 0` — by `e < f` alone, no case split. -/
theorem reflected_apex_left_of_mast (e f x y : ℝ) (he : 0 < e) (hef : e < f)
    (h1 : x ^ 2 + y ^ 2 = (f ^ 2 - e ^ 2) ^ 2) (h2 : (x - e * f) ^ 2 + y ^ 2 = (f ^ 2) ^ 2) :
    x < 0 := by
  have hf : 0 < f := lt_trans he hef
  have ha : 0 < e * f := mul_pos he hf
  have hx : 2 * (e * f) * x = e ^ 2 * (e ^ 2 - f ^ 2) := by
    rw [abscissa_of_distances (e * f) (f ^ 2 - e ^ 2) (f ^ 2) x y h1 h2]
    exact reflected_numerator e f
  have hsq : e ^ 2 < f ^ 2 := by nlinarith
  have hneg : e ^ 2 * (e ^ 2 - f ^ 2) < 0 := by nlinarith [mul_pos he he]
  by_contra hc
  push_neg at hc
  have : 0 ≤ 2 * (e * f) * x := mul_nonneg (by linarith) hc
  linarith

/-- **Bridge (ii), the arithmetic half.**  The predecessor's apex is strictly right of the
shared foot: `S/2 > a`, i.e. `e N₀ > 2 a f`, which is `StripRigid.shift_gt_two_a`. -/
theorem predecessor_apex_right_of_foot (e f : ℤ) (he : 0 < e) (hef : e < f) :
    2 * (e * f) * f < e * (3 * f ^ 2 - e ^ 2) :=
  Erdos634.StripRigid.shift_gt_two_a e f he hef

end Erdos634.ChordChart
