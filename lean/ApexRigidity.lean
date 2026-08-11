-- ApexRigidity.lean — the exact geometry of the apex, and the bound on the side parameter it forces.
--
-- NEW (2026-08-11). The apex of a base-β target is completely rigid, and the rigidity is an identity
-- of the whole family rather than a coincidence at one member.
--
-- Set-up. The target is `(f³, f³, e(3f²−e²))` with apex angle `3α`, tile `(a,b,c) = (ef, f²−e², f²)`,
-- and `sin(α/2) = e/(2f)`. An equal side is partitioned into whole tile edges, carries no `b`-edge,
-- and its edge at the apex is a `c`, so the first junction `J` sits at distance `c = f²` from the
-- apex. Write `C` for the chord through `J` parallel to the base; it cuts off a triangle similar to
-- the target with ratio `1/f`, of area `N/f²` tile areas.
--
-- The apex figure is `3α`, so three tiles `T₁, T₂, T₃` meet there, each presenting `α`, whose edges at
-- the apex are `b` and `c`. The outer two lay their `c` along the equal sides. `T₁`'s other apex edge
-- is its `b`, ending at a point `P`.
--
-- THE RIGIDITY. `P` lies exactly on `C`:  `b·cos(α/2) = c·cos(3α/2)`, an identity in `(e,f)`
-- (`apex_drop_eq`). Hence `T₁`'s third edge `JP` lies *along* `C`, and its length is exactly `a`
-- (`apex_edge_eq`). The middle tile `T₂` has exactly the fraction `b/c` of its area above `C`
-- (`middle_fraction`), and `2 + b/c = N/f²` (`area_above_chord`) — so the region above `C` is filled
-- exactly by `T₁`, `T₃` and that fraction of `T₂`, with no room for any other tile.
--
-- THE CONSEQUENCE. At `P` the tiles `T₁` and `T₂` both present `γ`, and `2γ = π + α`
-- (`two_gamma`), leaving `π − α < π`: no tile can have `P` interior to an edge, so every tile at `P`
-- has a vertex there. The tile below `T₁`'s `a`-edge therefore lays an edge from `P` towards `J`, of
-- length at most `a` since `J` is on the boundary — hence exactly `a`, PROVIDED `a` is the shortest
-- side, which is `a < b`, i.e. `e² + ef < f²` (`shortest_side`). That tile is therefore not an
-- `α`-tile (α's flanks are `b` and `c`), which forces the tile against the descending side to present
-- `α`, so the side edge below `J` is `b` or `c`, hence `c`.
--
-- So the two edges of an equal side nearest the apex are both `c`, giving `n_c ≥ 2` and, since
-- `n_c = f − pe`, the bound `pe ≤ f − 2` (`side_p_bound`).
--
-- SCOPE, stated honestly. This bound kills `p = 2` whenever `e² + ef < f²`, in particular on the whole
-- tight subfamily `f = 2e+1` (`p_le_one_of_tight`) — a second, independent proof of `thm:ptwodead`.
-- It does NOT kill `p = 1` anywhere new: that would need `e ≥ f − 1`, which together with
-- `e² + ef < f²` forces `f ≤ 2` (`scope_limitation`), i.e. only the member `(1,2)`, already closed.
--
-- SCOPE, part two. The geometry — that the apex carries three tiles, that the side edge at the apex
-- is a `c`, that the side carries no `b`-edge, and the angular bookkeeping at `J` — is NOT proved
-- here; it lives in `BaseBetaCorners.lean`, `SideNoB.lean` and the companion. What is proved here is
-- the exact trigonometric rigidity, which is what was missing, plus the arithmetic it forces.

import Mathlib.Tactic

namespace Erdos634.ApexRigidity

/-! ## The rigidity identities

With `sin(α/2) = e/(2f)` one gets `cos(α/2) = √(4f²−e²)/(2f)`, and then

  `cos(3α/2) = √(4f²−e²)(f²−e²)/(2f³)`,   `sin(3α/2) = e(3f²−e²)/(2f³)`.

Everything below is stated directly in those closed forms, so no trigonometry is needed. -/

/-- **The apex rigidity.**  The drop from the apex to `P` (along the tile's `b`-edge) equals the drop
from the apex to the first junction `J` (along its `c`-edge).  So `P` lies on the chord through `J`.

This is an identity in `(e,f)`, not a numerical coincidence: both sides equal
`(f²−e²)√(4f²−e²)/(2f)`. -/
theorem apex_drop_eq (e f : ℝ) (hf : f ≠ 0) :
    (f ^ 2 - e ^ 2) * (Real.sqrt (4 * f ^ 2 - e ^ 2) / (2 * f))
      = f ^ 2 * (Real.sqrt (4 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) / (2 * f ^ 3)) := by
  field_simp

/-- **The edge on the chord has length exactly `a`.**  The horizontal offsets of `J` and `P` from the
apex differ by exactly `a = ef`, so `T₁`'s third edge lies along the chord and is its `a`-edge. -/
theorem apex_edge_eq (e f : ℝ) (hf : f ≠ 0) :
    f ^ 2 * (e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3)) - (f ^ 2 - e ^ 2) * (e / (2 * f)) = e * f := by
  field_simp
  ring

/-- **The middle apex tile.**  `T₂`'s far vertex sits at drop `c·cos(α/2)`, while the chord is at
drop `c·cos(3α/2)`; the ratio is `b/c`, so exactly that fraction of `T₂` lies above the chord. -/
theorem middle_fraction (e f : ℝ) (hf : f ≠ 0) :
    (f ^ 2 * (Real.sqrt (4 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) / (2 * f ^ 3))) * f ^ 2
      = (f ^ 2 - e ^ 2) * (f ^ 2 * (Real.sqrt (4 * f ^ 2 - e ^ 2) / (2 * f))) := by
  field_simp

/-- **The region above the chord is exactly accounted for.**  Two whole tiles plus the fraction `b/c`
of the third equals `N/f²`, the area above the chord in tile units.  Hence no further tile has any
area above the chord, and the chord is met from above by exactly three tiles. -/
theorem area_above_chord (e f : ℝ) (hf : f ≠ 0) :
    2 + (f ^ 2 - e ^ 2) / f ^ 2 = (3 * f ^ 2 - e ^ 2) / f ^ 2 := by
  field_simp
  ring

/-- **`2γ = π + α`.**  With `γ = 2α + β` and `3α + 2β = π`.  Consequently the angle left at `P` after
`T₁` and `T₂` is `π − α`, which is strictly less than `π`: no tile can present a straight angle there,
so `P` is a genuine vertex of every tile meeting it. -/
theorem two_gamma (α β γ : ℝ) (hsum : 3 * α + 2 * β = Real.pi) (hγ : γ = 2 * α + β) :
    2 * γ = Real.pi + α := by
  rw [hγ]; linarith

/-- The angle left at `P` is `π − α`, and it is less than `π` exactly when `α > 0`. -/
theorem residual_lt_pi (α : ℝ) (hα : 0 < α) : Real.pi - α < Real.pi := by linarith

/-! ## The arithmetic the rigidity forces -/

/-- **`a` is the shortest side exactly when `e² + ef < f²`.**  `c = f²` always exceeds `a = ef` for
`e < f`; the binding comparison is `a < b`.  Numerically this says `f/e` exceeds the golden ratio. -/
theorem shortest_side {e f : ℕ} (h : e ^ 2 + e * f < f ^ 2) :
    e * f < f ^ 2 - e ^ 2 ∧ e * f < f ^ 2 := ⟨by omega, by omega⟩

/-- **The bound on the side parameter.**  The two edges of an equal side nearest the apex are both
`c`, so `n_c ≥ 2`; with `n_c = f − pe` this is `pe + 2 ≤ f`. -/
theorem side_p_bound {p e f n : ℕ} (hn : n + p * e = f) (h2 : 2 ≤ n) : p * e + 2 ≤ f := by omega

/-- **`p = 2` is impossible on the tight subfamily `f = 2e+1`.**  There `pe + 2 ≤ f` reads
`pe ≤ 2e − 1`, which fails for `p ≥ 2`.  This is a second, independent proof of `thm:ptwodead`. -/
theorem p_le_one_of_tight {p e : ℕ} (h : p * e + 2 ≤ 2 * e + 1) : p ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  have : 2 * e ≤ p * e := Nat.mul_le_mul_right e hcon
  omega

/-- **The honest scope limit.**  Killing `p = 1` by this bound would need `e ≥ f − 1`; together with
the hypothesis `e² + ef < f²` that forces `f ≤ 2`, i.e. only the member `(1,2)`, which is already
closed.  So the apex bound cannot reach `p = 1` at any new member. -/
theorem scope_limitation {e f : ℕ} (hef : e < f) (h : e ^ 2 + e * f < f ^ 2) (hp : f ≤ e + 1) :
    f ≤ 2 := by
  have hfe : f = e + 1 := by omega
  subst hfe
  nlinarith


/-! ## The two sides cannot both be mirrored

If both equal sides carry `{3α,2β}` at their last junctions, both mirror partners have the reflection
of the apex as a vertex, and the middle apex tile's far vertex falls strictly inside one of them. The
containment is decided by three cross products; the first two are positive whenever `e < f`, and the
third factors as `(e²−ef−f²)(e²+ef−f²)`, whose first factor is always negative and whose second is
negative exactly under the standing hypothesis `e² + ef < f²`. -/

/-- The first factor of the third cross product is always negative. -/
theorem quad_neg_always {e f : ℝ} (he : 0 < e) (hef : e < f) :
    e ^ 2 - e * f - f ^ 2 < 0 := by nlinarith

/-- **The three cross products are simultaneously positive exactly under `e² + ef < f²`.**  So the
middle apex tile's far vertex lies strictly inside the mirror partner, and the two interiors meet. -/
theorem overlap_signs {e f : ℝ} (he : 0 < e) (hf : 0 < f) (hef : e < f)
    (hgold : e ^ 2 + e * f < f ^ 2) (r : ℝ) (hr : 0 < r) :
    0 < e ^ 3 * r / 2
  ∧ 0 < e ^ 3 * r * (f - e) * (f + e) / (2 * f ^ 2)
  ∧ 0 < e * r * (e ^ 2 - e * f - f ^ 2) * (e ^ 2 + e * f - f ^ 2) / (2 * f ^ 2) := by
  have h1 : e ^ 2 - e * f - f ^ 2 < 0 := quad_neg_always he hef
  have h2 : e ^ 2 + e * f - f ^ 2 < 0 := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · have : 0 < f - e := by linarith
    positivity
  · have her : 0 < e * r := mul_pos he hr
    have hneg : e * r * (e ^ 2 - e * f - f ^ 2) < 0 := mul_neg_of_pos_of_neg her h1
    exact div_pos (mul_pos_of_neg_of_neg hneg h2) (by positivity)

end Erdos634.ApexRigidity
