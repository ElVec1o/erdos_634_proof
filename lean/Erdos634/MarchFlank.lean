import Erdos634.TilePlacement
import Erdos634.AngleSumDissection

/-!
# The two corners flanking an `a`-edge are the `β`- and `γ`-corners

The clause obligation (i) still needs on a boundary run: a tile laying its `a`-edge on the line
presents `β` at one end and `γ` at the other, never `α`.  The reason is that `α` is the angle
*opposite* `a`, so the `α`-corner is the apex and is not on the line at all; the two corners on the
line are those opposite `b` and `c`, which carry `β` and `γ`.

Formally the ordering does it: the angles of a triangle are ordered as their opposite sides
(`TilePlacement.angleAt_lt`), so with `a < b < c` the angle opposite `a` is strictly smallest.  A
corner *on* the `a`-edge is one of the other two, hence carries one of the two larger angles.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchFlank

open Erdos634.Geometry Erdos634.TilePlacement

/-- **The angles are ordered as their opposite sides.**  With the full chain
`sideOpp j < sideOpp (j+1) < sideOpp (j+2)` — for our tile, `a < b < c` — the angles chain the same
way, so the angle opposite the shortest side is strictly the smallest of the three. -/
theorem apex_angle_smallest (T : Tri) (j : Fin 3)
    (h1 : sideOpp T j < sideOpp T (j + 1)) (h2 : sideOpp T (j + 1) < sideOpp T (j + 2)) :
    angleAt T j < angleAt T (j + 1) ∧ angleAt T (j + 1) < angleAt T (j + 2) := by
  refine ⟨angleAt_lt T j h1, ?_⟩
  have hsh : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have h := angleAt_lt T (j + 1) (by rw [hsh]; exact h2)
  rwa [hsh] at h

/-- Neither endpoint of side `j` is the vertex `j`. -/
theorem endpoints_ne_apex : ∀ j : Fin 3, j + 1 ≠ j ∧ j + 2 ≠ j := by decide

/-- **The dichotomy, in the form `junction_cases` consumes.**  If the tile's three angles are
`{α, β, γ}` with `α` strictly smallest, and a corner of the tile carries an angle that is *not*
`α`, then it carries `β` or `γ`. -/
theorem beta_or_gamma {α β γ θ : ℝ} (hmem : θ = α ∨ θ = β ∨ θ = γ) (hne : θ ≠ α) :
    θ = β ∨ θ = γ := by
  rcases hmem with h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr h

/-- **Assembled**: a corner at an endpoint of the shortest side carries an angle strictly greater
than the apex angle, hence different from it, hence `β` or `γ`. -/
theorem flank_is_beta_or_gamma (T : Tri) (j : Fin 3) {α β γ : ℝ}
    (h1 : sideOpp T j < sideOpp T (j + 1)) (h2 : sideOpp T (j + 1) < sideOpp T (j + 2))
    (hapex : angleAt T j = α)
    (hmem1 : angleAt T (j + 1) = α ∨ angleAt T (j + 1) = β ∨ angleAt T (j + 1) = γ)
    (hmem2 : angleAt T (j + 2) = α ∨ angleAt T (j + 2) = β ∨ angleAt T (j + 2) = γ) :
    (angleAt T (j + 1) = β ∨ angleAt T (j + 1) = γ)
      ∧ (angleAt T (j + 2) = β ∨ angleAt T (j + 2) = γ) := by
  obtain ⟨o1, o2⟩ := apex_angle_smallest T j h1 h2
  refine ⟨beta_or_gamma hmem1 ?_, beta_or_gamma hmem2 ?_⟩
  · rw [← hapex]; exact ne_of_gt o1
  · rw [← hapex]; exact ne_of_gt (lt_trans o1 o2)

/-! ## The dichotomy as a statement about a *placed* tile

`flank_is_beta_or_gamma` speaks of `angleAt`, the tile's own corner angle.  What
`MarchRun.junction_cases` consumes is `localAngle` — what a tile of a dissection *presents* at a
point.  `Tri.localAngle_vertex` closes that seam: at its own vertex a tile's local angle is its
corner angle.  So the dichotomy transfers verbatim to a placed tile sitting at a junction. -/

/-- **What a placed tile presents at an endpoint of its `a`-edge.**  If the tile's `j`-th side is
strictly its shortest and the angles are `α, β, γ` with `angleAt T j = α`, then at either endpoint
of that side the tile presents `β` or `γ`. -/
theorem presents_beta_or_gamma (T : Tri) (j : Fin 3) {α β γ : ℝ}
    (h1 : sideOpp T j < sideOpp T (j + 1)) (h2 : sideOpp T (j + 1) < sideOpp T (j + 2))
    (hapex : angleAt T j = α)
    (hmem1 : angleAt T (j + 1) = α ∨ angleAt T (j + 1) = β ∨ angleAt T (j + 1) = γ)
    (hmem2 : angleAt T (j + 2) = α ∨ angleAt T (j + 2) = β ∨ angleAt T (j + 2) = γ) :
    (T.localAngle (T.pts (j + 1)) = β ∨ T.localAngle (T.pts (j + 1)) = γ)
      ∧ (T.localAngle (T.pts (j + 2)) = β ∨ T.localAngle (T.pts (j + 2)) = γ) := by
  obtain ⟨g1, g2⟩ := flank_is_beta_or_gamma T j h1 h2 hapex hmem1 hmem2
  constructor
  · rw [Erdos634.Geometry.Tri.localAngle_vertex]
    simpa [angleAt] using g1
  · rw [Erdos634.Geometry.Tri.localAngle_vertex]
    simpa [angleAt] using g2

end Erdos634.MarchFlank
