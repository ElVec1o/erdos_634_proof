import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# `N = 2` is impossible for a `3α + 2β = π` tile — gap (a) of `prop:b3prime`

Erdős #634, 2026-09-09.

## The gap this closes

`FourCompCongruence.fourcomp_no_odd_prime` (with `FCStep1`/`FCStep2`) reconstructs the arithmetic
core of Beeson III Theorem 12 for the `(2α, α, 2β)` target **without** Theorem 11, and concludes
`N = 2`.  Theorem 12 concludes "`N` is not prime", and `2` **is** prime, so that chain does not
prove Theorem 12.  `lean/PAPER_MAP.md` records this as gap (a):

> Thm 12 concludes "`N` is not prime"; this chain concludes `N = 2`, **and 2 is prime** —
> excluding `N = 2` is stated NOWHERE in the corpus.

This file excludes `N = 2` by a **separate, direct argument that touches no part of the broken
Theorem 11/12 route** and uses no arithmetic of `e, f, M, K` at all.  It is an angle argument.

## The argument

Let `T` be a triangle dissected into exactly `2` triangles congruent to a tile with angles
`(α, β, γ)`.

1. *(geometric interface, `TwoPieceCut` below)*  Two triangles with disjoint interiors whose union
   is a triangle meet along a **cevian**: a segment from a vertex of `T` to a point `D` in the
   **open** interior of the opposite side.  (Both endpoints on side-interiors would leave a
   quadrilateral piece; both at vertices is an edge of `T`, not a cut.)  At `D` the two pieces
   contribute angles `θ` and `π − θ` with `0 < θ < π`, and each is an angle of the tile.

2. `angles_at_interior_point_force_right`: if `θ` and `π − θ` are both among the tile's three
   angles, then `θ = π/2`.  Indeed if `θ ≠ π/2` they are *distinct* tile angles summing to `π`,
   so the remaining tile angle is `0` — impossible.  Hence **the tile has a right angle**.

3. `three_alpha_two_beta_no_right_angle`: a tile with `3α + 2β = π` and `α, β > 0` has angles
   `(α, β, 2α+β)` and **none of them is `π/2`**.  `α = π/2` forces `3α > π`; `β = π/2` forces
   `α = 0`; `2α + β = π/2` together with `3α + 2β = π` forces `α = 0`.

Steps 2 and 3 contradict, so `N ≠ 2`.  Note step 3 is *sharp and unconditional* on the branch: it
does not use the target shape, so the exclusion covers all five `3α + 2β` target shapes, not only
`(2α, α, 2β)`.

## Scope, stated honestly

Steps 2 and 3 are formalized here, zero axioms beyond the standard three, no `sorry`.  **Step 1 —
that a 2-piece triangle dissection is a cevian cut — is NOT formalized**; it is supplied as the
structure `TwoPieceCut`, which is the interface a real `CongruentDissection` with `N = 2` would
have to provide.  It is elementary plane topology (blockers 1/2 of `PAPER_MAP.md`, the
tile-placement layer), and it is exhibited **non-vacuously** below: `rightIsoscelesCut` is a
genuine inhabitant of `TwoPieceCut` (the isosceles right triangle split by its altitude), so
`no_two_tile_dissection` is not a `False → False`.

Even so, this is *not* a proof of Beeson III Theorem 12: gap (b) of `prop:b3prime` (that
`N · R² = M² · A · B` holds for a real dissection) is untouched.  What this file does is close
gap (a) — the `N = 2` hole — outright, modulo the same tile-placement layer every other geometric
statement in the corpus is modulo.
-/

namespace Erdos634.FCTwoTiles

open Real

/-! ## Step 3: a `3α + 2β = π` tile has no right angle -/

/-- The third angle of a `3α + 2β = π` tile is `2α + β`. -/
theorem third_angle {α β : ℝ} (h : 3 * α + 2 * β = π) : α + β + (2 * α + β) = π := by
  linarith

/-- **No `3α + 2β = π` tile has a right angle.**  Unconditional on the target shape. -/
theorem three_alpha_two_beta_no_right_angle {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (h : 3 * α + 2 * β = π) :
    α ≠ π / 2 ∧ β ≠ π / 2 ∧ 2 * α + β ≠ π / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro hc <;> linarith

/-! ## Step 2: an interior cut point forces a right angle in the tile -/

/-- If `θ` and `π - θ` are both angles of a triangle with angles `a₁, a₂, a₃`, all positive and
summing to `π`, then `θ = π/2`.  (The two must be the *same* angle, and an angle equal to its own
supplement is right.) -/
theorem angles_at_interior_point_force_right {a₁ a₂ a₃ θ : ℝ}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) (h₃ : 0 < a₃) (hsum : a₁ + a₂ + a₃ = π)
    (hθ : θ = a₁ ∨ θ = a₂ ∨ θ = a₃) (hsupp : π - θ = a₁ ∨ π - θ = a₂ ∨ π - θ = a₃) :
    θ = π / 2 := by
  rcases hθ with rfl | rfl | rfl <;> rcases hsupp with h | h | h <;> linarith

/-! ## The geometric interface, and the exclusion -/

/-- The data a 2-piece dissection of a triangle by a tile with angles `(a₁, a₂, a₃)` supplies.

`θ` is the angle one piece makes at the cut point `D`, which lies in the **open** interior of a
side of the target, so the other piece makes `π - θ` there; both are angles of the tile.

This is the interface, not a theorem: deriving it from a `CongruentDissection` with `N = 2` is
the (unformalized) plane-topology step 1.  It is inhabited — see `rightIsoscelesCut`. -/
structure TwoPieceCut (a₁ a₂ a₃ : ℝ) where
  pos₁ : 0 < a₁
  pos₂ : 0 < a₂
  pos₃ : 0 < a₃
  sum : a₁ + a₂ + a₃ = π
  θ : ℝ
  θ_pos : 0 < θ
  θ_lt : θ < π
  /-- the angle of one piece at the interior cut point is a tile angle -/
  θ_mem : θ = a₁ ∨ θ = a₂ ∨ θ = a₃
  /-- the angle of the other piece there is its supplement, also a tile angle -/
  supp_mem : π - θ = a₁ ∨ π - θ = a₂ ∨ π - θ = a₃

/-- **The interface is not vacuous.**  The isosceles right triangle `(π/2, π/4, π/4)` really is
cut into two congruent copies of itself by the altitude from the right angle: `θ = π/2`. -/
noncomputable def rightIsoscelesCut : TwoPieceCut (π / 2) (π / 4) (π / 4) where
  pos₁ := by positivity
  pos₂ := by positivity
  pos₃ := by positivity
  sum := by ring
  θ := π / 2
  θ_pos := by positivity
  θ_lt := by linarith [pi_pos]
  θ_mem := Or.inl rfl
  supp_mem := Or.inl (by ring)

/-- Any tile admitting a 2-piece dissection has a right angle. -/
theorem TwoPieceCut.right_angle {a₁ a₂ a₃ : ℝ} (c : TwoPieceCut a₁ a₂ a₃) :
    a₁ = π / 2 ∨ a₂ = π / 2 ∨ a₃ = π / 2 := by
  have hθ : c.θ = π / 2 :=
    angles_at_interior_point_force_right c.pos₁ c.pos₂ c.pos₃ c.sum c.θ_mem c.supp_mem
  rcases c.θ_mem with h | h | h
  · exact Or.inl (h ▸ hθ)
  · exact Or.inr (Or.inl (h ▸ hθ))
  · exact Or.inr (Or.inr (h ▸ hθ))

/-- **Gap (a), closed.**  No triangle is dissected into exactly two triangles congruent to a
`3α + 2β = π` tile.  Hence `N = 2` does not occur in this branch, and
`FourCompCongruence.fourcomp_no_odd_prime`'s conclusion `N = 2` is an empty verdict. -/
theorem no_two_tile_dissection {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (h : 3 * α + 2 * β = π)
    (c : TwoPieceCut α β (2 * α + β)) : False := by
  obtain ⟨h1, h2, h3⟩ := three_alpha_two_beta_no_right_angle hα hβ h
  rcases c.right_angle with hc | hc | hc
  exacts [h1 hc, h2 hc, h3 hc]

/-- The statement in the form the chain needs: in the `3α + 2β = π` branch, if a tile count `N`
is realized by a dissection whose 2-piece case would be a `TwoPieceCut`, then `N ≠ 2`. -/
theorem N_ne_two {α β : ℝ} {N : ℕ} (hα : 0 < α) (hβ : 0 < β) (h : 3 * α + 2 * β = π)
    (hN : N = 2 → TwoPieceCut α β (2 * α + β)) : N ≠ 2 := fun hEq =>
  no_two_tile_dissection hα hβ h (hN hEq)

end Erdos634.FCTwoTiles

#print axioms Erdos634.FCTwoTiles.three_alpha_two_beta_no_right_angle
#print axioms Erdos634.FCTwoTiles.angles_at_interior_point_force_right
#print axioms Erdos634.FCTwoTiles.rightIsoscelesCut
#print axioms Erdos634.FCTwoTiles.no_two_tile_dissection
