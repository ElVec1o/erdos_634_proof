import Mathlib
import Erdos634.VertexFigureReal

/-!
# The tile-placement layer

Erdős #634.  Thirty-one PROVED statements across the three papers wait on the same missing object:
a way to say, of a real dissection, that *this tile sits here* — at a corner, laying that edge on
that wall, presenting that angle at that point.  The papers use the language freely; the corpus has
no definitions for it, which is why those statements cannot be formalized as written.

This file starts the layer with the three notions the statements actually use, and proves the first
consumer: at a base corner of a base-`β` target, **exactly one tile has a nonzero angle**, which is
the first clause of `prop:cornerfig` at a real corner.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TilePlacement

open Erdos634.Geometry Finset

/-- Tile `i` has `v` among its vertices. -/
def HasVertex {N : ℕ} (D : Dissection N) (i : Fin N) (v : Plane) : Prop :=
  ∃ j : Fin 3, (D.tile i).pts j = v

/-- Tile `i` presents angle `θ` at the point `v`. -/
def PresentsAt {N : ℕ} (D : Dissection N) (i : Fin N) (v : Plane) (θ : ℝ) : Prop :=
  (D.tile i).localAngle v = θ

/-- Tile `i` lays its `k`-th edge inside the set `S` — the wall, a side, a chord. -/
def LaysOn {N : ℕ} (D : Dissection N) (i : Fin N) (k : Fin 3) (S : Set Plane) : Prop :=
  (D.tile i).edge k ⊆ S

/-- A tile laying an edge on a set has both endpoints there. -/
theorem laysOn_endpoints {N : ℕ} (D : Dissection N) (i : Fin N) (k : Fin 3) (S : Set Plane)
    (h : LaysOn D i k S) :
    (D.tile i).pts k ∈ S ∧ (D.tile i).pts (k + 1) ∈ S := by
  constructor
  · exact h (by rw [Tri.edge]; exact left_mem_segment ℝ _ _)
  · exact h (by rw [Tri.edge]; exact right_mem_segment ℝ _ _)

/-- **The corner figure, with multiplicities.**  At a vertex of the target, the tiles' local angles
sum to that corner's angle, and counting them by value turns the sum into a linear relation. -/
theorem corner_multiplicities {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    (({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card : ℝ) * γ
      + (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card : ℝ)
        * Real.pi
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
  classical
  have hsum := Erdos634.VertexFigureReal.corner_angle_sum D k
  rw [Erdos634.VertexFigureReal.sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ) _ hvals] at hsum
  rw [Finset.sum_insert (by simp [hαβ, hαγ, hαπ, hα0]),
      Finset.sum_insert (by simp [hβγ, hβπ, hβ0]),
      Finset.sum_insert (by simp [hγπ, hγ0]),
      Finset.sum_insert (by simp [hπ0]), Finset.sum_singleton] at hsum
  push_cast at hsum ⊢
  linarith [hsum]

/-- **A base corner is a single `β`-tile.**  With the corner angle `β`, the multiplicities are
`(0,1,0)` and no tile contributes a straight angle: exactly one tile presents `β` there, and every
other tile presents `0`.

This is `prop:cornerfig`'s first clause, at a real corner of a real dissection. -/
theorem base_corner_single_tile {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = β) :
    p = 0 ∧ q = 1 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((-3 * (s : ℤ) : ℤ) : ℝ) * α + ((1 - 2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast
    linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **Exactly one tile at a base corner.**  Combining the count with the multiplicity solution:
the number of tiles presenting `β` there is `1`, and no tile presents `α`, `γ` or a straight
angle. -/
theorem base_corner_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  classical
  have h := corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact base_corner_single_tile hγdef hrel hirr _ _ _ _ h

/-- **Exactly three `α`-tiles at the apex.**  The same count with the corner angle `3α`. -/
theorem apex_counts {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = 3 * α) :
    p = 3 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((3 - 3 * (s : ℤ) : ℤ) : ℝ) * α + ((-2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast; linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## The two edges at a corner

`prop:cornerfig`'s last clause names the *edges* at the base corner.  Given that the side opposite
the corner is `b`, the two incident sides are `a` and `c` in one order or the other — by sum and
product of the side multiset, which pins them as the roots of one quadratic. -/

/-- **The two incident sides.**  If the three sides are `{a, b, c}` and the one opposite the vertex
is `b`, the two at the vertex are `a` and `c`. -/
theorem incident_sides (x y a b c : ℝ) (hb : b ≠ 0)
    (hmul : ({x, y, b} : Multiset ℝ) = {a, b, c}) :
    (x = a ∧ y = c) ∨ (x = c ∧ y = a) := by
  classical
  have hsum : x + y + b = a + b + c := by
    have := congrArg Multiset.sum hmul
    simpa [Multiset.insert_eq_cons, add_assoc] using this
  have hprod : x * y * b = a * b * c := by
    have := congrArg Multiset.prod hmul
    simpa [Multiset.insert_eq_cons, mul_assoc] using this
  have hs : x + y = a + c := by linarith
  have hp : x * y = a * c := by
    have h : (x * y) * b = (a * c) * b := by
      rw [hprod]; ring
    exact mul_right_cancel₀ hb h
  have hroot : (x - a) * (x - c) = 0 := by linear_combination x * hs - hp
  rcases mul_eq_zero.mp hroot with h | h
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

end Erdos634.TilePlacement
