import Mathlib
import Erdos634.PinPlumbing

/-!
# From a real vertex figure to multiplicities

Erdős #634, `prop:vertexfigures`.  The paper's statement is about the angles a tiling actually
presents at a point; its Lean counterpart was the `omega` lemma on multiplicities, which is why the
statement was relabelled PROVED in this week's audit.  This file supplies the missing passage: at a
boundary point of a dissection that is not a target vertex, the tiles' local angles sum to `π`
(`PinPlumbing.pin_angle_sum`), and if each of them is one of `α, β, γ, π, 0`, then counting the
tiles by which value they contribute turns that sum into a linear relation with natural
multiplicities.

That relation is what every arithmetic vertex lemma in the corpus takes as its hypothesis, so this
is the step that lets them speak about tilings.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.VertexFigureReal

open Erdos634.Geometry Finset

/-- **Counting a sum by its values.**  If every term of a finite sum lies in `S`, the sum is the
sum over `S` of each value times the number of terms taking it. -/
theorem sum_by_value {N : ℕ} (S : Finset ℝ) (f : Fin N → ℝ) (h : ∀ i, f i ∈ S) :
    ∑ i, f i = ∑ v ∈ S, (({i | f i = v} : Finset (Fin N)).card : ℝ) * v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun i _ => h i) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const,
    nsmul_eq_mul]

/-- **The vertex figure, with multiplicities.**  At a boundary point that is not a target vertex,
if every tile's local angle is one of `α, β, γ, π, 0`, there are natural multiplicities with
`p·α + q·β + r·γ + s·π = π`.

The five values are assumed distinct, which for a base-`β` tile they are.  `s` counts the tiles
meeting the point in the interior of one of their edges. -/
theorem vertex_multiplicities_real {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    ∃ p q r s : ℕ, (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi := by
  classical
  have hsum := Erdos634.PinPlumbing.pin_angle_sum D hv hnv
  rw [sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ) _ hvals] at hsum
  refine ⟨({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card, ?_⟩
  rw [show ({α, β, γ, Real.pi, 0} : Finset ℝ)
      = insert α (insert β (insert γ (insert Real.pi {0}))) from rfl] at hsum
  rw [Finset.sum_insert (by simp [hαβ, hαγ, hαπ, hα0]),
      Finset.sum_insert (by simp [hβγ, hβπ, hβ0]),
      Finset.sum_insert (by simp [hγπ, hγ0]),
      Finset.sum_insert (by simp [hπ0]), Finset.sum_singleton] at hsum
  push_cast at hsum ⊢
  linarith [hsum]

/-- **The values a tile can contribute.**  At a boundary point that is not a target vertex, a
tile's local angle is one of its corner angles, or `π` (the point is interior to one of its edges),
or `0`.  The remaining case of `localAngle_cases`, a full `2π`, is excluded by
`PinPlumbing.no_interior_tile_at_pin`.

So `hvals` above is not an assumption about the dissection: it follows from the tiles being
congruent to one tile with angles `α, β, γ`. -/
theorem localAngle_mem {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hcorners : ∀ (i : Fin N) (j : Fin 3),
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        ∈ ({α, β, γ} : Finset ℝ))
    (i : Fin N) : (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
  classical
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with ⟨j, _, hval⟩ | h2 | hpi | h0
  · have := hcorners i j
    rw [hval]
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  · exact absurd (Erdos634.PinPlumbing.no_interior_tile_at_pin D hv hnv i h2) (by simp)
  · simp [hpi]
  · simp [h0]

/-! ## The classification, at a real boundary point

With the multiplicities in hand, `Dissection.vertex_multiplicities` converts the angle relation into
the linear equations, and those have two solutions.  So the boundary vertex figure of a real tiling
is classified: either a single tile covering the point with a straight angle, or `{3α, 2β}`, or
`{α, β, γ}`. -/

/-- **The boundary figure, classified.**  From `p·α + q·β + r·γ + s·π = π` with `γ = 2α + β`,
`3α + 2β = π` and `α/π` irrational. -/
theorem boundary_figure {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi) :
    ((p : ℤ) + 2 * r = 3 * (1 - s) ∧ (q : ℤ) + r = 2 * (1 - s)) := by
  have hπ : Real.pi = 3 * α + 2 * β := hrel.symm
  have h : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((3 * (1 - (s : ℤ)) : ℤ) : ℝ) * α + ((2 * (1 - (s : ℤ)) : ℤ) : ℝ) * β := by
    rw [← hγ]
    push_cast
    nlinarith [hsum, hπ]
  exact Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h

/-- **The two boundary figures.**  With no straight-angle contributor the multiplicities are
`(3,2,0)` or `(1,1,1)`; with one, everything else vanishes. -/
theorem boundary_figure_cases {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi) :
    (s = 1 ∧ p = 0 ∧ q = 0 ∧ r = 0) ∨
      (s = 0 ∧ ((p = 3 ∧ q = 2 ∧ r = 0) ∨ (p = 1 ∧ q = 1 ∧ r = 1))) := by
  obtain ⟨h1, h2⟩ := boundary_figure hγ hrel hirr p q r s hsum
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · right; refine ⟨rfl, ?_⟩; omega
  · left
    have hs1 : s = 1 := by omega
    subst hs1
    omega

/-! ## The interior figure

At an interior point the budget is `2π` and a tile may cover the point outright, contributing `2π`.
Otherwise the argument is the same, and `Dissection.vertex_multiplicities` at `t = 2` gives the
four interior figures the paper lists. -/

/-- The values a tile can contribute at an interior point. -/
theorem interior_localAngle_mem {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hcorners : ∀ (i : Fin N) (j : Fin 3),
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        ∈ ({α, β, γ} : Finset ℝ))
    (v : Plane) (i : Fin N) :
    (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ) := by
  classical
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with ⟨j, _, hval⟩ | h2 | hpi | h0
  · have := hcorners i j
    rw [hval]
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  · simp [h2]
  · simp [hpi]
  · simp [h0]

/-- **The interior figure, with multiplicities.** -/
theorem interior_multiplicities_real {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    {v : Plane} (hv : v ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ)) :
    ∃ p q r s u : ℕ,
      (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi + (u : ℝ) * (2 * Real.pi)
        = 2 * Real.pi := by
  classical
  have hsum := Erdos634.PinPlumbing.pin_angle_sum_interior D hv
  rw [sum_by_value ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ) _ hvals] at hsum
  refine ⟨({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = 2 * Real.pi} : Finset (Fin N)).card, ?_⟩
  rw [Finset.sum_insert (by simp [hαβ, hαγ, hαπ, hα2π, hα0]),
      Finset.sum_insert (by simp [hβγ, hβπ, hβ2π, hβ0]),
      Finset.sum_insert (by simp [hγπ, hγ2π, hγ0]),
      Finset.sum_insert (by simp [hπ2π, hπ0]),
      Finset.sum_insert (by simp [h2π0]), Finset.sum_singleton] at hsum
  push_cast at hsum ⊢
  linarith [hsum]

/-- **The four interior figures.**  With no straight-angle and no covering tile, the multiplicities
solve `p + 2r = 6`, `q + r = 4` — the four figures `{6α,4β}`, `{4α,3β,γ}`, `{2α,2β,2γ}`,
`{β,3γ}`. -/
theorem interior_figure_cases {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = 2 * Real.pi) :
    (p = 6 ∧ q = 4 ∧ r = 0) ∨ (p = 4 ∧ q = 3 ∧ r = 1) ∨ (p = 2 ∧ q = 2 ∧ r = 2) ∨
      (p = 0 ∧ q = 1 ∧ r = 3) := by
  have h : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((6 : ℤ) : ℝ) * α + ((4 : ℤ) : ℝ) * β := by
    rw [← hγ]; push_cast; nlinarith [hsum, hrel]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r 6 4 h
  omega

/-! ## The corner figures

At a vertex of the target the tiles' local angles sum to that corner's angle
(`Dissection.sum_localAngle_eq` with `Tri.localAngle_vertex`).  On a base-`β` target the base
corners have angle `β` and the apex `3α`, and the arithmetic lemmas then force the figures. -/

/-- **The corner sum.**  At a target vertex the tiles' local angles sum to the target's angle
there. -/
theorem corner_angle_sum {N : ℕ} (D : Dissection N) (k : Fin 3) :
    ∑ i, (D.tile i).localAngle (D.target.pts k)
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
  rw [D.sum_localAngle_eq (D.target.pts k), D.target.localAngle_vertex k]

/-- **The base corner is a single `β`-tile.**  From `p·α + q·β + r·γ = β` with the tile relation
and irrationality: `(p,q,r) = (0,1,0)`. -/
theorem base_corner_figure {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = β) :
    p = 0 ∧ q = 1 ∧ r = 0 := by
  have h : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((0 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * β := by
    rw [← hγ]; push_cast; linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r 0 1 h
  omega

/-- **The apex is exactly three `α`-tiles.**  From `p·α + q·β + r·γ = 3α`. -/
theorem apex_figure_real {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = 3 * α) :
    p = 3 ∧ q = 0 ∧ r = 0 := by
  have h : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((3 : ℤ) : ℝ) * α + ((0 : ℤ) : ℝ) * β := by
    rw [← hγ]; push_cast; linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r 3 0 h
  omega

end Erdos634.VertexFigureReal
