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

end Erdos634.VertexFigureReal
