import Mathlib
import Erdos634.BaseSelection

/-!
# The wall line meets the target exactly in its base

Erdős #634, bridge (c).  `BaseChain.base_chain_consecutive_meet` carries one hypothesis introduced
without proof: that the wall line meets the target only in the base.  This file proves it, from the
barycentric expansion and one strictness — that the target's third vertex is strictly off the wall.

For a target with two vertices on the wall line and the third strictly inside the half-plane, the
value of `g` at a point of the target is `c` reduced by the third barycentric coordinate times the
gap at the third vertex.  It equals `c` exactly when that coordinate vanishes, which is exactly
when the point is on the opposite edge.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WallFace

open Erdos634.Geometry

/-- An affine functional on a triangle is the barycentric average of its vertex values. -/
theorem affine_barycentric (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (y : Plane) :
    g y = (T.basis.coord 0 y) * g (T.pts 0) + (T.basis.coord 1 y) * g (T.pts 1)
        + (T.basis.coord 2 y) * g (T.pts 2) := by
  have h := T.basis.affineCombination_coord_eq_self (k := ℝ) y
  have hw : ∑ i : Fin 3, T.basis.coord i y = 1 := T.basis.sum_coord_apply_eq_one y
  have hm := Finset.map_affineCombination (Finset.univ : Finset (Fin 3)) (⇑T.basis)
    (fun i => T.basis.coord i y) hw g
  rw [h] at hm
  rw [hm, Finset.affineCombination_eq_linear_combination _ _ _ hw, Fin.sum_univ_three]
  rfl

/-- **The wall line meets the target in one edge.**  With vertices `0` and `1` on the wall and
vertex `2` strictly inside, a point of the target where `g = c` has vanishing third barycentric
coordinate, hence lies on edge `0` — the segment from vertex `0` to vertex `1`. -/
theorem face_eq_edge (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (h0 : g (T.pts 0) = c) (h1 : g (T.pts 1) = c) (h2 : g (T.pts 2) < c)
    {y : Plane} (hy : y ∈ T.carrier) (hgy : g y = c) :
    y ∈ T.edge 0 := by
  have hnn : ∀ j, 0 ≤ T.basis.coord j y := by
    have hy' : y ∈ T.carrier := hy
    rw [T.carrier_eq_nonneg_coord] at hy'
    exact hy'
  have hw : T.basis.coord 0 y + T.basis.coord 1 y + T.basis.coord 2 y = 1 := by
    have := T.basis.sum_coord_apply_eq_one (k := ℝ) y
    rwa [Fin.sum_univ_three] at this
  have hbar := affine_barycentric T g y
  rw [h0, h1, hgy] at hbar
  -- `c = c - coord₂ · (c - g(pts 2))`, so the third coordinate vanishes
  have hz : T.basis.coord 2 y = 0 := by
    by_contra hne
    have hpos : 0 < T.basis.coord 2 y := lt_of_le_of_ne (hnn 2) (Ne.symm hne)
    have hc : c = T.basis.coord 0 y * c + T.basis.coord 1 y * c
        + T.basis.coord 2 y * g (T.pts 2) := hbar
    have : T.basis.coord 0 y * c + T.basis.coord 1 y * c
        = (1 - T.basis.coord 2 y) * c := by rw [← hw]; ring
    rw [this] at hc
    nlinarith [hpos, h2]
  have hseg := Erdos634.BaseSelection.coord_zero_mem_segment T 2 y hz hnn
  rw [Tri.edge]
  simpa using hseg

end Erdos634.WallFace
