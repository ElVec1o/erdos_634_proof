import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Erdos634.Dissection

/-!
# Transporting a dissection along an affine equivalence

Erdős #634, the scale map.  Five PROVED statements — `thm:ladder`, `cor:ladder`, `prop:inflbdy`,
`cor:inflcrux`, `prop:inflparity` — wait on a way to move a dissection along a map of the plane.
The general step is here: an affine equivalence carries a dissection to a dissection, because it
carries triangles to triangles, unions to unions, and interiors to interiors.

What this does *not* yet give is `thm:ladder` itself, which needs the subdivision of `kT` into `k²`
copies of `T` — a construction, not a transport.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.DissectionMap

open Erdos634.Geometry

/-- The image of a tile under an affine equivalence. -/
noncomputable def mapTri (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) : Tri where
  pts := e ∘ T.pts
  indep := T.indep.map' e.toAffineMap e.injective

theorem mapTri_carrier (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    (mapTri e T).carrier = e '' T.carrier := by
  simp only [mapTri, Tri.carrier]
  rw [Set.range_comp]
  exact (AffineMap.image_convexHull (𝕜 := ℝ) e.toAffineMap (Set.range T.pts)).symm

/-- **A dissection transports.**  An affine equivalence carries a dissection of a triangle to a
dissection of its image. -/
noncomputable def mapDissection {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (D : Dissection N) :
    Dissection N where
  target := mapTri e D.target
  tile := fun i => mapTri e (D.tile i)
  covers := by
    simp only [mapTri_carrier]
    rw [← Set.image_iUnion, D.covers]
  interiors_disjoint := by
    intro i j hij
    have h := D.interiors_disjoint hij
    have hcont : Continuous e := AffineEquiv.continuous_of_finiteDimensional e
    have hcont' : Continuous e.symm := AffineEquiv.continuous_of_finiteDimensional e.symm
    let eh : Plane ≃ₜ Plane := ⟨e.toEquiv, hcont, hcont'⟩
    have himg : ∀ S : Set Plane, interior (e '' S) = e '' interior S := by
      intro S
      exact (eh.image_interior S).symm
    simp only [mapTri_carrier, himg]
    exact (Set.disjoint_image_iff e.injective).mpr h

theorem mapDissection_target {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (D : Dissection N) :
    (mapDissection e D).target = mapTri e D.target := rfl

theorem mapDissection_tile {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (D : Dissection N) (i : Fin N) :
    (mapDissection e D).tile i = mapTri e (D.tile i) := rfl

end Erdos634.DissectionMap
