import Mathlib
import Erdos634.WallFace
import Erdos634.BaseSelection

/-!
# Every side of the target is a wall

Erdős #634, bridge (c).  `BridgeC.chain_junctions` was written for the base, and the map rows say
"proved for the base, open for the equal sides".  Reading the statement again, nothing in it is
about the base: it takes a functional `g`, a level `c`, endpoints `a`, `b`, and four hypotheses
relating them.  What was missing was not a theorem but the *data* — a supporting functional for the
other sides.

The barycentric coordinates supply it.  For side `k` of a triangle, the coordinate of the opposite
vertex `k+2` is nonnegative on the carrier and vanishes exactly on that side, so `g = -coord (k+2)`
with level `0` is the side's wall functional.  This file builds that data for every side.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SideWall

open Erdos634.Geometry

/-- The wall functional of side `k`: minus the barycentric coordinate of the opposite vertex. -/
noncomputable def wallFun (T : Tri) (k : Fin 3) : Plane →ᵃ[ℝ] ℝ := -(T.basis.coord (k + 2))

/-- **The target lies on one side of it.** -/
theorem wallFun_le (T : Tri) (k : Fin 3) {y : Plane} (hy : y ∈ T.carrier) :
    wallFun T k y ≤ 0 := by
  have h : y ∈ T.carrier := hy
  rw [T.carrier_eq_nonneg_coord] at h
  simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply, neg_nonpos]
  exact h (k + 2)

/-- **It vanishes on the side.** -/
theorem wallFun_eq_zero (T : Tri) (k : Fin 3) {y : Plane} (hy : y ∈ T.edge k) :
    wallFun T k y = 0 := by
  have hk1 : (k + 2 : Fin 3) ≠ k := by
    have : ∀ x : Fin 3, x + 2 ≠ x := by decide
    exact this k
  have hk2 : (k + 2 : Fin 3) ≠ k + 1 := by
    have : ∀ x : Fin 3, x + 2 ≠ x + 1 := by decide
    exact this k
  have e1 : T.basis.coord (k + 2) (T.pts k) = 0 := by
    have := T.basis.coord_apply (k + 2) k
    simp only [if_neg hk1] at this; exact this
  have e2 : T.basis.coord (k + 2) (T.pts (k + 1)) = 0 := by
    have := T.basis.coord_apply (k + 2) (k + 1)
    simp only [if_neg hk2] at this; exact this
  rw [Tri.edge] at hy
  obtain ⟨u, v, _, _, huv, rfl⟩ := hy
  have hx : u • T.pts k + v • T.pts (k + 1)
      = AffineMap.lineMap (T.pts k) (T.pts (k + 1)) v := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub]
    have : u = 1 - v := by linarith
    rw [this]; module
  simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero]
  rw [hx, AffineMap.apply_lineMap, e1, e2]
  simp

/-- **And it meets the target exactly in that side.**  This is `WallFace.face_eq_edge` in the
coordinate form, and it is what makes the side a *face* rather than a chord. -/
theorem wallFun_face (T : Tri) (k : Fin 3) {y : Plane} (hy : y ∈ T.carrier)
    (h0 : wallFun T k y = 0) : y ∈ T.edge k := by
  have hnn : ∀ j, 0 ≤ T.basis.coord j y := by
    have h : y ∈ T.carrier := hy
    rw [T.carrier_eq_nonneg_coord] at h
    exact h
  have hz : T.basis.coord (k + 2) y = 0 := by
    simpa [wallFun] using h0
  have hseg := Erdos634.BaseSelection.coord_zero_mem_segment T (k + 2) y hz hnn
  have hs1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have hs2 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  rw [hs1 k, hs2 k] at hseg
  rw [Tri.edge]
  exact hseg

end Erdos634.SideWall
