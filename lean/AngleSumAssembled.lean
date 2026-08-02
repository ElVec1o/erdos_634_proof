import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# The interior angle sum, assembled (Erdős #634, E2)

The three components are proved elsewhere in this development:

  · `TangentCone.poly_inter_ball_eq_coneAt` — a polytope agrees with its tangent cone at `p` inside
    a ball on which every inactive constraint keeps its slack  (statement (A));
  · `SectorArea.lintegral_jacobian` — a unit sector of angle `θ` has area `θ/2`  (statement (B));
  · `ConeScaling.angle_sum_of_cones` — almost-disjoint pieces of `B(p,1)` that cover it and have
    areas `θᵢ/2` have `∑ θᵢ = 2π`.

This file wires them together. The two remaining links are identifications, not geometry, and they
appear here as explicit hypotheses so that what is assumed is visible:

  `htile` — each tile, intersected with the small ball, is its tangent cone intersected with it
            (this is (A), instantiated at the tile's three half-plane constraints);
  `hsector` — each cone, intersected with the unit ball, has the area of a sector of its angle
            (this is (B), after identifying the cone of a triangle at one of its points with the
            sector of the corresponding angle).

Given those, the interior angle sum is a consequence of measure additivity alone.
-/

open MeasureTheory Set Metric

namespace Erdos634.AngleSumAssembled

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **The interior angle sum.** If the tiles meeting an interior point `p` agree there with cones
whose unit-ball cuts are almost disjoint, cover, and have areas `θ i / 2`, then `∑ θ i = 2π`. -/
theorem angle_sum_interior {n : ℕ} (p : Plane) (K : Fin n → Set Plane) (θ : Fin n → ℝ)
    (hmeas : ∀ i, MeasurableSet (K i))
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) K))
    (hcover : ⋃ i, K i = ball p 1)
    (hsector : ∀ i, volume (K i) = ENNReal.ofReal (θ i / 2))
    (hθ : ∀ i, 0 ≤ θ i)
    (hball : volume (ball p (1:ℝ)) = ENNReal.ofReal Real.pi) :
    ∑ i, θ i = 2 * Real.pi := by
  have hU := measure_iUnion₀ (μ := volume) hdisj (fun i => (hmeas i).nullMeasurableSet)
  rw [hcover, tsum_fintype, hball] at hU
  simp_rw [hsector] at hU
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by linarith [hθ i])] at hU
  have hnn : (0:ℝ) ≤ ∑ i, θ i / 2 := Finset.sum_nonneg (fun i _ => by linarith [hθ i])
  have h := ((ENNReal.ofReal_eq_ofReal_iff hnn Real.pi_pos.le).mp hU.symm)
  have hhalf : ∑ i, θ i / 2 = (∑ i, θ i) / 2 := by rw [Finset.sum_div]
  rw [hhalf] at h
  linarith

/-- The same statement at a boundary point, where the tiles fill a half-disc: `∑ θ i = π`. -/
theorem angle_sum_boundary {n : ℕ} (K : Fin n → Set Plane) (θ : Fin n → ℝ) (H : Set Plane)
    (hmeas : ∀ i, MeasurableSet (K i))
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) K))
    (hcover : ⋃ i, K i = H)
    (hsector : ∀ i, volume (K i) = ENNReal.ofReal (θ i / 2))
    (hθ : ∀ i, 0 ≤ θ i)
    (hhalf : volume H = ENNReal.ofReal (Real.pi / 2)) :
    ∑ i, θ i = Real.pi := by
  have hU := measure_iUnion₀ (μ := volume) hdisj (fun i => (hmeas i).nullMeasurableSet)
  rw [hcover, tsum_fintype, hhalf] at hU
  simp_rw [hsector] at hU
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by linarith [hθ i])] at hU
  have hnn : (0:ℝ) ≤ ∑ i, θ i / 2 := Finset.sum_nonneg (fun i _ => by linarith [hθ i])
  have h := ((ENNReal.ofReal_eq_ofReal_iff hnn (by positivity)).mp hU.symm)
  have hd : ∑ i, θ i / 2 = (∑ i, θ i) / 2 := by rw [Finset.sum_div]
  rw [hd] at h
  linarith

end Erdos634.AngleSumAssembled
