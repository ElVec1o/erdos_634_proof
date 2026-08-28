import Mathlib.Tactic
import Erdos634.Congruence
import Erdos634.Dissection

/-!
# Congruent tiles have the same corner angles (SSS)

Erdős #634, the congruence layer's missing angle statement.  `Congruent.dist_eq` matches the
pairwise distances under one permutation; the law of cosines turns matched distances into matched
angles.  The consumer is the pin argument: a tile congruent to the base tile contributes, at any
vertex, one of the base tile's three corner angles — which is what feeds
`Geometry.vertex_multiplicities` through `PinPlumbing.localAngle_cases`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Geometry

open EuclideanGeometry

/-- **SSS for angles.**  Two point triples with matching side distances and nondegenerate corner
have equal angles at the matched vertex. -/
theorem angle_of_sss {p q r p' q' r' : Plane}
    (hpq : dist p q = dist p' q') (hqr : dist q r = dist q' r') (hpr : dist p r = dist p' r')
    (hp : p ≠ q) (hr : r ≠ q) :
    EuclideanGeometry.angle (V := Plane) p q r = EuclideanGeometry.angle (V := Plane) p' q' r' := by
  have hd1 : (0:ℝ) < dist p q := dist_pos.mpr hp
  have hd2 : (0:ℝ) < dist r q := dist_pos.mpr hr
  have law1 := EuclideanGeometry.law_cos (V := Plane) p q r
  have law2 := EuclideanGeometry.law_cos (V := Plane) p' q' r'
  have hqr'' : dist r q = dist r' q' := by rw [dist_comm r q, dist_comm r' q']; exact hqr
  have hcos : Real.cos (EuclideanGeometry.angle (V := Plane) p q r)
      = Real.cos (EuclideanGeometry.angle (V := Plane) p' q' r') := by
    rw [← hpq, ← hqr'', ← hpr] at law2
    have h2d : (0:ℝ) < 2 * dist p q * dist r q := by positivity
    have hmul : 2 * dist p q * dist r q * Real.cos (EuclideanGeometry.angle (V := Plane) p q r)
        = 2 * dist p q * dist r q * Real.cos (EuclideanGeometry.angle (V := Plane) p' q' r') := by
      nlinarith [law1, law2]
    exact mul_left_cancel₀ (ne_of_gt h2d) hmul
  have hmem1 : EuclideanGeometry.angle (V := Plane) p q r ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hmem2 : EuclideanGeometry.angle (V := Plane) p' q' r' ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  exact Real.injOn_cos hmem1 hmem2 hcos

/-- On `Fin 3`, anything different from `k` is `k + 1` or `k + 2`. -/
theorem fin3_cases (a k : Fin 3) (h : a ≠ k) : a = k + 1 ∨ a = k + 2 := by
  fin_cases a <;> fin_cases k <;> simp_all <;> decide

/-- **A congruent tile's corner angle is one of the model's three.**  For every vertex `j` of `U`
there is a vertex `k` of `T` with the same corner angle. -/
theorem congruent_corner_angles {T U : Tri} (h : T.Congruent U) (j : Fin 3) :
    ∃ k : Fin 3, cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  obtain ⟨σ, hd⟩ := h.dist_eq
  set k := σ.symm j with hk
  have hσk : σ k = j := by rw [hk]; simp
  refine ⟨k, ?_⟩
  -- the other two vertices match as a set
  have h1 : σ (k + 1) ≠ j := by
    intro hh; have := σ.injective (hh.trans hσk.symm)
    simp at this
  have h2 : σ (k + 2) ≠ j := by
    intro hh; have := σ.injective (hh.trans hσk.symm)
    simp at this
  have hne12 : σ (k + 1) ≠ σ (k + 2) := by
    intro hh; have := σ.injective hh; simp at this
  -- nondegeneracy of U at j
  have hUne1 : U.pts (j + 1) ≠ U.pts j := by
    intro hh
    have := U.indep.injective hh
    have hne : j + 1 ≠ j := by fin_cases j <;> decide
    exact hne this
  have hUne2 : U.pts (j + 2) ≠ U.pts j := by
    intro hh
    have := U.indep.injective hh
    have hne : j + 2 ≠ j := by fin_cases j <;> decide
    exact hne this
  rcases fin3_cases (σ (k+1)) j h1 with hc1 | hc1
  · -- σ(k+1) = j+1, so σ(k+2) = j+2
    have hc2 : σ (k + 2) = j + 2 := by
      rcases fin3_cases (σ (k+2)) j h2 with hx | hx
      · exfalso; exact hne12 (by rw [hc1, hx])
      · exact hx
    have ptj : U.pts j = U.pts (σ k) := by rw [hσk]
    have pt1 : U.pts (j + 1) = U.pts (σ (k + 1)) := by rw [hc1]
    have pt2 : U.pts (j + 2) = U.pts (σ (k + 2)) := by rw [hc2]
    refine angle_of_sss ?_ ?_ ?_ hUne1 hUne2
    · rw [pt1, ptj]; exact (hd (k+1) k).symm
    · rw [ptj, pt2]; exact (hd k (k+2)).symm
    · rw [pt1, pt2]; exact (hd (k+1) (k+2)).symm
  · -- σ(k+1) = j+2, swapped: use angle_comm
    have hc2 : σ (k + 2) = j + 1 := by
      rcases fin3_cases (σ (k+2)) j h2 with hx | hx
      · exact hx
      · exfalso; exact hne12 (by rw [hc1, hx])
    have hcomm : cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
        = cornerAngle (U.pts (j + 2)) (U.pts j) (U.pts (j + 1)) :=
      EuclideanGeometry.angle_comm (V := Plane) _ _ _
    rw [hcomm]
    have ptj : U.pts j = U.pts (σ k) := by rw [hσk]
    have pt1 : U.pts (j + 2) = U.pts (σ (k + 1)) := by rw [hc1]
    have pt2 : U.pts (j + 1) = U.pts (σ (k + 2)) := by rw [hc2]
    refine angle_of_sss ?_ ?_ ?_ hUne2 hUne1
    · rw [pt1, ptj]; exact (hd (k+1) k).symm
    · rw [ptj, pt2]; exact (hd k (k+2)).symm
    · rw [pt1, pt2]; exact (hd (k+1) (k+2)).symm

/-- **A congruent tile's edge lengths are the model's.**  Every side of `U` has the length of some
side of `T`.  This is the half the covering arguments consume: an edge lying on a wall contributes
one of the three model lengths to the run, which is what feeds the semigroup kills. -/
theorem congruent_edge_lengths {T U : Tri} (h : T.Congruent U) (j j' : Fin 3) (hjj : j ≠ j') :
    ∃ i i' : Fin 3, i ≠ i' ∧ dist (U.pts j) (U.pts j') = dist (T.pts i) (T.pts i') := by
  obtain ⟨σ, hd⟩ := h.dist_eq
  refine ⟨σ.symm j, σ.symm j', fun hh => hjj (σ.symm.injective hh), ?_⟩
  have := hd (σ.symm j) (σ.symm j')
  simpa using this.symm

end Erdos634.Geometry
