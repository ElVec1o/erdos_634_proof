import Erdos634.RouteOne

/-!
# Vacuity check for `RouteOne.EscapeData.ofWall`

Rule: exhibit a witness for every hypothesis before reporting a conditional as progress.  The
geometric hypotheses of `ofWall` describe a wall configuration, which is exactly what is at issue;
what *can* be checked mechanically is that the **analytic block** — the approach-sequence
constraints `hx`, `hslope`, `hnear`, `hpos` taken together — is satisfiable, i.e. that the four
inequalities do not silently contradict one another.  They do not: `pick n = ((n+1)⁻¹, (n+1)⁻³)`
satisfies all four at `V = 0`.
-/

namespace Erdos634.RouteOne

open Erdos634.Geometry

noncomputable def approachWitness (n : ℕ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(n + 1 : ℝ)⁻¹, (n + 1 : ℝ)⁻¹ ^ 3]

theorem approachWitness_sat (n : ℕ) :
    0 < (approachWitness n - (0 : Plane)) 0 ∧
    (approachWitness n - (0 : Plane)) 1
      ≤ (1 / (n + 1 : ℝ)) * ((approachWitness n - (0 : Plane)) 0) ∧
    0 < (approachWitness n - (0 : Plane)) 1 ∧
    dist (approachWitness n) (0 : Plane) < 2 / (n + 1 : ℝ) := by
  have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hi : (0:ℝ) < ((n:ℝ) + 1)⁻¹ := by positivity
  have hle1 : ((n:ℝ) + 1)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [approachWitness]; positivity
  · simp only [approachWitness, sub_zero]
    simp [EuclideanSpace.equiv, one_div]
    have h3 : (((n:ℝ)+1)^3)⁻¹ = ((n:ℝ)+1)⁻¹ ^ 3 := by rw [inv_pow]
    rw [h3]
    nlinarith [hi, hle1, sq_nonneg (((n:ℝ)+1)⁻¹)]
  · simp [approachWitness]; positivity
  · rw [EuclideanSpace.dist_eq]
    have hpos2 : (0:ℝ) < 2 / ((n:ℝ) + 1) := by positivity
    rw [show (2:ℝ) / ((n:ℝ)+1) = 2 * ((n:ℝ)+1)⁻¹ by field_simp]
    rw [Real.sqrt_lt' (by positivity)]
    simp [approachWitness, EuclideanSpace.equiv, Fin.sum_univ_two]
    have e1 : (((n:ℝ)+1)^2)⁻¹ = ((n:ℝ)+1)⁻¹ ^ 2 := by rw [inv_pow]
    have e2 : ((((n:ℝ)+1)^3)^2)⁻¹ = ((n:ℝ)+1)⁻¹ ^ 6 := by
      rw [← pow_mul, inv_pow]
    rw [e1, e2]
    have h6 : ((n:ℝ)+1)⁻¹ ^ 6 ≤ ((n:ℝ)+1)⁻¹ ^ 2 :=
      pow_le_pow_of_le_one hi.le hle1 (by norm_num)
    nlinarith [hi, pow_pos hi 2]

end Erdos634.RouteOne
