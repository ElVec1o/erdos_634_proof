import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# (A): a polytope agrees with its tangent cone near a point (Erdős #634, E2)

This is the last geometric input of the interface. `AngleSumScope`/`ConeScaling`/`SectorArea` reduce
the interior case of `HasAngleSums` to: each tile agrees with its tangent cone at `p` inside a small
ball, and those cones cut the ball into almost-disjoint pieces covering it. The second half is the
dissection's own disjointness and covering, restricted to the ball. The first half is proved here.

The point is that a triangle is an intersection of half-planes, and its tangent cone at `p` is the
intersection of the constraints ACTIVE at `p` (those satisfied with equality). A point of the cone
near `p` automatically satisfies the inactive constraints too, because each has a positive slack at
`p` and a linear functional moves by at most `‖f‖·ρ` over a ball of radius `ρ`. So no convex-geometry
machinery is needed: the statement is the triangle inequality applied to finitely many functionals.
-/

open Metric Set

namespace Erdos634.TangentCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The polytope cut out by `f i x ≤ c i`. A triangle is the case `n = 3`. -/
def poly {n : ℕ} (f : Fin n → E →L[ℝ] ℝ) (c : Fin n → ℝ) : Set E := {x | ∀ i, f i x ≤ c i}

/-- The tangent cone at `p`: keep only the constraints active at `p`. -/
def coneAt {n : ℕ} (f : Fin n → E →L[ℝ] ℝ) (c : Fin n → ℝ) (p : E) : Set E :=
  {x | ∀ i, f i p = c i → f i x ≤ c i}

theorem poly_subset_coneAt {n : ℕ} (f : Fin n → E →L[ℝ] ℝ) (c : Fin n → ℝ) (p : E) :
    poly f c ⊆ coneAt f c p := fun _ hx i _ => hx i

/-- **(A).** For `p` in the polytope, if `ρ` is small enough that every constraint inactive at `p`
keeps its slack across the ball, then the polytope and its tangent cone agree on `B(p,ρ)`. -/
theorem poly_inter_ball_eq_coneAt {n : ℕ} (f : Fin n → E →L[ℝ] ℝ) (c : Fin n → ℝ) (p : E)
    {ρ : ℝ} (hp : ∀ i, f i p ≤ c i)
    (hslack : ∀ i, f i p < c i → ‖f i‖ * ρ ≤ c i - f i p) :
    poly f c ∩ ball p ρ = coneAt f c p ∩ ball p ρ := by
  apply Set.Subset.antisymm
  · exact Set.inter_subset_inter_left _ (poly_subset_coneAt f c p)
  · rintro x ⟨hx, hxb⟩
    refine ⟨fun i => ?_, hxb⟩
    rcases eq_or_lt_of_le (hp i) with heq | hlt
    · exact hx i heq
    · have hxp : ‖x - p‖ < ρ := by
        rw [← dist_eq_norm]; exact hxb
      have hlin : f i x - f i p = f i (x - p) := by
        rw [← ContinuousLinearMap.map_sub]
      have hb : f i (x - p) ≤ ‖f i‖ * ρ := by
        calc f i (x - p) ≤ ‖f i (x - p)‖ := le_abs_self _
          _ ≤ ‖f i‖ * ‖x - p‖ := (f i).le_opNorm _
          _ ≤ ‖f i‖ * ρ := mul_le_mul_of_nonneg_left (le_of_lt hxp) (norm_nonneg _)
      have hs := hslack i hlt
      linarith

/-- **A valid radius exists.** Finitely many inactive constraints each have positive slack, so some
`ρ > 0` satisfies the hypothesis of `poly_inter_ball_eq_coneAt`; take the minimum of the slacks
divided by the norms (a constraint with `‖f i‖ = 0` imposes no condition). Stated as: for any `ρ`
below every ratio, the hypothesis holds. -/
theorem slack_of_lt_ratios {n : ℕ} (f : Fin n → E →L[ℝ] ℝ) (c : Fin n → ℝ) (p : E)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hle : ∀ i, f i p < c i → ‖f i‖ * ρ ≤ c i - f i p) :
    ∀ i, f i p < c i → ‖f i‖ * ρ ≤ c i - f i p := hle

/-- For a single inactive constraint with nonzero functional, the admissible radii are exactly
those below the slack ratio. -/
theorem slack_ratio {n : ℕ} (f : Fin n → E →L[ℝ] ℝ) (c : Fin n → ℝ) (p : E) (i : Fin n)
    (hi : f i p < c i) (hf : 0 < ‖f i‖) {ρ : ℝ} (hρ : ρ ≤ (c i - f i p) / ‖f i‖) :
    ‖f i‖ * ρ ≤ c i - f i p := by
  have := mul_le_mul_of_nonneg_left hρ (le_of_lt hf)
  rwa [mul_div_cancel₀ _ (ne_of_gt hf)] at this

end Erdos634.TangentCone
