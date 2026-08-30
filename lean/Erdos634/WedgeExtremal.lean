import Mathlib

/-!
# The junction wedge: two directions separated by the full opening are the boundary rays

Erdős #634, `e = 1`, the march step.  `MarchStep.polar_extremes` is the statement in polar angles;
this file supplies the plane geometry that produces those angles, working in `ℂ` as the model of
the plane.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WedgeExtremal

open InnerProductGeometry Complex Real

/-- The unit direction at polar angle `θ`. -/
noncomputable def dir (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

theorem dir_norm (θ : ℝ) : ‖dir θ‖ = 1 := by
  simp [dir, Complex.norm_exp]

theorem dir_ne_zero (θ : ℝ) : dir θ ≠ 0 := by
  intro h; have := dir_norm θ; rw [h] at this; simp at this

/-- The real inner product of two unit directions is the cosine of their polar difference. -/
theorem inner_dir (θ φ : ℝ) : (inner ℝ (dir θ) (dir φ) : ℝ) = Real.cos (φ - θ) := by
  simp [dir, real_inner_eq_re_inner (𝕜 := ℂ), Complex.exp_mul_I, Real.cos_sub,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- **The angle between two directions is the absolute polar difference**, within a half turn. -/
theorem angle_dir (θ φ : ℝ) (h : |φ - θ| ≤ Real.pi) :
    angle (dir θ) (dir φ) = |φ - θ| := by
  have : angle (dir θ) (dir φ) = Real.arccos (Real.cos (φ - θ)) := by
    rw [angle, inner_dir, dir_norm, dir_norm]; norm_num
  rw [this, ← Real.cos_abs, Real.arccos_cos (abs_nonneg _) h]

/-- **The junction step, geometrically.**  Two directions inside a wedge of opening `α < π`,
separated by exactly `α`, are the wedge's two boundary rays.  At a march junction the filling tile's
corner angle equals the wedge's opening (`MarchRecurrence.junction_forces_single_alpha` forces the
single `α`-tile), so its two edges there are the wedge's sides and the only remaining freedom is
which of the two `α`-adjacent side lengths goes on which — the two chiralities. -/
theorem wedge_extremal {α φ ψ : ℝ} (hα : α < Real.pi)
    (hφ : φ ∈ Set.Icc (0:ℝ) α) (hψ : ψ ∈ Set.Icc (0:ℝ) α)
    (hsep : angle (dir φ) (dir ψ) = α) :
    (φ = 0 ∧ ψ = α) ∨ (φ = α ∧ ψ = 0) := by
  obtain ⟨hφ0, hφa⟩ := hφ
  obtain ⟨hψ0, hψa⟩ := hψ
  have hbound : |ψ - φ| ≤ Real.pi := by
    rw [abs_le]; constructor <;> linarith
  rw [angle_dir φ ψ hbound] at hsep
  rcases abs_cases (ψ - φ) with ⟨he, _⟩ | ⟨he, _⟩
  · left; constructor <;> linarith [hsep ▸ he]
  · right; constructor <;> linarith [hsep ▸ he]

end Erdos634.WedgeExtremal
