import Mathlib
import Erdos634.Dissection

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


/-! ## The same statement in the plane of the dissection

`wedge_extremal` is stated in the complex model.  The dissection's plane is a two-dimensional real
inner product space, so the statement is repeated here in that generality, using Mathlib's oriented
angles.  This is the form the march step consumes: `u` is one side of the junction wedge, `P` and
`Q` are the directions of the filling tile's two edges at the junction, and the conclusion is that
they are the wedge's two sides in one order or the other — the two chiralities. -/

section Plane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

open Orientation in
/-- **The junction step in the dissection's plane.**  Two nonzero directions whose oriented angles
from the wedge's first side lie in `[0, α]`, with `α < π`, and whose unoriented angle is `α`, are
the wedge's two sides. -/
theorem wedge_extremal_plane (o : Orientation ℝ V (Fin 2)) {u P Q : V} {α φ ψ : ℝ}
    (hu : u ≠ 0) (hP : P ≠ 0) (hQ : Q ≠ 0) (hα : α < Real.pi)
    (hφ : (o.oangle u P).toReal = φ) (hψ : (o.oangle u Q).toReal = ψ)
    (hφm : φ ∈ Set.Icc (0:ℝ) α) (hψm : ψ ∈ Set.Icc (0:ℝ) α)
    (hsep : InnerProductGeometry.angle P Q = α) :
    (φ = 0 ∧ ψ = α) ∨ (φ = α ∧ ψ = 0) := by
  obtain ⟨hφ0, hφa⟩ := hφm
  obtain ⟨hψ0, hψa⟩ := hψm
  have hsub : o.oangle P Q = ((ψ - φ : ℝ) : Real.Angle) := by
    rw [← o.oangle_sub_left hu hP hQ, ← hφ, ← hψ, Real.Angle.coe_sub,
      Real.Angle.coe_toReal, Real.Angle.coe_toReal]
  have hrange : (o.oangle P Q).toReal = ψ - φ := by
    rw [hsub, Real.Angle.toReal_coe_eq_self_iff]
    constructor <;> linarith
  have habs : |ψ - φ| = α := by
    rw [← hrange, ← o.angle_eq_abs_oangle_toReal hP hQ, hsep]
  rcases abs_cases (ψ - φ) with ⟨he, _⟩ | ⟨he, _⟩
  · left; constructor <;> linarith [habs ▸ he]
  · right; constructor <;> linarith [habs ▸ he]

end Plane

/-! ## The form the dissection consumes

`cornerAngle` is the dissection's name for the interior angle of a tile at one of its vertices.
The corollary below is `wedge_extremal_plane` read through that name, with the tile's apex as the
junction and the wedge measured from a chosen side `u`.

What is still *not* proved is that the uncovered region at a march junction is such a wedge, with
opening equal to the tile's corner angle there.  That identification is the open link; everything
downstream of it is now formal. -/

namespace Dissection

open Erdos634.Geometry

/-- The dissection's plane is two-dimensional; Mathlib's oriented-angle API asks for this as a
`Fact`. -/
instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp⟩

/-- **The junction step, in the dissection's language.**  A tile corner of angle `α < π` at `A`,
whose two edges at `A` point into the wedge `[0, α]` measured from `u`, has those edges along the
wedge's two sides — in one order or the other. -/
theorem corner_on_wedge_sides (o : Orientation ℝ Plane (Fin 2)) {A P Q u : Plane} {α φ ψ : ℝ}
    (hu : u ≠ 0) (hP : P - A ≠ 0) (hQ : Q - A ≠ 0) (hα : α < Real.pi)
    (hφ : (o.oangle u (P - A)).toReal = φ) (hψ : (o.oangle u (Q - A)).toReal = ψ)
    (hφm : φ ∈ Set.Icc (0:ℝ) α) (hψm : ψ ∈ Set.Icc (0:ℝ) α)
    (hcorner : cornerAngle P A Q = α) :
    (φ = 0 ∧ ψ = α) ∨ (φ = α ∧ ψ = 0) := by
  have hang : InnerProductGeometry.angle (P - A) (Q - A) = α := by
    rw [← hcorner, cornerAngle, EuclideanGeometry.angle]; simp [vsub_eq_sub]
  exact wedge_extremal_plane o hu hP hQ hα hφ hψ hφm hψm hang

end Dissection

end Erdos634.WedgeExtremal
