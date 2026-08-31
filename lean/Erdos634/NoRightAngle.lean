import Erdos634.CongruentAngles

/-!
# No piece has a right angle

`rem:norightangle` says: every piece is congruent to the tile, so its corner angles are `α, β, γ`,
none of which is `π/2`; hence no piece of any dissection of a base-`β` region has a right angle, the
target cannot be split along its altitude, and no perpendicular cut is available in the branch.

`AngleArithmetic.no_right_angle` is the multiplicity arithmetic `¬(2x = 3 ∧ 2y = 2)`, and its own
docstring says it is "**not** the geometric claim that no dissection piece has a right angle: that
needs the piece's angles to be `α, β, γ`, which is congruence". `Geometry.congruent_corner_angles` supplies the
congruence half.  The composition was never written; it is written here.

`angles_ne_pi_div_two` also removes the appeal to "clause (1)": all three angles avoid `π/2` for the
single reason that `α` is not a rational multiple of `π`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.NoRightAngle

open Erdos634.Geometry

/-- **None of `α, β, γ` is a right angle**, from `α ∉ ℚπ` alone.  `β = π/2` and `γ = π/2` each
force `α = 0`, which is the rational multiple `0 · π`. -/
theorem angles_ne_pi_div_two {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hγ : γ = 2 * α + β) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    α ≠ Real.pi / 2 ∧ β ≠ Real.pi / 2 ∧ γ ≠ Real.pi / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact hirr ⟨1/2, by push_cast; linarith [h]⟩
  · intro h; exact hirr ⟨0, by push_cast; linarith [hrel, h]⟩
  · intro h
    exact hirr ⟨0, by push_cast; rw [hγ] at h; linarith [hrel, h]⟩

/-- **No piece congruent to the tile has a right angle.**  If every corner angle of `T` lies in
`{α, β, γ}` and none of those is `π/2`, then no corner angle of any `U` congruent to `T` is `π/2`. -/
theorem no_right_angle_of_congruent {T U : Tri} (h : T.Congruent U) {α β γ : ℝ}
    (hT : ∀ k : Fin 3, cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
      ∈ ({α, β, γ} : Finset ℝ))
    (hα : α ≠ Real.pi / 2) (hβ : β ≠ Real.pi / 2) (hγ : γ ≠ Real.pi / 2) (j : Fin 3) :
    cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2)) ≠ Real.pi / 2 := by
  obtain ⟨k, hk⟩ := Erdos634.Geometry.congruent_corner_angles h j
  rw [hk]
  have := hT k
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl
  · exact hα
  · exact hβ
  · exact hγ

/-- **The statement of `rem:norightangle`**, assembled: for a tile whose angles satisfy
`3α + 2β = π`, `γ = 2α + β` with `α ∉ ℚπ`, no piece congruent to it has a right angle. -/
theorem no_piece_has_right_angle {T U : Tri} (h : T.Congruent U) {α β γ : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hγ : γ = 2 * α + β)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hT : ∀ k : Fin 3, cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
      ∈ ({α, β, γ} : Finset ℝ)) (j : Fin 3) :
    cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2)) ≠ Real.pi / 2 := by
  obtain ⟨hα, hβ, hγ'⟩ := angles_ne_pi_div_two hrel hγ hirr
  exact no_right_angle_of_congruent h hT hα hβ hγ' j

end Erdos634.NoRightAngle
