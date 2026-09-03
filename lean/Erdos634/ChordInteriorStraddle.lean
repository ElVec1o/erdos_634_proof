import Erdos634.ChordTraceReal

/-!
# An interior point on the chord line forces a straddle

Erdős #634. Continuing the assembly: `wall_cover`'s `hwall` hypothesis ("no tile's interior meets
this open segment") is exactly the complement of "some straddler's trace passes through here" —
this file makes that precise. `interior_on_line_straddles`: if a tile has an *interior* point on
the chord line, that tile straddles the line. Flush tiles never do (a nonconstant affine function's
extreme value over a convex body with nonempty interior is never attained at an interior point),
so this is the missing link connecting `wall_cover`'s hypothesis to "no straddler crosses here".

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **An interior point on the chord line forces the tile to straddle.** If `y` is interior to `T`
and `f y = c`, `T` cannot lie weakly on either side: moving from `y` a small distance along a
direction where `f` increases (resp. decreases) stays inside `T` (interior) while leaving `f ≤ c`
(resp. `f ≥ c`), so by `sign_trichotomy` only the straddle case remains. -/
theorem interior_on_line_straddles (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {y : Plane} (hy : y ∈ interior T.carrier) (hfy : f y = c) :
    (∃ i, f (T.pts i) < c) ∧ (∃ j, c < f (T.pts j)) := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h; push Not at h; exact hf (LinearMap.ext fun z => by simp [h z])
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
  set t : ℝ := r / (2 * ‖v‖) with htdef
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr (fun h => hv (by simp [h]))
  have htpos : 0 < t := by positivity
  have hrhalf : t * ‖v‖ = r / 2 := by rw [htdef]; field_simp
  have hmem : y + t • v ∈ Metric.ball y r := by
    rw [Metric.mem_ball, dist_eq_norm, show y + t • v - y = t • v by abel, norm_smul,
      Real.norm_eq_abs, abs_of_pos htpos, hrhalf]
    linarith
  have hmem' : y - t • v ∈ Metric.ball y r := by
    rw [Metric.mem_ball, dist_eq_norm, show y - t • v - y = -(t • v) by abel, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hrhalf]
    linarith
  have hyt : y + t • v ∈ T.carrier := interior_subset (hball hmem)
  have hyt' : y - t • v ∈ T.carrier := interior_subset (hball hmem')
  have hfvt : f (y + t • v) = c + t * f v := by rw [map_add, map_smul, smul_eq_mul, hfy]
  have hfvt' : f (y - t • v) = c - t * f v := by rw [map_sub, map_smul, smul_eq_mul, hfy]
  have htv : t * f v ≠ 0 := mul_ne_zero htpos.ne' hv
  have hlo : ∃ x ∈ T.carrier, f x < c := by
    rcases lt_or_gt_of_ne htv with h | h
    · exact ⟨y + t • v, hyt, by rw [hfvt]; linarith⟩
    · exact ⟨y - t • v, hyt', by rw [hfvt']; linarith⟩
  have hhi : ∃ x ∈ T.carrier, c < f x := by
    rcases lt_or_gt_of_ne htv with h | h
    · exact ⟨y - t • v, hyt', by rw [hfvt']; linarith⟩
    · exact ⟨y + t • v, hyt, by rw [hfvt]; linarith⟩
  rcases Tri.sign_trichotomy T f c with hle | hge | hstr
  · obtain ⟨x, hx, hxc⟩ := hhi; exact absurd (hle x hx) (not_le.mpr hxc)
  · obtain ⟨x, hx, hxc⟩ := hlo; exact absurd (hge x hx) (not_le.mpr hxc)
  · exact hstr

end Erdos634.ChordTraceReal
