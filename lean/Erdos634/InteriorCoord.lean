import Erdos634.Dissection

/-!
# The interior of a triangle is where all three barycentric coordinates are positive

Erdős #634. `Tri.ball_subset_of_pos` gives one direction — all coordinates positive puts a ball
inside the carrier, hence the point in the interior. The converse was never proved, and it is the
direction the covering arguments need: to know that a point of `interior T.carrier` has *strictly*
positive coordinates, so that two cells whose coordinate boxes are disjoint have disjoint interiors.

The converse is short. A point of the interior is in the carrier, so its coordinates are
nonnegative (`Tri.carrier_eq_nonneg_coord`). If one of them vanished, then — the coordinate being a
nonconstant affine functional (`Tri.coord_linear_ne_zero`) — every ball around the point would
contain a point where it is negative, hence a point outside the carrier, contradicting
interiority.

This is the bridge `Subdivision`'s `openUp`/`openDown` need: those are exactly the strict
inequalities cutting out the two cell triangles, and `cell_pinned`/`up_down_disjoint` already show
the coordinate conditions are pairwise incompatible. With `interior_iff_pos_coord` those become
statements about `interior (cellUp …).carrier`, which is what `Dissection.interiors_disjoint`
asks for.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Geometry

open Metric

/-- **A nonconstant affine functional vanishing at `x` is negative arbitrarily near `x`.** -/
theorem exists_neg_near_of_affine_zero (g : Plane →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0)
    {x : Plane} (hx : g x = 0) {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ ball x r, g y < 0 := by
  obtain ⟨v, hv⟩ : ∃ v, g.linear v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hg (LinearMap.ext fun v => by simpa using hcon v)
  -- replace `v` by a direction on which `g.linear` is negative
  set w : Plane := if g.linear v < 0 then v else -v with hw
  have hwneg : g.linear w < 0 := by
    rw [hw]
    by_cases h : g.linear v < 0
    · simpa [h] using h
    · have : 0 < g.linear v := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hv)
      simpa [h] using by simpa using this
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hwneg
    simp at hwneg
  -- move a small positive multiple of `w` from `x`
  set t : ℝ := r / (2 * ‖w‖) with ht
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have htpos : 0 < t := by positivity
  refine ⟨x + t • w, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    have : ‖x + t • w - x‖ = t * ‖w‖ := by
      simp [norm_smul, abs_of_pos htpos]
    rw [this, ht]
    rw [div_mul_eq_mul_div, mul_comm]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hnorm, hr]
  · have hval : g (x + t • w) = g x + t * g.linear w := by
      have h := g.map_vadd x (t • w)
      simp only [vadd_eq_add, map_smul, smul_eq_mul] at h
      rw [add_comm x (t • w), h]
      ring
    rw [hval, hx]
    have : t * g.linear w < 0 := mul_neg_of_pos_of_neg htpos hwneg
    linarith

/-- **The interior of a triangle is exactly the strictly-positive locus of its barycentric
coordinates.** -/
theorem Tri.interior_iff_pos_coord (T : Tri) (x : Plane) :
    x ∈ interior T.carrier ↔ ∀ k, 0 < T.basis.coord k x := by
  constructor
  · intro hx
    have hxc : x ∈ T.carrier := interior_subset hx
    have hnn : ∀ k, 0 ≤ T.basis.coord k x := by
      rw [T.carrier_eq_nonneg_coord] at hxc; exact hxc
    intro k
    rcases lt_or_eq_of_le (hnn k) with h | h
    · exact h
    · -- the coordinate vanishes: find a nearby point outside the carrier
      exfalso
      obtain ⟨r, hr, hball⟩ := mem_interior_iff_mem_nhds.mp hx |> Metric.mem_nhds_iff.mp
      obtain ⟨y, hy, hyneg⟩ :=
        exists_neg_near_of_affine_zero (T.basis.coord k) (T.coord_linear_ne_zero k) h.symm hr
      have hyc : y ∈ T.carrier := hball hy
      rw [T.carrier_eq_nonneg_coord] at hyc
      exact absurd (hyc k) (not_le.mpr hyneg)
  · intro hpos
    obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
    exact mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨r, hr, hsub⟩)

end Erdos634.Geometry
