import Erdos634.CollarDisjointM4

/-!
# The `m=2 → m=4` collar step — containment, `Δ_4` and the apex piece

Erdős #634. `thm:realize12`'s existence half needs `Δ_4` built as one flat `Dissection 176`;
disjointness for all 176 pieces is done (`CollarDisjointM4.lean`). This file starts containment
(every piece ⊆ `Δ_4`'s own carrier): defines `Δ_4` as a real `Tri` (`delta4`), and proves the
first, simplest case — `Δ_2^apex` (a whole translated copy of `Tiling44Bridge.dissection`) sits
inside `Δ_4`.

The route: `CertGeom.carrier_subset_of_pts_mem` reduces "triangle `⊆` triangle" to "each vertex
`∈` the target's carrier"; `Δ_2^apex`'s own vertices are the *midpoints* of two of `Δ_4`'s edges
(and `Δ_4`'s own apex), so membership follows directly from `midpoint_mem_segment` +
`segment_subset_convexHull`, without any half-plane/cross-product argument.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.CertCoord Erdos634.TranslateDissection Erdos634.CertGeom

/-- **`Δ_4`**: the base-β target at scale `4`, vertices `(0,0)`, `(352,0)`, `(176,48√15)` (matching
`Δ_2 = Tiling44Bridge.dissection`'s own target at double the scale, per the hand-derivation in
`private/VERIFY_PLAN.md`'s 2026-09-05 entries: `Δ_m` has vertices `(0,0),(88m,0),(44m,12√15·m)`). -/
noncomputable def delta4 : Tri := mkTri 0 0 352 0 176 (48 * Real.sqrt 15)
  (by
    show (352 - 0) * (48 * Real.sqrt 15 - 0) - (176 - 0) * (0 - 0) ≠ 0
    have hpos : (0:ℝ) < 352 * (48 * Real.sqrt 15) := by positivity
    intro h
    rw [show (352 - 0) * (48 * Real.sqrt 15 - 0) - (176 - 0) * (0 - 0)
        = 352 * (48 * Real.sqrt 15) from by ring] at h
    linarith)

theorem mkPt_midpoint (x1 y1 x2 y2 : ℝ) :
    midpoint ℝ (mkPt x1 y1) (mkPt x2 y2) = mkPt ((x1 + x2) / 2) ((y1 + y2) / 2) := by
  unfold midpoint
  rw [AffineMap.lineMap_apply, vsub_eq_sub, invOf_eq_inv, vadd_eq_add]
  have hsub : mkPt x2 y2 - mkPt x1 y1 = mkPt (x2 - x1) (y2 - y1) := by
    ext j; fin_cases j <;> simp [PiLp.sub_apply, mkPt_zero, mkPt_one]
  rw [hsub]
  have hsmul : (2:ℝ)⁻¹ • mkPt (x2 - x1) (y2 - y1) = mkPt ((x2 - x1) / 2) ((y2 - y1) / 2) := by
    ext j; fin_cases j <;> simp [PiLp.smul_apply, mkPt_zero, mkPt_one] <;> ring
  rw [hsmul, add_comm, mkPt_add]
  congr 1 <;> ring

/-- `Δ_2^apex`'s base-left vertex is the midpoint of `Δ_4`'s left leg. -/
theorem apex_vertex0_mem_delta4 : mkPt 88 (24 * Real.sqrt 15) ∈ delta4.carrier := by
  have heq : mkPt (88:ℝ) (24 * Real.sqrt 15) = midpoint ℝ (delta4.pts 0) (delta4.pts 2) := by
    show mkPt (88:ℝ) (24 * Real.sqrt 15) = midpoint ℝ (mkPt 0 0) (mkPt 176 (48 * Real.sqrt 15))
    rw [mkPt_midpoint]; congr 1
    · norm_num
    · ring
  rw [heq]
  exact segment_subset_convexHull (Set.mem_range_self _) (Set.mem_range_self _)
    (midpoint_mem_segment _ _)

/-- `Δ_2^apex`'s base-right vertex is the midpoint of `Δ_4`'s right leg. -/
theorem apex_vertex1_mem_delta4 : mkPt 264 (24 * Real.sqrt 15) ∈ delta4.carrier := by
  have heq : mkPt (264:ℝ) (24 * Real.sqrt 15) = midpoint ℝ (delta4.pts 1) (delta4.pts 2) := by
    show mkPt (264:ℝ) (24 * Real.sqrt 15) = midpoint ℝ (mkPt 352 0) (mkPt 176 (48 * Real.sqrt 15))
    rw [mkPt_midpoint]; congr 1
    · norm_num
    · ring
  rw [heq]
  exact segment_subset_convexHull (Set.mem_range_self _) (Set.mem_range_self _)
    (midpoint_mem_segment _ _)

/-- `Δ_2^apex`'s own apex coincides with `Δ_4`'s apex. -/
theorem apex_vertex2_mem_delta4 : mkPt 176 (48 * Real.sqrt 15) ∈ delta4.carrier :=
  subset_convexHull ℝ _ (Set.mem_range_self 2)

/-- **`Δ_2^apex` sits inside `Δ_4`.** -/
theorem apex_subset_delta4 :
    (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
      Erdos634.Tiling44Bridge.dissection).target.carrier ⊆ delta4.carrier := by
  apply carrier_subset_of_pts_mem
  intro k
  fin_cases k
  · show (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
      Erdos634.Tiling44Bridge.dissection).target.pts 0 ∈ delta4.carrier
    rw [apex_copy_pts.1]; exact apex_vertex0_mem_delta4
  · show (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
      Erdos634.Tiling44Bridge.dissection).target.pts 1 ∈ delta4.carrier
    rw [apex_copy_pts.2.1]; exact apex_vertex1_mem_delta4
  · show (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
      Erdos634.Tiling44Bridge.dissection).target.pts 2 ∈ delta4.carrier
    rw [apex_copy_pts.2.2]; exact apex_vertex2_mem_delta4

/-! ## Corner-triangle containment

The corner triangle's vertices are also midpoints/vertices of `Δ_4`'s own edges — the same
shortcut as `Δ_2^apex` applies. -/

/-- The corner's base-left vertex is the midpoint of `Δ_4`'s base. -/
theorem corner_vertex0_mem_delta4 : mkPt 176 0 ∈ delta4.carrier := by
  have heq : mkPt (176:ℝ) 0 = midpoint ℝ (delta4.pts 0) (delta4.pts 1) := by
    show mkPt (176:ℝ) 0 = midpoint ℝ (mkPt 0 0) (mkPt 352 0)
    rw [mkPt_midpoint]; norm_num
  rw [heq]
  exact segment_subset_convexHull (Set.mem_range_self _) (Set.mem_range_self _)
    (midpoint_mem_segment _ _)

/-- The corner's base-right vertex coincides with `Δ_4`'s own base-right vertex. -/
theorem corner_vertex1_mem_delta4 : mkPt 352 0 ∈ delta4.carrier :=
  subset_convexHull ℝ _ (Set.mem_range_self 1)

/-- The corner's apex is the same point as `Δ_2^apex`'s base-right vertex — the midpoint of
`Δ_4`'s right leg. -/
theorem corner_vertex2_mem_delta4 : mkPt 264 (24 * Real.sqrt 15) ∈ delta4.carrier :=
  apex_vertex1_mem_delta4

/-- **The corner triangle sits inside `Δ_4`.** -/
theorem corner_subset_delta4 :
    (translateCongruentDissection (mkPt 176 0)
      Erdos634.Tiling44Bridge.dissection).target.carrier ⊆ delta4.carrier := by
  apply carrier_subset_of_pts_mem
  intro k
  fin_cases k
  · show (translateCongruentDissection (mkPt 176 0)
      Erdos634.Tiling44Bridge.dissection).target.pts 0 ∈ delta4.carrier
    rw [corner_copy_pts.1]; exact corner_vertex0_mem_delta4
  · show (translateCongruentDissection (mkPt 176 0)
      Erdos634.Tiling44Bridge.dissection).target.pts 1 ∈ delta4.carrier
    rw [corner_copy_pts.2.1]; exact corner_vertex1_mem_delta4
  · show (translateCongruentDissection (mkPt 176 0)
      Erdos634.Tiling44Bridge.dissection).target.pts 2 ∈ delta4.carrier
    rw [corner_copy_pts.2.2]; exact corner_vertex2_mem_delta4
