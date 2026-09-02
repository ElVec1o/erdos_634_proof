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
open Erdos634.DissectionMap

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

/-! ## Column containment — the general half-plane route

Unlike the apex/corner shortcut, column pieces need the general route: `Δ_4`'s three supporting
half-planes are `y ≥ 0` (base, via `yAff`), `l ≥ 0` (left leg, `l(x,y) = 48√15·x − 176·y`), and
`r ≤ 16896√15` (right leg, `r(x,y) = 48√15·x + 176·y`) — both new functionals, following the same
pattern as `gAff`. `mem_delta4_of_bounds` converts the three bounds into membership via
`CertCoord.mem_carrier_of_dets` (the same generic point-in-triangle fact the source certificates'
own (C2) checks use). Every column piece satisfies all three bounds after placement (the `y`/`l`
bounds mirror `scaledPiece_yBound`/`.gBound`'s pattern; `r`'s bound composes similarly), so
`column_piece_subset_delta4` closes containment for the last of `Δ_4`'s four regions. -/

noncomputable def lFun : Plane →ₗ[ℝ] ℝ := (48 * Real.sqrt 15) • xFun - (176:ℝ) • yFun
noncomputable def rFun : Plane →ₗ[ℝ] ℝ := (48 * Real.sqrt 15) • xFun + (176:ℝ) • yFun

theorem lFun_mkPt (x y : ℝ) : lFun (mkPt x y) = 48 * Real.sqrt 15 * x - 176 * y := by
  simp only [lFun, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, xFun_mkPt, yFun_mkPt]

theorem rFun_mkPt (x y : ℝ) : rFun (mkPt x y) = 48 * Real.sqrt 15 * x + 176 * y := by
  simp only [rFun, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, xFun_mkPt, yFun_mkPt]

theorem lFun_ne_zero : lFun ≠ 0 := by
  intro h
  have h2 : lFun (mkPt 1 0) = 48 * Real.sqrt 15 := by rw [lFun_mkPt]; ring
  rw [h] at h2
  simp only [LinearMap.zero_apply] at h2
  have hpos : (0:ℝ) < 48 * Real.sqrt 15 := by positivity
  linarith

noncomputable def lAff : Plane →ᵃ[ℝ] ℝ := lFun.toAffineMap
noncomputable def rAff : Plane →ᵃ[ℝ] ℝ := rFun.toAffineMap

theorem lAff_mkPt (x y : ℝ) : lAff (mkPt x y) = 48 * Real.sqrt 15 * x - 176 * y := lFun_mkPt x y
theorem rAff_mkPt (x y : ℝ) : rAff (mkPt x y) = 48 * Real.sqrt 15 * x + 176 * y := rFun_mkPt x y

theorem v_lrcoords :
    lAff Erdos634.PgramTiling22Bridge.v1 = 0 ∧
    lAff Erdos634.PgramTiling22Bridge.v2 = 2112 * Real.sqrt 15 ∧
    lAff Erdos634.PgramTiling22Bridge.v3 = 2112 * Real.sqrt 15 ∧
    lAff Erdos634.PgramTiling22Bridge.v4 = 0 ∧
    rAff Erdos634.PgramTiling22Bridge.v1 = 0 ∧
    rAff Erdos634.PgramTiling22Bridge.v2 = 2112 * Real.sqrt 15 ∧
    rAff Erdos634.PgramTiling22Bridge.v3 = 4224 * Real.sqrt 15 ∧
    rAff Erdos634.PgramTiling22Bridge.v4 = 2112 * Real.sqrt 15 := by
  have key : ∀ (q : PgramTiling22.Pt) (a b : ℤ),
      Erdos634.Z15Real.zx (q : Erdos634.Z15Real.ZPt) = (a, 0) →
      Erdos634.Z15Real.zy (q : Erdos634.Z15Real.ZPt) = (0, b) →
      lAff (mkPt (Erdos634.Z15Real.toR (Erdos634.Z15Real.zx (q : Erdos634.Z15Real.ZPt)))
          (Erdos634.Z15Real.toR (Erdos634.Z15Real.zy (q : Erdos634.Z15Real.ZPt))))
        = 48 * (a:ℝ) * Real.sqrt 15 - 176 * (b:ℝ) * Real.sqrt 15 ∧
      rAff (mkPt (Erdos634.Z15Real.toR (Erdos634.Z15Real.zx (q : Erdos634.Z15Real.ZPt)))
          (Erdos634.Z15Real.toR (Erdos634.Z15Real.zy (q : Erdos634.Z15Real.ZPt))))
        = 48 * (a:ℝ) * Real.sqrt 15 + 176 * (b:ℝ) * Real.sqrt 15 := by
    intro q a b hx hy
    constructor
    · rw [hx, hy, lAff_mkPt]; simp only [Erdos634.Z15Real.toR]; push_cast; ring
    · rw [hx, hy, rAff_mkPt]; simp only [Erdos634.Z15Real.toR]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (have h1 := (key PgramTiling22.q1 0 0 (by decide) (by decide)).1
       unfold Erdos634.PgramTiling22Bridge.v1 Erdos634.PgramTiling22Bridge.toZPt
       rw [h1]; ring)
    | (have h1 := (key PgramTiling22.q2 44 0 (by decide) (by decide)).1
       unfold Erdos634.PgramTiling22Bridge.v2 Erdos634.PgramTiling22Bridge.toZPt
       rw [h1]; ring)
    | (have h1 := (key PgramTiling22.q3 66 6 (by decide) (by decide)).1
       unfold Erdos634.PgramTiling22Bridge.v3 Erdos634.PgramTiling22Bridge.toZPt
       rw [h1]; ring)
    | (have h1 := (key PgramTiling22.q4 22 6 (by decide) (by decide)).1
       unfold Erdos634.PgramTiling22Bridge.v4 Erdos634.PgramTiling22Bridge.toZPt
       rw [h1]; ring)
    | (have h2 := (key PgramTiling22.q1 0 0 (by decide) (by decide)).2
       unfold Erdos634.PgramTiling22Bridge.v1 Erdos634.PgramTiling22Bridge.toZPt
       rw [h2]; ring)
    | (have h2 := (key PgramTiling22.q2 44 0 (by decide) (by decide)).2
       unfold Erdos634.PgramTiling22Bridge.v2 Erdos634.PgramTiling22Bridge.toZPt
       rw [h2]; ring)
    | (have h2 := (key PgramTiling22.q3 66 6 (by decide) (by decide)).2
       unfold Erdos634.PgramTiling22Bridge.v3 Erdos634.PgramTiling22Bridge.toZPt
       rw [h2]; ring)
    | (have h2 := (key PgramTiling22.q4 22 6 (by decide) (by decide)).2
       unfold Erdos634.PgramTiling22Bridge.v4 Erdos634.PgramTiling22Bridge.toZPt
       rw [h2]; ring)

theorem carrier_lBound :
    ∀ p ∈ Erdos634.PgramTiling22Bridge.carrier, 0 ≤ lAff p ∧ lAff p ≤ 2112 * Real.sqrt 15 := by
  have hconv : Convex ℝ {p : Plane | 0 ≤ lAff p ∧ lAff p ≤ 2112 * Real.sqrt 15} := by
    apply Convex.inter
    · exact (convex_Ici (0:ℝ)).affine_preimage lAff
    · exact (convex_Iic (2112 * Real.sqrt 15)).affine_preimage lAff
  have hsub : ({Erdos634.PgramTiling22Bridge.v1, Erdos634.PgramTiling22Bridge.v2,
      Erdos634.PgramTiling22Bridge.v3, Erdos634.PgramTiling22Bridge.v4} : Set Plane)
      ⊆ {p : Plane | 0 ≤ lAff p ∧ lAff p ≤ 2112 * Real.sqrt 15} := by
    have h1 := v_lrcoords.1
    have h2 := v_lrcoords.2.1
    have h3 := v_lrcoords.2.2.1
    have h4 := v_lrcoords.2.2.2.1
    have hpos : (0:ℝ) ≤ 2112 * Real.sqrt 15 := by positivity
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨h1.ge, by rw [h1]; exact hpos⟩
    · exact ⟨by rw [h2]; exact hpos, h2.le⟩
    · exact ⟨by rw [h3]; exact hpos, h3.le⟩
    · exact ⟨h4.ge, by rw [h4]; exact hpos⟩
  exact convexHull_min hsub hconv

theorem carrier_rBound :
    ∀ p ∈ Erdos634.PgramTiling22Bridge.carrier, 0 ≤ rAff p ∧ rAff p ≤ 4224 * Real.sqrt 15 := by
  have hconv : Convex ℝ {p : Plane | 0 ≤ rAff p ∧ rAff p ≤ 4224 * Real.sqrt 15} := by
    apply Convex.inter
    · exact (convex_Ici (0:ℝ)).affine_preimage rAff
    · exact (convex_Iic (4224 * Real.sqrt 15)).affine_preimage rAff
  have hsub : ({Erdos634.PgramTiling22Bridge.v1, Erdos634.PgramTiling22Bridge.v2,
      Erdos634.PgramTiling22Bridge.v3, Erdos634.PgramTiling22Bridge.v4} : Set Plane)
      ⊆ {p : Plane | 0 ≤ rAff p ∧ rAff p ≤ 4224 * Real.sqrt 15} := by
    have h1 := v_lrcoords.2.2.2.2.1
    have h2 := v_lrcoords.2.2.2.2.2.1
    have h3 := v_lrcoords.2.2.2.2.2.2.1
    have h4 := v_lrcoords.2.2.2.2.2.2.2
    have hpos : (0:ℝ) ≤ 4224 * Real.sqrt 15 := by positivity
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · refine ⟨h1.ge, ?_⟩; rw [h1]; nlinarith [Real.sqrt_nonneg (15:ℝ)]
    · refine ⟨?_, ?_⟩ <;> rw [h2] <;> nlinarith [Real.sqrt_nonneg (15:ℝ)]
    · refine ⟨?_, ?_⟩ <;> rw [h3] <;> nlinarith [Real.sqrt_nonneg (15:ℝ)]
    · refine ⟨?_, ?_⟩ <;> rw [h4] <;> nlinarith [Real.sqrt_nonneg (15:ℝ)]
  exact convexHull_min hsub hconv

theorem piece_lBound {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles) (i : Fin 3) :
    0 ≤ lAff ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i) ∧
    lAff ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i) ≤ 2112 * Real.sqrt 15 := by
  apply carrier_lBound
  apply Erdos634.PgramTiling22Bridge.pieceTri_subset_carrier ht
  exact subset_convexHull ℝ _ (Set.mem_range_self i)

theorem piece_rBound {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles) (i : Fin 3) :
    0 ≤ rAff ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i) ∧
    rAff ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i) ≤ 4224 * Real.sqrt 15 := by
  apply carrier_rBound
  apply Erdos634.PgramTiling22Bridge.pieceTri_subset_carrier ht
  exact subset_convexHull ℝ _ (Set.mem_range_self i)

theorem lAff_homothety (v p : Plane) (r : ℝ) :
    lAff (AffineMap.homothety v r p) = r * lAff p + (1 - r) * lAff v := by
  rw [AffineMap.homothety_apply, AffineMap.map_vadd, vadd_eq_add]
  have h1 : lAff.linear (r • (p -ᵥ v)) = r * lAff p - r * lAff v := by
    rw [map_smul]
    show r * lFun (p -ᵥ v) = _
    have h2 : lFun (p -ᵥ v) = lAff p - lAff v := by
      show lFun (p - v) = _
      rw [map_sub]; rfl
    rw [h2]; ring
  rw [h1]; ring

theorem rAff_homothety (v p : Plane) (r : ℝ) :
    rAff (AffineMap.homothety v r p) = r * rAff p + (1 - r) * rAff v := by
  rw [AffineMap.homothety_apply, AffineMap.map_vadd, vadd_eq_add]
  have h1 : rAff.linear (r • (p -ᵥ v)) = r * rAff p - r * rAff v := by
    rw [map_smul]
    show r * rFun (p -ᵥ v) = _
    have h2 : rFun (p -ᵥ v) = rAff p - rAff v := by
      show rFun (p - v) = _
      rw [map_sub]; rfl
    rw [h2]; ring
  rw [h1]; ring

theorem lAff_vadd (p w : Plane) : lAff (w +ᵥ p) = lAff w + lAff p := by
  rw [AffineMap.map_vadd, vadd_eq_add]; rfl

theorem rAff_vadd (p w : Plane) : rAff (w +ᵥ p) = rAff w + rAff p := by
  rw [AffineMap.map_vadd, vadd_eq_add]; rfl

theorem scaledPiece_lBound {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles) (i : Fin 3) :
    0 ≤ lAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ∧
    lAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ≤ 4224 * Real.sqrt 15 := by
  rw [Erdos634.Realizable.homothetyEquiv_apply, lAff_homothety, lAff_mkPt]
  have hb := piece_lBound ht i
  constructor <;> nlinarith [hb.1, hb.2]

theorem scaledPiece_rBound {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles) (i : Fin 3) :
    0 ≤ rAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ∧
    rAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ≤ 8448 * Real.sqrt 15 := by
  rw [Erdos634.Realizable.homothetyEquiv_apply, rAff_homothety, rAff_mkPt]
  have hb := piece_rBound ht i
  constructor <;> nlinarith [hb.1, hb.2]

/-- **Every placed column piece sits inside `Δ_4`.** A raw `PgramTiling22` piece, scaled ×2 about
the origin then translated by `w` with `0 ≤ lAff w` and `rAff w ≤ 8448√15` (satisfied by every
column/half combination: `lAff w = 4224√15·j ≥ 0`, `rAff w = 4224√15·(j+h) ≤ 8448√15` for
`j, h ∈ {0,1}`) — has carrier `⊆ Δ_4.carrier`. -/
theorem mem_delta4_of_bounds (a b : ℝ)
    (hy0 : 0 ≤ b) (hy1 : b ≤ 48 * Real.sqrt 15)
    (hl : 0 ≤ 48 * Real.sqrt 15 * a - 176 * b)
    (hr : 48 * Real.sqrt 15 * a + 176 * b ≤ 16896 * Real.sqrt 15) :
    mkPt a b ∈ delta4.carrier := by
  have hD : (0:ℝ) < Erdos634.CertCoord.det3 0 0 352 0 176 (48 * Real.sqrt 15) := by
    show 0 < (352 - 0) * (48 * Real.sqrt 15 - 0) - (176 - 0) * (0 - 0)
    have : (0:ℝ) < 352 * (48 * Real.sqrt 15) := by positivity
    nlinarith
  have h0 : 0 ≤ Erdos634.CertCoord.det3 a b 352 0 176 (48 * Real.sqrt 15) := by
    show 0 ≤ (352 - a) * (48 * Real.sqrt 15 - b) - (176 - a) * (0 - b)
    nlinarith [Real.sqrt_nonneg (15:ℝ)]
  have h1 : 0 ≤ Erdos634.CertCoord.det3 0 0 a b 176 (48 * Real.sqrt 15) := by
    show 0 ≤ (a - 0) * (48 * Real.sqrt 15 - 0) - (176 - 0) * (b - 0)
    nlinarith
  have h2 : 0 ≤ Erdos634.CertCoord.det3 0 0 352 0 a b := by
    show 0 ≤ (352 - 0) * (b - 0) - (a - 0) * (0 - 0)
    nlinarith
  exact Erdos634.CertCoord.mem_carrier_of_dets hD h0 h1 h2

theorem column_piece_subset_delta4 {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles)
    (w : Plane) (hw0 : 0 ≤ yAff w) (hwy1 : yAff w ≤ 24 * Real.sqrt 15)
    (hwl : 0 ≤ lAff w) (hwr : rAff w ≤ 8448 * Real.sqrt 15) :
    (mapTri (AffineEquiv.constVAdd ℝ Plane w)
      (mapTri (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num))
        (Erdos634.PgramTiling22Bridge.pieceTri ht))).carrier ⊆ delta4.carrier := by
  apply carrier_subset_of_pts_mem
  intro k
  show (AffineEquiv.constVAdd ℝ Plane w)
    ((Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num))
      ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)) ∈ delta4.carrier
  show w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
      ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k) ∈ delta4.carrier
  have hy := scaledPiece_yBound ht k
  have hl := scaledPiece_lBound ht k
  have hr := scaledPiece_rBound ht k
  have hyv : yAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
      ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)) = yAff w +
      yAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)) := yAff_vadd _ _
  have hlv : lAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
      ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)) = lAff w +
      lAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)) := lAff_vadd _ _
  have hrv : rAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
      ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)) = rAff w +
      rAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)) := rAff_vadd _ _
  have hpt : w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
      ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)
      = mkPt (xFun (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)))
        (yAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k))) := by
    ext j; fin_cases j
    · show _ = xFun _; rfl
    · show _ = yAff _; rfl
  rw [hpt]
  apply mem_delta4_of_bounds
  · rw [hyv]; linarith [hy.1]
  · rw [hyv]; linarith [hy.2, hwy1]
  · rw [show (48 * Real.sqrt 15 * xFun (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2
        (by norm_num) ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k))
        - 176 * yAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)))
        = lAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)) from rfl]
    rw [hlv]; linarith [hl.1, hwl]
  · rw [show (48 * Real.sqrt 15 * xFun (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2
        (by norm_num) ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k))
        + 176 * yAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)))
        = rAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts k)) from rfl]
    rw [hrv]; linarith [hr.2, hwr]
