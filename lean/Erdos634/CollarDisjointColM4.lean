import Erdos634.CollarPieceContainM4

/-!
# The `m=2 → m=4` collar step — cross-column-copy disjointness (new geometry)

Erdős #634. `thm:realize12`'s existence half needs `AreaDet.ofDetCertificate`'s (C3) hypothesis:
pairwise disjoint interiors for all `176` pieces of `delta4Pieces`. The prior disjointness work
(`CollarDisjointM4.lean`) covers every region-pair EXCEPT one: two column pieces from *different*
`(j,h)` positions among the four column copies were never checked against each other — a genuinely
new geometric case, not a port, since it needed its own separating functional.

**The new functional**: `hFun := 12√15·x - 44·y`, matching the slanted right edge of column `0`'s
scaled parallelogram (its direction, `(44, 12√15)`, is exactly the direction `colVec`'s own
diagonal `h`-shift moves along — so `hFun` is *invariant* under that shift, and only detects the
`j`-shift). At the four `colVec j h` positions: `hAff (colVec j h) = 1056√15·j` (checked in Lean,
`colVec_hAff`) — separates column `j=0` from column `j=1` cleanly, independent of `h`.

Combined with the pre-existing `yAff`-based separation for same-column, different-half pairs
(`column_h_disjoint`, the same pattern `column_piece_apex_disjoint` already uses), this closes the
last open region-pair: `columnPieceAt_disjoint` gives disjointness for any two of the four column
copies, dispatching on whether `j = j'`.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.CertGeom
open Erdos634.Realizable Erdos634.TranslateDissection

noncomputable def hFun : Plane →ₗ[ℝ] ℝ := (12 * Real.sqrt 15) • xFun - (44:ℝ) • yFun

theorem hFun_mkPt (x y : ℝ) : hFun (mkPt x y) = 12 * Real.sqrt 15 * x - 44 * y := by
  simp only [hFun, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, xFun_mkPt, yFun_mkPt]

theorem hFun_ne_zero : hFun ≠ 0 := by
  intro h
  have h2 : hFun (mkPt 1 0) = 12 * Real.sqrt 15 := by rw [hFun_mkPt]; ring
  rw [h] at h2
  simp only [LinearMap.zero_apply] at h2
  have hpos : (0:ℝ) < 12 * Real.sqrt 15 := by positivity
  linarith

noncomputable def hAff : Plane →ᵃ[ℝ] ℝ := hFun.toAffineMap

theorem hAff_linear_ne_zero : hAff.linear ≠ 0 := hFun_ne_zero
theorem hAff_mkPt (x y : ℝ) : hAff (mkPt x y) = 12 * Real.sqrt 15 * x - 44 * y := hFun_mkPt x y

theorem hAff_homothety (v p : Plane) (r : ℝ) :
    hAff (AffineMap.homothety v r p) = r * hAff p + (1 - r) * hAff v := by
  rw [AffineMap.homothety_apply, AffineMap.map_vadd, vadd_eq_add]
  have h1 : hAff.linear (r • (p -ᵥ v)) = r * hAff p - r * hAff v := by
    rw [map_smul]
    show r * hFun (p -ᵥ v) = _
    have h2 : hFun (p -ᵥ v) = hAff p - hAff v := by
      show hFun (p - v) = _
      rw [map_sub]; rfl
    rw [h2]; ring
  rw [h1]; ring

theorem hAff_vadd (p w : Plane) : hAff (w +ᵥ p) = hAff w + hAff p := by
  rw [AffineMap.map_vadd, vadd_eq_add]; rfl

theorem v_hcoords :
    hAff Erdos634.PgramTiling22Bridge.v1 = 0 ∧
    hAff Erdos634.PgramTiling22Bridge.v2 = 528 * Real.sqrt 15 ∧
    hAff Erdos634.PgramTiling22Bridge.v3 = 528 * Real.sqrt 15 ∧
    hAff Erdos634.PgramTiling22Bridge.v4 = 0 := by
  have key : ∀ (q : PgramTiling22.Pt) (a b : ℤ),
      Erdos634.Z15Real.zx (q : Erdos634.Z15Real.ZPt) = (a, 0) →
      Erdos634.Z15Real.zy (q : Erdos634.Z15Real.ZPt) = (0, b) →
      hAff (mkPt (Erdos634.Z15Real.toR (Erdos634.Z15Real.zx (q : Erdos634.Z15Real.ZPt)))
          (Erdos634.Z15Real.toR (Erdos634.Z15Real.zy (q : Erdos634.Z15Real.ZPt))))
        = 12 * (a:ℝ) * Real.sqrt 15 - 44 * (b:ℝ) * Real.sqrt 15 := by
    intro q a b hx hy
    rw [hx, hy, hAff_mkPt]
    simp only [Erdos634.Z15Real.toR]
    push_cast
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := key PgramTiling22.q1 0 0 (by decide) (by decide)
    unfold Erdos634.PgramTiling22Bridge.v1 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; ring
  · have := key PgramTiling22.q2 44 0 (by decide) (by decide)
    unfold Erdos634.PgramTiling22Bridge.v2 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; ring
  · have := key PgramTiling22.q3 66 6 (by decide) (by decide)
    unfold Erdos634.PgramTiling22Bridge.v3 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; ring
  · have := key PgramTiling22.q4 22 6 (by decide) (by decide)
    unfold Erdos634.PgramTiling22Bridge.v4 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; ring

theorem carrier_hBound :
    ∀ p ∈ Erdos634.PgramTiling22Bridge.carrier, 0 ≤ hAff p ∧ hAff p ≤ 528 * Real.sqrt 15 := by
  have hconv : Convex ℝ {p : Plane | 0 ≤ hAff p ∧ hAff p ≤ 528 * Real.sqrt 15} := by
    apply Convex.inter
    · exact (convex_Ici (0:ℝ)).affine_preimage hAff
    · exact (convex_Iic (528 * Real.sqrt 15)).affine_preimage hAff
  have hsub : ({Erdos634.PgramTiling22Bridge.v1, Erdos634.PgramTiling22Bridge.v2,
      Erdos634.PgramTiling22Bridge.v3, Erdos634.PgramTiling22Bridge.v4} : Set Plane)
      ⊆ {p : Plane | 0 ≤ hAff p ∧ hAff p ≤ 528 * Real.sqrt 15} := by
    have h1 := v_hcoords.1
    have h2 := v_hcoords.2.1
    have h3 := v_hcoords.2.2.1
    have h4 := v_hcoords.2.2.2
    have hpos : (0:ℝ) ≤ 528 * Real.sqrt 15 := by positivity
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨h1.ge, by rw [h1]; exact hpos⟩
    · exact ⟨by rw [h2]; exact hpos, h2.le⟩
    · exact ⟨by rw [h3]; exact hpos, h3.le⟩
    · exact ⟨h4.ge, by rw [h4]; exact hpos⟩
  exact convexHull_min hsub hconv

theorem piece_hBound {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles) (i : Fin 3) :
    0 ≤ hAff ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i) ∧
    hAff ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i) ≤ 528 * Real.sqrt 15 := by
  apply carrier_hBound
  apply Erdos634.PgramTiling22Bridge.pieceTri_subset_carrier ht
  exact subset_convexHull ℝ _ (Set.mem_range_self i)

theorem scaledPiece_hBound {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles) (i : Fin 3) :
    0 ≤ hAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ∧
    hAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ≤ 1056 * Real.sqrt 15 := by
  rw [Erdos634.Realizable.homothetyEquiv_apply, hAff_homothety, hAff_mkPt]
  have hb := piece_hBound ht i
  constructor <;> nlinarith [hb.1, hb.2]

theorem carrier_hAff_ge (T : Tri) (c : ℝ) (h : ∀ i, c ≤ hAff (T.pts i)) :
    ∀ y ∈ T.carrier, c ≤ hAff y := by
  have hg : ∀ i, 0 ≤ (hAff - AffineMap.const ℝ Plane c) (T.pts i) := by
    intro i
    show 0 ≤ hAff (T.pts i) - c
    linarith [h i]
  have hsub := Tri.carrier_subset_halfplane_affine T (hAff - AffineMap.const ℝ Plane c) hg
  intro y hy
  have h2 : 0 ≤ hAff y - c := hsub y hy
  linarith

theorem carrier_hAff_le (T : Tri) (c : ℝ) (h : ∀ i, hAff (T.pts i) ≤ c) :
    ∀ y ∈ T.carrier, hAff y ≤ c := by
  have hg : ∀ i, 0 ≤ (AffineMap.const ℝ Plane c - hAff) (T.pts i) := by
    intro i
    show 0 ≤ c - hAff (T.pts i)
    linarith [h i]
  have hsub := Tri.carrier_subset_halfplane_affine T (AffineMap.const ℝ Plane c - hAff) hg
  intro y hy
  have h2 : 0 ≤ c - hAff y := hsub y hy
  linarith

/-- **Two placed column pieces from different columns (`j ≠ j'`) are interior-disjoint.**
Separated by `hAff = 1056√15·max(j,j')`. -/
theorem column_j_disjoint {t t' : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles)
    (ht' : t' ∈ PgramTiling22.tiles) (w w' : Plane)
    (hw : hAff w = 0 ∨ hAff w = 1056 * Real.sqrt 15)
    (hw' : hAff w' = 0 ∨ hAff w' = 1056 * Real.sqrt 15) (hne : hAff w ≠ hAff w') :
    Disjoint
      (interior (mapTri (AffineEquiv.constVAdd ℝ Plane w)
        (mapTri (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num))
          (Erdos634.PgramTiling22Bridge.pieceTri ht))).carrier)
      (interior (mapTri (AffineEquiv.constVAdd ℝ Plane w')
        (mapTri (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num))
          (Erdos634.PgramTiling22Bridge.pieceTri ht'))).carrier) := by
  have hcases : (hAff w = 0 ∧ hAff w' = 1056 * Real.sqrt 15) ∨
      (hAff w = 1056 * Real.sqrt 15 ∧ hAff w' = 0) := by
    rcases hw with hw | hw <;> rcases hw' with hw' | hw' <;>
      first | (left; exact ⟨hw, hw'⟩) | (right; exact ⟨hw, hw'⟩) | (exfalso; exact hne (hw.trans hw'.symm))
  rcases hcases with ⟨hw, hw'⟩ | ⟨hw, hw'⟩
  · refine interiors_disjoint_of_separating hAff hAff_linear_ne_zero (1056 * Real.sqrt 15) ?_ ?_
    · apply carrier_hAff_le _ (1056 * Real.sqrt 15)
      intro i
      show hAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ≤ _
      rw [hAff_vadd, hw]
      have hb := scaledPiece_hBound ht i
      linarith [hb.2]
    · apply carrier_hAff_ge _ (1056 * Real.sqrt 15)
      intro i
      show _ ≤ hAff (w' +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht').pts i))
      rw [hAff_vadd, hw']
      have hb := scaledPiece_hBound ht' i
      linarith [hb.1]
  · apply Disjoint.symm
    refine interiors_disjoint_of_separating hAff hAff_linear_ne_zero (1056 * Real.sqrt 15) ?_ ?_
    · apply carrier_hAff_le _ (1056 * Real.sqrt 15)
      intro i
      show hAff (w' +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht').pts i)) ≤ _
      rw [hAff_vadd, hw']
      have hb := scaledPiece_hBound ht' i
      linarith [hb.2]
    · apply carrier_hAff_ge _ (1056 * Real.sqrt 15)
      intro i
      show _ ≤ hAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i))
      rw [hAff_vadd, hw]
      have hb := scaledPiece_hBound ht i
      linarith [hb.1]

/-- **Two placed column pieces at the same column but different halves (`h ≠ h'`) are
interior-disjoint.** Separated by `yAff = 12√15`, the same functional/pattern
`column_piece_apex_disjoint` uses. -/
theorem column_h_disjoint {t t' : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles)
    (ht' : t' ∈ PgramTiling22.tiles) (w w' : Plane)
    (hw : yAff w = 0 ∨ yAff w = 12 * Real.sqrt 15)
    (hw' : yAff w' = 0 ∨ yAff w' = 12 * Real.sqrt 15) (hne : yAff w ≠ yAff w') :
    Disjoint
      (interior (mapTri (AffineEquiv.constVAdd ℝ Plane w)
        (mapTri (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num))
          (Erdos634.PgramTiling22Bridge.pieceTri ht))).carrier)
      (interior (mapTri (AffineEquiv.constVAdd ℝ Plane w')
        (mapTri (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num))
          (Erdos634.PgramTiling22Bridge.pieceTri ht'))).carrier) := by
  have hcases : (yAff w = 0 ∧ yAff w' = 12 * Real.sqrt 15) ∨
      (yAff w = 12 * Real.sqrt 15 ∧ yAff w' = 0) := by
    rcases hw with hw | hw <;> rcases hw' with hw' | hw' <;>
      first | (left; exact ⟨hw, hw'⟩) | (right; exact ⟨hw, hw'⟩) | (exfalso; exact hne (hw.trans hw'.symm))
  rcases hcases with ⟨hw, hw'⟩ | ⟨hw, hw'⟩
  · refine interiors_disjoint_of_separating yAff yAff_linear_ne_zero (12 * Real.sqrt 15) ?_ ?_
    · apply carrier_yAff_le _ (12 * Real.sqrt 15)
      intro i
      show yAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ≤ _
      rw [yAff_vadd, hw]
      have hb := scaledPiece_yBound ht i
      linarith [hb.2]
    · apply carrier_yAff_ge _ (12 * Real.sqrt 15)
      intro i
      show _ ≤ yAff (w' +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht').pts i))
      rw [yAff_vadd, hw']
      have hb := scaledPiece_yBound ht' i
      linarith [hb.1]
  · apply Disjoint.symm
    refine interiors_disjoint_of_separating yAff yAff_linear_ne_zero (12 * Real.sqrt 15) ?_ ?_
    · apply carrier_yAff_le _ (12 * Real.sqrt 15)
      intro i
      show yAff (w' +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht').pts i)) ≤ _
      rw [yAff_vadd, hw']
      have hb := scaledPiece_yBound ht' i
      linarith [hb.2]
    · apply carrier_yAff_ge _ (12 * Real.sqrt 15)
      intro i
      show _ ≤ yAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
          ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i))
      rw [yAff_vadd, hw]
      have hb := scaledPiece_yBound ht i
      linarith [hb.1]

theorem colVec_yAff (j h : Fin 2) : yAff (colVec j h) = 12 * Real.sqrt 15 * h.val := by
  unfold colVec; rw [yAff_mkPt]

theorem colVec_hAff (j h : Fin 2) : hAff (colVec j h) = 1056 * Real.sqrt 15 * j.val := by
  unfold colVec; rw [hAff_mkPt]
  fin_cases h <;> fin_cases j <;> norm_num <;> ring

/-- **Two column pieces at different `(j,h)` positions, contained in `Δ_4`, are
interior-disjoint.** Dispatches to `column_j_disjoint` (different column) or `column_h_disjoint`
(same column, different half). -/
theorem columnPieceAt_disjoint (j h j' h' : Fin 2) (i i' : Fin PgramTiling22.tiles.length)
    (hne : (j, h) ≠ (j', h')) :
    Disjoint (interior (columnPieceAt (colVec j h) i).carrier)
      (interior (columnPieceAt (colVec j' h') i').carrier) := by
  unfold columnPieceAt
  by_cases hj : j = j'
  · subst hj
    have hh : h ≠ h' := fun heq => hne (by rw [heq])
    apply column_h_disjoint (List.getElem_mem i.isLt) (List.getElem_mem i'.isLt)
    · rw [colVec_yAff]; fin_cases h <;> simp
    · rw [colVec_yAff]; fin_cases h' <;> simp
    · rw [colVec_yAff, colVec_yAff]
      fin_cases h <;> fin_cases h' <;> simp_all
  · apply column_j_disjoint (List.getElem_mem i.isLt) (List.getElem_mem i'.isLt)
    · rw [colVec_hAff]; fin_cases j <;> simp
    · rw [colVec_hAff]; fin_cases j' <;> simp
    · rw [colVec_hAff, colVec_hAff]
      fin_cases j <;> fin_cases j' <;> simp_all
