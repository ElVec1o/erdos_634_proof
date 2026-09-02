import Erdos634.CollarPiecesM4

/-!
# The `m=2 → m=4` collar step — per-piece containment, matching `delta4Pieces`'s indexing

Erdős #634. `thm:realize12`'s existence half needs `AreaDet.ofDetCertificate`'s exact hypothesis
shape: `∀ i, (tile i).carrier ⊆ target.carrier` for `tile = delta4Pieces` (`Fin 176 → Tri`, from
`CollarPiecesM4.lean`). The existing containment facts (`CollarContainM4.lean`) are stated at the
*region* level (`apex_subset_delta4`/`corner_subset_delta4`, whole translated copies) or with a
`List`-membership index (`column_piece_subset_delta4`, `t ∈ PgramTiling22.tiles`) — neither matches
`delta4Pieces`'s `Fin`-indexed pieces directly. This file bridges both gaps.

**Correction found this turn**: `CollarPiecesM4.lean`'s `colVec` used `(88j, 12√15·h)`, but the
hand-derived geometry (`private/VERIFY_PLAN.md`, `column_piece_corner_disjoint`'s entry) is
`w = (88j+44h, 12√15·h)` — the `+44h` term was missing. Fixed in `CollarPiecesM4.lean` (this did
not affect `delta4_area_sum`'s correctness, since translation preserves area for *any* vector, but
it matters here: the corrected vectors are exactly what makes `column_piece_subset_delta4`'s bound
hypotheses (`yAff`/`lAff`/`rAff` at each of the 4 `(j,h)` combinations) actually hold.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.AreaDet
open Erdos634.Realizable Erdos634.TranslateDissection

/-- **Containment transports under any affine equivalence.** -/
theorem mapTri_subset {A B : Tri} (e : Plane ≃ᵃ[ℝ] Plane) (h : A.carrier ⊆ B.carrier) :
    (mapTri e A).carrier ⊆ (mapTri e B).carrier := by
  rw [mapTri_carrier, mapTri_carrier]
  exact Set.image_mono h

/-- **The apex piece indexed at `i`, contained in `Δ_4`** — composes `Tiling44Bridge`'s own (C2)
containment (`pieceTri_subset_target`) with `apex_subset_delta4` (region ⊆ `Δ_4`) via
`mapTri_subset`. -/
theorem apexPieceAt_subset_delta4 (i : Fin Tiling44.tiles.length) :
    (apexPieceAt i).carrier ⊆ delta4.carrier := by
  unfold apexPieceAt
  have hstep : (mapTri (transEquiv (mkPt 88 (24 * Real.sqrt 15))).toAffineEquiv
      Erdos634.Tiling44Bridge.targetTri).carrier ⊆ delta4.carrier := by
    have := apex_subset_delta4
    rwa [translateCongruentDissection_target] at this
  calc (mapTri (transEquiv (mkPt 88 (24 * Real.sqrt 15))).toAffineEquiv
        (Erdos634.Tiling44Bridge.pieceAt i)).carrier
      ⊆ (mapTri (transEquiv (mkPt 88 (24 * Real.sqrt 15))).toAffineEquiv
          Erdos634.Tiling44Bridge.targetTri).carrier :=
        mapTri_subset _ (Erdos634.Tiling44Bridge.pieceTri_subset_target (List.getElem_mem i.isLt))
    _ ⊆ delta4.carrier := hstep

/-- **The corner piece indexed at `i`, contained in `Δ_4`** — the same route, at `corner_subset_delta4`. -/
theorem cornerPieceAt_subset_delta4 (i : Fin Tiling44.tiles.length) :
    (cornerPieceAt i).carrier ⊆ delta4.carrier := by
  unfold cornerPieceAt
  have hstep : (mapTri (transEquiv (mkPt 176 0)).toAffineEquiv
      Erdos634.Tiling44Bridge.targetTri).carrier ⊆ delta4.carrier := by
    have := corner_subset_delta4
    rwa [translateCongruentDissection_target] at this
  calc (mapTri (transEquiv (mkPt 176 0)).toAffineEquiv
        (Erdos634.Tiling44Bridge.pieceAt i)).carrier
      ⊆ (mapTri (transEquiv (mkPt 176 0)).toAffineEquiv
          Erdos634.Tiling44Bridge.targetTri).carrier :=
        mapTri_subset _ (Erdos634.Tiling44Bridge.pieceTri_subset_target (List.getElem_mem i.isLt))
    _ ⊆ delta4.carrier := hstep

theorem colVec_yAff_bounds (j h : Fin 2) :
    0 ≤ yAff (colVec j h) ∧ yAff (colVec j h) ≤ 24 * Real.sqrt 15 := by
  unfold colVec
  rw [yAff_mkPt]
  fin_cases h <;> fin_cases j <;> norm_num

theorem colVec_lAff_bound (j h : Fin 2) : 0 ≤ lAff (colVec j h) := by
  unfold colVec
  rw [lAff_mkPt]
  fin_cases h <;> fin_cases j <;> norm_num <;> nlinarith [Real.sqrt_nonneg (15:ℝ)]

theorem colVec_rAff_bound (j h : Fin 2) : rAff (colVec j h) ≤ 8448 * Real.sqrt 15 := by
  unfold colVec
  rw [rAff_mkPt]
  fin_cases h <;> fin_cases j <;> norm_num <;> nlinarith [Real.sqrt_nonneg (15:ℝ)]

/-- **The column piece indexed at `(j, h, i)`, contained in `Δ_4`** — bridges
`column_piece_subset_delta4`'s `List`-membership index to `Fin`, and discharges its four bound
hypotheses at each of the corrected `colVec j h`. -/
theorem columnPieceAt_subset_delta4 (j h : Fin 2) (i : Fin PgramTiling22.tiles.length) :
    (columnPieceAt (colVec j h) i).carrier ⊆ delta4.carrier := by
  unfold columnPieceAt
  have := column_piece_subset_delta4 (List.getElem_mem i.isLt) (colVec j h)
    (colVec_yAff_bounds j h).1 (colVec_yAff_bounds j h).2
    (colVec_lAff_bound j h) (colVec_rAff_bound j h)
  convert this using 3
