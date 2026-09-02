import Erdos634.CollarAssembleM4

/-!
# The `m=2 → m=4` collar step — congruence, and the final `CongruentDissection 176` witness

Erdős #634. `delta4Dissection : Dissection 176` (`CollarAssembleM4.lean`) is a genuine flat
dissection of `Δ_4`, but `thm:realize12` needs a `CongruentDissection` — every piece congruent to
one fixed model tile. This file settles the open question from the previous session's entry: are
`Tiling44`'s and `PgramTiling22`'s piece shapes actually mutually congruent?

**Yes.** `Tiling44`'s model has squared side lengths `{256, 576, 1024}` (sides `16, 24, 32`).
`PgramTiling22`'s raw model has squared side lengths `{64, 144, 256}` (sides `8, 12, 16`) — exactly
`Tiling44`'s sides `÷2`. Since the column pieces are placed via the same `×2` homothety already
used throughout this construction (`CollarPiecesM4.lean`'s `columnPieceAt`), the scaled
`PgramTiling22` model has sides `{16, 24, 32}` — an *exact* match with `Tiling44`'s model, in the
same cyclic edge order (`(0,1)=16, (1,2)=24, (2,0)=32` on both), so `SssCongruent.congruent_of_dist`
applies directly with no relabelling.

Every piece of `delta4Pieces` is therefore congruent to `Tiling44`'s own model: `apexPieceAt`/
`cornerPieceAt` via translation of an already-congruent `Tiling44` piece (`Tri.Congruent.map_left`);
`columnPieceAt` via `PgramTiling22`'s own internal congruence, transported through the homothety
(`Realizable.mapTri_congruent`) to the scaled model, composed with the scaled-model-to-`Tiling44`
congruence just established, then translated.

**With (C1) congruence, (C2) containment, (C3) disjointness and (C4) area all in hand,
`delta4CongruentDissection : CongruentDissection 176` is the complete witness: a concrete
realization of `N = 176 = 11·4²` for the `m=2→m=4` step of `thm:realize12`'s existence half.**

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.AreaDet
open Erdos634.Realizable Erdos634.TranslateDissection

theorem tiling44_model01 :
    dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
      = 16 := by
  have h2 : dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1) ^ 2 = 256 := by
    rw [Erdos634.Tiling44Bridge.pieceTri_dist_sq _ Erdos634.Tiling44Bridge.headI_mem_tiles]
    have : Tiling44.dist2 (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 0)
        (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 1) = ((256:ℤ),(0:ℤ)) := by decide
    rw [this]; simp [Erdos634.Z15Real.toR]
  nlinarith [dist_nonneg (α := Plane)
    (x := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
    (y := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1), h2]

theorem tiling44_model12 :
    dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
      = 24 := by
  have h2 : dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2) ^ 2 = 576 := by
    rw [Erdos634.Tiling44Bridge.pieceTri_dist_sq _ Erdos634.Tiling44Bridge.headI_mem_tiles]
    have : Tiling44.dist2 (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 1)
        (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 2) = ((576:ℤ),(0:ℤ)) := by decide
    rw [this]; simp [Erdos634.Z15Real.toR]
  nlinarith [dist_nonneg (α := Plane)
    (x := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
    (y := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2), h2]

theorem tiling44_model20 :
    dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
      = 32 := by
  have h2 : dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0) ^ 2 = 1024 := by
    rw [Erdos634.Tiling44Bridge.pieceTri_dist_sq _ Erdos634.Tiling44Bridge.headI_mem_tiles]
    have : Tiling44.dist2 (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 2)
        (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 0) = ((1024:ℤ),(0:ℤ)) := by decide
    rw [this]; simp [Erdos634.Z15Real.toR]
  nlinarith [dist_nonneg (α := Plane)
    (x := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
    (y := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0), h2]

/-- **The scaled `PgramTiling22` model is congruent to the `Tiling44` model.** -/
theorem scaledPgramModel_congruent_tiling44Model :
    (mapTri (homothetyEquiv (mkPt 0 0) 2 (by norm_num))
      (Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles)).Congruent
      (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) := by
  apply Erdos634.SssCongruent.congruent_of_dist
  intro i j
  show dist (homothetyEquiv (mkPt 0 0) 2 (by norm_num)
      ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts i))
    (homothetyEquiv (mkPt 0 0) 2 (by norm_num)
      ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts j)) = _
  rw [homothetyEquiv_apply, homothetyEquiv_apply, dist_homothety]
  have hp2 := Erdos634.PgramTiling22Bridge.model_sides
  have hp01 : dist ((Erdos634.PgramTiling22Bridge.pieceTri
        Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 0)
      ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 1)
      = 8 := by
    nlinarith [dist_nonneg (α := Plane)
      (x := (Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 0)
      (y := (Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 1),
      hp2.1]
  have hp12 : dist ((Erdos634.PgramTiling22Bridge.pieceTri
        Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 1)
      ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 2)
      = 12 := by
    nlinarith [dist_nonneg (α := Plane)
      (x := (Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 1)
      (y := (Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 2),
      hp2.2.1]
  have hp20 : dist ((Erdos634.PgramTiling22Bridge.pieceTri
        Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 2)
      ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 0)
      = 16 := by
    nlinarith [dist_nonneg (α := Plane)
      (x := (Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 2)
      (y := (Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 0),
      hp2.2.2]
  have goal : ∀ a b : Fin 3,
      |(2:ℝ)| * dist ((Erdos634.PgramTiling22Bridge.pieceTri
          Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts a)
        ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts b)
      = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts a)
        ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts b) := by
    intro a b
    fin_cases a <;> fin_cases b
    · show |(2:ℝ)| * dist ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 0) ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 0) = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0) ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
      rw [dist_self]; norm_num
    · show |(2:ℝ)| * dist ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 0) ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 1) = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0) ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
      rw [hp01, tiling44_model01]; norm_num
    · show |(2:ℝ)| * dist ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 0) ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 2) = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0) ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
      rw [dist_comm, hp20, dist_comm, tiling44_model20]; norm_num
    · show |(2:ℝ)| * dist ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 1) ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 0) = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1) ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
      rw [dist_comm, hp01, dist_comm, tiling44_model01]; norm_num
    · show |(2:ℝ)| * dist ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 1) ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 1) = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1) ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
      rw [dist_self]; norm_num
    · show |(2:ℝ)| * dist ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 1) ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 2) = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1) ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
      rw [hp12, tiling44_model12]; norm_num
    · show |(2:ℝ)| * dist ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 2) ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 0) = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2) ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
      rw [hp20, tiling44_model20]; norm_num
    · show |(2:ℝ)| * dist ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 2) ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 1) = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2) ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
      rw [dist_comm, hp12, dist_comm, tiling44_model12]; norm_num
    · show |(2:ℝ)| * dist ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 2) ((Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles).pts 2) = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2) ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
      rw [dist_self]; norm_num
  exact goal i j

theorem apexPieceAt_congruent (i : Fin Tiling44.tiles.length) :
    (apexPieceAt i).Congruent (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) := by
  unfold apexPieceAt
  exact (Erdos634.Tiling44Bridge.pieceTri_congruent (List.getElem_mem i.isLt)).map_left (transEquiv _)

theorem cornerPieceAt_congruent (i : Fin Tiling44.tiles.length) :
    (cornerPieceAt i).Congruent (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) := by
  unfold cornerPieceAt
  exact (Erdos634.Tiling44Bridge.pieceTri_congruent (List.getElem_mem i.isLt)).map_left (transEquiv _)

theorem columnPieceAt_congruent (w : Plane) (i : Fin PgramTiling22.tiles.length) :
    (columnPieceAt w i).Congruent
      (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) := by
  unfold columnPieceAt
  have h1 := Erdos634.PgramTiling22Bridge.pieceTri_congruent (List.getElem_mem i.isLt)
  have h2 := Erdos634.Realizable.mapTri_congruent (mkPt 0 0) 2 (by norm_num) h1
  exact (h2.trans scaledPgramModel_congruent_tiling44Model).map_left (transEquiv w)

/-- **`delta4PiecesAux` satisfies (C1) congruence to a fixed model.** -/
theorem delta4PiecesAux_congruent :
    ∀ i, (delta4PiecesAux i).Congruent
      (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) := by
  unfold delta4PiecesAux
  apply forall_fin_append (F := fun (T : Tri) => T.Congruent
    (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles))
  · exact apexPieceAt_congruent
  apply forall_fin_append (F := fun (T : Tri) => T.Congruent
    (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles))
  · exact cornerPieceAt_congruent
  apply forall_fin_append (F := fun (T : Tri) => T.Congruent
    (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles))
  · exact columnPieceAt_congruent (colVec 0 0)
  apply forall_fin_append (F := fun (T : Tri) => T.Congruent
    (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles))
  · exact columnPieceAt_congruent (colVec 0 1)
  apply forall_fin_append (F := fun (T : Tri) => T.Congruent
    (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles))
  · exact columnPieceAt_congruent (colVec 1 0)
  · exact columnPieceAt_congruent (colVec 1 1)

theorem delta4Pieces_congruent :
    ∀ i : Fin 176, (delta4Pieces i).Congruent
      (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) := by
  intro i
  exact delta4PiecesAux_congruent _

noncomputable def delta4CongruentDissection : CongruentDissection 176 where
  toDissection := Erdos634.AreaDet.ofDetCertificate delta4 delta4Pieces
    delta4Pieces_subset_delta4 delta4Pieces_pairwise delta4_area_sum
  model := Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles
  tiles_congruent := delta4Pieces_congruent
