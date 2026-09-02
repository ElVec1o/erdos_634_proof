import Erdos634.CollarDisjointColM4

/-!
# The `m=2 → m=4` collar step — final assembly: `hsub` and `hdisj` for `Fin 176`

Erdős #634. `thm:realize12`'s existence half needs `AreaDet.ofDetCertificate`'s exact hypothesis
shape for `delta4Pieces : Fin 176 → Tri` (`CollarPiecesM4.lean`): `hsub : ∀ i, (tile i).carrier ⊆
target.carrier`, `hdisj : Pairwise (fun i j => Disjoint (interior (tile i).carrier) (interior
(tile j).carrier))`, and `hdet` (already done, `delta4_area_sum`). Every ingredient for `hsub`
(per-piece containment, `CollarPieceContainM4.lean`) and `hdisj` (every named region-pair,
`CollarDisjointM4.lean`/`CollarDisjointColM4.lean`) already exists — what was missing was the
index bookkeeping to dispatch an arbitrary `i : Fin 176` (for `hsub`) or `i ≠ j : Fin 176` (for
`hdisj`) to the right one of these facts, by which of the six `Fin.append` blocks (apex, corner,
4 column copies) it falls in.

This file supplies two small general combinators — `forall_fin_append` (splits `∀ i, F (Fin.append
f g i)` into the two component `∀`s, the `Prop`-valued cousin of `CollarPiecesM4`'s `sum_fin_append`)
and `pairwise_fin_append` (splits `Pairwise` over `Fin.append f g` into within-`f`, within-`g`, and
cross `f`-`g` disjointness, given `R` symmetric) — then chains them through the same six-block tree
`delta4PiecesAux` uses, mirroring `delta4PiecesAux_area_sum`'s own five-step `sum_fin_append`
chain. `hsub` closes directly; `hdisj` needs one bridging fact per pair of blocks (built here:
`apexPieceAt_disjoint_cornerPieceAt`, `apexPieceAt_disjoint_columnPieceAt`,
`cornerPieceAt_disjoint_columnPieceAt`, plus the within-block `*_pairwise` facts) via a general
`disjoint_of_subset` (containment transports disjointness the same way it transports through
`mapTri`, via `Set.Disjoint.mono`/`interior_mono`).

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.CertGeom
open Erdos634.Realizable Erdos634.TranslateDissection Erdos634.AreaDet

theorem disjoint_of_subset {A A' B B' : Tri} (h1 : A.carrier ⊆ A'.carrier)
    (h2 : B.carrier ⊆ B'.carrier) (hd : Disjoint (interior A'.carrier) (interior B'.carrier)) :
    Disjoint (interior A.carrier) (interior B.carrier) :=
  hd.mono (interior_mono h1) (interior_mono h2)

theorem apexPieceAt_subset_apexRegion (i : Fin Tiling44.tiles.length) :
    (apexPieceAt i).carrier ⊆
      (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.carrier := by
  unfold apexPieceAt
  rw [translateCongruentDissection_target]
  exact mapTri_subset _ (Erdos634.Tiling44Bridge.pieceTri_subset_target (List.getElem_mem i.isLt))

theorem cornerPieceAt_subset_cornerRegion (i : Fin Tiling44.tiles.length) :
    (cornerPieceAt i).carrier ⊆
      (translateCongruentDissection (mkPt 176 0)
        Erdos634.Tiling44Bridge.dissection).target.carrier := by
  unfold cornerPieceAt
  rw [translateCongruentDissection_target]
  exact mapTri_subset _ (Erdos634.Tiling44Bridge.pieceTri_subset_target (List.getElem_mem i.isLt))

/-- **Every apex piece is disjoint from every corner piece.** -/
theorem apexPieceAt_disjoint_cornerPieceAt (i i' : Fin Tiling44.tiles.length) :
    Disjoint (interior (apexPieceAt i).carrier) (interior (cornerPieceAt i').carrier) :=
  disjoint_of_subset (apexPieceAt_subset_apexRegion i) (cornerPieceAt_subset_cornerRegion i')
    apex_corner_disjoint

theorem colVec_yAff' (j h : Fin 2) :
    yAff (colVec j h) = 0 ∨ yAff (colVec j h) = 12 * Real.sqrt 15 := by
  rw [colVec_yAff]; fin_cases h <;> simp

theorem colVec_gAff (j h : Fin 2) : gAff (colVec j h) = 2112 * Real.sqrt 15 * j.val := by
  unfold colVec; rw [gAff_mkPt]
  fin_cases h <;> fin_cases j <;> norm_num <;> ring

theorem colVec_gAff' (j h : Fin 2) :
    gAff (colVec j h) = 0 ∨ gAff (colVec j h) = 2112 * Real.sqrt 15 := by
  rw [colVec_gAff]; fin_cases j <;> simp

/-- **Every apex piece is disjoint from every column piece.** -/
theorem apexPieceAt_disjoint_columnPieceAt (i : Fin Tiling44.tiles.length) (j h : Fin 2)
    (i' : Fin PgramTiling22.tiles.length) :
    Disjoint (interior (apexPieceAt i).carrier)
      (interior (columnPieceAt (colVec j h) i').carrier) := by
  unfold columnPieceAt
  exact disjoint_of_subset (apexPieceAt_subset_apexRegion i) (le_refl _)
    (column_piece_apex_disjoint (List.getElem_mem i'.isLt) (colVec j h) (colVec_yAff' j h)).symm

/-- **Every corner piece is disjoint from every column piece.** -/
theorem cornerPieceAt_disjoint_columnPieceAt (i : Fin Tiling44.tiles.length) (j h : Fin 2)
    (i' : Fin PgramTiling22.tiles.length) :
    Disjoint (interior (cornerPieceAt i).carrier)
      (interior (columnPieceAt (colVec j h) i').carrier) := by
  unfold columnPieceAt
  exact disjoint_of_subset (cornerPieceAt_subset_cornerRegion i) (le_refl _)
    (column_piece_corner_disjoint (List.getElem_mem i'.isLt) (colVec j h) (colVec_gAff' j h)).symm

/-- **Any two distinct apex pieces are disjoint.** -/
theorem apexPieceAt_pairwise :
    Pairwise (fun i j : Fin Tiling44.tiles.length =>
      Disjoint (interior (apexPieceAt i).carrier) (interior (apexPieceAt j).carrier)) := by
  intro i j hij
  unfold apexPieceAt
  exact translated_tiling44_interiors_disjoint (mkPt 88 (24 * Real.sqrt 15)) hij

/-- **Any two distinct corner pieces are disjoint.** -/
theorem cornerPieceAt_pairwise :
    Pairwise (fun i j : Fin Tiling44.tiles.length =>
      Disjoint (interior (cornerPieceAt i).carrier) (interior (cornerPieceAt j).carrier)) := by
  intro i j hij
  unfold cornerPieceAt
  exact translated_tiling44_interiors_disjoint (mkPt 176 0) hij

/-- **Any two distinct pieces of the same placed column copy are disjoint.** -/
theorem columnPieceAt_pairwise (j h : Fin 2) :
    Pairwise (fun i i' : Fin PgramTiling22.tiles.length =>
      Disjoint (interior (columnPieceAt (colVec j h) i).carrier)
        (interior (columnPieceAt (colVec j h) i').carrier)) := by
  intro i i' hii'
  unfold columnPieceAt
  have := placed_pieces_interiors_disjoint (List.getElem_mem i.isLt) (List.getElem_mem i'.isLt)
    (Erdos634.PgramTiling22Bridge.tiles_getElem_inj i i' hii') (colVec j h)
  convert this using 3

theorem forall_fin_append {α : Type*} (m n : ℕ) (F : α → Prop) (f : Fin m → α) (g : Fin n → α)
    (hf : ∀ i, F (f i)) (hg : ∀ i, F (g i)) : ∀ i : Fin (m + n), F (Fin.append f g i) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; exact hf j
  · rw [Fin.append_right]; exact hg j

/-- **`delta4PiecesAux` satisfies (C2) containment.** -/
theorem delta4PiecesAux_subset_delta4 :
    ∀ i, (delta4PiecesAux i).carrier ⊆ delta4.carrier := by
  unfold delta4PiecesAux
  apply forall_fin_append (F := fun (T : Tri) => T.carrier ⊆ delta4.carrier)
  · exact apexPieceAt_subset_delta4
  apply forall_fin_append (F := fun (T : Tri) => T.carrier ⊆ delta4.carrier)
  · exact cornerPieceAt_subset_delta4
  apply forall_fin_append (F := fun (T : Tri) => T.carrier ⊆ delta4.carrier)
  · exact columnPieceAt_subset_delta4 0 0
  apply forall_fin_append (F := fun (T : Tri) => T.carrier ⊆ delta4.carrier)
  · exact columnPieceAt_subset_delta4 0 1
  apply forall_fin_append (F := fun (T : Tri) => T.carrier ⊆ delta4.carrier)
  · exact columnPieceAt_subset_delta4 1 0
  · exact columnPieceAt_subset_delta4 1 1

/-- **`delta4Pieces` satisfies (C2) containment** — exactly `AreaDet.ofDetCertificate`'s `hsub`. -/
theorem delta4Pieces_subset_delta4 :
    ∀ i : Fin 176, (delta4Pieces i).carrier ⊆ delta4.carrier := by
  intro i
  exact delta4PiecesAux_subset_delta4 _

theorem pairwise_fin_append {α : Type*} (m n : ℕ) (R : α → α → Prop) (hsymm : Symmetric R)
    (f : Fin m → α) (g : Fin n → α)
    (hf : Pairwise (fun i j : Fin m => R (f i) (f j)))
    (hg : Pairwise (fun i j : Fin n => R (g i) (g j)))
    (hcross : ∀ (a : Fin m) (b : Fin n), R (f a) (g b)) :
    Pairwise (fun i j : Fin (m + n) => R (Fin.append f g i) (Fin.append f g j)) := by
  intro i j hij
  revert hij
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    (refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;> intro hij)
  · rw [Fin.append_left, Fin.append_left]
    apply hf
    intro heq; apply hij; rw [heq]
  · rw [Fin.append_left, Fin.append_right]; exact hcross a b
  · rw [Fin.append_right, Fin.append_left]; exact hsymm (hcross b a)
  · rw [Fin.append_right, Fin.append_right]
    apply hg
    intro heq; apply hij; rw [heq]

/-- Cross-disjointness of column copy `(0,0)` against the whole tail `c01 ++ c10 ++ c11`. -/
theorem c00_tail_disjoint (a : Fin PgramTiling22.tiles.length) :
    ∀ b : Fin (PgramTiling22.tiles.length + (PgramTiling22.tiles.length + PgramTiling22.tiles.length)),
      Disjoint (interior (columnPieceAt (colVec 0 0) a).carrier)
        (interior ((Fin.append (columnPieceAt (colVec 0 1))
          (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))) b).carrier) := by
  apply forall_fin_append (F := fun T => Disjoint (interior (columnPieceAt (colVec 0 0) a).carrier)
    (interior T.carrier)) (f := columnPieceAt (colVec 0 1))
    (g := Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))
  · exact fun i => columnPieceAt_disjoint 0 0 0 1 a i (by decide)
  apply forall_fin_append (F := fun T => Disjoint (interior (columnPieceAt (colVec 0 0) a).carrier)
    (interior T.carrier)) (f := columnPieceAt (colVec 1 0)) (g := columnPieceAt (colVec 1 1))
  · exact fun i => columnPieceAt_disjoint 0 0 1 0 a i (by decide)
  · exact fun i => columnPieceAt_disjoint 0 0 1 1 a i (by decide)

/-- Cross-disjointness of column copy `(0,1)` against the whole tail `c10 ++ c11`. -/
theorem c01_tail_disjoint (a : Fin PgramTiling22.tiles.length) :
    ∀ b : Fin (PgramTiling22.tiles.length + PgramTiling22.tiles.length),
      Disjoint (interior (columnPieceAt (colVec 0 1) a).carrier)
        (interior ((Fin.append (columnPieceAt (colVec 1 0))
          (columnPieceAt (colVec 1 1))) b).carrier) := by
  apply forall_fin_append (F := fun T => Disjoint (interior (columnPieceAt (colVec 0 1) a).carrier)
    (interior T.carrier)) (f := columnPieceAt (colVec 1 0)) (g := columnPieceAt (colVec 1 1))
  · exact fun i => columnPieceAt_disjoint 0 1 1 0 a i (by decide)
  · exact fun i => columnPieceAt_disjoint 0 1 1 1 a i (by decide)

theorem c10_c11_disjoint :
    ∀ (a : Fin PgramTiling22.tiles.length) (b : Fin PgramTiling22.tiles.length),
      Disjoint (interior (columnPieceAt (colVec 1 0) a).carrier)
        (interior (columnPieceAt (colVec 1 1) b).carrier) :=
  fun a b => columnPieceAt_disjoint 1 0 1 1 a b (by decide)

/-- `T5 = c10 ++ c11` : pairwise disjoint. -/
theorem T5_pairwise :
    Pairwise (fun i j : Fin (PgramTiling22.tiles.length + PgramTiling22.tiles.length) =>
      Disjoint
        (interior ((Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))) i).carrier)
        (interior ((Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))) j).carrier)) :=
  pairwise_fin_append _ _
    (fun (A B : Tri) => Disjoint (interior A.carrier) (interior B.carrier))
    (fun (_ _ : Tri) h => h.symm) (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))
    (columnPieceAt_pairwise 1 0) (columnPieceAt_pairwise 1 1) c10_c11_disjoint

/-- `T4 = c01 ++ T5` : pairwise disjoint. -/
theorem T4_pairwise :
    Pairwise (fun i j :
        Fin (PgramTiling22.tiles.length +
          (PgramTiling22.tiles.length + PgramTiling22.tiles.length)) =>
      Disjoint
        (interior ((Fin.append (columnPieceAt (colVec 0 1))
          (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))) i).carrier)
        (interior ((Fin.append (columnPieceAt (colVec 0 1))
          (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))) j).carrier)) :=
  pairwise_fin_append _ _
    (fun (A B : Tri) => Disjoint (interior A.carrier) (interior B.carrier))
    (fun (_ _ : Tri) h => h.symm) (columnPieceAt (colVec 0 1))
    (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))
    (columnPieceAt_pairwise 0 1) T5_pairwise c01_tail_disjoint

/-- `T3 = c00 ++ T4` : pairwise disjoint. -/
theorem T3_pairwise :
    Pairwise (fun i j :
        Fin (PgramTiling22.tiles.length +
          (PgramTiling22.tiles.length +
            (PgramTiling22.tiles.length + PgramTiling22.tiles.length))) =>
      Disjoint
        (interior ((Fin.append (columnPieceAt (colVec 0 0))
          (Fin.append (columnPieceAt (colVec 0 1))
            (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))))) i).carrier)
        (interior ((Fin.append (columnPieceAt (colVec 0 0))
          (Fin.append (columnPieceAt (colVec 0 1))
            (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))))) j).carrier)) :=
  pairwise_fin_append _ _
    (fun (A B : Tri) => Disjoint (interior A.carrier) (interior B.carrier))
    (fun (_ _ : Tri) h => h.symm) (columnPieceAt (colVec 0 0))
    (Fin.append (columnPieceAt (colVec 0 1))
      (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))))
    (columnPieceAt_pairwise 0 0) T4_pairwise c00_tail_disjoint

/-- Cross-disjointness of the corner block against the whole column tail `T3`. -/
theorem corner_T3_disjoint (a : Fin Tiling44.tiles.length) :
    ∀ b : Fin (PgramTiling22.tiles.length +
        (PgramTiling22.tiles.length +
          (PgramTiling22.tiles.length + PgramTiling22.tiles.length))),
      Disjoint (interior (cornerPieceAt a).carrier)
        (interior ((Fin.append (columnPieceAt (colVec 0 0))
          (Fin.append (columnPieceAt (colVec 0 1))
            (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))))) b).carrier) := by
  apply forall_fin_append (F := fun T => Disjoint (interior (cornerPieceAt a).carrier)
    (interior T.carrier)) (f := columnPieceAt (colVec 0 0))
    (g := Fin.append (columnPieceAt (colVec 0 1))
      (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))))
  · exact fun i => cornerPieceAt_disjoint_columnPieceAt a 0 0 i
  apply forall_fin_append (F := fun T => Disjoint (interior (cornerPieceAt a).carrier)
    (interior T.carrier)) (f := columnPieceAt (colVec 0 1))
    (g := Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))
  · exact fun i => cornerPieceAt_disjoint_columnPieceAt a 0 1 i
  apply forall_fin_append (F := fun T => Disjoint (interior (cornerPieceAt a).carrier)
    (interior T.carrier)) (f := columnPieceAt (colVec 1 0)) (g := columnPieceAt (colVec 1 1))
  · exact fun i => cornerPieceAt_disjoint_columnPieceAt a 1 0 i
  · exact fun i => cornerPieceAt_disjoint_columnPieceAt a 1 1 i

/-- `T2 = corner ++ T3` : pairwise disjoint. -/
theorem T2_pairwise :
    Pairwise (fun i j :
        Fin (Tiling44.tiles.length +
          (PgramTiling22.tiles.length +
            (PgramTiling22.tiles.length +
              (PgramTiling22.tiles.length + PgramTiling22.tiles.length)))) =>
      Disjoint
        (interior ((Fin.append cornerPieceAt (Fin.append (columnPieceAt (colVec 0 0))
          (Fin.append (columnPieceAt (colVec 0 1))
            (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))))) i).carrier)
        (interior ((Fin.append cornerPieceAt (Fin.append (columnPieceAt (colVec 0 0))
          (Fin.append (columnPieceAt (colVec 0 1))
            (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))))) j).carrier)) :=
  pairwise_fin_append _ _
    (fun (A B : Tri) => Disjoint (interior A.carrier) (interior B.carrier))
    (fun (_ _ : Tri) h => h.symm) cornerPieceAt
    (Fin.append (columnPieceAt (colVec 0 0))
      (Fin.append (columnPieceAt (colVec 0 1))
        (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))))
    cornerPieceAt_pairwise T3_pairwise corner_T3_disjoint

/-- Cross-disjointness of the apex block against the whole tail `T2`. -/
theorem apex_T2_disjoint (a : Fin Tiling44.tiles.length) :
    ∀ b : Fin (Tiling44.tiles.length +
        (PgramTiling22.tiles.length +
          (PgramTiling22.tiles.length +
            (PgramTiling22.tiles.length + PgramTiling22.tiles.length)))),
      Disjoint (interior (apexPieceAt a).carrier)
        (interior ((Fin.append cornerPieceAt (Fin.append (columnPieceAt (colVec 0 0))
          (Fin.append (columnPieceAt (colVec 0 1))
            (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))))) b).carrier) := by
  apply forall_fin_append (F := fun T => Disjoint (interior (apexPieceAt a).carrier)
    (interior T.carrier)) (f := cornerPieceAt)
    (g := Fin.append (columnPieceAt (colVec 0 0))
      (Fin.append (columnPieceAt (colVec 0 1))
        (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))))
  · exact fun i => apexPieceAt_disjoint_cornerPieceAt a i
  apply forall_fin_append (F := fun T => Disjoint (interior (apexPieceAt a).carrier)
    (interior T.carrier)) (f := columnPieceAt (colVec 0 0))
    (g := Fin.append (columnPieceAt (colVec 0 1))
      (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))))
  · exact fun i => apexPieceAt_disjoint_columnPieceAt a 0 0 i
  apply forall_fin_append (F := fun T => Disjoint (interior (apexPieceAt a).carrier)
    (interior T.carrier)) (f := columnPieceAt (colVec 0 1))
    (g := Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1)))
  · exact fun i => apexPieceAt_disjoint_columnPieceAt a 0 1 i
  apply forall_fin_append (F := fun T => Disjoint (interior (apexPieceAt a).carrier)
    (interior T.carrier)) (f := columnPieceAt (colVec 1 0)) (g := columnPieceAt (colVec 1 1))
  · exact fun i => apexPieceAt_disjoint_columnPieceAt a 1 0 i
  · exact fun i => apexPieceAt_disjoint_columnPieceAt a 1 1 i

/-- **`delta4PiecesAux` is pairwise interior-disjoint.** -/
theorem delta4PiecesAux_pairwise :
    Pairwise (fun i j => Disjoint (interior (delta4PiecesAux i).carrier)
      (interior (delta4PiecesAux j).carrier)) := by
  unfold delta4PiecesAux
  exact pairwise_fin_append _ _
    (fun (A B : Tri) => Disjoint (interior A.carrier) (interior B.carrier))
    (fun (_ _ : Tri) h => h.symm) apexPieceAt
    (Fin.append cornerPieceAt (Fin.append (columnPieceAt (colVec 0 0))
      (Fin.append (columnPieceAt (colVec 0 1))
        (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))))))
    apexPieceAt_pairwise T2_pairwise apex_T2_disjoint

theorem delta4Pieces_pairwise :
    Pairwise (fun i j : Fin 176 => Disjoint (interior (delta4Pieces i).carrier)
      (interior (delta4Pieces j).carrier)) := by
  intro i j hij
  exact delta4PiecesAux_pairwise (fun heq => hij (by
    have := congrArg (finCongr delta4PiecesAux_len) heq
    simpa using this))

/-- **`Δ_4` as a genuine flat `Dissection 176`.** All three certificate ingredients — (C2)
`delta4Pieces_subset_delta4`, (C3) `delta4Pieces_pairwise`, (C4) `delta4_area_sum` — are now
proved, so `AreaDet.ofDetCertificate` assembles the actual witness: a real `Dissection` of `Δ_4`
into `176` triangles, matching the `m=2→m=4` step of `thm:realize12`'s existence half. This is the
concrete `m=4` object, not yet wrapped as a `CongruentDissection` (needs `model`/`tiles_congruent`,
not yet attempted) and not yet the general `∀m≥2` statement (needs an `m=3` base too). -/
noncomputable def delta4Dissection : Dissection 176 :=
  Erdos634.AreaDet.ofDetCertificate delta4 delta4Pieces
    delta4Pieces_subset_delta4 delta4Pieces_pairwise delta4_area_sum
