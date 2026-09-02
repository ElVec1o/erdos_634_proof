import Erdos634.CollarAreaM4

/-!
# The `m=2 → m=4` collar step — the flat 176-piece list and the area-sum identity

Erdős #634. `thm:realize12`'s existence half needs `Δ_4` built as one flat `Dissection 176`.
Containment and disjointness for all 176 pieces are done (`CollarContainM4.lean`,
`CollarDisjointM4.lean`); the per-region area sums are done (`CollarAreaM4.lean`). This file
assembles the last ingredient: the actual flat piece function `Fin 176 → Tri` (apex ++ corner ++
the four column copies, via `Fin.append`), and proves the (C4) area-sum identity over it —
`∑ i, |detTri (delta4Pieces i)| = |detTri delta4|` — the exact hypothesis `AreaDet.ofDetCertificate`
needs.

The general tool this needed and didn't have: a way to split `∑ i : Fin (m+n), F (Fin.append f g i)`
back into `∑ F (f i) + ∑ F (g i)` — built here as `sum_fin_append` (`Fintype.sum_sum_type` composed
with `finSumFinEquiv`), since no ready-made Mathlib lemma covers it.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.AreaDet
open Erdos634.Realizable Erdos634.TranslateDissection Erdos634.Z15Real

/-- **Splitting a sum over `Fin.append`** back into a sum over each piece — the general
combinator `sum_fin_append` needed, with no ready-made Mathlib lemma for it. -/
theorem sum_fin_append {α : Type*} {β : Type*} [AddCommMonoid β] (m n : ℕ) (F : α → β)
    (f : Fin m → α) (g : Fin n → α) :
    ∑ i : Fin (m + n), F (Fin.append f g i) = (∑ i : Fin m, F (f i)) + ∑ i : Fin n, F (g i) := by
  rw [← Fintype.sum_equiv finSumFinEquiv (fun x => F (Fin.append f g (finSumFinEquiv x)))
      (fun x => F (Fin.append f g x)) (fun x => rfl)]
  rw [Fintype.sum_sum_type]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by simp)
  · exact Finset.sum_congr rfl (fun i _ => by simp)

/-- The apex piece function: translated `Tiling44Bridge` pieces, `v = (88, 24√15)`. -/
noncomputable def apexPieceAt (i : Fin Tiling44.tiles.length) : Tri :=
  mapTri (transEquiv (mkPt 88 (24 * Real.sqrt 15))).toAffineEquiv
    (Erdos634.Tiling44Bridge.pieceAt i)

/-- The corner piece function: translated `Tiling44Bridge` pieces, `v = (176, 0)`. -/
noncomputable def cornerPieceAt (i : Fin Tiling44.tiles.length) : Tri :=
  mapTri (transEquiv (mkPt 176 0)).toAffineEquiv (Erdos634.Tiling44Bridge.pieceAt i)

/-- One column-copy's piece function: `PgramTiling22Bridge` pieces scaled ×2 about the origin,
translated by `w`. -/
noncomputable def columnPieceAt (w : Plane) (i : Fin PgramTiling22.tiles.length) : Tri :=
  mapTri (transEquiv w).toAffineEquiv
    (mapTri (homothetyEquiv (mkPt 0 0) 2 (by norm_num)) (Erdos634.PgramTiling22Bridge.pieceAt i))

/-- The four column-copy translation vectors: `(88j, 12√15·h)` for `j,h ∈ {0,1}`. -/
noncomputable def colVec (j h : Fin 2) : Plane := mkPt (88 * j.val) (12 * Real.sqrt 15 * h.val)

/-- **`Δ_4`'s 176 pieces, as one flat list** (pre-cast form): apex ++ corner ++ the four column
copies, indexed by the natural (non-literal) sum of the source lengths — kept in this form so the
individual sums below stay syntactically matched against `CollarAreaM4`'s own per-region facts;
`delta4Pieces` below re-indexes it to the literal `Fin 176`. -/
noncomputable def delta4PiecesAux :
    Fin (Tiling44.tiles.length +
      (Tiling44.tiles.length +
        (PgramTiling22.tiles.length +
          (PgramTiling22.tiles.length +
            (PgramTiling22.tiles.length + PgramTiling22.tiles.length))))) → Tri :=
  Fin.append apexPieceAt
    (Fin.append cornerPieceAt
      (Fin.append (columnPieceAt (colVec 0 0))
        (Fin.append (columnPieceAt (colVec 0 1))
          (Fin.append (columnPieceAt (colVec 1 0)) (columnPieceAt (colVec 1 1))))))

theorem delta4PiecesAux_len :
    Tiling44.tiles.length +
      (Tiling44.tiles.length +
        (PgramTiling22.tiles.length +
          (PgramTiling22.tiles.length +
            (PgramTiling22.tiles.length + PgramTiling22.tiles.length)))) = 176 := by decide

/-- **`Δ_4`'s 176 pieces, as one flat list.** -/
noncomputable def delta4Pieces : Fin 176 → Tri :=
  delta4PiecesAux ∘ (finCongr delta4PiecesAux_len.symm)

theorem delta4PiecesAux_area_sum :
    ∑ i, |detTri (delta4PiecesAux i)| = |detTri delta4| := by
  unfold delta4PiecesAux
  rw [sum_fin_append (F := fun T => |detTri T|), sum_fin_append (F := fun T => |detTri T|),
    sum_fin_append (F := fun T => |detTri T|), sum_fin_append (F := fun T => |detTri T|),
    sum_fin_append (F := fun T => |detTri T|)]
  unfold apexPieceAt cornerPieceAt columnPieceAt
  rw [apex_area_sum (mkPt 88 (24 * Real.sqrt 15)), apex_area_sum (mkPt 176 0),
    column_area_sum (colVec 0 0), column_area_sum (colVec 0 1),
    column_area_sum (colVec 1 0), column_area_sum (colVec 1 1)]
  have h1 : |detTri Erdos634.Tiling44Bridge.targetTri| = 4224 * Real.sqrt 15 := by
    have htarget : Erdos634.AreaDet.detTri Erdos634.Tiling44Bridge.targetTri
        = toR (Tiling44.area2 Tiling44.target) := by
      unfold Erdos634.Tiling44Bridge.targetTri
      rw [Erdos634.CertCoord.detTri_mkTri, Erdos634.Tiling44Bridge.det3_eq_toR_cross]
      rfl
    have hval : Tiling44.area2 Tiling44.target = ((0:ℤ), (4224:ℤ)) := by decide
    have hs : Real.sqrt 15 > 0 := Real.sqrt_pos.mpr (by norm_num)
    rw [htarget, hval, toR]
    push_cast
    rw [abs_of_pos] <;> nlinarith [hs]
  have h2 : |toR PgramTiling22.area2target| = 528 * Real.sqrt 15 := by
    have hval : PgramTiling22.area2target = ((0:ℤ), (528:ℤ)) := by decide
    have hs : Real.sqrt 15 > 0 := Real.sqrt_pos.mpr (by norm_num)
    rw [hval, toR]
    push_cast
    rw [abs_of_pos] <;> nlinarith [hs]
  have h3 : |detTri delta4| = 16896 * Real.sqrt 15 := by
    unfold delta4
    rw [Erdos634.CertCoord.detTri_mkTri]
    unfold det3
    have hs : Real.sqrt 15 > 0 := Real.sqrt_pos.mpr (by norm_num)
    rw [abs_of_pos] <;> nlinarith [hs]
  rw [h1, h2, h3]; ring

/-- **The `Δ_4` area-sum identity (C4)**: the 176 pieces' unsigned determinants sum to `Δ_4`'s
own — exactly the hypothesis `AreaDet.ofDetCertificate` needs. -/
theorem delta4_area_sum :
    ∑ i : Fin 176, |detTri (delta4Pieces i)| = |detTri delta4| := by
  rw [← delta4PiecesAux_area_sum]
  exact Fintype.sum_equiv (finCongr delta4PiecesAux_len.symm) _ _ (fun i => rfl)
