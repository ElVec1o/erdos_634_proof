import Erdos634.CollarCongruentM4
import Erdos634.SubDissection
import Erdos634.Tiling44Bridge

/-!
# `prop:orientmono`'s covering-equality witness: the apex block of `delta4CongruentDissection`

`prop:orientmono` (the inflated-tile version, `PAPER_MAP.md`'s row) needs a `CongruentDissection`
built by *restricting* a real dissection to a tile subset that fills one occurrence `Δ_k` —
`SubDissection.restrictCongruent` supplies the restriction mechanically, given a covering-equality
hypothesis `⋃ i ∈ S, (D.tile i).carrier = T.carrier`. That hypothesis was recorded as "genuinely
unbuilt, confirmed, not assumed" — no concrete `S`, `T`, `D` triple existed anywhere in the corpus.

This file supplies the first one. `CollarCongruentM4.delta4CongruentDissection : CongruentDissection
176` (the `m=2→4` collar witness) is built from six `Fin.append` blocks; its first block,
`apexPieceAt`, is literally `Tiling44Bridge.dissection`'s own 44 pieces translated by
`(88, 24√15)`. So the 44 tile-indices of that block, inside `Fin 176`, are exactly an occurrence of
the `N=44` tiling — `Δ_2` — sitting inside `Δ_4`, and restricting `delta4CongruentDissection` to
them recovers a genuine `CongruentDissection 44`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.OrientMonoWitness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap
open Erdos634.Realizable Erdos634.TranslateDissection Erdos634.SubDissection

/-- The apex block's 44 indices, as a `Finset (Fin 176)`. -/
noncomputable def apexIndices : Finset (Fin 176) :=
  Finset.univ.image (fun j : Fin Tiling44.tiles.length =>
    (finCongr delta4PiecesAux_len) (Fin.castAdd _ j))

/-- **`delta4Pieces` at an apex index is `apexPieceAt` at the corresponding `Fin 44`.** -/
theorem delta4Pieces_apex (j : Fin Tiling44.tiles.length) :
    delta4Pieces ((finCongr delta4PiecesAux_len) (Fin.castAdd _ j)) = apexPieceAt j := by
  show delta4PiecesAux ((finCongr delta4PiecesAux_len).symm
    ((finCongr delta4PiecesAux_len) (Fin.castAdd _ j))) = apexPieceAt j
  rw [Equiv.symm_apply_apply]
  unfold delta4PiecesAux
  rw [Fin.append_left]

/-- **The apex block's carrier union is the translated `Tiling44` target.**  This is
`Tiling44Bridge.dissection.covers` transported through the translation: `apexPieceAt i` is
definitionally `mapTri (transEquiv v) (Tiling44Bridge.pieceAt i)`, and `pieceAt = dissection.tile`,
so the union of the 44 apex tiles equals the translated target's carrier exactly. -/
theorem apex_union_eq_translated_target :
    (⋃ j : Fin Tiling44.tiles.length, (apexPieceAt j).carrier)
      = (mapTri (transEquiv (mkPt 88 (24 * Real.sqrt 15))).toAffineEquiv
          Erdos634.Tiling44Bridge.targetTri).carrier := by
  have hcov := (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
    Erdos634.Tiling44Bridge.dissection).covers
  rw [translateCongruentDissection_target] at hcov
  convert hcov using 2

/-- **The covering-equality witness itself.**  The apex block of `delta4CongruentDissection`'s 176
tiles covers exactly the translated `Tiling44` target — a real occurrence `Δ_2` inside `Δ_4`. -/
theorem apex_covers :
    (⋃ i ∈ apexIndices, (delta4CongruentDissection.tile i).carrier)
      = (mapTri (transEquiv (mkPt 88 (24 * Real.sqrt 15))).toAffineEquiv
          Erdos634.Tiling44Bridge.targetTri).carrier := by
  rw [← apex_union_eq_translated_target]
  unfold apexIndices
  ext x
  simp only [Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, ⟨j, hj⟩, hx⟩
    refine ⟨j, ?_⟩
    rw [← hj, show delta4CongruentDissection.tile = delta4Pieces from rfl, delta4Pieces_apex] at hx
    exact hx
  · rintro ⟨j, hx⟩
    refine ⟨(finCongr delta4PiecesAux_len) (Fin.castAdd _ j), ⟨j, rfl⟩, ?_⟩
    rw [show delta4CongruentDissection.tile = delta4Pieces from rfl, delta4Pieces_apex]
    exact hx

/-- **The witness, assembled.**  Restricting `delta4CongruentDissection` to the apex block's 44
indices produces a genuine `CongruentDissection 44` of the translated `Tiling44` target — the first
concrete covering-equality witness for `prop:orientmono`'s residual gap. -/
noncomputable def occurrenceWitness : CongruentDissection apexIndices.card :=
  restrictCongruent delta4CongruentDissection apexIndices
    (mapTri (transEquiv (mkPt 88 (24 * Real.sqrt 15))).toAffineEquiv
      Erdos634.Tiling44Bridge.targetTri)
    apex_covers



/-! ## The corner block: a second occurrence, same type — and where the pattern stops

`cornerPieceAt` is likewise a full translated copy of `Tiling44Bridge.dissection` (at
`v = (176, 0)`), so the same argument gives a second, independent occurrence witness. The four
`columnPieceAt` blocks do **not** admit the same treatment: `PgramTiling22Bridge` has no
`CongruentDissection` object at all — its `pieceAt`/`covers` are stated over a **parallelogram**
carrier (`convexHull ℝ {v1,v2,v3,v4}`), not a `Tri`, so there is no `Tri` target to restrict to and
`SubDissection.restrictCongruent` does not apply. That gap is exactly what `RegionDissection`
(built two ticks ago) was designed for, but `RegionDissection` currently has union operations only,
no restriction-to-a-covering-subregion primitive — building that is separate, real work, not
attempted here. -/

/-- The corner block's 44 indices, as a `Finset (Fin 176)`. -/
noncomputable def cornerIndices : Finset (Fin 176) :=
  Finset.univ.image (fun j : Fin Tiling44.tiles.length =>
    (finCongr delta4PiecesAux_len)
      (Fin.natAdd Tiling44.tiles.length (Fin.castAdd _ j)))

theorem delta4Pieces_corner (j : Fin Tiling44.tiles.length) :
    delta4Pieces ((finCongr delta4PiecesAux_len)
      (Fin.natAdd Tiling44.tiles.length (Fin.castAdd _ j))) = cornerPieceAt j := by
  show delta4PiecesAux ((finCongr delta4PiecesAux_len).symm
    ((finCongr delta4PiecesAux_len) (Fin.natAdd Tiling44.tiles.length (Fin.castAdd _ j))))
    = cornerPieceAt j
  rw [Equiv.symm_apply_apply]
  unfold delta4PiecesAux
  rw [Fin.append_right, Fin.append_left]

theorem corner_union_eq_translated_target :
    (⋃ j : Fin Tiling44.tiles.length, (cornerPieceAt j).carrier)
      = (mapTri (transEquiv (mkPt 176 0)).toAffineEquiv
          Erdos634.Tiling44Bridge.targetTri).carrier := by
  have hcov := (translateCongruentDissection (mkPt 176 0)
    Erdos634.Tiling44Bridge.dissection).covers
  rw [translateCongruentDissection_target] at hcov
  convert hcov using 2

theorem corner_covers :
    (⋃ i ∈ cornerIndices, (delta4CongruentDissection.tile i).carrier)
      = (mapTri (transEquiv (mkPt 176 0)).toAffineEquiv
          Erdos634.Tiling44Bridge.targetTri).carrier := by
  rw [← corner_union_eq_translated_target]
  unfold cornerIndices
  ext x
  simp only [Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, ⟨j, hj⟩, hx⟩
    refine ⟨j, ?_⟩
    rw [← hj, show delta4CongruentDissection.tile = delta4Pieces from rfl, delta4Pieces_corner] at hx
    exact hx
  · rintro ⟨j, hx⟩
    refine ⟨(finCongr delta4PiecesAux_len) (Fin.natAdd Tiling44.tiles.length (Fin.castAdd _ j)),
      ⟨j, rfl⟩, ?_⟩
    rw [show delta4CongruentDissection.tile = delta4Pieces from rfl, delta4Pieces_corner]
    exact hx

/-- **The second occurrence witness**, at the corner block. -/
noncomputable def cornerOccurrenceWitness : CongruentDissection cornerIndices.card :=
  restrictCongruent delta4CongruentDissection cornerIndices
    (mapTri (transEquiv (mkPt 176 0)).toAffineEquiv Erdos634.Tiling44Bridge.targetTri)
    corner_covers

end Erdos634.OrientMonoWitness
