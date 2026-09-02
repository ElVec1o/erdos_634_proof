import Erdos634.Tiling44WallSetup
import Erdos634.BaseChain

/-!
# `side_walk_of_dissection`'s `hthird` hypothesis, in its exact required shape

Erdős #634. The last of `side_walk_of_dissection`'s hypotheses for `Tiling44Bridge.dissection`'s
wall line. Translates the `List`-indexed, Bool-valued `all_hthird_ok` (over `Tiling44.tiles`) into
the real-valued, `BaseChain.wallList`-indexed shape `side_walk_of_dissection` actually requires,
via `g_eq_iff_wallVal` and the definitional equality `dissection.tile p.1 = pieceTri ht`
(`ofDetCertificate`'s `tile` field is literally the supplied `tile` argument).

Axiom-clean; no `sorry`.
-/

open Erdos634.CertCoord Erdos634.Geometry Erdos634.Z15Real Erdos634.Tiling44Bridge

/-- **`hthird` for `Tiling44Bridge.dissection`'s wall line.** Every wall edge's third vertex is
strictly on the target's interior side of the wall — exactly `side_walk_of_dissection`'s `hthird`
hypothesis, assembled from `all_hthird_ok`'s Bool fact via `g_eq_iff_wallVal`. -/
theorem hthird_wall :
    ∀ p ∈ Erdos634.BaseChain.wallList dissection.toDissection gWallAff
      (4224 * Real.sqrt 15),
      gWallAff ((dissection.tile p.1).pts (p.2 + 2)) < 4224 * Real.sqrt 15 := by
  intro p hp
  rw [Erdos634.BaseChain.mem_wallList] at hp
  obtain ⟨h0, h1⟩ := hp
  set t := Tiling44.tiles[p.1.val] with htdef
  have ht : t ∈ Tiling44.tiles := List.getElem_mem p.1.isLt
  have htile : dissection.tile p.1 = pieceTri ht := rfl
  rw [htile] at h0 h1 ⊢
  have hw0 : wallVal (vertexOf t p.2) = ((0:ℤ), (4224:ℤ)) := (g_eq_iff_wallVal ht p.2).1 h0
  have hw1 : wallVal (vertexOf t (p.2 + 1)) = ((0:ℤ), (4224:ℤ)) := (g_eq_iff_wallVal ht (p.2+1)).1 h1
  have hedge : isWallEdge t p.2 = true := by
    simp only [isWallEdge, isWallVertex, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hw0, hw1⟩
  have hthirdOKfact := all_hthird_ok t ht
  simp only [hthirdOK, decide_eq_true_eq] at hthirdOKfact
  have hne := hthirdOKfact p.2 hedge
  by_contra hle
  push_neg at hle
  have hmemtri : (pieceTri ht).pts (p.2 + 2) ∈ (pieceTri ht).carrier :=
    subset_convexHull ℝ _ (Set.mem_range_self (p.2+2))
  have hmemtarget : (pieceTri ht).pts (p.2 + 2) ∈ targetTri.carrier :=
    pieceTri_subset_target ht hmemtri
  have hle' : gWallAff ((pieceTri ht).pts (p.2 + 2)) ≤ 4224 * Real.sqrt 15 :=
    hwall_wall _ hmemtarget
  have heq : gWallAff ((pieceTri ht).pts (p.2 + 2)) = 4224 * Real.sqrt 15 := le_antisymm hle' hle
  have hw2 : wallVal (vertexOf t (p.2 + 2)) = ((0:ℤ), (4224:ℤ)) := (g_eq_iff_wallVal ht (p.2+2)).1 heq
  rw [hw2] at hne
  simp at hne
