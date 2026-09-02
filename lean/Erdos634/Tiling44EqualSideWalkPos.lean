import Erdos634.Tiling44CornerTile
import Erdos634.Tiling44WallFinal
import Erdos634.Tiling44EqualSideWalk
import Erdos634.SideWalk
import Erdos634.Tiling44Scalene

/-!
# The equal side's walk equation, with a positive count

Erdős #634. Toward `lem:ccornerside`, past `equal_side_walk` and `SideWalk.side_walk_pos1_of_dissection`:
applies the latter to `Tiling44Bridge.dissection`'s equal side using the actual corner tile
identified in `Tiling44CornerTile.lean` (`tiles[13]`, vertex `1` at the corner) as the witness edge
`p0`. Its wall edge (vertex `1` to vertex `2`) has length `32 = sideOpp dissection.model 1` — this
file checks the two remaining facts `side_walk_pos1_of_dissection` needs about that witness: it is
itself a wall edge (`hp0mem`, both endpoints have `wallVal = (0,4224)`, decide-checked), and its
length matches `sideOpp dissection.model 1` (`hp0len`, via the certificate-level `dist2` equality
`Tiling44.dist2 (vertexOf tiles[13] 1) (vertexOf tiles[13] 2) = Tiling44.dist2 (vertexOf headI 2)
(vertexOf headI 0)`, both `= 1024`, i.e. `32²`).

This gives `Qc ≥ 1` in the equal side's walk equation — the first count-positivity result for a
real dissection's side anywhere in the corpus. Whether `Qc` is the count `lem:ccornerside` actually
needs (matching the paper's own `a`/`b`/`c` naming, not just an index) is not yet checked here.

Axiom-clean; no `sorry`.
-/

open Erdos634.CertCoord Erdos634.Geometry Erdos634.Z15Real Erdos634.Tiling44Bridge
open Erdos634.SideWalk Erdos634.TilePlacement

/-- **The equal side's walk equation has `Qc ≥ 1`.** The corner tile `tiles[13]`'s wall edge
(length `32`) forces the count matching `sideOpp dissection.model 1` to be at least `1`. -/
theorem equal_side_walk_pos :
    ∃ Pc Qc Rc : ℕ, 1 ≤ Qc ∧
      dist (targetTri.pts 1) (targetTri.pts 2)
        = Pc * sideOpp dissection.model 0 + Qc * sideOpp dissection.model 1
          + Rc * sideOpp dissection.model 2 := by
  have ht13 : Tiling44.tiles[13] ∈ Tiling44.tiles := List.getElem_mem (by decide)
  set p0 : Fin Tiling44.tiles.length × Fin 3 := (⟨13, by decide⟩, 1) with hp0def
  have hp0mem : p0 ∈ Erdos634.BaseChain.wallList dissection.toDissection gWallAff
      (4224 * Real.sqrt 15) := by
    rw [Erdos634.BaseChain.mem_wallList]
    refine ⟨?_, ?_⟩
    · show gWallAff ((dissection.tile p0.1).pts p0.2) = 4224 * Real.sqrt 15
      have htile : dissection.tile p0.1 = pieceTri ht13 := rfl
      rw [htile]
      exact (g_eq_iff_wallVal ht13 1).2 (by decide)
    · show gWallAff ((dissection.tile p0.1).pts (p0.2 + 1)) = 4224 * Real.sqrt 15
      have htile : dissection.tile p0.1 = pieceTri ht13 := rfl
      rw [htile]
      exact (g_eq_iff_wallVal ht13 2).2 (by decide)
  have hp0len : dist ((dissection.tile p0.1).pts p0.2) ((dissection.tile p0.1).pts (p0.2 + 1))
      = sideOpp dissection.model 1 := by
    have htile : dissection.tile p0.1 = pieceTri ht13 := rfl
    have hmodel : dissection.model = pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles := rfl
    rw [htile]
    show dist ((pieceTri ht13).pts 1) ((pieceTri ht13).pts 2) = sideOpp dissection.model 1
    rw [hmodel]
    show dist ((pieceTri ht13).pts 1) ((pieceTri ht13).pts 2)
      = dist ((pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
        ((pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
    have hsq : dist ((pieceTri ht13).pts 1) ((pieceTri ht13).pts 2) ^ 2
        = dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
          ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0) ^ 2 := by
      rw [pieceTri_dist_sq _ ht13 1 2,
        pieceTri_dist_sq _ Erdos634.Tiling44Bridge.headI_mem_tiles 2 0]
      show toR (Tiling44.dist2 (vertexOf Tiling44.tiles[13] 1) (vertexOf Tiling44.tiles[13] 2))
        = toR (Tiling44.dist2 (vertexOf Tiling44.tiles.headI 2) (vertexOf Tiling44.tiles.headI 0))
      congr 1
    nlinarith [dist_nonneg (α := Plane) (x := (pieceTri ht13).pts 1) (y := (pieceTri ht13).pts 2),
      dist_nonneg (α := Plane)
        (x := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
        (y := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0),
      hsq]
  have hdirab : dirWall (targetTri.pts 1) ≤ dirWall (targetTri.pts 2) := by
    rw [tiling44_targetTri_pts1, tiling44_targetTri_pts2, dirWall_mkPt, dirWall_mkPt]
    nlinarith [Real.sqrt_nonneg (15:ℝ), Real.sq_sqrt (show (0:ℝ) ≤ 15 by norm_num)]
  have hab : targetTri.pts 1 ≠ targetTri.pts 2 := by
    rw [tiling44_targetTri_pts1, tiling44_targetTri_pts2]
    intro h
    have := congrArg (fun p => xFun p) h
    simp [xFun_mkPt] at this
  have hkerl : ∀ v : Plane, gWallAff.linear v = 0 → dirWall v = 0 → v = 0 := hker_wall
  exact side_walk_pos1_of_dissection dissection gWallAff (4224 * Real.sqrt 15) dirWall
    hkerl hwall_wall (targetTri.pts 1) (targetTri.pts 2) hab hdirab
    hbase_wall hline_wall hface_wall hthird_wall hiso_wall tiling44_model_scalene
    (by show 0 < Tiling44.tiles.length; decide)
    p0 hp0mem hp0len
