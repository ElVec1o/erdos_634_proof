import Erdos634.Tiling44Bridge
import Erdos634.TilePlacement

/-!
# `Tiling44Bridge.dissection`'s model is scalene

Erdős #634. Toward instantiating `SideWalk.side_walk_of_dissection` for a concrete real
`CongruentDissection` (needed to close `lem:ccornerside`, `thm:walkstruct`, `cor:wallsf2e` — all
of which stop at exactly this "real dissection" connection). `side_walk_of_dissection`'s `hscalene`
hypothesis needs the model tile's three sides to be pairwise distinct; this file supplies that for
`Tiling44Bridge.dissection`, using the exact side lengths `(16, 24, 32)` already confirmed this
session (`CollarCongruentM4.lean`'s congruence work).

Axiom-clean; no `sorry`.
-/

open Erdos634.TilePlacement

theorem tiling44_model01 :
    dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1) = 16 := by
  have h2 : dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1) ^ 2 = 256 := by
    rw [Erdos634.Tiling44Bridge.pieceTri_dist_sq _ Erdos634.Tiling44Bridge.headI_mem_tiles]
    have : Tiling44.dist2 (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 0)
        (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 1) = ((256:ℤ),(0:ℤ)) := by decide
    rw [this]; simp [Erdos634.Z15Real.toR]
  nlinarith [dist_nonneg (α := Erdos634.Geometry.Plane)
    (x := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
    (y := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1), h2]

theorem tiling44_model12 :
    dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2) = 24 := by
  have h2 : dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2) ^ 2 = 576 := by
    rw [Erdos634.Tiling44Bridge.pieceTri_dist_sq _ Erdos634.Tiling44Bridge.headI_mem_tiles]
    have : Tiling44.dist2 (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 1)
        (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 2) = ((576:ℤ),(0:ℤ)) := by decide
    rw [this]; simp [Erdos634.Z15Real.toR]
  nlinarith [dist_nonneg (α := Erdos634.Geometry.Plane)
    (x := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
    (y := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2), h2]

theorem tiling44_model20 :
    dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0) = 32 := by
  have h2 : dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0) ^ 2 = 1024 := by
    rw [Erdos634.Tiling44Bridge.pieceTri_dist_sq _ Erdos634.Tiling44Bridge.headI_mem_tiles]
    have : Tiling44.dist2 (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 2)
        (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 0) = ((1024:ℤ),(0:ℤ)) := by decide
    rw [this]; simp [Erdos634.Z15Real.toR]
  nlinarith [dist_nonneg (α := Erdos634.Geometry.Plane)
    (x := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
    (y := (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0), h2]

/-- **`Tiling44Bridge.dissection.model` is scalene** — the `hscalene` hypothesis
`SideWalk.side_walk_of_dissection` needs, for this specific target. -/
theorem tiling44_model_scalene :
    sideOpp Erdos634.Tiling44Bridge.dissection.model 0
      ≠ sideOpp Erdos634.Tiling44Bridge.dissection.model 1 ∧
    sideOpp Erdos634.Tiling44Bridge.dissection.model 0
      ≠ sideOpp Erdos634.Tiling44Bridge.dissection.model 2 ∧
    sideOpp Erdos634.Tiling44Bridge.dissection.model 1
      ≠ sideOpp Erdos634.Tiling44Bridge.dissection.model 2 := by
  show sideOpp (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) 0
      ≠ sideOpp (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) 1 ∧
    sideOpp (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) 0
      ≠ sideOpp (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) 2 ∧
    sideOpp (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) 1
      ≠ sideOpp (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) 2
  have e0 : sideOpp (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) 0 = 24 := by
    show dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2) = 24
    exact tiling44_model12
  have e1 : sideOpp (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) 1 = 32 := by
    show dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0) = 32
    exact tiling44_model20
  have e2 : sideOpp (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) 2 = 16 := by
    show dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1) = 16
    exact tiling44_model01
  rw [e0, e1, e2]; norm_num
