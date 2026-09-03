import Erdos634.PgramTiling22Bridge
import Erdos634.RegionDissection

/-!
# `PgramTiling22Bridge` as a `CongruentRegionDissection`

`PgramTiling22Bridge` has no `CongruentDissection` object — its target is a parallelogram carrier
(`convexHull ℝ {v1,v2,v3,v4}`), not a `Tri`, so `Dissection`'s `Tri`-typed target can't express it.
`RegionDissection` (built to close exactly this kind of gap) can. Every ingredient already exists:
`pgram22_covers` (the 22 pieces' union is the carrier), `pieces_interiors_disjoint`, and
`pieceTri_congruent` (every piece congruent to the model). This file assembles them.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PgramTiling22Region

open Erdos634.Geometry Erdos634.RegionDissection

/-- `PgramTiling22Bridge`'s 22 pieces, as a `CongruentRegionDissection` of the parallelogram
carrier. -/
noncomputable def dissection : CongruentRegionDissection PgramTiling22.tiles.length where
  region := Erdos634.PgramTiling22Bridge.carrier
  tile := Erdos634.PgramTiling22Bridge.pieceAt
  covers := Erdos634.PgramTiling22Bridge.pgram22_covers
  interiors_disjoint := fun i j hij =>
    Erdos634.PgramTiling22Bridge.pieces_interiors_disjoint
      (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
      (Erdos634.PgramTiling22Bridge.tiles_getElem_inj i j hij)
  model := Erdos634.PgramTiling22Bridge.pieceTri Erdos634.PgramTiling22Bridge.headI_mem_tiles
  tiles_congruent := fun i =>
    Erdos634.PgramTiling22Bridge.pieceTri_congruent (List.getElem_mem i.isLt)

end Erdos634.PgramTiling22Region
