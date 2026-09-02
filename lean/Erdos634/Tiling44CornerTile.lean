import Erdos634.Tiling44Bridge

/-!
# The specific tile at `Tiling44Bridge`'s target corner `(176,0)`

Erdős #634. Toward `lem:ccornerside`, past `Tiling44EqualSideWalk.equal_side_walk`: that theorem
gives `∃ Pc Qc Rc, dist(pts1,pts2) = Pc·s₀+Qc·s₁+Rc·s₂` but not which count is forced positive.
This file identifies the actual corner tile — `Tiling44.tiles[13]`, whose vertex `1` sits exactly
at `targetTri.pts 1 = (176,0)`, the wall's own start point — and checks its two vertex-1-incident
edges directly: squared lengths `256` (`= 16²`) and `1024` (`= 32²`), never `576` (`= 24²`). So the
`b`-side (length `24`) is not incident to this corner at all; the two edges leaving the corner are
the `a`-side (`16`) and `c`-side (`32`).

**Not yet done**: identifying which of these two edges is the WALL edge (collinear with the wall's
own direction from `(176,0)` toward the apex, vs. the other going into the target's interior), and
connecting that to `WallEndpoints.chain_starts_at_a`'s abstract edge-at-position-0 to actually pin
`Pc>0`/`Rc>0` in `equal_side_walk`'s conclusion. Hand computation (not yet formalized) suggests the
edge to `(154,0,0,6)` (length `32`, the `c`-side) is the one collinear with the wall direction
`(-88, 24√15)` (both proportional by `1/4`), leaving the `16`-length edge as the one going inward —
but this has not been checked in Lean and is not asserted as a theorem here.

Axiom-clean; no `sorry`.
-/

open Erdos634.Tiling44Bridge

/-- Tile `13`'s vertex `1` is exactly the target's corner `(176,0)` — the wall's own start point. -/
theorem corner_tile_vertex : vertexOf Tiling44.tiles[13] 1 = (176, 0, 0, 0) := by decide

/-- The edge from the corner to `Tiling44.tiles[13]`'s vertex `0` has squared length `256 = 16²`
— the model's `a`-side. -/
theorem corner_tile_edge_a :
    Tiling44.dist2 (Tiling44.t2 Tiling44.tiles[13]) (Tiling44.t1 Tiling44.tiles[13])
      = (256, 0) := by decide

/-- The edge from the corner to `Tiling44.tiles[13]`'s vertex `2` has squared length `1024 = 32²`
— the model's `c`-side. -/
theorem corner_tile_edge_c :
    Tiling44.dist2 (Tiling44.t2 Tiling44.tiles[13]) (Tiling44.t3 Tiling44.tiles[13])
      = (1024, 0) := by decide
