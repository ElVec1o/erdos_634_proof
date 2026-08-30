import Erdos634.ChainInstance

/-!
# Every boundary point of the target lies on a tile edge

Erdős #634, bridge (c), the selection.  `ChainInstance` reduces the ordering of the base chain to
two facts about a particular dissection: which edges make up the chain, and that their shadows
cover the base.  This file proves the first half of the covering — that a point of the target's
boundary which is not a tile vertex lies in the relative interior of some tile's edge.

The argument is short once `Tri.classify` is in hand: the point is in some tile by `covers`; it
cannot be interior to that tile, since a tile's interior lies in the target's interior and the
point is on the frontier; and it has no negative barycentric coordinate, being in the tile.  The
remaining case of `classify` is exactly `OnEdge`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BaseSelection

open Erdos634.Geometry

/-- A tile's carrier lies in the target's. -/
theorem tile_subset_target {N : ℕ} (D : Dissection N) (i : Fin N) :
    (D.tile i).carrier ⊆ D.target.carrier := by
  rw [← D.covers]
  exact Set.subset_iUnion (fun j => (D.tile j).carrier) i

/-- Hence a tile's interior lies in the target's interior. -/
theorem tile_interior_subset {N : ℕ} (D : Dissection N) (i : Fin N) :
    interior (D.tile i).carrier ⊆ interior D.target.carrier :=
  interior_mono (tile_subset_target D i)

/-- **Boundary points sit on edges.**  A point of the target's frontier that is not a vertex of the
tile containing it lies in the relative interior of one of that tile's edges.

This is the selection's covering half: the base of the target is part of its frontier, so every
base point but finitely many is on a tile edge, and those edges are the base chain. -/
theorem boundary_point_on_edge {N : ℕ} (D : Dissection N) {x : Plane}
    (hx : x ∈ frontier D.target.carrier)
    (hvert : ∀ i k, x ≠ (D.tile i).pts k) :
    ∃ i, Erdos634.Geometry.OnEdge D x i := by
  classical
  -- the point is in some tile
  have hmem : x ∈ D.target.carrier := by
    have hcl : IsClosed D.target.carrier := by
      rw [Tri.carrier]
      exact (Set.finite_range D.target.pts).isClosed_convexHull (𝕜 := ℝ)
    rw [← hcl.closure_eq]; exact hx.1
  obtain ⟨S, ⟨i, rfl⟩, hxi⟩ : ∃ S ∈ Set.range (fun j => (D.tile j).carrier), x ∈ S := by
    have : x ∈ ⋃ j, (D.tile j).carrier := by rw [D.covers]; exact hmem
    simpa [Set.mem_iUnion] using this
  refine ⟨i, ?_⟩
  -- no negative coordinate, since `x` is in the tile
  have hnonneg : ∀ k, 0 ≤ (D.tile i).basis.coord k x := by
    have hxi' : x ∈ (D.tile i).carrier := hxi
    rw [(D.tile i).carrier_eq_nonneg_coord] at hxi'
    exact hxi'
  -- not interior, since the target's frontier is disjoint from its interior
  have hnotint : ¬ (∀ k, 0 < (D.tile i).basis.coord k x) := by
    intro hpos
    obtain ⟨r, hr, hsub⟩ := (D.tile i).ball_subset_of_pos hpos
    have hint : x ∈ interior (D.tile i).carrier :=
      mem_interior.mpr ⟨Metric.ball x r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
    exact hx.2 (tile_interior_subset D i hint)
  rcases (D.tile i).classify (fun k => hvert i k) with h | h | h
  · exact absurd h hnotint
  · exact h
  · obtain ⟨k, hk⟩ := h
    exact absurd (hnonneg k) (not_le.mpr hk)

end Erdos634.BaseSelection
