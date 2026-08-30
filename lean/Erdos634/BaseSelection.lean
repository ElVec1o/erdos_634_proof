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

/-- **A vanishing barycentric coordinate puts the point on the opposite edge.**  Written out from
the affine-basis expansion: the two surviving coordinates are nonnegative and sum to one. -/
theorem coord_zero_mem_segment (T : Tri) (k : Fin 3) (x : Plane)
    (h0 : T.basis.coord k x = 0) (hnn : ∀ j, 0 ≤ T.basis.coord j x) :
    x ∈ segment ℝ (T.pts (k+1)) (T.pts (k+2)) := by
  have hx : x = (T.basis.coord 0 x) • T.pts 0 + (T.basis.coord 1 x) • T.pts 1
        + (T.basis.coord 2 x) • T.pts 2 := by
    have h := T.basis.affineCombination_coord_eq_self (k := ℝ) x
    rw [Finset.affineCombination_eq_linear_combination] at h
    · rw [Fin.sum_univ_three] at h; simpa [Tri.basis] using h.symm
    · exact T.basis.sum_coord_apply_eq_one x
  have hsum : T.basis.coord 0 x + T.basis.coord 1 x + T.basis.coord 2 x = 1 := by
    have := T.basis.sum_coord_apply_eq_one (k := ℝ) x
    rwa [Fin.sum_univ_three] at this
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · refine ⟨T.basis.coord 1 x, T.basis.coord 2 x, hnn 1, hnn 2, by linarith [h0, hsum], ?_⟩
    simp only [show ((0:Fin 3)+1) = 1 from rfl, show ((0:Fin 3)+2) = 2 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
  · refine ⟨T.basis.coord 2 x, T.basis.coord 0 x, hnn 2, hnn 0, by linarith [h0, hsum], ?_⟩
    simp only [show ((1:Fin 3)+1) = 2 from rfl, show ((1:Fin 3)+2) = 0 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
  · refine ⟨T.basis.coord 0 x, T.basis.coord 1 x, hnn 0, hnn 1, by linarith [h0, hsum], ?_⟩
    simp only [show ((2:Fin 3)+1) = 0 from rfl, show ((2:Fin 3)+2) = 1 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module

/-- **The target's frontier is covered by tile edges.**  A frontier point that is a tile vertex is
an endpoint of that tile's edge; any other lies in the relative interior of one, by
`boundary_point_on_edge`.  No density argument is needed, the vertices being handled directly.

This is the covering the base chain needs.  What it does not give is the *chain*: which edges to
take, in what order, and that their shadows are intervals meeting end to end — that is
`ChainInstance.consecutive_edges_meet`, whose hypotheses this feeds but does not discharge. -/
theorem frontier_subset_edges {N : ℕ} (D : Dissection N) {x : Plane}
    (hx : x ∈ frontier D.target.carrier) :
    ∃ i k, x ∈ (D.tile i).edge k := by
  classical
  by_cases hv : ∃ i k, x = (D.tile i).pts k
  · obtain ⟨i, k, rfl⟩ := hv
    exact ⟨i, k, by rw [Tri.edge]; exact left_mem_segment ℝ _ _⟩
  · push_neg at hv
    obtain ⟨i, k, h0, hpos⟩ := boundary_point_on_edge D hx (fun i k => hv i k)
    have hnn : ∀ j, 0 ≤ (D.tile i).basis.coord j x := by
      intro j
      by_cases hjk : j = k
      · exact hjk ▸ le_of_eq h0.symm
      · exact le_of_lt (hpos j hjk)
    refine ⟨i, k + 1, ?_⟩
    rw [Tri.edge, show k + 1 + 1 = k + 2 from by omega]
    exact coord_zero_mem_segment (D.tile i) k x h0 hnn

end Erdos634.BaseSelection
