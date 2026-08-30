import Erdos634.ChainOrder
import Erdos634.OrientBridge

/-!
# The chain's intervals are the edges' shadows

Erdős #634, bridge (c).  `ChainOrder` proves the no-gap property for intervals on `ℝ`;
`OrientBridge.edgePos` keys a tile edge by the smaller of its endpoints' coordinates.  This file
supplies the missing identification: the shadow of a tile edge under a linear functional is exactly
the interval between its endpoints' coordinates, so the chain really is a family of closed
intervals and `ChainOrder.reach_next` applies to it.

What is still not built is the *selection* — which edges of a dissection form the base chain, and
that their shadows cover the base.  That is a property of a particular dissection, not of the
machinery, and it enters `consecutive_edges_meet` as hypotheses.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ChainInstance

open Erdos634.Geometry Erdos634.OrientBridge Set

/-- The far end of an edge's shadow: the larger of the two endpoint coordinates. -/
noncomputable def edgeEnd {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (e : Fin N × Fin 3) : ℝ :=
  max (dir ((D.tile e.1).pts e.2)) (dir ((D.tile e.1).pts (e.2 + 1)))

/-- **An edge's shadow is an interval.**  The image of a tile edge under a linear functional is the
closed interval between the coordinates of its endpoints. -/
theorem edge_image_eq_uIcc (T : Tri) (i : Fin 3) (dir : Plane →ₗ[ℝ] ℝ) :
    dir '' (T.edge i) = uIcc (dir (T.pts i)) (dir (T.pts (i + 1))) := by
  have h := image_segment ℝ dir.toAffineMap (T.pts i) (T.pts (i + 1))
  simp only [LinearMap.coe_toAffineMap] at h
  rw [Tri.edge, h, segment_eq_uIcc]

/-- The same, with the endpoints named by the chain's key and its far end. -/
theorem edge_image_eq_Icc {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (e : Fin N × Fin 3) :
    dir '' ((D.tile e.1).edge e.2) = Icc (edgePos D dir e) (edgeEnd D dir e) := by
  rw [edge_image_eq_uIcc, uIcc, edgePos, edgeEnd]

/-- The key never exceeds the far end. -/
theorem edgePos_le_edgeEnd {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (e : Fin N × Fin 3) : edgePos D dir e ≤ edgeEnd D dir e :=
  le_trans (min_le_left _ _) (le_max_left _ _)

/-- **Consecutive edges of the base chain meet.**  Given an enumeration `E` of the chain in order
of its key, whose shadows lie in the base and cover it, one of the first `k+1` edges reaches the
`(k+1)`-st edge's key: there is no uncovered stretch between them.

The hypotheses are the selection facts about a particular dissection — that these edges are the
base chain, in order, and that their shadows cover the base — and the conclusion is what the march
induction consumes. -/
theorem consecutive_edges_meet {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (n : ℕ) (E : ℕ → Fin N × Fin 3) (a b : ℝ) (k : ℕ) (hk1 : k + 1 < n)
    (hcov : Icc a b ⊆ ⋃ j ∈ Finset.range n, dir '' ((D.tile (E j).1).edge (E j).2))
    (hsub : ∀ j, j < n → dir '' ((D.tile (E j).1).edge (E j).2) ⊆ Icc a b)
    (hsorted : ∀ i j, i ≤ j → j < n → edgePos D dir (E i) ≤ edgePos D dir (E j)) :
    ∃ j ≤ k, edgePos D dir (E (k + 1)) ≤ edgeEnd D dir (E j) := by
  refine Erdos634.ChainOrder.reach_next n (fun j => edgePos D dir (E j))
    (fun j => edgeEnd D dir (E j)) a b k hk1
    (fun j _ => edgePos_le_edgeEnd D dir (E j)) ?_ ?_ hsorted
  · refine hcov.trans (Set.iUnion₂_mono fun j _ => ?_)
    rw [edge_image_eq_Icc]
  · intro j hj
    rw [← edge_image_eq_Icc]
    exact hsub j hj

end Erdos634.ChainInstance
