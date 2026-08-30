import Erdos634.BaseSelection

/-!
# An edge touching the wall in its interior lies along the wall

Erdős #634, bridge (c), the last step of the selection.  `BaseSelection.frontier_subset_edges` says
every point of the target's frontier is on some tile edge, but not that the edge lies *along* the
base: a priori it could cross it.  It cannot, and the reason is an inequality rather than geometry.

The target lies in a closed half-plane bounded by the line of its base, so an affine functional `g`
cutting that line attains its maximum `c` on the whole target.  An edge with an interior point on
the line has `g = c` at an interior point of a segment on which `g ≤ c`; an affine function on a
segment attaining its maximum in the interior is constant there.  So both endpoints lie on the
line, and the edge lies along the wall.

That is what makes the base chain a chain of intervals rather than an arbitrary family of edges.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WallEdges

open Erdos634.Geometry

/-- **An affine function on a segment attaining its bound strictly inside is constant.** -/
theorem endpoints_of_interior_max (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (p q : Plane) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hp : g p ≤ c) (hq : g q ≤ c)
    (hx : g (AffineMap.lineMap p q t) = c) :
    g p = c ∧ g q = c := by
  rw [AffineMap.apply_lineMap] at hx
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] at hx
  constructor <;> nlinarith

/-- **The wall lemma.**  If a tile edge has a point of the open wall line in its relative interior,
both its endpoints lie on that line: the edge lies along the wall.

`hwall` is the half-plane containment — the whole target on one side of the base line, which is
what makes the base a side of the target rather than a chord. -/
theorem edge_along_wall {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c)
    (i : Fin N) (k : Fin 3) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hx : g (AffineMap.lineMap ((D.tile i).pts k) ((D.tile i).pts (k + 1)) t) = c) :
    g ((D.tile i).pts k) = c ∧ g ((D.tile i).pts (k + 1)) = c := by
  have hsub := Erdos634.BaseSelection.tile_subset_target D i
  have hmem : ∀ j : Fin 3, (D.tile i).pts j ∈ (D.tile i).carrier := by
    intro j
    rw [Tri.carrier]
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  have hp : g ((D.tile i).pts k) ≤ c := hwall _ (hsub (hmem k))
  have hq : g ((D.tile i).pts (k + 1)) ≤ c := hwall _ (hsub (hmem (k + 1)))
  exact endpoints_of_interior_max g c _ _ t ht0 ht1 hp hq hx


/-! ## The base chain, assembled

With the wall lemma in hand the base chain is definable: the edges whose two endpoints lie on the
wall line.  Every base point is on one of them.  The finitely many tile vertices are handled by
density (`SegmentDense.subset_closure_diff_finite`) rather than by a separate argument, the union
of the chain's edges being closed. -/

/-- An edge is a *wall edge* when both its endpoints lie on the wall line. -/
def WallEdge {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (p : Fin N × Fin 3) : Prop :=
  g ((D.tile p.1).pts p.2) = c ∧ g ((D.tile p.1).pts (p.2 + 1)) = c

/-- A point of a segment that is neither endpoint is `lineMap` at an interior parameter. -/
theorem mem_segment_interior {p q x : Plane} (hx : x ∈ segment ℝ p q) (hp : x ≠ p) (hq : x ≠ q) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = AffineMap.lineMap p q t := by
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := hx
  have hu0 : u ≠ 0 := by rintro rfl; exact hq (by simp_all)
  have hv0 : v ≠ 0 := by rintro rfl; exact hp (by simp_all)
  refine ⟨v, lt_of_le_of_ne hv (Ne.symm hv0), by
    rcases lt_or_eq_of_le hu with h | h
    · linarith
    · exact absurd h.symm hu0, ?_⟩
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_sub]
  have : u = 1 - v := by linarith
  rw [this]
  module

/-- **The base is covered by wall edges.**  A nondegenerate segment of the target's frontier lying
on the wall line is contained in the union of the edges whose endpoints lie on that line.

This discharges the covering hypothesis of `ChainInstance.consecutive_edges_meet` for the base;
what it still does not fix is the *order*, which is `edgePos` and the sortedness. -/
theorem base_covered_by_wall_edges {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c) :
    segment ℝ a b ⊆ ⋃ p ∈ {p : Fin N × Fin 3 | WallEdge D g c p}, (D.tile p.1).edge p.2 := by
  classical
  set U : Set Plane := ⋃ p ∈ {p : Fin N × Fin 3 | WallEdge D g c p}, (D.tile p.1).edge p.2 with hU
  -- the union is closed
  have hUclosed : IsClosed U := by
    rw [hU]
    exact Set.Finite.isClosed_biUnion (Set.toFinite _)
      (fun p _ => (D.tile p.1).isClosed_edge p.2)
  -- the tile vertices form a finite set
  set V : Set Plane := Set.range (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2) with hV
  have hVfin : V.Finite := Set.finite_range _
  -- off the vertices, every base point is on a wall edge
  have hoff : segment ℝ a b \ V ⊆ U := by
    rintro x ⟨hxs, hxv⟩
    obtain ⟨i, k, hxe⟩ := Erdos634.BaseSelection.frontier_subset_edges D (hbase hxs)
    have hne : ∀ j : Fin 3, x ≠ (D.tile i).pts j := by
      intro j hj; exact hxv ⟨(i, j), hj.symm⟩
    rw [Tri.edge] at hxe
    obtain ⟨t, ht0, ht1, hxt⟩ := mem_segment_interior hxe (hne k) (hne (k + 1))
    have hgc : g (AffineMap.lineMap ((D.tile i).pts k) ((D.tile i).pts (k + 1)) t) = c := by
      rw [← hxt]; exact hline x hxs
    have hw := edge_along_wall D g c hwall i k t ht0 ht1 hgc
    exact Set.mem_biUnion (show (i, k) ∈ {p : Fin N × Fin 3 | WallEdge D g c p} from hw)
      (by rw [Tri.edge]; exact hxt ▸ hxe)
  -- density closes the gap at the vertices
  intro x hx
  have := Erdos634.SegmentDense.subset_closure_diff_finite hab hVfin hx
  exact hUclosed.closure_subset (closure_mono hoff this)

end Erdos634.WallEdges
