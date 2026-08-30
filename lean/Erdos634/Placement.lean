import Mathlib
import Erdos634.ChainInstance
import Erdos634.EdgeDisjoint
import Erdos634.WallFace

/-!
# Where an edge sits along the wall: its west and east ends

Erdős #634, bridge (c).  The chain work so far speaks of an edge's *shadow* `[edgePos, edgeEnd]`.
The word layer needs the endpoints themselves — which vertex of the tile is the west end of its
base edge and which the east — and the incidence that the east end of one chain edge is the west
end of the next.

This file names the ends and proves the interval half of that incidence: a sorted family of
non-overlapping intervals with no gap is *contiguous*, consecutive members sharing an endpoint.
`ChainOrder.reach_next` supplies the no-gap side and `EdgeDisjoint.no_same_side_contact` the
non-overlap side.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Placement

open Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance

/-- The west end of an edge along `dir`: the endpoint with the smaller coordinate. -/
noncomputable def edgeWest {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (e : Fin N × Fin 3) : Plane :=
  open Classical in
  if dir ((D.tile e.1).pts e.2) ≤ dir ((D.tile e.1).pts (e.2 + 1))
  then (D.tile e.1).pts e.2 else (D.tile e.1).pts (e.2 + 1)

/-- The east end: the endpoint with the larger coordinate. -/
noncomputable def edgeEast {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (e : Fin N × Fin 3) : Plane :=
  open Classical in
  if dir ((D.tile e.1).pts e.2) ≤ dir ((D.tile e.1).pts (e.2 + 1))
  then (D.tile e.1).pts (e.2 + 1) else (D.tile e.1).pts e.2

theorem dir_edgeWest {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) :
    dir (edgeWest D dir e) = edgePos D dir e := by
  classical
  unfold edgeWest edgePos
  split <;> rename_i h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

theorem dir_edgeEast {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) :
    dir (edgeEast D dir e) = edgeEnd D dir e := by
  classical
  unfold edgeEast edgeEnd
  split <;> rename_i h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

/-- **Contiguity from no gap and no overlap.**  A family of intervals sorted by left endpoint, no
two overlapping, with the reach property of `ChainOrder.reach_next`, has consecutive members
sharing an endpoint. -/
theorem contiguous_of_no_gap (L R : ℕ → ℝ) (n k : ℕ) (hk1 : k + 1 < n)
    (hnd : ∀ j < n, L j ≤ R j)
    (hsorted : ∀ i j, i ≤ j → j < n → L i ≤ L j)
    (hnoov : ∀ i j, i < j → j < n → R i ≤ L j)
    (hreach : ∃ j ≤ k, L (k + 1) ≤ R j) :
    R k = L (k + 1) := by
  obtain ⟨j, hjk, hj⟩ := hreach
  have hup : R k ≤ L (k + 1) := hnoov k (k + 1) (by omega) hk1
  rcases eq_or_lt_of_le hjk with rfl | hlt
  · exact le_antisymm hup hj
  · have h1 : R j ≤ L k := hnoov j k hlt (by omega)
    have h2 : L k ≤ R k := hnd k (by omega)
    exact le_antisymm hup (le_trans hj (le_trans h1 h2))

/-- **The shared junction.**  Two chain edges whose shadows abut share the point: the east end of
the first *is* the west end of the second, provided the wall's coordinate separates points of the
wall.  This is the incidence `OrientWord.word_isChain` asks for at each junction. -/
theorem shared_junction {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (S : Set Plane)
    (hinj : Set.InjOn dir S) (e f : Fin N × Fin 3)
    (hE : edgeEast D dir e ∈ S) (hW : edgeWest D dir f ∈ S)
    (h : edgeEnd D dir e = edgePos D dir f) :
    edgeEast D dir e = edgeWest D dir f := by
  refine hinj hE hW ?_
  rw [dir_edgeEast, dir_edgeWest, h]

/-! ## Consecutive chain edges belong to distinct tiles

Two edges of one tile cannot both lie along the wall: if they did, all three of the tile's vertices
would lie on the wall line, and an affine functional constant on all three is constant everywhere,
by the barycentric expansion.  So a nonzero functional forbids it. -/

/-- **A functional equal at all three vertices is constant.**  Immediate from
`WallFace.affine_barycentric` and the coordinates summing to one. -/
theorem constant_of_vertices_eq (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (h0 : g (T.pts 0) = c) (h1 : g (T.pts 1) = c) (h2 : g (T.pts 2) = c) (y : Plane) :
    g y = c := by
  have hb := Erdos634.WallFace.affine_barycentric T g y
  have hw : T.basis.coord 0 y + T.basis.coord 1 y + T.basis.coord 2 y = 1 := by
    have := T.basis.sum_coord_apply_eq_one (k := ℝ) y
    rwa [Fin.sum_univ_three] at this
  rw [h0, h1, h2] at hb
  rw [hb]
  have : T.basis.coord 0 y * c + T.basis.coord 1 y * c + T.basis.coord 2 y * c
      = (T.basis.coord 0 y + T.basis.coord 1 y + T.basis.coord 2 y) * c := by ring
  rw [this, hw, one_mul]

/-- **No tile contributes two wall edges.**  If all three of a tile's vertices lie on the wall,
the wall functional is constant, contradicting `hlin`. -/
theorem no_double_wall_tile (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (hlin : ∃ y, g y ≠ c)
    (h0 : g (T.pts 0) = c) (h1 : g (T.pts 1) = c) (h2 : g (T.pts 2) = c) : False := by
  obtain ⟨y, hy⟩ := hlin
  exact hy (constant_of_vertices_eq T g c h0 h1 h2 y)

end Erdos634.Placement
