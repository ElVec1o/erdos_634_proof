import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Real.StarOrdered
import Erdos634.WallFace
import Erdos634.BaseSelection
import Erdos634.EdgeDisjoint
import Erdos634.BridgeC
import Erdos634.TilePlacement
import Erdos634.ChainWalk
import Erdos634.Placement

/-!
# Every side of the target is a wall

Erdős #634, bridge (c).  `BridgeC.chain_junctions` was written for the base, and the map rows say
"proved for the base, open for the equal sides".  Reading the statement again, nothing in it is
about the base: it takes a functional `g`, a level `c`, endpoints `a`, `b`, and four hypotheses
relating them.  What was missing was not a theorem but the *data* — a supporting functional for the
other sides.

The barycentric coordinates supply it.  For side `k` of a triangle, the coordinate of the opposite
vertex `k+2` is nonnegative on the carrier and vanishes exactly on that side, so `g = -coord (k+2)`
with level `0` is the side's wall functional.  This file builds that data for every side.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SideWall

open Erdos634.Geometry

/-- The wall functional of side `k`: minus the barycentric coordinate of the opposite vertex. -/
noncomputable def wallFun (T : Tri) (k : Fin 3) : Plane →ᵃ[ℝ] ℝ := -(T.basis.coord (k + 2))

/-- **The target lies on one side of it.** -/
theorem wallFun_le (T : Tri) (k : Fin 3) {y : Plane} (hy : y ∈ T.carrier) :
    wallFun T k y ≤ 0 := by
  have h : y ∈ T.carrier := hy
  rw [T.carrier_eq_nonneg_coord] at h
  simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply, neg_nonpos]
  exact h (k + 2)

/-- **It vanishes on the side.** -/
theorem wallFun_eq_zero (T : Tri) (k : Fin 3) {y : Plane} (hy : y ∈ T.edge k) :
    wallFun T k y = 0 := by
  have hk1 : (k + 2 : Fin 3) ≠ k := by
    have : ∀ x : Fin 3, x + 2 ≠ x := by decide
    exact this k
  have hk2 : (k + 2 : Fin 3) ≠ k + 1 := by
    have : ∀ x : Fin 3, x + 2 ≠ x + 1 := by decide
    exact this k
  have e1 : T.basis.coord (k + 2) (T.pts k) = 0 := by
    have := T.basis.coord_apply (k + 2) k
    simp only [if_neg hk1] at this; exact this
  have e2 : T.basis.coord (k + 2) (T.pts (k + 1)) = 0 := by
    have := T.basis.coord_apply (k + 2) (k + 1)
    simp only [if_neg hk2] at this; exact this
  rw [Tri.edge] at hy
  obtain ⟨u, v, _, _, huv, rfl⟩ := hy
  have hx : u • T.pts k + v • T.pts (k + 1)
      = AffineMap.lineMap (T.pts k) (T.pts (k + 1)) v := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub]
    have : u = 1 - v := by linarith
    rw [this]; module
  simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero]
  rw [hx, AffineMap.apply_lineMap, e1, e2]
  simp

/-- **And it meets the target exactly in that side.**  This is `WallFace.face_eq_edge` in the
coordinate form, and it is what makes the side a *face* rather than a chord. -/
theorem wallFun_face (T : Tri) (k : Fin 3) {y : Plane} (hy : y ∈ T.carrier)
    (h0 : wallFun T k y = 0) : y ∈ T.edge k := by
  have hnn : ∀ j, 0 ≤ T.basis.coord j y := by
    have h : y ∈ T.carrier := hy
    rw [T.carrier_eq_nonneg_coord] at h
    exact h
  have hz : T.basis.coord (k + 2) y = 0 := by
    simpa [wallFun] using h0
  have hseg := Erdos634.BaseSelection.coord_zero_mem_segment T (k + 2) y hz hnn
  have hs1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have hs2 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  rw [hs1 k, hs2 k] at hseg
  rw [Tri.edge]
  exact hseg

/-- **A side lies in the frontier.**  A point of an edge has a vanishing barycentric coordinate, and
moving off it in the direction where that coordinate decreases leaves the carrier, so the point is
not interior. -/
theorem edge_subset_frontier (T : Tri) (k : Fin 3) : T.edge k ⊆ frontier T.carrier := by
  intro x hx
  have hxc : x ∈ T.carrier := T.edge_subset_carrier k hx
  have hcl : IsClosed T.carrier := by
    rw [Tri.carrier]
    exact (Set.finite_range T.pts).isClosed_convexHull (𝕜 := ℝ)
  refine ⟨by rw [hcl.closure_eq]; exact hxc, ?_⟩
  intro hint
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hint
  obtain ⟨v, hv⟩ := Erdos634.EdgeDisjoint.exists_pos_dir T (k + 2)
  have hvne : v ≠ 0 := by rintro rfl; simp at hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  set t : ℝ := min (r / (2 * ‖v‖)) 1 with ht
  have htpos : 0 < t := lt_min (by positivity) one_pos
  set y : Plane := x + t • (-v) with hy
  have hdist : dist y x < r := by
    have : dist y x = t * ‖v‖ := by
      simp [hy, dist_eq_norm, norm_smul, abs_of_pos htpos]
    rw [this]
    calc t * ‖v‖ ≤ (r / (2 * ‖v‖)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hvpos)
      _ = r / 2 := by field_simp
      _ < r := by linarith
  have hyc : y ∈ T.carrier := interior_subset (hsub (Metric.mem_ball.mpr hdist))
  have hx0 : T.basis.coord (k + 2) x = 0 := by
    have := wallFun_eq_zero T k hx
    simpa [wallFun] using this
  have hyneg : T.basis.coord (k + 2) y < 0 := by
    have := Erdos634.EdgeDisjoint.coord_add_smul (T.basis.coord (k + 2)) x (-v) t
    rw [hy, this, hx0]
    simp only [map_neg]
    nlinarith [hv, htpos]
  have : 0 ≤ T.basis.coord (k + 2) y := by
    have h : y ∈ T.carrier := hyc
    rw [T.carrier_eq_nonneg_coord] at h
    exact h (k + 2)
  linarith

/-! ## The chain, at any side

`BridgeC.chain_junctions` with the wall data of side `k`.  Only two inputs remain the caller's:
a coordinate `dir` along the side, separating its points, and the non-degeneracy of the tiles that
lay edges there. -/

open Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.Placement in
/-- **The chain's junctions, at an arbitrary side of the target.** -/
theorem side_chain_junctions {N : ℕ} (hN : 0 < N) (D : Dissection N) (k : Fin 3)
    (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, (wallFun D.target k).linear v = 0 → dir v = 0 → v = 0)
    (hthird : ∀ p ∈ Erdos634.BaseChain.wallList D (wallFun D.target k) 0,
      wallFun D.target k ((D.tile p.1).pts (p.2 + 2)) < 0) :
    ∃ E : ℕ → Fin N × Fin 3,
      ∀ j, j + 1 < (Erdos634.BaseChain.wallList D (wallFun D.target k) 0).length →
        edgeEast D dir (E j) = edgeWest D dir (E (j + 1)) := by
  have hab : D.target.pts k ≠ D.target.pts (k + 1) := by
    have h : ∀ x : Fin 3, x ≠ x + 1 := by decide
    exact Erdos634.TilePlacement.pts_ne D.target (h k)
  refine Erdos634.BridgeC.chain_junctions hN D (wallFun D.target k) 0 dir hker
    (fun y hy => wallFun_le D.target k hy) (D.target.pts k) (D.target.pts (k + 1)) hab ?_ ?_ ?_
    hthird
  · intro y hy
    exact edge_subset_frontier D.target k (by rw [Tri.edge]; exact hy)
  · intro y hy
    exact wallFun_eq_zero D.target k (by rw [Tri.edge]; exact hy)
  · intro y hy h0
    have := wallFun_face D.target k hy h0
    rw [Tri.edge] at this
    exact this

/-! ## The side's own vertices

`BridgeC.junction_frontier_nonvertex` needs to know that the target's vertices are the side's two
endpoints and one point strictly inside the half-plane.  For the wall functional of side `k` that is
immediate: the opposite vertex has coordinate `1`, so the functional takes the value `-1` there. -/

/-- **The target's vertices, relative to side `k`.** -/
theorem side_vertices (T : Tri) (k j : Fin 3) :
    T.pts j = T.pts k ∨ T.pts j = T.pts (k + 1) ∨ wallFun T k (T.pts j) < 0 := by
  have hfin : ∀ a b : Fin 3, a = b ∨ a = b + 1 ∨ a = b + 2 := by decide
  have hself : T.basis.coord (k + 2) (T.pts (k + 2)) = 1 := by
    have h := T.basis.coord_apply (k + 2) (k + 2)
    simp only [if_pos rfl] at h; exact h
  rcases hfin j k with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · refine Or.inr (Or.inr ?_)
    simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply]
    rw [hself]
    norm_num

/-- **A junction of side `k` is a non-vertex point of the frontier.**  `SideWall`'s data fed to
`BridgeC.junction_frontier_nonvertex`. -/
theorem side_junction_frontier_nonvertex {N : ℕ} (D : Dissection N) (k : Fin 3)
    (dir : Plane →ₗ[ℝ] ℝ) {p : Plane} (hp : p ∈ D.target.carrier)
    (hgp : wallFun D.target k p = 0)
    (hstrict : min (dir (D.target.pts k)) (dir (D.target.pts (k + 1))) < dir p ∧
      dir p < max (dir (D.target.pts k)) (dir (D.target.pts (k + 1)))) :
    p ∈ frontier D.target.carrier ∧ p ∉ Set.range D.target.pts := by
  refine Erdos634.BridgeC.junction_frontier_nonvertex D (wallFun D.target k) 0 dir
    (D.target.pts k) (D.target.pts (k + 1)) ?_ ?_ ?_ hp hgp hstrict
  · intro y hy
    exact edge_subset_frontier D.target k (by rw [Tri.edge]; exact hy)
  · intro y hy h0
    have := wallFun_face D.target k hy h0
    rw [Tri.edge] at this
    exact this
  · intro j
    exact side_vertices D.target k j

/-! ## The side's walk

`side_chain_junctions` gives the chain; `ChainWalk.chain_walk` turns a chain into a walk.  The one
thing to check in between is that the junction equality of *points* becomes contiguity of
*shadows*, which is `Placement.dir_edgeEast` and `.dir_edgeWest`. -/

open Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.Placement in
/-- **A side's chain satisfies its walk equation.**  For a chain whose consecutive edges meet and
whose shadows have the three tile lengths, the span is `P'a + Q'b + R'c` with `P'`, `Q'`, `R'` the
counts of edges of each length. -/
theorem side_walk {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (n : ℕ) (hn : 1 ≤ n) (E : ℕ → Fin N × Fin 3) (a b c : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmeet : ∀ j, j + 1 < n → edgeEast D dir (E j) = edgeWest D dir (E (j + 1)))
    (hlen : ∀ j ∈ Finset.range n,
      edgeEnd D dir (E j) - edgePos D dir (E j) ∈ ({a, b, c} : Finset ℝ)) :
    edgeEnd D dir (E (n - 1)) - edgePos D dir (E 0)
      = ((Finset.range n).filter
          (fun j => edgeEnd D dir (E j) - edgePos D dir (E j) = a)).card * a
        + ((Finset.range n).filter
          (fun j => edgeEnd D dir (E j) - edgePos D dir (E j) = b)).card * b
        + ((Finset.range n).filter
          (fun j => edgeEnd D dir (E j) - edgePos D dir (E j) = c)).card * c := by
  refine Erdos634.ChainWalk.chain_walk n hn (fun j => edgePos D dir (E j))
    (fun j => edgeEnd D dir (E j)) a b c hab hac hbc ?_ hlen
  intro j hj
  have h := hmeet j hj
  have h1 : dir (edgeEast D dir (E j)) = edgeEnd D dir (E j) := dir_edgeEast D dir (E j)
  have h2 : dir (edgeWest D dir (E (j + 1))) = edgePos D dir (E (j + 1)) :=
    dir_edgeWest D dir (E (j + 1))
  show edgeEnd D dir (E j) = edgePos D dir (E (j + 1))
  rw [← h1, ← h2, h]

end Erdos634.SideWall
