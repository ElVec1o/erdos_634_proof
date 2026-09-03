import Erdos634.RouteOne
import Erdos634.CertCoord
import Mathlib.LinearAlgebra.AffineSpace.MidpointZero

/-!
# The `π` branch at `V`, pinned — Route 1's flank without the straight-angle assumption

Erdős #634, `conj:advance` / `rem:route1uniform`.

`route_one_flank_composed` reaches its conclusion — the tile serving the tangential approach at `V`
lays a horizontal rightward edge there — only after excluding `localAngle = π` for that tile, and it
excludes it with `hcard`/`hb`: the `π`-count at `V` is one and the tile *below the line* carries it.
That pair is exactly the fact `conj:advance` lists as unproved ("that a through-edge, rather than a
junction, runs below the line at `V`"), so the chain's dependence on the open case runs through this
one step.

This file removes that dependence from the step. The observation is that the `π` branch does not
need excluding: it is *pinned* by the same `habove` the vertex branch already assumes.

If `V` is not a vertex of `T` and `T.localAngle V = π`, then `V` has one barycentric coordinate `0`
and the other two strictly positive, so `V` lies strictly between two vertices of `T` — and
`sub_vertex_eq_combo`, applied at each of them, writes the two displacements as opposite positive
multiples of one vector `w`. With every carrier point weakly above `V`, both displacements have
nonnegative second component; being antiparallel, both components vanish, so `w` is *horizontal*.
`w ≠ 0` because otherwise `V` would be a vertex. Hence one of the two vertices lies strictly to the
right of `V` at exactly `V`'s height.

Combining with `escape_flank` for the vertex branch gives `serving_lays_rightward`: with only the
two exclusions that are already discharged independently (`serving_ne_zero` from the approach,
`serving_ne_two_pi` from `V` lying in another tile's carrier), the serving tile lays a horizontal
rightward segment at `V` — **no `π`-count, no below-tile, no straight angle**.

**Scope, exactly.** This does *not* close `conj:advance`'s case (a). In the vertex branch the
rightward segment is a whole edge with `V` as its endpoint, so its length is `a`, `b` or `c` and
`overshoot_dichotomy` applies; in the `π` branch it is a *suffix* of an edge, of unconstrained
length, and the dichotomy does not apply to it as it stands. What the file changes is the shape of
the remaining gap: case (a) is not needed to put a horizontal rightward segment at `V`, only to know
that segment is a whole edge from `V`.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry

namespace Erdos634.RouteOne

/-- **The `π` case, read off the definition.** A point that is not a vertex and whose local angle is
`π` has one barycentric coordinate `0` and the other two strictly positive — it lies in the relative
interior of the edge opposite that coordinate. -/
theorem coords_of_localAngle_pi (T : Tri) (V : Plane)
    (hnv : ¬ ∃ j, V = T.pts j) (hpi : T.localAngle V = Real.pi) :
    ∃ k : Fin 3, T.basis.coord k V = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j V := by
  classical
  rw [Erdos634.Geometry.Tri.localAngle] at hpi
  split at hpi
  · rename_i hv; exact absurd hv hnv
  · split at hpi
    · have := Real.pi_pos; linarith
    · split at hpi
      · rename_i h3; exact h3
      · have := Real.pi_pos; linarith

/-- **The through-edge at `V` is horizontal, and reaches to the right.** A tile whose every point
lies weakly above `V`, and which has `V` in the relative interior of one of its edges, has that edge
horizontal; in particular one of its endpoints lies strictly right of `V` at `V`'s own height.

No hypothesis about the figure at `V`, about a tile below, or about the `π`-count. -/
theorem through_edge_lays_rightward (T : Tri) (V : Plane)
    (hnv : ¬ ∃ j, V = T.pts j) (hpi : T.localAngle V = Real.pi)
    (habove : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - V) 1) :
    ∃ P : Plane, P ∈ T.carrier ∧ (P - V) 1 = 0 ∧ 0 < (P - V) 0 := by
  classical
  obtain ⟨k, hk0, hkpos⟩ := coords_of_localAngle_pi T V hnv hpi
  have hidx : ∀ x : Fin 3, (x + 1) + 1 = x + 2 ∧ (x + 1) + 2 = x
      ∧ (x + 2) + 1 = x ∧ (x + 2) + 2 = x + 1 ∧ (x + 1 ≠ x) ∧ (x + 2 ≠ x) := by decide
  obtain ⟨i11, i12, i21, i22, hne1, hne2⟩ := hidx k
  have hc1 : 0 < T.basis.coord (k + 1) V := hkpos _ hne1
  have hc2 : 0 < T.basis.coord (k + 2) V := hkpos _ hne2
  have e1 := sub_vertex_eq_combo T (k + 1) V
  have e2 := sub_vertex_eq_combo T (k + 2) V
  rw [i11, i12, hk0, zero_smul, add_zero] at e1
  rw [i21, i22, hk0, zero_smul, zero_add] at e2
  -- `e1 : V - pts (k+1) = c₂ • w`,  `e2 : V - pts (k+2) = c₁ • (-w)`, with `w = pts (k+2) - pts (k+1)`
  have hmem1 : T.pts (k + 1) ∈ T.carrier := by
    rw [Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨k + 1, rfl⟩
  have hmem2 : T.pts (k + 2) ∈ T.carrier := by
    rw [Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨k + 2, rfl⟩
  have d1 : T.pts (k + 1) - V
      = -(T.basis.coord (k + 2) V • (T.pts (k + 2) - T.pts (k + 1))) := by
    rw [← e1]; abel
  have d2 : T.pts (k + 2) - V
      = T.basis.coord (k + 1) V • (T.pts (k + 2) - T.pts (k + 1)) := by
    rw [show T.pts (k + 2) - V = -(V - T.pts (k + 2)) by abel, e2]
    rw [show T.pts (k + 1) - T.pts (k + 2) = -(T.pts (k + 2) - T.pts (k + 1)) by abel]
    rw [smul_neg, neg_neg]
  have c1y := congrArg (fun v : Plane => v 1) d1
  have c2y := congrArg (fun v : Plane => v 1) d2
  have c1x := congrArg (fun v : Plane => v 0) d1
  have c2x := congrArg (fun v : Plane => v 0) d2
  simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul] at c1y c2y c1x c2x
  have hab1 : 0 ≤ (T.pts (k + 1) - V) 1 := habove _ hmem1
  have hab2 : 0 ≤ (T.pts (k + 2) - V) 1 := habove _ hmem2
  rw [c1y] at hab1
  rw [c2y] at hab2
  have hwy : (T.pts (k + 2) - T.pts (k + 1)) 1 = 0 := by nlinarith
  have hwx : (T.pts (k + 2) - T.pts (k + 1)) 0 ≠ 0 := by
    intro hwx0
    have hw : T.pts (k + 2) - T.pts (k + 1) = 0 := by
      have hn : ‖T.pts (k + 2) - T.pts (k + 1)‖ = 0 := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, hwx0, hwy]
        simp
      exact norm_eq_zero.mp hn
    rw [hw, smul_zero] at e1
    exact hnv ⟨k + 1, by have := sub_eq_zero.mp e1; exact this⟩
  rcases lt_or_gt_of_ne hwx with hneg | hpos
  · refine ⟨T.pts (k + 1), hmem1, ?_, ?_⟩
    · rw [c1y, hwy]; ring
    · rw [c1x]; nlinarith
  · refine ⟨T.pts (k + 2), hmem2, ?_, ?_⟩
    · rw [c2y, hwy]; ring
    · rw [c2x]; nlinarith

/-- **The serving tile lays a horizontal rightward segment at `V`, unconditionally.** The only
inputs are the two exclusions already discharged elsewhere — `localAngle ≠ 0` (`serving_ne_zero`,
from the approach points) and `localAngle ≠ 2π` (`serving_ne_two_pi`, from `V` lying in another
tile's carrier) — together with `habove` and the tangential approach.

Neither `hcard` (the `π`-count) nor `hb` (a tile below carrying the straight angle) appears: the
`π` branch is pinned by `through_edge_lays_rightward` instead of excluded. -/
theorem serving_lays_rightward (T : Tri) (V : Plane)
    (hne0 : T.localAngle V ≠ 0) (hne2pi : T.localAngle V ≠ 2 * Real.pi)
    (habove : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - V) 1)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ T.carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0)) :
    ∃ P : Plane, P ∈ T.carrier ∧ (P - V) 1 = 0 ∧ 0 < (P - V) 0 := by
  classical
  by_cases hnv : ∃ j, V = T.pts j
  · obtain ⟨j, hj⟩ := hnv
    have hab' : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - T.pts j) 1 := by
      intro q hq; rw [← hj]; exact habove q hq
    have hse' : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ T.carrier ∧
        0 < (q - T.pts j) 0 ∧ (q - T.pts j) 1 ≤ δ * ((q - T.pts j) 0) := by
      intro δ hδ; rw [← hj]; exact hserve δ hδ
    rcases escape_flank T j hab' hse' with ⟨hy, hx⟩ | ⟨hy, hx⟩
    · refine ⟨T.pts (j + 1), ?_, ?_, ?_⟩
      · rw [Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨j + 1, rfl⟩
      · rw [hj]; exact hy
      · rw [hj]; exact hx
    · refine ⟨T.pts (j + 2), ?_, ?_, ?_⟩
      · rw [Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨j + 2, rfl⟩
      · rw [hj]; exact hy
      · rw [hj]; exact hx
  · rcases Erdos634.PinPlumbing.localAngle_cases T V with
      ⟨j, hj, -⟩ | h2pi | hpi | h0
    · exact absurd ⟨j, hj⟩ hnv
    · exact absurd h2pi hne2pi
    · exact through_edge_lays_rightward T V hnv hpi habove
    · exact absurd h0 hne0

/-! ## Vacuity check for the `π` branch

Project rule: exhibit a witness before reporting a conditional as progress.  The `π` branch of
`serving_lays_rightward` combines `localAngle V = π` with `habove`, and those must be shown jointly
satisfiable — otherwise `through_edge_lays_rightward` would be about nothing.  The midpoint of an
edge always has local angle `π`, for any triangle and any edge, which is the reusable half; taking
an edge that is horizontal with the triangle above it supplies `habove`. -/

/-- The barycentric coordinates of a midpoint are the averages of the endpoints'. -/
theorem coord_midpoint (T : Tri) (j : Fin 3) (a b : Plane) :
    T.basis.coord j (midpoint ℝ a b)
      = (T.basis.coord j b - T.basis.coord j a) * (1 / 2) + T.basis.coord j a := by
  rw [← lineMap_one_half, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
  ring

/-- The three barycentric coordinates of an edge midpoint: `0` opposite, `1/2` at each endpoint. -/
theorem coord_midpoint_edge (T : Tri) (k : Fin 3) :
    T.basis.coord k (midpoint ℝ (T.pts (k + 1)) (T.pts (k + 2))) = 0 ∧
    T.basis.coord (k + 1) (midpoint ℝ (T.pts (k + 1)) (T.pts (k + 2))) = 1 / 2 ∧
    T.basis.coord (k + 2) (midpoint ℝ (T.pts (k + 1)) (T.pts (k + 2))) = 1 / 2 := by
  have hidx : ∀ x : Fin 3, (x ≠ x + 1) ∧ (x ≠ x + 2) ∧ (x + 1 ≠ x + 2) := by decide
  obtain ⟨h1, h2, h12⟩ := hidx k
  have hcne : ∀ i j : Fin 3, i ≠ j → T.basis.coord i (T.pts j) = 0 :=
    fun i j h => T.basis.coord_apply_ne h
  have hceq : ∀ i : Fin 3, T.basis.coord i (T.pts i) = 1 := fun i => T.basis.coord_apply_eq i
  refine ⟨?_, ?_, ?_⟩
  · rw [coord_midpoint, hcne k (k + 1) h1, hcne k (k + 2) h2]; ring
  · rw [coord_midpoint, hcne (k + 1) (k + 2) h12, hceq (k + 1)]; ring
  · rw [coord_midpoint, hcne (k + 2) (k + 1) (Ne.symm h12), hceq (k + 2)]; ring

/-- **The midpoint of an edge is not a vertex**: its coordinate opposite that edge is `0`, and
every vertex has some coordinate `1`. -/
theorem midpoint_not_vertex (T : Tri) (k : Fin 3) :
    ¬ ∃ j, midpoint ℝ (T.pts (k + 1)) (T.pts (k + 2)) = T.pts j := by
  obtain ⟨hk, hk1, hk2⟩ := coord_midpoint_edge T k
  have hcases : ∀ j : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by
    have h : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
    exact fun j => h k j
  rintro ⟨j, hj⟩
  have hself : T.basis.coord j (T.pts j) = 1 := T.basis.coord_apply_eq j
  rcases hcases j with rfl | rfl | rfl
  · rw [← hj, hk] at hself; norm_num at hself
  · rw [← hj, hk1] at hself; norm_num at hself
  · rw [← hj, hk2] at hself; norm_num at hself

/-- **The midpoint of an edge has local angle `π`.**  Any triangle, any edge — the witness the
`π` branch needs, and a fact worth having on its own. -/
theorem midpoint_localAngle_pi (T : Tri) (k : Fin 3) :
    T.localAngle (midpoint ℝ (T.pts (k + 1)) (T.pts (k + 2))) = Real.pi := by
  classical
  obtain ⟨hk, hk1, hk2⟩ := coord_midpoint_edge T k
  have hcases : ∀ j : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by
    have h : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
    exact fun j => h k j
  have hkpos : ∀ j, j ≠ k →
      0 < T.basis.coord j (midpoint ℝ (T.pts (k + 1)) (T.pts (k + 2))) := by
    intro j hj
    rcases hcases j with rfl | rfl | rfl
    · exact absurd rfl hj
    · rw [hk1]; norm_num
    · rw [hk2]; norm_num
  rw [Erdos634.Geometry.Tri.localAngle, dif_neg (midpoint_not_vertex T k),
    if_neg (by intro hall; exact absurd hk (ne_of_gt (hall k))),
    if_pos ⟨k, hk, hkpos⟩]

/-- **The `π` branch is not vacuous.**  A triangle with a horizontal edge, sitting above it, has
its midpoint satisfying all three hypotheses of `through_edge_lays_rightward` at once. -/
theorem through_edge_hyps_satisfiable (T : Tri) (k : Fin 3)
    (hflat : (T.pts (k + 2) - T.pts (k + 1)) 1 = 0)
    (hup : 0 ≤ (T.pts k - T.pts (k + 1)) 1) :
    (¬ ∃ j, midpoint ℝ (T.pts (k + 1)) (T.pts (k + 2)) = T.pts j) ∧
    T.localAngle (midpoint ℝ (T.pts (k + 1)) (T.pts (k + 2))) = Real.pi ∧
    (∀ q : Plane, q ∈ T.carrier →
      0 ≤ (q - midpoint ℝ (T.pts (k + 1)) (T.pts (k + 2))) 1) := by
  refine ⟨midpoint_not_vertex T k, midpoint_localAngle_pi T k, ?_⟩
  set V := midpoint ℝ (T.pts (k + 1)) (T.pts (k + 2)) with hV
  have hVy : (V - T.pts (k + 1)) 1 = 0 := by
    have hsm : V = (2⁻¹ : ℝ) • (T.pts (k + 1) + T.pts (k + 2)) := by
      rw [hV, midpoint_eq_smul_add]; norm_num
    have hf : (T.pts (k + 2)) 1 - (T.pts (k + 1)) 1 = 0 := by
      simpa only [PiLp.sub_apply] using hflat
    rw [hsm]
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    linarith
  have hcvx : Convex ℝ {q : Plane | 0 ≤ (q - V) 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, PiLp.sub_apply] at *
    have hVsplit : (a • x + b • y : Plane) 1 = a * x 1 + b * y 1 := by simp
    rw [hVsplit]
    have p1 : 0 ≤ a * (x 1 - V 1) := mul_nonneg ha hx
    have p2 : 0 ≤ b * (y 1 - V 1) := mul_nonneg hb hy
    have hV1 : (a + b) * V 1 = V 1 := by rw [hab]; ring
    nlinarith [p1, p2, hV1]
  intro q hq
  rw [Erdos634.Geometry.Tri.carrier] at hq
  refine convexHull_min ?_ hcvx hq
  rintro p ⟨j, rfl⟩
  have hcases : ∀ j : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by
    have h : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
    exact fun j => h k j
  have hbase : ∀ z : Plane, (z - V) 1 = (z - T.pts (k + 1)) 1 - (V - T.pts (k + 1)) 1 := by
    intro z; simp only [PiLp.sub_apply]; ring
  simp only [Set.mem_setOf_eq]
  rcases hcases j with rfl | rfl | rfl
  · rw [hbase, hVy]; simpa using hup
  · rw [hbase, hVy]; simp
  · rw [hbase, hVy]
    have : (T.pts (k + 2) - T.pts (k + 1)) 1 = 0 := hflat
    simp only [PiLp.sub_apply] at this ⊢
    linarith

/-- **A concrete witness.**  The triangle `(0,0), (2,0), (1,1)` and the midpoint `(1,0)` of its
bottom edge satisfy all three hypotheses of `through_edge_lays_rightward` simultaneously, so the
`π` branch is about something. -/
theorem through_edge_witness :
    ∃ (T : Tri) (V : Plane), (¬ ∃ j, V = T.pts j) ∧ T.localAngle V = Real.pi ∧
      (∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - V) 1) := by
  have hdet : Erdos634.CertCoord.det3 0 0 2 0 1 1 ≠ 0 := by
    simp [Erdos634.CertCoord.det3]
  have h1 : (2 : Fin 3) + 1 = 0 := by decide
  have h2 : (2 : Fin 3) + 2 = 1 := by decide
  refine ⟨Erdos634.CertCoord.mkTri 0 0 2 0 1 1 hdet, _,
    through_edge_hyps_satisfiable (Erdos634.CertCoord.mkTri 0 0 2 0 1 1 hdet) 2 ?_ ?_⟩
  · rw [h1, h2]
    simp [Erdos634.CertCoord.mkTri_pts, Erdos634.CertCoord.mkPt_one]
  · rw [h1]
    simp [Erdos634.CertCoord.mkTri_pts, Erdos634.CertCoord.mkPt_one]

end Erdos634.RouteOne
