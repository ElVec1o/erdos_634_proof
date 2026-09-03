import Erdos634.RouteOne
import Erdos634.CertCoord
import Mathlib.LinearAlgebra.AffineSpace.MidpointZero

/-!
# Route 1's flank at `V` without `conj:advance`'s case (a)

Erdős #634, `conj:advance` / `rem:route1uniform`.

`route_one_flank_composed` reaches Route 1's flank conclusion at `V` only after excluding
`localAngle = π` for the tile serving the tangential approach, and it excludes it with `hcard`/`hb`:
the `π`-count at `V` is one and the tile *below the line* carries the straight angle. That pair is
exactly what `conj:advance` lists as unproved — "that a through-edge, rather than a junction, runs
below the line at `V`" — and tracing the proof shows it is consumed at that one place and nowhere
else.

This file removes it, in three steps.

**1. The `π` branch is pinned, not excluded.** If `V` is not a vertex of `T` and `T.localAngle V = π`
then `V` has one barycentric coordinate `0` and two positive, so it lies in an open edge;
`sub_vertex_eq_combo` at each flanking vertex writes the two displacements as *opposite* positive
multiples of one vector `w`, and `habove` — already a hypothesis of the vertex branch — makes both
second components nonnegative. Antiparallel then forces `w` horizontal (`through_edge_data`,
`through_edge_lays_rightward`). So the alternative branch does not add cases: it puts a *horizontal*
edge through `V`, running along the wall line.

**2. Two through-edges leave no room.** At an interior point two straight angles already exhaust the
`2π`, so no third tile may even contain the point (`two_through_excludes_third`,
`two_through_excludes_mem`, sharpening `PinPlumbing.at_most_two_through`). Since every point of an
open edge carries `π` (`openSegment_localAngle_pi`), two tiles cannot share an edge-interior point
while a third tile touches it (`shared_edge_interior_excludes_third`).

**3. The overlap exists.** The serving tile's through-edge and the `α`-tile's own horizontal edge
`VA` both run left from `V` along the wall, so they share a stretch; `mem_openSegment_of_horizontal`
builds a point of it explicitly. The tiles below the wall contain that point, and step 2 fires:
`serving_ne_pi_of_left_edge` kills the `π` branch outright.

`route_one_flank_no_straight` is then `route_one_flank_composed` with `hcard` and `hb` gone. What
stands in their place is (i) that the `α`-tile lays a horizontal edge from `V` leftward — this is
`rem:route1uniform`'s own geometry, whose algebra is already verified
(`Frontier.route1_spacings`, `.side_tile_third_vertex`) — and (ii) `hthird`, that the open stretch
is interior to the target and carries a tile other than the two.

**Scope, stated exactly.** `hthird` is a *hypothesis here, not a theorem*: deriving it needs the
routine covering argument (points just below the wall are covered, the covering tile is neither of
the two upper tiles, and it contains the limit point) — standard dissection bookkeeping, but not
done in this file. Nor is the configuration attached to a hypothetical tiling; that is
`rem:routeoneopen`'s standing obligation and it is untouched. `conj:advance` remains a conjecture,
`e = 1` is not closed, and the prime case is not advanced. What changed is the *kind* of the
remaining obligation at this step: a crossing-question fact about where an edge lies has been
replaced by a covering fact about what lies beneath the wall.

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

/-! ## Sharpening: the `π` branch dies outright once a second tile shares the line

`at_most_two_through` (PinPlumbing) says three straight angles at an interior point are impossible.
The sharper statement below is what the route-1 configuration actually needs: **two** straight
angles at an interior point already exhaust the `2π`, so no third tile may so much as *contain* the
point.  Combined with `through_edge_lays_rightward` this is the mechanism that kills the `π` branch
without any appeal to case (a) — the serving tile's through-edge would have to share the wall line
with the `α`-tile's own horizontal edge, and the tiles below the wall contain the shared points. -/

/-- **Two through-edges leave no room for a third tile.**  At an interior point two distinct tiles
with local angle `π` already sum to `2π`, so any further tile has local angle `0` there — it does
not touch the point at all. -/
theorem two_through_excludes_third {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ interior D.target.carrier) (i j k : Fin N)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : (D.tile i).localAngle p = Real.pi)
    (hj : (D.tile j).localAngle p = Real.pi)
    (hk : (D.tile k).localAngle p ≠ 0) : False := by
  classical
  have hsum := Erdos634.PinPlumbing.pin_angle_sum_interior D hp
  have hkpos : 0 < (D.tile k).localAngle p :=
    lt_of_le_of_ne ((D.tile k).localAngle_nonneg p) (Ne.symm hk)
  have hle : (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      ≤ ∑ m, (D.tile m).localAngle p := by
    have h1 : ({i, j, k} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
    have h2 : ∑ m ∈ ({i, j, k} : Finset (Fin N)), (D.tile m).localAngle p
        ≤ ∑ m, (D.tile m).localAngle p :=
      Finset.sum_le_sum_of_subset_of_nonneg h1
        (fun m _ _ => (D.tile m).localAngle_nonneg p)
    rw [Finset.sum_insert (by simp [hij, hik]),
        Finset.sum_insert (by simp [hjk]), Finset.sum_singleton] at h2
    linarith
  rw [hsum, hi, hj] at hle
  linarith

/-- **The same, with the third tile given by mere containment.**  A tile whose carrier contains the
point has nonzero local angle there, so two through-edges at an interior point forbid any third
tile from containing it. -/
theorem two_through_excludes_mem {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ interior D.target.carrier) (i j k : Fin N)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : (D.tile i).localAngle p = Real.pi)
    (hj : (D.tile j).localAngle p = Real.pi)
    (hk : p ∈ (D.tile k).carrier) : False :=
  two_through_excludes_third D hp i j k hij hik hjk hi hj
    (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hk)

/-! ## Every interior point of an edge carries `π`, not just the midpoint -/

/-- **Not a vertex**, from the coordinate signature of an edge-interior point. -/
theorem not_vertex_of_coord_zero (T : Tri) (W : Plane) (k : Fin 3)
    (h0 : T.basis.coord k W = 0) (hpos : ∀ j, j ≠ k → 0 < T.basis.coord j W) :
    ¬ ∃ j, W = T.pts j := by
  have hthird : ∀ u v : Fin 3, u ≠ v → ∃ w : Fin 3, w ≠ u ∧ w ≠ v := by decide
  have hcne : ∀ (i j : Fin 3), i ≠ j → T.basis.coord i (T.pts j) = 0 :=
    fun i j h => T.basis.coord_apply_ne h
  have hceq : ∀ i : Fin 3, T.basis.coord i (T.pts i) = 1 := fun i => T.basis.coord_apply_eq i
  rintro ⟨j, rfl⟩
  by_cases hjk : j = k
  · subst hjk
    rw [hceq j] at h0
    norm_num at h0
  · obtain ⟨w, hwj, hwk⟩ := hthird j k (Ne.symm (Ne.symm hjk))
    have := hpos w hwk
    rw [hcne w j hwj] at this
    exact absurd this (lt_irrefl 0)

/-- **The local angle is `π` at any point with one vanishing and two positive coordinates.** -/
theorem localAngle_pi_of_coords (T : Tri) (W : Plane) (k : Fin 3)
    (h0 : T.basis.coord k W = 0) (hpos : ∀ j, j ≠ k → 0 < T.basis.coord j W) :
    T.localAngle W = Real.pi := by
  classical
  rw [Erdos634.Geometry.Tri.localAngle, dif_neg (not_vertex_of_coord_zero T W k h0 hpos),
    if_neg (by intro hall; exact absurd h0 (ne_of_gt (hall k))), if_pos ⟨k, h0, hpos⟩]

/-- **Every interior point of an edge has local angle `π`** — the midpoint statement, generalised to
the whole open edge.  This is what lets the route-1 argument move slightly along the wall line from
`V` to a point the two upper tiles share. -/
theorem openSegment_localAngle_pi (T : Tri) (k : Fin 3) {W : Plane}
    (hW : W ∈ openSegment ℝ (T.pts (k + 1)) (T.pts (k + 2))) :
    T.localAngle W = Real.pi := by
  classical
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hW
  have hidx : ∀ x : Fin 3, (x ≠ x + 1) ∧ (x ≠ x + 2) ∧ (x + 1 ≠ x + 2)
      ∧ (∀ j : Fin 3, j ≠ x → j = x + 1 ∨ j = x + 2) := by decide
  obtain ⟨h1, h2, h12, hcases⟩ := hidx k
  have hcne : ∀ (i j : Fin 3), i ≠ j → T.basis.coord i (T.pts j) = 0 :=
    fun i j h => T.basis.coord_apply_ne h
  have hceq : ∀ i : Fin 3, T.basis.coord i (T.pts i) = 1 := fun i => T.basis.coord_apply_eq i
  have hlm : W = AffineMap.lineMap (T.pts (k + 1)) (T.pts (k + 2)) b := by
    rw [AffineMap.lineMap_apply, ← heq]
    have ha' : a = 1 - b := by linarith
    rw [ha']
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  have hcoord : ∀ j : Fin 3, T.basis.coord j W
      = (T.basis.coord j (T.pts (k + 2)) - T.basis.coord j (T.pts (k + 1))) * b
        + T.basis.coord j (T.pts (k + 1)) := by
    intro j
    rw [hlm, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
    ring
  refine localAngle_pi_of_coords T W k ?_ ?_
  · rw [hcoord k, hcne k (k + 1) h1, hcne k (k + 2) h2]; ring
  · intro j hj
    rcases hcases j hj with rfl | rfl
    · rw [hcoord (k + 1), hcne (k + 1) (k + 2) h12, hceq (k + 1)]
      have hb1 : (0 : ℝ) - 1 = -1 := by norm_num
      rw [hb1]; linarith
    · rw [hcoord (k + 2), hcne (k + 2) (k + 1) (Ne.symm h12), hceq (k + 2)]
      linarith

/-! ## The through-edge exhibited, and the exclusion it feeds -/

/-- **The through-edge, exhibited.**  Under the hypotheses of `through_edge_lays_rightward`, `V`
lies in the *open* edge joining two vertices of `T`, and that edge is horizontal.  This is the form
the wall argument consumes: it names the edge, not just a point on one side of `V`. -/
theorem through_edge_data (T : Tri) (V : Plane)
    (hnv : ¬ ∃ j, V = T.pts j) (hpi : T.localAngle V = Real.pi)
    (habove : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - V) 1) :
    ∃ k : Fin 3, V ∈ openSegment ℝ (T.pts (k + 1)) (T.pts (k + 2)) ∧
      (T.pts (k + 2) - T.pts (k + 1)) 1 = 0 := by
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
  simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul] at c1y c2y
  have hab1 : 0 ≤ (T.pts (k + 1) - V) 1 := habove _ hmem1
  have hab2 : 0 ≤ (T.pts (k + 2) - V) 1 := habove _ hmem2
  rw [c1y] at hab1
  rw [c2y] at hab2
  have hwy : (T.pts (k + 2) - T.pts (k + 1)) 1 = 0 := by nlinarith
  -- `w ≠ 0`, else `V` is a vertex
  have hwne : T.pts (k + 2) - T.pts (k + 1) ≠ 0 := by
    intro hw
    rw [hw, smul_zero] at e1
    exact hnv ⟨k + 1, sub_eq_zero.mp e1⟩
  -- the two coefficients sum to `1`, by adding the two displacements
  have hsum1 : T.basis.coord (k + 1) V + T.basis.coord (k + 2) V = 1 := by
    have hadd : (T.basis.coord (k + 1) V + T.basis.coord (k + 2) V)
        • (T.pts (k + 2) - T.pts (k + 1)) = T.pts (k + 2) - T.pts (k + 1) := by
      rw [add_smul, ← d2, ← e1]; abel
    by_contra hne
    have : (T.basis.coord (k + 1) V + T.basis.coord (k + 2) V - 1)
        • (T.pts (k + 2) - T.pts (k + 1)) = 0 := by
      rw [sub_smul, hadd, one_smul, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact hne (by linarith [sub_eq_zero.mp h])
    · exact hwne h
  refine ⟨k, ⟨T.basis.coord (k + 1) V, T.basis.coord (k + 2) V, hc1, hc2, hsum1, ?_⟩, hwy⟩
  have : T.basis.coord (k + 1) V • T.pts (k + 1) + T.basis.coord (k + 2) V • T.pts (k + 2)
      = T.pts (k + 1) + T.basis.coord (k + 2) V • (T.pts (k + 2) - T.pts (k + 1)) := by
    rw [smul_sub, show T.basis.coord (k + 1) V = 1 - T.basis.coord (k + 2) V by linarith,
      sub_smul, one_smul]
    abel
  rw [this, ← e1]; abel

/-- **Two tiles cannot share an edge-interior point while a third tile touches it.**  At an interior
point of the target, a point lying in the relative interior of an edge of each of two distinct tiles
already accounts for the whole `2π`; any third tile containing it is impossible.

This is the location-sensitive exclusion the route-1 configuration needs: the serving tile's
through-edge at `V` is horizontal (`through_edge_data`), so it runs along the wall line and overlaps
the `α`-tile's own horizontal edge there — and the tiles below the wall contain the overlap. -/
theorem shared_edge_interior_excludes_third {N : ℕ} (D : Dissection N) (i j k : Fin N) (W : Plane)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hWint : W ∈ interior D.target.carrier)
    (mi : Fin 3) (hWi : W ∈ openSegment ℝ ((D.tile i).pts (mi + 1)) ((D.tile i).pts (mi + 2)))
    (mj : Fin 3) (hWj : W ∈ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (hWk : W ∈ (D.tile k).carrier) : False :=
  two_through_excludes_mem D hWint i j k hij hik hjk
    (openSegment_localAngle_pi (D.tile i) mi hWi)
    (openSegment_localAngle_pi (D.tile j) mj hWj) hWk

/-! ## Constructing the overlap point: the `π` branch excluded outright

The two open edges — the serving tile's through-edge at `V` and the `α`-tile's horizontal edge from
`V` to `A` — both run along the wall line and both extend to the left of `V`, so they share a whole
stretch.  Exhibiting one point of it turns `shared_edge_interior_excludes_third` into an outright
exclusion of the `π` branch. -/

/-- **Horizontal points and open segments.**  For `X, Y, Z` on a common horizontal line, an
`x`-coordinate strictly between puts `Z` in the open segment. -/
theorem mem_openSegment_of_horizontal {X Y Z : Plane}
    (hY : (Y - X) 1 = 0) (hZ : (Z - X) 1 = 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hx : (Z - X) 0 = t * ((Y - X) 0)) :
    Z ∈ openSegment ℝ X Y := by
  refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
  have hzero : (1 - t) • X + t • Y - Z = 0 := by
    have hxc : Z 0 - X 0 = t * (Y 0 - X 0) := by simpa only [PiLp.sub_apply] using hx
    have hyc : Y 1 - X 1 = 0 := by simpa only [PiLp.sub_apply] using hY
    have hzc : Z 1 - X 1 = 0 := by simpa only [PiLp.sub_apply] using hZ
    have hn : ‖(1 - t) • X + t • Y - Z‖ = 0 := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      have h0 : ((1 - t) • X + t • Y - Z) 0 = 0 := by
        simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        linear_combination -hxc
      have h1 : ((1 - t) • X + t • Y - Z) 1 = 0 := by
        simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        linear_combination t * hyc - hzc
      rw [h0, h1]; simp
    exact norm_eq_zero.mp hn
  exact sub_eq_zero.mp hzero

/-- **The `π` branch is impossible.**  If the serving tile `i` lies weakly above `V`, a second tile
`j` lays a horizontal edge from `V` leftward to `A`, and every point of that open stretch is interior
to the target and lies in some third tile (the tiles below the wall), then `i` cannot have `V`
interior to one of its edges.

This is `conj:advance`'s case (a) discharged *for this step*: the straight angle below the line is
never invoked. What replaces it is the `α`-tile's own horizontal edge, together with the fact that
the wall carries tiles beneath it. -/
theorem serving_ne_pi_of_left_edge {N : ℕ} (D : Dissection N) (i j : Fin N) (V A : Plane)
    (hij : i ≠ j)
    (habove : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - V) 1)
    (hnv : ¬ ∃ m, V = (D.tile i).pts m)
    (mj : Fin 3) (hjV : (D.tile j).pts (mj + 1) = V) (hjA : (D.tile j).pts (mj + 2) = A)
    (hAy : (A - V) 1 = 0) (hAx : (A - V) 0 < 0)
    (hthird : ∀ W : Plane, W ∈ openSegment ℝ V A →
      W ∈ interior D.target.carrier ∧ ∃ k : Fin N, k ≠ i ∧ k ≠ j ∧ W ∈ (D.tile k).carrier) :
    (D.tile i).localAngle V ≠ Real.pi := by
  classical
  intro hpi
  obtain ⟨k, hVseg, hedge⟩ := through_edge_data (D.tile i) V hnv hpi habove
  obtain ⟨a, b, ha, hb, hab, hVeq⟩ := hVseg
  have hb1 : b < 1 := by linarith
  have hVP : V - (D.tile i).pts (k + 1)
      = b • ((D.tile i).pts (k + 2) - (D.tile i).pts (k + 1)) := by
    rw [← hVeq, smul_sub, show a = 1 - b by linarith, sub_smul, one_smul]
    abel
  have hVPy : (V - (D.tile i).pts (k + 1)) 1 = 0 := by
    rw [hVP]; simp only [PiLp.smul_apply, smul_eq_mul, hedge]; ring
  have hVPx : (V - (D.tile i).pts (k + 1)) 0
      = b * (((D.tile i).pts (k + 2) - (D.tile i).pts (k + 1)) 0) := by
    rw [hVP]; simp only [PiLp.smul_apply, smul_eq_mul]
  have hd : ((D.tile i).pts (k + 2) - (D.tile i).pts (k + 1)) 0 ≠ 0 := by
    intro hd0
    have hw : (D.tile i).pts (k + 2) - (D.tile i).pts (k + 1) = 0 := by
      have hn : ‖(D.tile i).pts (k + 2) - (D.tile i).pts (k + 1)‖ = 0 := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, hd0, hedge]; simp
      exact norm_eq_zero.mp hn
    rw [hw, smul_zero] at hVP
    exact hnv ⟨k + 1, (sub_eq_zero.mp hVP)⟩
  set d := ((D.tile i).pts (k + 2) - (D.tile i).pts (k + 1)) 0 with hddef
  set v := (A - V) 0 with hvdef
  set r := v / d with hrdef
  have hrne : r ≠ 0 := div_ne_zero (ne_of_lt hAx) hd
  have hrpos : 0 < |r| := abs_pos.mpr hrne
  have hmpos : 0 < min b (1 - b) := lt_min hb (by linarith)
  set t := min (1 / 2 : ℝ) (min b (1 - b) / (2 * |r|)) with htdef
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have htr : t * |r| ≤ min b (1 - b) / 2 := by
    have h := min_le_right (1 / 2 : ℝ) (min b (1 - b) / (2 * |r|))
    calc t * |r| ≤ (min b (1 - b) / (2 * |r|)) * |r| :=
          mul_le_mul_of_nonneg_right h (le_of_lt hrpos)
      _ = min b (1 - b) / 2 := by field_simp
  have habs : |t * r| ≤ min b (1 - b) / 2 := by
    rw [abs_mul, abs_of_pos ht0]; exact htr
  have hlo : -(min b (1 - b) / 2) ≤ t * r := (abs_le.mp habs).1
  have hhi : t * r ≤ min b (1 - b) / 2 := (abs_le.mp habs).2
  have hminb : min b (1 - b) ≤ b := min_le_left _ _
  have hmin1b : min b (1 - b) ≤ 1 - b := min_le_right _ _
  set W := t • (A - V) + V with hWdef
  have hWV : W - V = t • (A - V) := by rw [hWdef]; abel
  have hWVy : (W - V) 1 = 0 := by
    rw [hWV]; simp only [PiLp.smul_apply, smul_eq_mul, hAy]; ring
  have hWVx : (W - V) 0 = t * v := by
    rw [hWV]; simp only [PiLp.smul_apply, smul_eq_mul]; rw [← hvdef]
  have hW1 : W ∈ openSegment ℝ V A :=
    mem_openSegment_of_horizontal hAy hWVy ht0 ht1 (by rw [hWVx])
  have hW2 : W ∈ openSegment ℝ ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) := by
    refine mem_openSegment_of_horizontal (t := b + t * r) hedge ?_ ?_ ?_ ?_
    · have hs : (W - (D.tile i).pts (k + 1)) 1 = (W - V) 1 + (V - (D.tile i).pts (k + 1)) 1 := by
        simp only [PiLp.sub_apply]; ring
      rw [hs, hWVy, hVPy]; ring
    · have hh : min b (1 - b) / 2 ≤ b / 2 := by linarith
      linarith
    · have hh : min b (1 - b) / 2 ≤ (1 - b) / 2 := by linarith
      linarith
    · have hsplit : (W - (D.tile i).pts (k + 1)) 0
          = (W - V) 0 + (V - (D.tile i).pts (k + 1)) 0 := by
        simp only [PiLp.sub_apply]; ring
      rw [hsplit, hWVx, hVPx, ← hddef, hrdef]
      field_simp
      ring
  obtain ⟨hWint, kk, hki, hkj, hWk⟩ := hthird W hW1
  exact shared_edge_interior_excludes_third D i j kk W hij (Ne.symm hki) (Ne.symm hkj)
    hWint k hW2 mj (by rw [hjV, hjA]; exact hW1) hWk

/-- **Route 1's flank at `V`, with the straight-angle hypothesis removed.**  This is
`route_one_flank_composed` with `hcard` (the `π`-count is one) and `hb` (the tile below carries the
straight angle) — jointly `conj:advance`'s case (a) — replaced by two facts about the configuration
that carry no open content: the `α`-tile `j` lays a horizontal edge from `V` leftward to `A`, and the
wall stretch `VA` is interior to the target with a tile beneath it.

The serving tile then has `V` as a vertex and a horizontal rightward edge there — the input the
overshoot dichotomy consumes. -/
theorem route_one_flank_no_straight {N : ℕ} (D : Dissection N) (i j : Fin N) (V A : Plane)
    (hij : i ≠ j)
    (hne0 : (D.tile i).localAngle V ≠ 0)
    (hne2pi : (D.tile i).localAngle V ≠ 2 * Real.pi)
    (habove : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - V) 1)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0))
    (mj : Fin 3) (hjV : (D.tile j).pts (mj + 1) = V) (hjA : (D.tile j).pts (mj + 2) = A)
    (hAy : (A - V) 1 = 0) (hAx : (A - V) 0 < 0)
    (hthird : ∀ W : Plane, W ∈ openSegment ℝ V A →
      W ∈ interior D.target.carrier ∧ ∃ k : Fin N, k ≠ i ∧ k ≠ j ∧ W ∈ (D.tile k).carrier) :
    ∃ m : Fin 3, (D.tile i).pts m = V ∧
      ((((D.tile i).pts (m + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 1) - V) 0) ∨
       (((D.tile i).pts (m + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 2) - V) 0)) := by
  classical
  by_cases hnv : ∃ m, V = (D.tile i).pts m
  · obtain ⟨m, hm⟩ := hnv
    have hab' : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - (D.tile i).pts m) 1 := by
      intro q hq; rw [← hm]; exact habove q hq
    have hse' : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
        0 < (q - (D.tile i).pts m) 0 ∧
        (q - (D.tile i).pts m) 1 ≤ δ * ((q - (D.tile i).pts m) 0) := by
      intro δ hδ; rw [← hm]; exact hserve δ hδ
    refine ⟨m, hm.symm, ?_⟩
    rcases escape_flank (D.tile i) m hab' hse' with ⟨hy, hx⟩ | ⟨hy, hx⟩
    · exact Or.inl ⟨by rw [hm]; exact hy, by rw [hm]; exact hx⟩
    · exact Or.inr ⟨by rw [hm]; exact hy, by rw [hm]; exact hx⟩
  · exact absurd (serving_has_vertex D i V hne0 hne2pi
      (serving_ne_pi_of_left_edge D i j V A hij habove hnv mj hjV hjA hAy hAx hthird))
      (by rintro ⟨m, hm⟩; exact hnv ⟨m, hm.symm⟩)

end Erdos634.RouteOne
