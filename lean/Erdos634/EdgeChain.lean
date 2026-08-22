import Mathlib.Tactic
import Erdos634.Dissection

/-!
# EdgeChain.lean — G3 sharpened: the exactly-once edge chain along a supporting line

`Dissection.hasEdgeChains_edge` proves that each side of the target is a *union* of whole tile
edges.  That is `HasEdgeChains` as stated, but it is weaker than what the walk equations
(`Interface.BaseBeta.walk_base` / `walk_side`, `WalkEquation.walk_equation`) consume: a union says
nothing about multiplicity, so no length identity follows from it.  This file supplies the missing
half — that the covering is *exactly once* — and assembles the length identity:

* `Tri.edge_inward` — **the same-side crux**.  A tile lying in the half-plane `f ≤ c` whose edge
  meets the line `f = c` at an edge-interior point is entered by *every* direction `v` with
  `f v < 0`.  (Route: the edge is forced onto the line, so `cross (leftDir) ·` and `f` are
  proportional — `proportional_of_ker_le` plus the rotation vector `rotVec` of a plane
  functional — and the constant is negative because an interior point of the tile has `f < c`;
  `Tri.mem_interior_of_cross_pos` then pushes inward.)
* `Dissection.no_second_tile_same_side` — **two distinct tiles on the same side of a line cannot
  share an edge-interior point**: both would be entered by a common `v` with `f v < 0`, violating
  `interiors_disjoint`.  This is the overlap exclusion that upgrades the union to a partition.
* `Dissection.side_partition` — each side of the target is covered by whole tile edges meeting
  pairwise in at most a point, and the edge lengths sum **exactly** to the side length (`edist`).
* `Dissection.side_walk` — the real-valued form `∑ dist(edge endpoints) = dist(side endpoints)`.
* `Dissection.side_walk_abc` — the interface's walk equation `P·a + Q·b + R·c = L`, for a
  dissection all of whose tile edges have length `a`, `b` or `c`.
* `Dissection.chain_breakpoint_vertex` — a common point of two same-side chain edges is a vertex
  of one of the two tiles: the breakpoints of the chain are tiling vertices.

Everything here is proved: no new axioms, no `sorry`, no hypothesis-shaped definitions.
-/

namespace Erdos634.Geometry

open MeasureTheory Set

/-! ## Plane linear algebra: the rotation vector of a functional -/

/-- `cross` is subtractive in its second argument. -/
theorem cross_sub_right (u a b : Plane) : cross u (a - b) = cross u a - cross u b := by
  simp only [cross, PiLp.sub_apply]; ring

/-- `cross` is homogeneous in its *first* argument. -/
theorem cross_smul_left (t : ℝ) (u v : Plane) : cross (t • u) v = t * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

/-- **Two vectors annihilated by `cross n ·` are mutually parallel.**  The 2×2 identity
`n₀·(u₀v₁ − u₁v₀) = u₀·(n₀v₁ − n₁v₀) − v₀·(n₀u₁ − n₁u₀)` (and its `n₁` twin) forces
`cross u v = 0` from `cross n u = cross n v = 0` once `n ≠ 0`. -/
theorem cross_eq_zero_of_common_ker {n u v : Plane} (hn : n ≠ 0)
    (hu : cross n u = 0) (hv : cross n v = 0) : cross u v = 0 := by
  have hcomp : n 0 ≠ 0 ∨ n 1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hn (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  simp only [cross] at hu hv ⊢
  rcases hcomp with h | h
  · have key : n 0 * (u 0 * v 1 - u 1 * v 0) = 0 := by
      linear_combination u 0 * hv - v 0 * hu
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' h
    · exact h'
  · have key : n 1 * (u 0 * v 1 - u 1 * v 0) = 0 := by
      linear_combination u 1 * hv - v 1 * hu
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' h
    · exact h'

/-- **Vanishing cross means parallel.**  If `cross a b = 0` and `a ≠ 0` then `b` is a scalar
multiple of `a`. -/
theorem parallel_of_cross_eq_zero {a b : Plane} (ha : a ≠ 0) (h : cross a b = 0) :
    ∃ τ : ℝ, b = τ • a := by
  have hcomp : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ha (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  simp only [cross] at h
  rcases hcomp with h0 | h1
  · refine ⟨b 0 / a 0, ?_⟩
    have key0 : b 0 = b 0 / a 0 * a 0 := by field_simp
    have key1 : b 1 = b 0 / a 0 * a 1 := by field_simp; linear_combination h
    ext i
    fin_cases i
    · simpa [smul_eq_mul] using key0
    · simpa [smul_eq_mul] using key1
  · refine ⟨b 1 / a 1, ?_⟩
    have key0 : b 0 = b 1 / a 1 * a 0 := by field_simp; linear_combination -h
    have key1 : b 1 = b 1 / a 1 * a 1 := by field_simp
    ext i
    fin_cases i
    · simpa [smul_eq_mul] using key0
    · simpa [smul_eq_mul] using key1

/-- Every plane vector is the sum of its two coordinate components. -/
theorem plane_decomp (y : Plane) :
    y = EuclideanSpace.single (0 : Fin 2) (y 0) + EuclideanSpace.single (1 : Fin 2) (y 1) := by
  ext i
  fin_cases i <;> simp

/-- A coordinate single is a scalar multiple of the unit single. -/
theorem single_eq_smul (i : Fin 2) (a : ℝ) :
    EuclideanSpace.single i a = a • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i <;> simp [h]

/-- **The rotation vector of a plane functional**: an `n` with `f = cross n ·`. -/
noncomputable def rotVec (f : Plane →ₗ[ℝ] ℝ) : Plane :=
  EuclideanSpace.single (0 : Fin 2) (f (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
    + EuclideanSpace.single (1 : Fin 2) (-(f (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))

theorem rotVec_spec (f : Plane →ₗ[ℝ] ℝ) (y : Plane) : f y = cross (rotVec f) y := by
  have h0 : EuclideanSpace.single (0 : Fin 2) (y 0)
      = y 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := single_eq_smul 0 (y 0)
  have h1 : EuclideanSpace.single (1 : Fin 2) (y 1)
      = y 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := single_eq_smul 1 (y 1)
  have hf : f y = y 0 * f (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      + y 1 * f (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
    conv_lhs => rw [plane_decomp y, h0, h1]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hcross : cross (rotVec f) y
      = f (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) * y 1
        + f (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) * y 0 := by
    simp only [cross, rotVec, PiLp.add_apply]
    simp
  rw [hf, hcross]; ring

theorem rotVec_ne_zero {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) : rotVec f ≠ 0 := by
  intro h
  apply hf
  apply LinearMap.ext
  intro y
  rw [rotVec_spec f y, h]
  simp [cross]

/-! ## Local data at an edge-interior point -/

/-- Moving from the centre of a ball stays inside it (with a definite positive step). -/
theorem move_in_ball {x v : Plane} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) :
    x + (r / (2 * ‖v‖)) • v ∈ Metric.ball x r ∧ 0 < r / (2 * ‖v‖) := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have htpos : 0 < r / (2 * ‖v‖) := by positivity
  refine ⟨?_, htpos⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hxy : x + (r / (2 * ‖v‖)) • v - x = (r / (2 * ‖v‖)) • v := by abel
  rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  have hval : r / (2 * ‖v‖) * ‖v‖ = r / 2 := by field_simp
  rw [hval]; linarith

/-- **Interior points have all barycentric coordinates strictly positive** — the converse of
`Tri.ball_subset_of_pos`. -/
theorem Tri.interior_coord_pos (T : Tri) {y : Plane} (hy : y ∈ interior T.carrier) :
    ∀ j, 0 < T.basis.coord j y := by
  intro j
  have hnn : 0 ≤ T.basis.coord j y := by
    have hmem := interior_subset hy
    rw [T.carrier_eq_nonneg_coord] at hmem
    exact hmem j
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
    obtain ⟨w, hw⟩ : ∃ w, (T.basis.coord j).linear w ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact T.coord_linear_ne_zero j (LinearMap.ext fun w => by simpa using hc w)
    obtain ⟨v, hv⟩ : ∃ v, (T.basis.coord j).linear v < 0 := by
      rcases lt_or_gt_of_ne hw with h' | h'
      · exact ⟨w, h'⟩
      · exact ⟨-w, by rw [map_neg]; linarith⟩
    have hvne : v ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact absurd hv (lt_irrefl 0)
    obtain ⟨hmem, htpos⟩ := move_in_ball (x := y) hvne hr
    have hin : y + (r / (2 * ‖v‖)) • v ∈ T.carrier := interior_subset (hball hmem)
    rw [T.carrier_eq_nonneg_coord] at hin
    have hcoord : T.basis.coord j (y + (r / (2 * ‖v‖)) • v)
        = (T.basis.coord j).linear ((r / (2 * ‖v‖)) • v) + T.basis.coord j y := by
      have h1 := (T.basis.coord j).map_vadd y ((r / (2 * ‖v‖)) • v)
      simp only [vadd_eq_add] at h1
      rw [add_comm ((r / (2 * ‖v‖)) • v) y] at h1
      exact h1
    have hneg : T.basis.coord j (y + (r / (2 * ‖v‖)) • v) < 0 := by
      rw [hcoord, map_smul, smul_eq_mul, h.symm, add_zero]
      exact mul_neg_of_pos_of_neg htpos hv
    exact absurd (hin j) (not_le.mpr hneg)

/-- **Interior points of a tile in the half-plane `f ≤ c` have `f < c` strictly.** -/
theorem Tri.interior_lt_of_le (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ y ∈ T.carrier, f y ≤ c) {y : Plane} (hy : y ∈ interior T.carrier) : f y < c := by
  rcases (hle y (interior_subset hy)).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
    obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hf (LinearMap.ext fun z => by simpa using hc z)
    obtain ⟨v, hv⟩ : ∃ v, 0 < f v := by
      rcases lt_or_gt_of_ne hw with h' | h'
      · exact ⟨-w, by rw [map_neg]; linarith⟩
      · exact ⟨w, h'⟩
    have hvne : v ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact absurd hv (lt_irrefl 0)
    obtain ⟨hmem, htpos⟩ := move_in_ball (x := y) hvne hr
    have hin : f (y + (r / (2 * ‖v‖)) • v) ≤ c := hle _ (interior_subset (hball hmem))
    rw [map_add, map_smul, smul_eq_mul, h] at hin
    nlinarith [mul_pos htpos hv]

/-- **Non-endpoint points of an edge carry the `OnEdge` data**: the opposite coordinate vanishes
and the other two are strictly positive.  Only the two *endpoint* exclusions are needed — a point
of `edge k` can never be the third vertex. -/
theorem Tri.onEdge_param (T : Tri) {k : Fin 3} {x : Plane} (hx : x ∈ T.edge k)
    (h1 : x ≠ T.pts k) (h2 : x ≠ T.pts (k + 1)) :
    T.basis.coord (k + 2) x = 0 ∧ ∀ j, j ≠ k + 2 → 0 < T.basis.coord j x := by
  have hz := T.coord_eq_zero_of_mem_edge k hx
  rw [Tri.edge] at hx
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hx
  have hca : T.basis.coord k x = a := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq k
    have e2 : T.basis.coord k (T.pts (k + 1)) = 0 :=
      T.basis.coord_apply_ne (by fin_cases k <;> decide)
    rw [e1, e2]; ring
  have hcb : T.basis.coord (k + 1) x = b := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord (k + 1) (T.pts k) = 0 :=
      T.basis.coord_apply_ne (by fin_cases k <;> decide)
    have e2 : T.basis.coord (k + 1) (T.pts (k + 1)) = 1 := T.basis.coord_apply_eq (k + 1)
    rw [e1, e2]; ring
  have hapos : 0 < a := by
    rcases ha.lt_or_eq with h | h
    · exact h
    · exfalso
      apply h2
      have hb1 : b = 1 := by linarith
      rw [← hcomb, ← h, hb1]
      simp
  have hbpos : 0 < b := by
    rcases hb.lt_or_eq with h | h
    · exact h
    · exfalso
      apply h1
      have ha1 : a = 1 := by linarith
      rw [← hcomb, ← h, ha1]
      simp
  refine ⟨hz, fun j hj => ?_⟩
  have hcases : j = k ∨ j = k + 1 := by
    have hall : ∀ j k : Fin 3, j ≠ k + 2 → j = k ∨ j = k + 1 := by decide
    exact hall j k hj
  rcases hcases with rfl | rfl
  · rw [hca]; exact hapos
  · rw [hcb]; exact hbpos

/-- **The average of two distinct points of a segment lies on it and is not an endpoint.** -/
theorem mem_ne_ends_of_avg {A B p q : Plane} (hpq : p ≠ q)
    (hp : p ∈ segment ℝ A B) (hq : q ∈ segment ℝ A B) :
    ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ∈ segment ℝ A B
      ∧ ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ≠ A ∧ ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ≠ B := by
  have hmem : ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ∈ segment ℝ A B :=
    (convex_segment A B) hp hq (by norm_num) (by norm_num) (by norm_num)
  have hAB : A ≠ B := by
    rintro rfl
    rw [segment_same] at hp hq
    rw [Set.mem_singleton_iff] at hp hq
    exact hpq (hp.trans hq.symm)
  rw [segment_eq_image' ℝ A B] at hp hq
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  have hmid : ((1:ℝ)/2) • (A + s • (B - A)) + ((1:ℝ)/2) • (A + t • (B - A))
      = A + ((s + t)/2) • (B - A) := by module
  refine ⟨hmem, ?_, ?_⟩
  · intro hcon
    rw [hmid] at hcon
    have hkey : ((s + t)/2) • (B - A) = 0 := by
      have h1 := congrArg (fun y => y - A) hcon
      simpa using h1
    rcases smul_eq_zero.mp hkey with h | h
    · have hs0 : s = 0 := by
        have := hs.1; have := ht.1
        have h2 : s + t = 0 := by linarith
        linarith
      have ht0 : t = 0 := by
        have := hs.1
        have h2 : s + t = 0 := by linarith
        linarith
      exact hpq (by rw [hs0, ht0])
    · exact hAB (sub_eq_zero.mp h).symm
  · intro hcon
    rw [hmid] at hcon
    have hB : A + (1:ℝ) • (B - A) = B := by module
    rw [← hB] at hcon
    have h2 : ((s + t)/2) • (B - A) = (1:ℝ) • (B - A) := by
      have h1 := congrArg (fun y => y - A) hcon
      simpa using h1
    have h3 : ((s + t)/2 - 1) • (B - A) = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · have hs1 : s = 1 := by
        have := hs.2; have := ht.2
        have h4 : s + t = 2 := by linarith
        linarith
      have ht1 : t = 1 := by
        have := hs.2
        have h4 : s + t = 2 := by linarith
        linarith
      exact hpq (by rw [hs1, ht1])
    · exact hAB (sub_eq_zero.mp h).symm

/-! ## The crux: same-side overlap exclusion -/

/-- **The endpoints of an edge through an edge-interior point on a supporting line lie on the
line.**  If `f ≤ c` at both endpoints and the strict convex combination `x` has `f x = c`, both
endpoints must attain `c`. -/
theorem Tri.edge_endpoints_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    (hfx : f x = c) (hle1 : f (T.pts (m + 1)) ≤ c) (hle2 : f (T.pts (m + 2)) ≤ c) :
    f (T.pts (m + 1)) = c ∧ f (T.pts (m + 2)) = c := by
  have hxe := T.mem_edge_of_coord_zero hm ho
  have hidx : (m + 1) + 1 = m + 2 := by fin_cases m <;> rfl
  rw [Tri.edge, hidx] at hxe
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hxe
  have hfxc : a * f (T.pts (m + 1)) + b * f (T.pts (m + 2)) = c := by
    rw [← hfx, ← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hca : T.basis.coord (m + 1) x = a := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord (m + 1) (T.pts (m + 1)) = 1 := T.basis.coord_apply_eq (m + 1)
    have e2 : T.basis.coord (m + 1) (T.pts (m + 2)) = 0 :=
      T.basis.coord_apply_ne (by fin_cases m <;> decide)
    rw [e1, e2]; ring
  have hcb : T.basis.coord (m + 2) x = b := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord (m + 2) (T.pts (m + 1)) = 0 :=
      T.basis.coord_apply_ne (by fin_cases m <;> decide)
    have e2 : T.basis.coord (m + 2) (T.pts (m + 2)) = 1 := T.basis.coord_apply_eq (m + 2)
    rw [e1, e2]; ring
  have hapos : 0 < a := by
    rw [← hca]; exact ho _ (by fin_cases m <;> decide)
  have hbpos : 0 < b := by
    rw [← hcb]; exact ho _ (by fin_cases m <;> decide)
  have habc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  constructor
  · by_contra hne
    have hlt : f (T.pts (m + 1)) < c := lt_of_le_of_ne hle1 hne
    have h1 : a * f (T.pts (m + 1)) < a * c := mul_lt_mul_of_pos_left hlt hapos
    have h2 : b * f (T.pts (m + 2)) ≤ b * c := mul_le_mul_of_nonneg_left hle2 hb
    linarith
  · by_contra hne
    have hlt : f (T.pts (m + 2)) < c := lt_of_le_of_ne hle2 hne
    have h1 : a * f (T.pts (m + 1)) ≤ a * c := mul_le_mul_of_nonneg_left hle1 ha
    have h2 : b * f (T.pts (m + 2)) < b * c := mul_lt_mul_of_pos_left hlt hbpos
    linarith

/-- **The same-side crux, tile form.**  A tile inside the half-plane `f ≤ c` that meets the line
`f = c` at an edge-interior point `x` is entered by every direction `v` with `f v < 0`: the
cross-functional of its left-directed edge is a *negative* multiple of `f`. -/
theorem Tri.edge_inward (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ y ∈ T.carrier, f y ≤ c) {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    (hfx : f x = c) {v : Plane} (hv : f v < 0) :
    0 < cross (T.leftDir (m + 1)) v := by
  have hmem : ∀ i, T.pts i ∈ T.carrier := fun i => subset_convexHull ℝ _ ⟨i, rfl⟩
  obtain ⟨hP, hQ⟩ := T.edge_endpoints_on_line f c hm ho hfx
    (hle _ (hmem _)) (hle _ (hmem _))
  have hidx : (m + 1) + 1 = m + 2 := by fin_cases m <;> rfl
  have hfdir : f (T.leftDir (m + 1)) = 0 := by
    rcases T.leftDir_eq_or (m + 1) with h | h
    · rw [h, hidx, map_sub, hP, hQ, sub_self]
    · rw [h, hidx, map_neg, map_sub, hP, hQ, sub_self, neg_zero]
  have hker : ∀ w, f w = 0 → crossL (T.leftDir (m + 1)) w = 0 := by
    intro w hw
    have hn := rotVec_ne_zero hf
    have h1 : cross (rotVec f) (T.leftDir (m + 1)) = 0 := by
      rw [← rotVec_spec]; exact hfdir
    have h2 : cross (rotVec f) w = 0 := by rw [← rotVec_spec]; exact hw
    rw [crossL_apply]
    exact cross_eq_zero_of_common_ker hn h1 h2
  obtain ⟨c₀, hc₀⟩ := proportional_of_ker_le f (crossL (T.leftDir (m + 1))) hf hker
  obtain ⟨y₀, hy₀⟩ := T.interior_nonempty
  have hy₀pos := T.interior_coord_pos hy₀
  have hcpos : 0 < cross (T.leftDir (m + 1)) (y₀ - T.pts (m + 1)) :=
    T.interior_left_of_leftDir (m + 1) hy₀pos
  have hylt : f y₀ < c := T.interior_lt_of_le f c hf hle hy₀
  have hval : cross (T.leftDir (m + 1)) (y₀ - T.pts (m + 1)) = c₀ * (f y₀ - c) := by
    have h1 := hc₀ (y₀ - T.pts (m + 1))
    rw [crossL_apply] at h1
    rw [h1, map_sub, hP]
  have hc₀neg : c₀ < 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 : 0 < c₀ * (f y₀ - c) := hval ▸ hcpos
    nlinarith
  have h2 := hc₀ v
  rw [crossL_apply] at h2
  rw [h2]
  exact mul_pos_of_neg_of_neg hc₀neg hv

/-- **The same-side crux, dissection form.**  Two *distinct* tiles both lying in the half-plane
`f ≤ c` cannot both meet the line `f = c` at a common edge-interior point: a direction `v` with
`f v < 0` would enter both interiors, violating `interiors_disjoint`.

This is the overlap exclusion of G3: it is what makes the chain along a supporting line cover it
*exactly once*, and with it the union statement `hasEdgeChains_edge` upgrades to a partition. -/
theorem Dissection.no_second_tile_same_side {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle₁ : ∀ y ∈ (D.tile i₁).carrier, f y ≤ c) (hle₂ : ∀ y ∈ (D.tile i₂).carrier, f y ≤ c)
    {x : Plane} (hfx : f x = c) {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x) : False := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf (LinearMap.ext fun z => by simpa using hc z)
  obtain ⟨v, hv⟩ : ∃ v, f v < 0 := by
    rcases lt_or_gt_of_ne hw with h' | h'
    · exact ⟨w, h'⟩
    · exact ⟨-w, by rw [map_neg]; linarith⟩
  exact D.cross_disjoint_of_onEdge hne hm₁ ho₁ hm₂ ho₂ v
    ⟨(D.tile i₁).edge_inward f c hf hle₁ hm₁ ho₁ hfx hv,
     (D.tile i₂).edge_inward f c hf hle₂ hm₂ ho₂ hfx hv⟩

/-- The clash dispatcher: `OnEdge` data for two chain members at one point is impossible —
same tile gives a coordinate clash, distinct tiles give the same-side crux. -/
theorem Dissection.two_edge_data_clash {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {j₁ j₂ : Fin N} {k₁ k₂ : Fin 3}
    (hne : (j₁, k₁) ≠ (j₂, k₂))
    (hle₁ : ∀ y ∈ (D.tile j₁).carrier, f y ≤ c) (hle₂ : ∀ y ∈ (D.tile j₂).carrier, f y ≤ c)
    {x : Plane} (hfx : f x = c)
    (hz₁ : (D.tile j₁).basis.coord (k₁ + 2) x = 0)
    (hp₁ : ∀ j, j ≠ k₁ + 2 → 0 < (D.tile j₁).basis.coord j x)
    (hz₂ : (D.tile j₂).basis.coord (k₂ + 2) x = 0)
    (hp₂ : ∀ j, j ≠ k₂ + 2 → 0 < (D.tile j₂).basis.coord j x) : False := by
  by_cases hsame : j₁ = j₂
  · subst hsame
    have hk : k₁ ≠ k₂ := fun h => hne (by rw [h])
    have hk2 : k₁ + 2 ≠ k₂ + 2 := fun h => hk (add_right_cancel h)
    exact absurd hz₁ (ne_of_gt (hp₂ _ hk2))
  · exact D.no_second_tile_same_side hsame f c hf hle₁ hle₂ hfx hz₁ hp₁ hz₂ hp₂

/-- **Same-side chain edges meet in at most one point.** -/
theorem Dissection.sameside_edges_subsingleton {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    {e₁ e₂ : Fin N × Fin 3} (hne : e₁ ≠ e₂)
    (hle₁ : ∀ y ∈ (D.tile e₁.1).carrier, f y ≤ c)
    (hle₂ : ∀ y ∈ (D.tile e₂.1).carrier, f y ≤ c)
    (hE₁ : ∀ y ∈ (D.tile e₁.1).edge e₁.2, f y = c)
    (hE₂ : ∀ y ∈ (D.tile e₂.1).edge e₂.2, f y = c) :
    ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨hm1, hn1A, hn1B⟩ := mem_ne_ends_of_avg hpq hp.1 hq.1
  obtain ⟨hm2, hn2A, hn2B⟩ := mem_ne_ends_of_avg hpq hp.2 hq.2
  obtain ⟨hz₁, hp₁⟩ := (D.tile e₁.1).onEdge_param hm1 hn1A hn1B
  obtain ⟨hz₂, hp₂⟩ := (D.tile e₂.1).onEdge_param hm2 hn2A hn2B
  have hne' : (e₁.1, e₁.2) ≠ (e₂.1, e₂.2) := by simpa using hne
  exact D.two_edge_data_clash f c hf hne' hle₁ hle₂ (hE₁ _ hm1) hz₁ hp₁ hz₂ hp₂

/-- **Chain breakpoints are tiling vertices.**  A common point of two same-side chain edges is a
vertex of one of the two tiles. -/
theorem Dissection.chain_breakpoint_vertex {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {e₁ e₂ : Fin N × Fin 3} (hne : e₁ ≠ e₂)
    (hle₁ : ∀ y ∈ (D.tile e₁.1).carrier, f y ≤ c)
    (hle₂ : ∀ y ∈ (D.tile e₂.1).carrier, f y ≤ c)
    (hE₁ : ∀ y ∈ (D.tile e₁.1).edge e₁.2, f y = c)
    (hE₂ : ∀ y ∈ (D.tile e₂.1).edge e₂.2, f y = c)
    {x : Plane} (hx₁ : x ∈ (D.tile e₁.1).edge e₁.2) (hx₂ : x ∈ (D.tile e₂.1).edge e₂.2) :
    (∃ v, x = (D.tile e₁.1).pts v) ∨ ∃ v, x = (D.tile e₂.1).pts v := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hv₁, hv₂⟩ := hcon
  obtain ⟨hz₁, hp₁⟩ := (D.tile e₁.1).onEdge_param hx₁ (hv₁ _) (hv₁ _)
  obtain ⟨hz₂, hp₂⟩ := (D.tile e₂.1).onEdge_param hx₂ (hv₂ _) (hv₂ _)
  have hne' : (e₁.1, e₁.2) ≠ (e₂.1, e₂.2) := by simpa using hne
  exact D.two_edge_data_clash f c hf hne' hle₁ hle₂ (hE₁ _ hx₁) hz₁ hp₁ hz₂ hp₂

/-! ## The exact partition and the length identity -/

/-- **The length identity for an exactly-once cover.**  Finitely many measurable subsets of `S`
with pairwise at-most-a-point intersections that cover `S` up to a finite set have
`μH¹`-measures summing to `μH¹ S`. -/
theorem sum_hausdorff_of_partition {ι : Type*} (part : Finset ι)
    (E : ι → Set Plane) (S : Set Plane) (F : Set Plane) (hF : F.Finite)
    (hmeas : ∀ e ∈ part, MeasurableSet (E e))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ → (E e₁ ∩ E e₂).Subsingleton)
    (hsub : ∀ e ∈ part, E e ⊆ S)
    (hcov : S \ F ⊆ ⋃ e ∈ part, E e) :
    ∑ e ∈ part, (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) (E e)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) S := by
  classical
  haveI : MeasureTheory.NoAtoms
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) :=
    MeasureTheory.Measure.noAtoms_hausdorff Plane (by norm_num)
  set μ := (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) with hμ
  have hadd := MeasureTheory.measure_biUnion_finset₀ (μ := μ) (s := part) (f := E)
    (fun e₁ h₁ e₂ h₂ hne => ((hdisj e₁ h₁ e₂ h₂ hne).finite.measure_zero μ))
    (fun e he => (hmeas e he).nullMeasurableSet)
  have hle1 : μ (⋃ e ∈ part, E e) ≤ μ S := measure_mono (Set.iUnion₂_subset hsub)
  have hFnull : μ F = 0 := hF.measure_zero μ
  have hle2 : μ S ≤ μ (⋃ e ∈ part, E e) := by
    calc μ S ≤ μ ((⋃ e ∈ part, E e) ∪ F) := by
          refine measure_mono fun x hx => ?_
          by_cases hxF : x ∈ F
          · exact Or.inr hxF
          · exact Or.inl (hcov ⟨hx, hxF⟩)
      _ ≤ μ (⋃ e ∈ part, E e) + μ F := measure_union_le _ _
      _ = μ (⋃ e ∈ part, E e) := by rw [hFnull, add_zero]
  rw [← hadd]
  exact le_antisymm hle1 hle2

/-- **G3, boundary form, sharpened to a partition with the length identity.**  Each side of the
target is covered by whole tile edges lying on it, distinct covering edges meet in at most one
point, and the `edist`-lengths of the covering edges sum exactly to the side length.

This is what `hasEdgeChains_edge` (the union statement) could not give: the walk equations need
each piece counted exactly once. -/
theorem Dissection.side_partition {N : ℕ} (D : Dissection N) (i : Fin 3) :
    ∃ part : Finset (Fin N × Fin 3),
      ((⋃ e ∈ part, (D.tile e.1).edge e.2)
          = segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
      ∧ (∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
          ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
      ∧ ∑ e ∈ part, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
          = edist (D.target.pts i) (D.target.pts (i + 1)) := by
  classical
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  obtain ⟨part, hpart⟩ := hasEdgeChains_edge D i
  have hS : {x ∈ D.target.carrier | f x = c}
      = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) :=
    target_contact_side D.target f c hle hi hi1 hi2
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2
      ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
    intro e he y hy
    rw [← hpart]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  have hlineE : ∀ e ∈ part, ∀ y ∈ (D.tile e.1).edge e.2, f y = c := by
    intro e he y hy
    have h1 : y ∈ {x ∈ D.target.carrier | f x = c} := by
      rw [hS]; exact hsub e he hy
    exact h1.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, f y ≤ c :=
    fun e y hy => hle y (tile_subset_target D e.1 hy)
  have hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton :=
    fun e₁ h₁ e₂ h₂ hne => D.sameside_edges_subsingleton f c hf hne
      (hleT e₁) (hleT e₂) (hlineE e₁ h₁) (hlineE e₂ h₂)
  refine ⟨part, hpart, hdisj, ?_⟩
  have hsum := sum_hausdorff_of_partition part (fun e => (D.tile e.1).edge e.2)
    (segment ℝ (D.target.pts i) (D.target.pts (i + 1))) ∅ Set.finite_empty
    (fun e _ => ((D.tile e.1).isClosed_edge e.2).measurableSet)
    hdisj hsub
    (by
      intro x hx
      rw [← hpart] at hx
      exact hx.1)
  calc ∑ e ∈ part, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = ∑ e ∈ part,
          (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
            ((D.tile e.1).edge e.2) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        exact ((D.tile e.1).hausdorff_edge e.2).symm
    _ = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
          (segment ℝ (D.target.pts i) (D.target.pts (i + 1))) := hsum
    _ = edist (D.target.pts i) (D.target.pts (i + 1)) :=
        MeasureTheory.hausdorffMeasure_segment _ _

/-- **The real-valued walk identity.**  The distances of the covering edges' endpoints sum to the
side length. -/
theorem Dissection.side_walk {N : ℕ} (D : Dissection N) (i : Fin 3) :
    ∃ part : Finset (Fin N × Fin 3),
      ((⋃ e ∈ part, (D.tile e.1).edge e.2)
          = segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
      ∧ (∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
          ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
      ∧ ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
          = dist (D.target.pts i) (D.target.pts (i + 1)) := by
  obtain ⟨part, hcov, hdisj, hsum⟩ := D.side_partition i
  refine ⟨part, hcov, hdisj, ?_⟩
  have h1 : ENNReal.ofReal
        (∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist (D.target.pts i) (D.target.pts (i + 1))) := by
    calc ENNReal.ofReal
          (∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
        = ∑ e ∈ part,
            ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) :=
          ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg)
      _ = ∑ e ∈ part, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) :=
          Finset.sum_congr rfl fun e _ => (edist_dist _ _).symm
      _ = edist (D.target.pts i) (D.target.pts (i + 1)) := hsum
      _ = ENNReal.ofReal (dist (D.target.pts i) (D.target.pts (i + 1))) := edist_dist _ _
  exact (ENNReal.ofReal_eq_ofReal_iff
    (Finset.sum_nonneg fun e _ => dist_nonneg) dist_nonneg).mp h1

/-- Grouping a sum whose terms take three values into `P·a + Q·b + R·c`. -/
theorem sum_three_values {ι : Type*} (s : Finset ι) (len : ι → ℝ) (a b c : ℝ)
    (h : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) :
    ∃ P Q R : ℕ, ((P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c = ∑ e ∈ s, len e)
      ∧ P + Q + R = s.card := by
  classical
  refine ⟨(s.filter fun e => len e = a).card,
          (s.filter fun e => ¬ len e = a ∧ len e = b).card,
          (s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card, ?_, ?_⟩
  · have hsplit1 := Finset.sum_filter_add_sum_filter_not s (fun e => len e = a) len
    have hsplit2 := Finset.sum_filter_add_sum_filter_not
      (s.filter fun e => ¬ len e = a) (fun e => len e = b) len
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
    have hA : ∑ e ∈ s.filter (fun e => len e = a), len e
        = ((s.filter fun e => len e = a).card : ℝ) * a := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
        Finset.sum_const, nsmul_eq_mul]
    have hB : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ len e = b), len e
        = ((s.filter fun e => ¬ len e = a ∧ len e = b).card : ℝ) * b := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2.2),
        Finset.sum_const, nsmul_eq_mul]
    have hC : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ ¬ len e = b), len e
        = ((s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card : ℝ) * c := by
      rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
      have hmem := Finset.mem_filter.mp he
      rcases h e hmem.1 with h' | h' | h'
      · exact absurd h' hmem.2.1
      · exact absurd h' hmem.2.2
      · exact h'
    rw [hA] at hsplit1
    rw [hB, hC] at hsplit2
    linarith [hsplit1, hsplit2]
  · have h1 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := s) (p := fun e => len e = a)
    have h2 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := s.filter fun e => ¬ len e = a) (p := fun e => len e = b)
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    omega

/-- **The walk equation of the interface.**  If every tile edge has length `a`, `b` or `c`, each
side of the target satisfies `P·a + Q·b + R·c = L` for some multiplicities `P, Q, R`.  This is
the geometric content of `Interface.BaseBeta.walk_base` / `walk_side`. -/
theorem Dissection.side_walk_abc {N : ℕ} (D : Dissection N) (i : Fin 3) (a b c : ℝ)
    (habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = a
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = b
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = c) :
    ∃ P Q R : ℕ, (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c
      = dist (D.target.pts i) (D.target.pts (i + 1)) := by
  obtain ⟨part, -, -, hsum⟩ := D.side_walk i
  obtain ⟨P, Q, R, hPQR, -⟩ := sum_three_values part
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
    (fun e _ => habc e.1 e.2)
  exact ⟨P, Q, R, by rw [hPQR, hsum]⟩

/-- **The walk equation over ℕ** — the exact shape of the interface fields
`Interface.BaseBeta.walk_base` / `walk_side`.  For natural tile-side lengths `a, b, c` and a side
of natural length `L`, the multiplicities satisfy `P·a + Q·b + R·c = L` in ℕ. -/
theorem Dissection.side_walk_abc_nat {N : ℕ} (D : Dissection N) (i : Fin 3) (a b c L : ℕ)
    (habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (a : ℝ)
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (b : ℝ)
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (c : ℝ))
    (hL : dist (D.target.pts i) (D.target.pts (i + 1)) = (L : ℝ)) :
    ∃ P Q R : ℕ, P * a + Q * b + R * c = L := by
  obtain ⟨P, Q, R, hPQR⟩ := D.side_walk_abc i (a : ℝ) (b : ℝ) (c : ℝ) habc
  refine ⟨P, Q, R, ?_⟩
  rw [hL] at hPQR
  exact_mod_cast hPQR

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Dissection.no_second_tile_same_side
#print axioms Erdos634.Geometry.Dissection.side_partition
#print axioms Erdos634.Geometry.Dissection.side_walk
#print axioms Erdos634.Geometry.Dissection.side_walk_abc
#print axioms Erdos634.Geometry.Dissection.side_walk_abc_nat
#print axioms Erdos634.Geometry.Dissection.chain_breakpoint_vertex
