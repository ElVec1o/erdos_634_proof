import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Erdos634.WallSide
import Erdos634.WallEdges

/-!
# The wall coordinate separates the wall, and the shadows do not overlap

Erdős #634, bridge (c), the last join.  `WallSide.no_wall_contact` forbids two tiles sharing a point
in the relative interiors of their wall edges; `Placement.contiguous_of_no_gap` wants the intervals
not to overlap.  Bridging them needs the wall coordinate to separate points of the wall: then
overlapping shadows produce a genuinely shared point, and the contact theorem applies.

The separation hypothesis is that `g`'s linear part and `dir` have trivial common kernel — `g` kills
the wall's direction and `dir` does not, so together they see every vector.  In the plane that is
just their independence.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WallInjective

open Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance

/-- An affine map's increment is its linear part. -/
theorem affine_sub (g : Plane →ᵃ[ℝ] ℝ) (x y : Plane) : g y - g x = g.linear (y - x) := by
  have h : y = (y - x) +ᵥ x := by simp [vadd_eq_add]
  rw [h, g.map_vadd]; simp

/-- **The wall coordinate separates the wall.**  On the level set `g = c`, equal `dir` means equal
points, provided `g`'s linear part and `dir` have trivial common kernel. -/
theorem dir_injOn_wall (g : Plane →ᵃ[ℝ] ℝ) (dir : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0) :
    Set.InjOn dir {y : Plane | g y = c} := by
  intro x hx y hy hxy
  have h1 : g.linear (y - x) = 0 := by
    rw [← affine_sub g x y, hx, hy]; ring
  have h2 : dir (y - x) = 0 := by
    rw [map_sub, hxy]; ring
  have := hker _ h1 h2
  have : y = x := by
    have := sub_eq_zero.mp this
    exact this
  exact this.symm

/-- A point strictly inside an edge has both flanking barycentric coordinates positive. -/
theorem coord_pos_of_lineMap (T : Tri) (k : Fin 3) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < T.basis.coord (k + 1) (AffineMap.lineMap (T.pts (k + 1)) (T.pts (k + 2)) t) ∧
    0 < T.basis.coord (k + 2) (AffineMap.lineMap (T.pts (k + 1)) (T.pts (k + 2)) t) := by
  have hne : (k + 1) ≠ (k + 2) := by
    intro h
    have : (1 : Fin 3) = 2 := by
      have := congrArg (fun z => z - k) h; simpa using this
    exact absurd this (by decide)
  have hself : ∀ i : Fin 3, T.basis.coord i (T.pts i) = 1 := by
    intro i; have h := T.basis.coord_apply i i; simp only [if_pos rfl] at h; exact h
  have hother : ∀ i j : Fin 3, i ≠ j → T.basis.coord i (T.pts j) = 0 := by
    intro i j h; have := T.basis.coord_apply i j; simp only [if_neg h] at this; exact this
  constructor
  · have := AffineMap.apply_lineMap (T.basis.coord (k + 1)) (T.pts (k + 1)) (T.pts (k + 2)) t
    rw [this, hself (k + 1), hother (k + 1) (k + 2) hne]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    linarith
  · have := AffineMap.apply_lineMap (T.basis.coord (k + 2)) (T.pts (k + 1)) (T.pts (k + 2)) t
    rw [this, hself (k + 2), hother (k + 2) (k + 1) (Ne.symm hne)]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    linarith

/-- On a wall edge the functional is constant at `c`. -/
theorem g_const_on_wall_edge (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (m : Fin 3)
    (h1 : g (T.pts m) = c) (h2 : g (T.pts (m + 1)) = c) {x : Plane} (hx : x ∈ T.edge m) :
    g x = c := by
  rw [Tri.edge] at hx
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := hx
  have hx' : u • T.pts m + v • T.pts (m + 1)
      = AffineMap.lineMap (T.pts m) (T.pts (m + 1)) v := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub]
    have : u = 1 - v := by linarith
    rw [this]; module
  rw [hx', AffineMap.apply_lineMap, h1, h2]
  simp

/-- A wall edge's endpoints have distinct coordinates, so its shadow is nondegenerate. -/
theorem shadow_nondegenerate {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (i : Fin N) (m : Fin 3) (h1 : g ((D.tile i).pts m) = c) (h2 : g ((D.tile i).pts (m + 1)) = c) :
    edgePos D dir (i, m) < edgeEnd D dir (i, m) := by
  have hne : (D.tile i).pts m ≠ (D.tile i).pts (m + 1) := by
    intro h
    have : m = m + 1 := (D.tile i).indep.injective h
    omega
  have hdir : dir ((D.tile i).pts m) ≠ dir ((D.tile i).pts (m + 1)) := by
    intro h
    exact hne (dir_injOn_wall g dir c hker (by exact h1) (by exact h2) h)
  unfold edgePos edgeEnd
  rcases lt_or_gt_of_ne hdir with h | h
  · rw [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)]; exact h
  · rw [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)]; exact h

/-- A coordinate strictly inside an edge's shadow comes from a point strictly inside the edge. -/
theorem pull_back {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (a : Fin N) (b : Fin 3) (t : ℝ)
    (hlt : edgePos D dir (a, b) < t) (hgt : t < edgeEnd D dir (a, b)) :
    ∃ x ∈ (D.tile a).edge b, dir x = t ∧ x ≠ (D.tile a).pts b ∧ x ≠ (D.tile a).pts (b + 1) := by
  have hmem : t ∈ Set.Icc (edgePos D dir (a, b)) (edgeEnd D dir (a, b)) :=
    ⟨le_of_lt hlt, le_of_lt hgt⟩
  rw [← edge_image_eq_Icc] at hmem
  obtain ⟨x, hx, hxt⟩ := hmem
  have hends : (dir ((D.tile a).pts b) = edgePos D dir (a, b) ∧
      dir ((D.tile a).pts (b+1)) = edgeEnd D dir (a, b)) ∨
      (dir ((D.tile a).pts b) = edgeEnd D dir (a, b) ∧
      dir ((D.tile a).pts (b+1)) = edgePos D dir (a, b)) := by
    unfold edgePos edgeEnd
    rcases le_total (dir ((D.tile a).pts b)) (dir ((D.tile a).pts (b+1))) with h | h
    · exact Or.inl ⟨(min_eq_left h).symm, (max_eq_right h).symm⟩
    · exact Or.inr ⟨(max_eq_left h).symm, (min_eq_right h).symm⟩
  refine ⟨x, hx, hxt, ?_, ?_⟩
  · intro hcon
    rw [hcon] at hxt
    rcases hends with ⟨e1, _⟩ | ⟨e1, _⟩
    · rw [e1] at hxt; linarith
    · rw [e1] at hxt; linarith
  · intro hcon
    rw [hcon] at hxt
    rcases hends with ⟨_, e2⟩ | ⟨_, e2⟩
    · rw [e2] at hxt; linarith
    · rw [e2] at hxt; linarith

theorem fin_shift : ∀ m : Fin 3, m + 2 + 1 = m ∧ m + 2 + 2 = m + 1 := by decide

/-- **The shadows of two wall edges of distinct tiles do not overlap.**  A coordinate strictly
inside both shadows comes from a point strictly inside each edge; the two points have the same
`dir` and lie on the wall, so they are the same point, and `WallSide.no_wall_contact` forbids that.

This is the `hnoov` hypothesis of `Placement.contiguous_of_no_gap`, discharged. -/
theorem shadows_disjoint {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (dir : Plane →ₗ[ℝ] ℝ)
    (c : ℝ) (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (i j : Fin N) (hij : i ≠ j) (m n : Fin 3)
    (hi1 : g ((D.tile i).pts m) = c) (hi2 : g ((D.tile i).pts (m + 1)) = c)
    (hi3 : g ((D.tile i).pts (m + 2)) < c)
    (hj1 : g ((D.tile j).pts n) = c) (hj2 : g ((D.tile j).pts (n + 1)) = c)
    (hj3 : g ((D.tile j).pts (n + 2)) < c) :
    edgeEnd D dir (i, m) ≤ edgePos D dir (j, n) ∨
      edgeEnd D dir (j, n) ≤ edgePos D dir (i, m) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hi := shadow_nondegenerate D g dir c hker i m hi1 hi2
  have hj := shadow_nondegenerate D g dir c hker j n hj1 hj2
  obtain ⟨t, ht1, ht2⟩ : ∃ t, max (edgePos D dir (i, m)) (edgePos D dir (j, n)) < t ∧
      t < min (edgeEnd D dir (i, m)) (edgeEnd D dir (j, n)) := by
    refine exists_between ?_
    rcases max_cases (edgePos D dir (i, m)) (edgePos D dir (j, n)) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rcases min_cases (edgeEnd D dir (i, m)) (edgeEnd D dir (j, n)) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
      rw [he, hm] <;> first | exact hi | exact hj | linarith
  rw [max_lt_iff] at ht1
  rw [lt_min_iff] at ht2
  obtain ⟨x, hxe, hxt, hxa, hxb⟩ := pull_back D dir i m t ht1.1 ht2.1
  obtain ⟨y, hye, hyt, hya, hyb⟩ := pull_back D dir j n t ht1.2 ht2.2
  -- both lie on the wall, so they are the same point
  have hgx : g x = c := g_const_on_wall_edge (D.tile i) g c m hi1 hi2 hxe
  have hgy : g y = c := g_const_on_wall_edge (D.tile j) g c n hj1 hj2 hye
  have hxy : x = y := dir_injOn_wall g dir c hker (by exact hgx) (by exact hgy) (by rw [hxt, hyt])
  -- and each is strictly inside its edge
  have hpos : ∀ (a : Fin N) (b : Fin 3) (z : Plane), z ∈ (D.tile a).edge b →
      z ≠ (D.tile a).pts b → z ≠ (D.tile a).pts (b + 1) →
      0 < (D.tile a).basis.coord b z ∧ 0 < (D.tile a).basis.coord (b + 1) z := by
    intro a b z hz hz1 hz2
    rw [Tri.edge] at hz
    obtain ⟨u, hu0, hu1, rfl⟩ := Erdos634.WallEdges.mem_segment_interior hz hz1 hz2
    obtain ⟨hs1, hs2⟩ := fin_shift b
    have := coord_pos_of_lineMap (D.tile a) (b + 2) u hu0 hu1
    rw [hs1, hs2] at this
    exact this
  obtain ⟨hxp1, hxp2⟩ := hpos i m x hxe hxa hxb
  obtain ⟨hyp1, hyp2⟩ := hpos j n y hye hya hyb
  obtain ⟨hs1i, hs2i⟩ := fin_shift m
  obtain ⟨hs1j, hs2j⟩ := fin_shift n
  refine Erdos634.WallSide.no_wall_contact D g c i j hij (m + 2) (n + 2) x
    ((D.tile i).edge_subset_carrier m hxe) (hxy ▸ (D.tile j).edge_subset_carrier n hye)
    (by rw [hs1i]; exact hi1) (by rw [hs2i]; exact hi2) hi3
    (by rw [hs1j]; exact hj1) (by rw [hs2j]; exact hj2) hj3
    (by rw [hs1i]; exact hxp1) (by rw [hs2i]; exact hxp2)
    (by rw [hs1j, hxy]; exact hyp1) (by rw [hs2j, hxy]; exact hyp2)

end Erdos634.WallInjective
