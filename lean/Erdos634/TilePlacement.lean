import Mathlib
import Erdos634.VertexFigureReal
import Erdos634.OrientBridge

/-!
# The tile-placement layer

Erdős #634.  Thirty-one PROVED statements across the three papers wait on the same missing object:
a way to say, of a real dissection, that *this tile sits here* — at a corner, laying that edge on
that wall, presenting that angle at that point.  The papers use the language freely; the corpus has
no definitions for it, which is why those statements cannot be formalized as written.

This file starts the layer with the three notions the statements actually use, and proves the first
consumer: at a base corner of a base-`β` target, **exactly one tile has a nonzero angle**, which is
the first clause of `prop:cornerfig` at a real corner.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TilePlacement

open Erdos634.Geometry Finset

/-- Tile `i` has `v` among its vertices. -/
def HasVertex {N : ℕ} (D : Dissection N) (i : Fin N) (v : Plane) : Prop :=
  ∃ j : Fin 3, (D.tile i).pts j = v

/-- Tile `i` presents angle `θ` at the point `v`. -/
def PresentsAt {N : ℕ} (D : Dissection N) (i : Fin N) (v : Plane) (θ : ℝ) : Prop :=
  (D.tile i).localAngle v = θ

/-- Tile `i` lays its `k`-th edge inside the set `S` — the wall, a side, a chord. -/
def LaysOn {N : ℕ} (D : Dissection N) (i : Fin N) (k : Fin 3) (S : Set Plane) : Prop :=
  (D.tile i).edge k ⊆ S

/-- A tile laying an edge on a set has both endpoints there. -/
theorem laysOn_endpoints {N : ℕ} (D : Dissection N) (i : Fin N) (k : Fin 3) (S : Set Plane)
    (h : LaysOn D i k S) :
    (D.tile i).pts k ∈ S ∧ (D.tile i).pts (k + 1) ∈ S := by
  constructor
  · exact h (by rw [Tri.edge]; exact left_mem_segment ℝ _ _)
  · exact h (by rw [Tri.edge]; exact right_mem_segment ℝ _ _)

/-- **The corner figure, with multiplicities.**  At a vertex of the target, the tiles' local angles
sum to that corner's angle, and counting them by value turns the sum into a linear relation. -/
theorem corner_multiplicities {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    (({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card : ℝ) * γ
      + (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card : ℝ)
        * Real.pi
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
  classical
  have hsum := Erdos634.VertexFigureReal.corner_angle_sum D k
  rw [Erdos634.VertexFigureReal.sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ) _ hvals] at hsum
  rw [Finset.sum_insert (by simp [hαβ, hαγ, hαπ, hα0]),
      Finset.sum_insert (by simp [hβγ, hβπ, hβ0]),
      Finset.sum_insert (by simp [hγπ, hγ0]),
      Finset.sum_insert (by simp [hπ0]), Finset.sum_singleton] at hsum
  push_cast at hsum ⊢
  linarith [hsum]

/-- **A base corner is a single `β`-tile.**  With the corner angle `β`, the multiplicities are
`(0,1,0)` and no tile contributes a straight angle: exactly one tile presents `β` there, and every
other tile presents `0`.

This is `prop:cornerfig`'s first clause, at a real corner of a real dissection. -/
theorem base_corner_single_tile {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = β) :
    p = 0 ∧ q = 1 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((-3 * (s : ℤ) : ℤ) : ℝ) * α + ((1 - 2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast
    linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **Exactly one tile at a base corner.**  Combining the count with the multiplicity solution:
the number of tiles presenting `β` there is `1`, and no tile presents `α`, `γ` or a straight
angle. -/
theorem base_corner_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  classical
  have h := corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact base_corner_single_tile hγdef hrel hirr _ _ _ _ h

/-- **Exactly three `α`-tiles at the apex.**  The same count with the corner angle `3α`. -/
theorem apex_counts {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = 3 * α) :
    p = 3 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((3 - 3 * (s : ℤ) : ℤ) : ℝ) * α + ((-2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast; linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## The two edges at a corner

`prop:cornerfig`'s last clause names the *edges* at the base corner.  Given that the side opposite
the corner is `b`, the two incident sides are `a` and `c` in one order or the other — by sum and
product of the side multiset, which pins them as the roots of one quadratic. -/

/-- **The two incident sides.**  If the three sides are `{a, b, c}` and the one opposite the vertex
is `b`, the two at the vertex are `a` and `c`. -/
theorem incident_sides (x y a b c : ℝ) (hb : b ≠ 0)
    (hmul : ({x, y, b} : Multiset ℝ) = {a, b, c}) :
    (x = a ∧ y = c) ∨ (x = c ∧ y = a) := by
  classical
  have hsum : x + y + b = a + b + c := by
    have := congrArg Multiset.sum hmul
    simpa [Multiset.insert_eq_cons, add_assoc] using this
  have hprod : x * y * b = a * b * c := by
    have := congrArg Multiset.prod hmul
    simpa [Multiset.insert_eq_cons, mul_assoc] using this
  have hs : x + y = a + c := by linarith
  have hp : x * y = a * c := by
    have h : (x * y) * b = (a * c) * b := by
      rw [hprod]; ring
    exact mul_right_cancel₀ hb h
  have hroot : (x - a) * (x - c) = 0 := by linear_combination x * hs - hp
  rcases mul_eq_zero.mp hroot with h | h
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

/-! ## Non-degeneracy: the strict triangle inequality

The angle-ordering lemma needs `c < a + b` strictly, and `dist_triangle` gives only `≤`.  Strictness
is exactly non-degeneracy: equality would put a vertex between the other two, making the tile's
three points collinear, which `Tri.indep` forbids. -/

/-- The tile's three vertices, listed from any starting index. -/
theorem range_pts_eq (T : Tri) (j : Fin 3) :
    Set.range T.pts = {T.pts (j + 1), T.pts j, T.pts (j + 2)} := by
  have hfin : ∀ a b : Fin 3, a = b ∨ a = b + 1 ∨ a = b + 2 := by decide
  have hfin' : ∀ i : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := fun i => hfin i j
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases hfin' i with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨j + 1, rfl⟩
    · exact ⟨j, rfl⟩
    · exact ⟨j + 2, rfl⟩

/-- **The strict triangle inequality in a tile.** -/
theorem strict_triangle (T : Tri) (j : Fin 3) :
    dist (T.pts (j + 1)) (T.pts (j + 2))
      < dist (T.pts (j + 1)) (T.pts j) + dist (T.pts j) (T.pts (j + 2)) := by
  rcases lt_or_eq_of_le (dist_triangle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exact h
  · exfalso
    have hw : Wbtw ℝ (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) :=
      dist_add_dist_eq_iff.mp h.symm
    have hcol : Collinear ℝ (Set.range T.pts) := by
      rw [range_pts_eq T j]; exact hw.collinear
    exact (affineIndependent_iff_not_collinear.mp T.indep) hcol

/-- **A larger side faces a larger angle, inside a tile.**  With `a` the side opposite vertex `j`,
`b` the side opposite `j+1` and `c` the side they share, `a < b` gives `A < B`.  The strict triangle
inequality comes from `strict_triangle`, i.e. from the tile's non-degeneracy. -/
theorem angle_lt_of_side_lt (T : Tri) (j : Fin 3)
    (hlt : dist (T.pts (j + 1)) (T.pts (j + 2)) < dist (T.pts (j + 2)) (T.pts j)) :
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))
      < cornerAngle (T.pts (j + 2)) (T.pts (j + 1)) (T.pts j) := by
  have hne : ∀ i k : Fin 3, i ≠ k → T.pts i ≠ T.pts k := by
    intro i k hik h
    exact hik (T.indep.injective h)
  have h01 : (j : Fin 3) ≠ j + 1 := by
    have : ∀ x : Fin 3, x ≠ x + 1 := by decide
    exact this j
  have h12 : (j + 1 : Fin 3) ≠ j + 2 := by
    have : ∀ x : Fin 3, x + 1 ≠ x + 2 := by decide
    exact this j
  have h02 : (j : Fin 3) ≠ j + 2 := by
    have : ∀ x : Fin 3, x ≠ x + 2 := by decide
    exact this j
  have hA : cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hB : cornerAngle (T.pts (j + 2)) (T.pts (j + 1)) (T.pts j) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hsh1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have hsh2 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have htri := strict_triangle T (j + 2)
  rw [hsh1 j, hsh2 j] at htri
  have lawA := EuclideanGeometry.law_cos (V := Plane) (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))
  have lawB := EuclideanGeometry.law_cos (V := Plane) (T.pts (j + 2)) (T.pts (j + 1)) (T.pts j)
  refine Erdos634.OrientBridge.smallest_angle_opposite_shortest_side
    (dist (T.pts (j + 1)) (T.pts (j + 2))) (dist (T.pts (j + 2)) (T.pts j))
    (dist (T.pts j) (T.pts (j + 1))) _ _
    (dist_pos.mpr (hne _ _ h12)) (dist_pos.mpr (hne _ _ (Ne.symm h02)))
    (dist_pos.mpr (hne _ _ h01)) ?_ hlt hA hB ?_ ?_
  · have e1 : dist (T.pts (j + 1)) (T.pts (j + 2)) = dist (T.pts (j + 2)) (T.pts (j + 1)) :=
      dist_comm _ _
    have e2 : dist (T.pts (j + 2)) (T.pts j) = dist (T.pts j) (T.pts (j + 2)) := dist_comm _ _
    rw [e1, e2]
    linarith [htri]
  · rw [cornerAngle]
    rw [dist_comm (T.pts (j + 1)) (T.pts j)] at lawA
    linarith [lawA]
  · rw [cornerAngle]
    rw [dist_comm (T.pts (j + 2)) (T.pts (j + 1))] at lawB
    linarith [lawB]

/-! ## The middle angle faces the middle side

`prop:cornerfig`'s edge clause needs the side opposite a `β`-corner to be `b`.  With the angle
ordering in hand that is a trichotomy argument on a scalene tile. -/

/-- The side of the tile opposite vertex `j`. -/
noncomputable def sideOpp (T : Tri) (j : Fin 3) : ℝ := dist (T.pts (j + 1)) (T.pts (j + 2))

/-- The tile's angle at vertex `j`. -/
noncomputable def angleAt (T : Tri) (j : Fin 3) : ℝ :=
  cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))

/-- `angle_lt_of_side_lt`, in the `sideOpp`/`angleAt` notation. -/
theorem angleAt_lt (T : Tri) (j : Fin 3) (h : sideOpp T j < sideOpp T (j + 1)) :
    angleAt T j < angleAt T (j + 1) := by
  have hsh : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have hsh2 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  unfold sideOpp at h
  rw [hsh j, hsh2 j] at h
  have := angle_lt_of_side_lt T j h
  unfold angleAt
  rw [hsh j, hsh2 j]
  exact this

/-! ## The ordering lemma over three points

Stating it with `Fin 3` indices made each unordered pair of vertices reachable in only one
direction, and the index arithmetic for the other cost an iteration.  Over three explicit points
the lemma is symmetric in `p` and `q`, so both directions are one instantiation each. -/

/-- **A larger side faces a larger angle**, for three points with the strict triangle inequality.
The side opposite `p` is `dist q r`; the side opposite `q` is `dist p r`. -/
theorem angle_lt_of_side_lt_pts (p q r : Plane) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (htri : dist p q < dist q r + dist p r) (h : dist q r < dist p r) :
    cornerAngle q p r < cornerAngle p q r := by
  have lawA := EuclideanGeometry.law_cos (V := Plane) q p r
  have lawB := EuclideanGeometry.law_cos (V := Plane) p q r
  rw [dist_comm q p, dist_comm r p] at lawA
  rw [dist_comm r q] at lawB
  refine Erdos634.OrientBridge.smallest_angle_opposite_shortest_side
    (dist q r) (dist p r) (dist p q) _ _ (dist_pos.mpr hqr) (dist_pos.mpr hpr)
    (dist_pos.mpr hpq) htri h
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ ?_ ?_
  · rw [cornerAngle]; linarith [lawA]
  · rw [cornerAngle]; linarith [lawB]

/-- The strict triangle inequality at a tile, in point form. -/
theorem strict_triangle_pts (T : Tri) (j : Fin 3) :
    dist (T.pts j) (T.pts (j + 1))
      < dist (T.pts (j + 1)) (T.pts (j + 2)) + dist (T.pts j) (T.pts (j + 2)) := by
  have hsh1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have hsh2 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have h := strict_triangle T (j + 2)
  rw [hsh1 j, hsh2 j] at h
  have e1 : dist (T.pts j) (T.pts (j + 2)) = dist (T.pts (j + 2)) (T.pts j) := dist_comm _ _
  have e2 : dist (T.pts (j + 1)) (T.pts (j + 2)) = dist (T.pts (j + 2)) (T.pts (j + 1)) :=
    dist_comm _ _
  rw [e1, e2]
  have e3 : dist (T.pts (j + 2)) (T.pts (j + 1)) = dist (T.pts (j + 1)) (T.pts (j + 2)) :=
    dist_comm _ _
  linarith [h]

/-- Distinct vertices of a tile are distinct points. -/
theorem pts_ne (T : Tri) {i k : Fin 3} (h : i ≠ k) : T.pts i ≠ T.pts k := by
  intro hh; exact h (T.indep.injective hh)

/-- **Both directions at once.**  For a tile and any two distinct vertices, the one with the
smaller opposite side has the smaller angle. -/
theorem angle_lt_of_sideOpp_lt (T : Tri) (j : Fin 3)
    (h : dist (T.pts (j + 1)) (T.pts (j + 2)) < dist (T.pts j) (T.pts (j + 2))) :
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))
      < cornerAngle (T.pts j) (T.pts (j + 1)) (T.pts (j + 2)) := by
  have h01 : ∀ x : Fin 3, x ≠ x + 1 := by decide
  have h12 : ∀ x : Fin 3, x + 1 ≠ x + 2 := by decide
  have h02 : ∀ x : Fin 3, x ≠ x + 2 := by decide
  exact angle_lt_of_side_lt_pts (T.pts j) (T.pts (j + 1)) (T.pts (j + 2))
    (pts_ne T (h01 j)) (pts_ne T (h12 j)) (pts_ne T (h02 j)) (strict_triangle_pts T j) h

/-! ## The converse, and the middle side

With both directions available the ordering reverses: on a tile whose sides are distinct, a smaller
angle faces a smaller side.  The middle angle therefore faces the middle side, which is what
`prop:cornerfig`'s edge clause needs. -/

/-- **A smaller angle faces a smaller side**, given the two sides are distinct. -/
theorem side_lt_of_angle_lt (p q r : Plane) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (htri : dist p q < dist q r + dist p r) (htri' : dist q p < dist p r + dist q r)
    (hne : dist q r ≠ dist p r) (h : cornerAngle q p r < cornerAngle p q r) :
    dist q r < dist p r := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlt
  · exfalso
    have := angle_lt_of_side_lt_pts q p r (Ne.symm hpq) hpr hqr htri' hgt
    linarith

/-- **The middle angle faces the middle side.**  If the angle at `p` is strictly between the angles
at `q` and `r`, and the three sides are distinct, the side opposite `p` is strictly between the
other two. -/
theorem middle_side_of_middle_angle (p q r : Plane) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (t1 : dist p q < dist q r + dist p r) (t2 : dist q p < dist p r + dist q r)
    (t3 : dist p r < dist q r + dist p q) (t4 : dist r p < dist p q + dist q r)
    (hne1 : dist q r ≠ dist p r) (hne2 : dist p q ≠ dist q r)
    (hlo : cornerAngle q r p < cornerAngle q p r)
    (hhi : cornerAngle q p r < cornerAngle p q r) :
    dist q r < dist p r ∧ dist p q < dist q r := by
  refine ⟨side_lt_of_angle_lt p q r hpq hqr hpr t1 t2 hne1 hhi, ?_⟩
  -- the angle at `r` is below the angle at `p`, so the side opposite `r` is below the one
  -- opposite `p`
  have hmain := side_lt_of_angle_lt r p q (Ne.symm hpr) hpq (Ne.symm hqr) ?_ ?_ ?_ ?_
  · rw [dist_comm r q] at hmain; exact hmain
  · rw [dist_comm r p, dist_comm r q]; linarith [t4]
  · rw [dist_comm p r, dist_comm r q]; linarith [t3]
  · rw [dist_comm r q]; exact hne2
  · show EuclideanGeometry.angle (V := Plane) p r q < cornerAngle r p q
    rw [EuclideanGeometry.angle_comm (V := Plane) p r q]
    show EuclideanGeometry.angle (V := Plane) q r p < EuclideanGeometry.angle (V := Plane) r p q
    rw [EuclideanGeometry.angle_comm (V := Plane) r p q]
    exact hlo

/-! ## The corner tile's two edges

Assembling: the side opposite the corner is the middle one, hence `b`; the two edges at the corner
are then `a` and `c`.  This is `prop:cornerfig`'s edge clause. -/

/-- A value of the multiset `{a,b,c}` lying strictly between the other two is `b`. -/
theorem middle_is_b (x y z a b c : ℝ) (hmul : ({x, y, z} : Multiset ℝ) = {a, b, c})
    (hab : a < b) (hbc : b < c) (h1 : x < y) (h2 : y < z) : y = b := by
  classical
  have hy : y ∈ ({a, b, c} : Multiset ℝ) := by rw [← hmul]; simp
  have hx : x ∈ ({a, b, c} : Multiset ℝ) := by rw [← hmul]; simp
  have hz : z ∈ ({a, b, c} : Multiset ℝ) := by rw [← hmul]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx hy hz
  rcases hy with rfl | rfl | rfl
  · rcases hx with h | h | h <;> linarith [h ▸ h1]
  · rfl
  · rcases hz with h | h | h <;> linarith [h ▸ h2]

/-- **The two edges at the corner.**  With the side opposite the corner equal to `b`, the two
incident edges are `a` and `c` in one order or the other. -/
theorem corner_tile_edges (T : Tri) (j : Fin 3) (a b c : ℝ) (hb : b ≠ 0)
    (hopp : dist (T.pts (j + 1)) (T.pts (j + 2)) = b)
    (hmul : ({dist (T.pts j) (T.pts (j + 1)), dist (T.pts (j + 2)) (T.pts j),
      dist (T.pts (j + 1)) (T.pts (j + 2))} : Multiset ℝ) = {a, b, c}) :
    (dist (T.pts j) (T.pts (j + 1)) = a ∧ dist (T.pts (j + 2)) (T.pts j) = c) ∨
      (dist (T.pts j) (T.pts (j + 1)) = c ∧ dist (T.pts (j + 2)) (T.pts j) = a) := by
  rw [hopp] at hmul
  exact incident_sides _ _ a b c hb hmul

/-! ## A `c`-corner carries a side `a`-edge

`lem:ccornerside` of the obstructions note: the base corner's two flanks are `a` and `c`, so a
corner tile laying `c` on the base lays `a` on the side.  With `corner_tile_edges` that is now a
two-line consequence. -/

/-- **`lem:ccornerside`.**  If the corner tile's base edge is its `c`-edge, its other edge at the
corner is the `a`-edge. -/
theorem c_corner_side_a (T : Tri) (j : Fin 3) (a b c : ℝ) (hb : b ≠ 0) (hac : a ≠ c)
    (hopp : dist (T.pts (j + 1)) (T.pts (j + 2)) = b)
    (hmul : ({dist (T.pts j) (T.pts (j + 1)), dist (T.pts (j + 2)) (T.pts j),
      dist (T.pts (j + 1)) (T.pts (j + 2))} : Multiset ℝ) = {a, b, c})
    (hbase : dist (T.pts j) (T.pts (j + 1)) = c) :
    dist (T.pts (j + 2)) (T.pts j) = a := by
  rcases corner_tile_edges T j a b c hb hopp hmul with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact absurd (h1.symm.trans hbase) hac
  · exact h2

/-- The mirror: a corner tile laying `a` on the base lays `c` on the side. -/
theorem a_corner_side_c (T : Tri) (j : Fin 3) (a b c : ℝ) (hb : b ≠ 0) (hac : a ≠ c)
    (hopp : dist (T.pts (j + 1)) (T.pts (j + 2)) = b)
    (hmul : ({dist (T.pts j) (T.pts (j + 1)), dist (T.pts (j + 2)) (T.pts j),
      dist (T.pts (j + 1)) (T.pts (j + 2))} : Multiset ℝ) = {a, b, c})
    (hbase : dist (T.pts j) (T.pts (j + 1)) = a) :
    dist (T.pts (j + 2)) (T.pts j) = c := by
  rcases corner_tile_edges T j a b c hb hopp hmul with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · exact absurd (hbase.symm.trans h1) hac

/-! ## The `c`-corner's side parameter

`lem:ccornerside` runs: a `c`-corner forces an `a`-edge on the side, so that side's `a`-count is
positive; quantization makes it `fp`, and with `pe + R' = f` and the `γ`-trap `R' ≥ 1` the parameter
is pinned between `1` and `(f-1)/e`.  The last step is arithmetic and is proved here; the step
before it needs the side's chain edges related to its walk counts, which is what the lemma still
waits on. -/

/-- **The `c`-corner's parameter bounds.**  From `pe + R' = f` with `R' ≥ 1` and `p ≥ 1`. -/
theorem p_bounds (p e f R : ℕ) (h : p * e + R = f) (hR : 1 ≤ R) (hp : 1 ≤ p) :
    1 ≤ p ∧ p * e + 1 ≤ f := by
  exact ⟨hp, by omega⟩

/-- With `e ≥ 1` this is the bound `p ≤ (f-1)/e` the lemma states. -/
theorem p_le_of_bounds (p e f : ℕ) (he : 1 ≤ e) (h : p * e + 1 ≤ f) : p ≤ (f - 1) / e := by
  have h1 : p * e ≤ f - 1 := by omega
  exact Nat.le_div_iff_mul_le (by omega) |>.mpr h1

end Erdos634.TilePlacement
