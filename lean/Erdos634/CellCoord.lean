import Erdos634.Subdivision
import Erdos634.InteriorCoord
import Erdos634.CongruentArea

/-!
# The cells' barycentric coordinates, and their interiors as `openUp` / `openDown`

Erdős #634, `thm:ladder`'s obligation **(C3)**.

`Subdivision` proves the coordinate conditions `openUp` / `openDown` pairwise incompatible
(`cell_pinned`, `up_down_disjoint`) — but those are predicates on the *lattice* coordinates
`(s,t) = (coord 1 x, coord 2 x)` of the big triangle, not statements about
`interior (cellUp …).carrier`, which is what `Dissection.interiors_disjoint` asks for. This file
supplies the missing identification.

The computation is exact. Writing `s`, `t` for the big triangle's lattice coordinates of `x`:

* the upward cell `(i,j)` has vertices at lattice points `(i,j)`, `(i+1,j)`, `(i,j+1)`, and the
  barycentric coordinates of `x` in it are `(1 - (s-i) - (t-j), s-i, t-j)`;
* the downward cell `(i,j)` has vertices `(i+1,j)`, `(i,j+1)`, `(i+1,j+1)`, and they are
  `(1-(t-j), 1-(s-i), (s-i)+(t-j)-1)`.

Positivity of the first triple is literally `openUp i j s t`; of the second, `openDown i j s t`.
With `Tri.interior_iff_pos_coord` that turns `Subdivision`'s coordinate lemmas into disjointness of
the cells' actual interiors.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Subdivision

open Erdos634.Geometry

variable (A B C : Plane)

/-- **Barycentric coordinates are determined by any affine representation.** If `x` is written as a
weighted sum of the vertices with weights summing to `1`, those weights *are* the coordinates. -/
theorem Tri.coord_eq_of_combo (T : Tri) (x : Plane) (w : Fin 3 → ℝ)
    (hsum : w 0 + w 1 + w 2 = 1)
    (hx : x = w 0 • T.pts 0 + w 1 • T.pts 1 + w 2 • T.pts 2) (k : Fin 3) :
    T.basis.coord k x = w k := by
  have hw : Finset.univ.sum w = 1 := by rw [Fin.sum_univ_three]; exact hsum
  have hcomb : Finset.univ.affineCombination ℝ T.pts w = x := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, Fin.sum_univ_three, hx]
  have hcoe : (⇑T.basis : Fin 3 → Plane) = T.pts := rfl
  have h2 := T.basis.coord_apply_combination_of_mem (i := k) (Finset.mem_univ k) hw
  rw [hcoe, hcomb] at h2
  exact h2

/-- **The upward cell's coordinates.** -/
theorem cellUp_coord (hindep : AffineIndependent ℝ ![A, B, C]) (i j : ℕ) (x : Plane)
    (s t : ℝ) (hs : s = (⟨![A,B,C], hindep⟩ : Tri).basis.coord 1 x)
    (ht : t = (⟨![A,B,C], hindep⟩ : Tri).basis.coord 2 x) :
    (cellUp A B C hindep i j).basis.coord 0 x = 1 - (s - i) - (t - j) ∧
    (cellUp A B C hindep i j).basis.coord 1 x = s - i ∧
    (cellUp A B C hindep i j).basis.coord 2 x = t - j := by
  set T : Tri := ⟨![A,B,C], hindep⟩ with hT
  have hA : T.pts 0 = A := rfl
  have hB : T.pts 1 = B := rfl
  have hC : T.pts 2 = C := rfl
  -- `x` in lattice form
  have hlat : x = A + s • (B - A) + t • (C - A) := by
    rw [hs, ht]
    have := lattice_coords T x
    rw [hA, hB, hC] at this
    exact this
  set w : Fin 3 → ℝ := ![1 - (s - i) - (t - j), s - i, t - j] with hw
  have hsum : w 0 + w 1 + w 2 = 1 := by simp [hw]; ring
  have hcomb : x = w 0 • (cellUp A B C hindep i j).pts 0
      + w 1 • (cellUp A B C hindep i j).pts 1 + w 2 • (cellUp A B C hindep i j).pts 2 := by
    rw [cellUp_pts0, cellUp_pts1, cellUp_pts2]
    simp only [hw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, P]
    rw [hlat]
    push_cast
    module
  refine ⟨?_, ?_, ?_⟩ <;>
    [ have := Tri.coord_eq_of_combo _ x w hsum hcomb 0;
      have := Tri.coord_eq_of_combo _ x w hsum hcomb 1;
      have := Tri.coord_eq_of_combo _ x w hsum hcomb 2 ] <;>
    simpa [hw] using this

/-- **The upward cell's interior is exactly `openUp`.** -/
theorem mem_interior_cellUp_iff (hindep : AffineIndependent ℝ ![A, B, C]) (i j : ℕ) (x : Plane) :
    x ∈ interior (cellUp A B C hindep i j).carrier ↔
      openUp i j ((⟨![A,B,C], hindep⟩ : Tri).basis.coord 1 x)
        ((⟨![A,B,C], hindep⟩ : Tri).basis.coord 2 x) := by
  set s := (⟨![A,B,C], hindep⟩ : Tri).basis.coord 1 x with hs
  set t := (⟨![A,B,C], hindep⟩ : Tri).basis.coord 2 x with ht
  obtain ⟨h0, h1, h2⟩ := cellUp_coord A B C hindep i j x s t hs ht
  rw [Tri.interior_iff_pos_coord]
  constructor
  · intro h
    have p0 := h 0; have p1 := h 1; have p2 := h 2
    rw [h0] at p0; rw [h1] at p1; rw [h2] at p2
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hi, hj, hij⟩ k
    have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
    rcases htri k with rfl | rfl | rfl
    · rw [h0]; linarith
    · rw [h1]; linarith
    · rw [h2]; linarith

/-- **The downward cell's coordinates.** Vertices at lattice points `(i+1,j)`, `(i,j+1)`,
`(i+1,j+1)`; the weights are `(1-(t-j), 1-(s-i), (s-i)+(t-j)-1)`. -/
theorem cellDown_coord (hindep : AffineIndependent ℝ ![A, B, C]) (i j : ℕ) (x : Plane)
    (s t : ℝ) (hs : s = (⟨![A,B,C], hindep⟩ : Tri).basis.coord 1 x)
    (ht : t = (⟨![A,B,C], hindep⟩ : Tri).basis.coord 2 x) :
    (cellDown A B C hindep i j).basis.coord 0 x = 1 - (t - j) ∧
    (cellDown A B C hindep i j).basis.coord 1 x = 1 - (s - i) ∧
    (cellDown A B C hindep i j).basis.coord 2 x = (s - i) + (t - j) - 1 := by
  set T : Tri := ⟨![A,B,C], hindep⟩ with hT
  have hA : T.pts 0 = A := rfl
  have hB : T.pts 1 = B := rfl
  have hC : T.pts 2 = C := rfl
  have hlat : x = A + s • (B - A) + t • (C - A) := by
    rw [hs, ht]
    have := lattice_coords T x
    rw [hA, hB, hC] at this
    exact this
  set w : Fin 3 → ℝ := ![1 - (t - j), 1 - (s - i), (s - i) + (t - j) - 1] with hw
  have hsum : w 0 + w 1 + w 2 = 1 := by simp [hw]; ring
  have hcomb : x = w 0 • (cellDown A B C hindep i j).pts 0
      + w 1 • (cellDown A B C hindep i j).pts 1 + w 2 • (cellDown A B C hindep i j).pts 2 := by
    rw [cellDown_pts0, cellDown_pts1, cellDown_pts2]
    simp only [hw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, P]
    rw [hlat]
    push_cast
    module
  refine ⟨?_, ?_, ?_⟩ <;>
    [ have := Tri.coord_eq_of_combo _ x w hsum hcomb 0;
      have := Tri.coord_eq_of_combo _ x w hsum hcomb 1;
      have := Tri.coord_eq_of_combo _ x w hsum hcomb 2 ] <;>
    simpa [hw] using this

/-- **The downward cell's interior is exactly `openDown`.** -/
theorem mem_interior_cellDown_iff (hindep : AffineIndependent ℝ ![A, B, C]) (i j : ℕ) (x : Plane) :
    x ∈ interior (cellDown A B C hindep i j).carrier ↔
      openDown i j ((⟨![A,B,C], hindep⟩ : Tri).basis.coord 1 x)
        ((⟨![A,B,C], hindep⟩ : Tri).basis.coord 2 x) := by
  set s := (⟨![A,B,C], hindep⟩ : Tri).basis.coord 1 x with hs
  set t := (⟨![A,B,C], hindep⟩ : Tri).basis.coord 2 x with ht
  obtain ⟨h0, h1, h2⟩ := cellDown_coord A B C hindep i j x s t hs ht
  rw [Tri.interior_iff_pos_coord]
  constructor
  · intro h
    have p0 := h 0; have p1 := h 1; have p2 := h 2
    rw [h0] at p0; rw [h1] at p1; rw [h2] at p2
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hi, hj, hij⟩ k
    have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
    rcases htri k with rfl | rfl | rfl
    · rw [h0]; linarith
    · rw [h1]; linarith
    · rw [h2]; linarith

/-! ## (C3): the cells' interiors are pairwise disjoint

With the two identifications above, `Subdivision`'s coordinate lemmas transfer verbatim. A cell is
named by its lattice indices together with a shape; distinct names give disjoint interiors. -/

/-- **Two distinct upward cells have disjoint interiors.** -/
theorem cellUp_interiors_disjoint (hindep : AffineIndependent ℝ ![A, B, C]) (i j i' j' : ℕ)
    (hne : (i, j) ≠ (i', j')) :
    Disjoint (interior (cellUp A B C hindep i j).carrier)
      (interior (cellUp A B C hindep i' j').carrier) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_interior_cellUp_iff] at hx hx'
  obtain ⟨hii, hjj⟩ := cell_pinned i i' j j' _ _
    (up_pins_i i j _ _ hx) (up_pins_i i' j' _ _ hx')
    (up_pins_j i j _ _ hx) (up_pins_j i' j' _ _ hx')
  exact hne (by rw [hii, hjj])

/-- **Two distinct downward cells have disjoint interiors.** -/
theorem cellDown_interiors_disjoint (hindep : AffineIndependent ℝ ![A, B, C]) (i j i' j' : ℕ)
    (hne : (i, j) ≠ (i', j')) :
    Disjoint (interior (cellDown A B C hindep i j).carrier)
      (interior (cellDown A B C hindep i' j').carrier) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_interior_cellDown_iff] at hx hx'
  obtain ⟨hii, hjj⟩ := cell_pinned i i' j j' _ _
    (down_pins_i i j _ _ hx) (down_pins_i i' j' _ _ hx')
    (down_pins_j i j _ _ hx) (down_pins_j i' j' _ _ hx')
  exact hne (by rw [hii, hjj])

/-- **An upward and a downward cell have disjoint interiors**, whatever their indices: if the
indices differ they are pinned apart, and within one cell the diagonal separates the two shapes
(`up_down_disjoint`). -/
theorem cellUp_cellDown_disjoint (hindep : AffineIndependent ℝ ![A, B, C]) (i j i' j' : ℕ) :
    Disjoint (interior (cellUp A B C hindep i j).carrier)
      (interior (cellDown A B C hindep i' j').carrier) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_interior_cellUp_iff] at hx
  rw [mem_interior_cellDown_iff] at hx'
  obtain ⟨hii, hjj⟩ := cell_pinned i i' j j' _ _
    (up_pins_i i j _ _ hx) (down_pins_i i' j' _ _ hx')
    (up_pins_j i j _ _ hx) (down_pins_j i' j' _ _ hx')
  subst hii; subst hjj
  exact up_down_disjoint i j _ _ hx hx'

/-! ## (C2): every cell lies in the big triangle

The big triangle at scale `k` is the homothety image of `(A,B,C)` centred at `A` with ratio `k`;
its vertices are the lattice points `(0,0)`, `(k,0)`, `(0,k)`. A lattice point `(i,j)` with
`i + j ≤ k` has big-triangle barycentric coordinates `(1 - i/k - j/k, i/k, j/k)`, all nonnegative,
so it lies in the big triangle; convexity then carries the whole cell. -/

/-- The homothety carrying `(A,B,C)` to the scale-`k` triangle. -/
noncomputable def bigMap (k : ℝ) : Plane →ᵃ[ℝ] Plane := AffineMap.homothety A k

theorem bigMap_injective {k : ℝ} (hk : k ≠ 0) : Function.Injective (bigMap A k) := by
  intro x y hxy
  simp only [bigMap, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] at hxy
  have h : k • (x - A) = k • (y - A) := by
    have := congrArg (fun z => z - A) hxy
    simpa using this
  have hx : x - A = y - A := smul_right_injective Plane hk h
  exact sub_left_inj.mp hx

/-- **The scale-`k` triangle.** -/
noncomputable def bigTri (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) : Tri where
  pts := ![A, P A B C k 0, P A B C 0 k]
  indep := by
    have hmap : (![A, P A B C k 0, P A B C 0 k] : Fin 3 → Plane)
        = (bigMap A (k : ℝ)) ∘ ![A, B, C] := by
      funext x
      have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
      rcases htri x with rfl | rfl | rfl <;>
        simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, bigMap,
          AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, P] <;>
        push_cast <;> module
    rw [hmap]
    exact hindep.map' _ (bigMap_injective A (by exact_mod_cast hk.ne'))

theorem bigTri_pts0 (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) :
    (bigTri A B C hindep k hk).pts 0 = A := rfl

theorem bigTri_pts1 (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) :
    (bigTri A B C hindep k hk).pts 1 = P A B C k 0 := rfl

theorem bigTri_pts2 (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) :
    (bigTri A B C hindep k hk).pts 2 = P A B C 0 k := rfl

/-- **A lattice point with `i + j ≤ k` lies in the scale-`k` triangle.** -/
theorem P_mem_bigTri (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)
    (i j : ℕ) (hij : i + j ≤ k) :
    P A B C i j ∈ (bigTri A B C hindep k hk).carrier := by
  set G : Tri := bigTri A B C hindep k hk with hG
  have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  set w : Fin 3 → ℝ := ![1 - i / k - j / k, i / k, j / k] with hw
  have hsum : w 0 + w 1 + w 2 = 1 := by simp [hw]; ring
  have hcomb : P A B C i j = w 0 • G.pts 0 + w 1 • G.pts 1 + w 2 • G.pts 2 := by
    rw [bigTri_pts0, bigTri_pts1, bigTri_pts2]
    simp only [hw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, P]
    match_scalars <;> (field_simp; try ring)
  rw [G.carrier_eq_nonneg_coord]
  intro m
  rw [Tri.coord_eq_of_combo G _ w hsum hcomb m]
  have hijR : (i : ℝ) + (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hij
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  rcases htri m with rfl | rfl | rfl <;> simp only [hw, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · have h1 : ((i:ℝ) + (j:ℝ)) / (k:ℝ) ≤ 1 := (div_le_one hkR).mpr hijR
    have h2 : (i:ℝ)/(k:ℝ) + (j:ℝ)/(k:ℝ) = ((i:ℝ) + (j:ℝ))/(k:ℝ) := by ring
    linarith
  · positivity
  · positivity

/-- **(C2), upward cells.** -/
theorem cellUp_subset_bigTri (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)
    (i j : ℕ) (hij : i + j + 1 ≤ k) :
    (cellUp A B C hindep i j).carrier ⊆ (bigTri A B C hindep k hk).carrier := by
  refine convexHull_min ?_ (bigTri A B C hindep k hk).convex
  rintro y ⟨m, rfl⟩
  have htri : ∀ z : Fin 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
  rcases htri m with rfl | rfl | rfl
  · rw [cellUp_pts0]; exact P_mem_bigTri A B C hindep k hk i j (by omega)
  · rw [cellUp_pts1]; exact P_mem_bigTri A B C hindep k hk (i+1) j (by omega)
  · rw [cellUp_pts2]; exact P_mem_bigTri A B C hindep k hk i (j+1) (by omega)

/-- **(C2), downward cells.** -/
theorem cellDown_subset_bigTri (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)
    (i j : ℕ) (hij : i + j + 2 ≤ k) :
    (cellDown A B C hindep i j).carrier ⊆ (bigTri A B C hindep k hk).carrier := by
  refine convexHull_min ?_ (bigTri A B C hindep k hk).convex
  rintro y ⟨m, rfl⟩
  have htri : ∀ z : Fin 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
  rcases htri m with rfl | rfl | rfl
  · rw [cellDown_pts0]; exact P_mem_bigTri A B C hindep k hk (i+1) j (by omega)
  · rw [cellDown_pts1]; exact P_mem_bigTri A B C hindep k hk i (j+1) (by omega)
  · rw [cellDown_pts2]; exact P_mem_bigTri A B C hindep k hk (i+1) (j+1) (by omega)

/-! ## (C4): each cell has the tile's area

The upward cell is a translate of `(A,B,C)`; the downward cell is the point reflection
`x ↦ v - x` of the reversed triple, `v = P(i+1,j+1) + A`. Both are isometries, so
`CongruentArea.volume_congruent` gives each cell the tile's area. -/

/-- Translation as an isometry equivalence. -/
noncomputable def transIso (c : Plane) : Plane ≃ᵢ Plane where
  toEquiv := Equiv.addRight c
  isometry_toFun := Isometry.of_dist_eq (by intro x y; simp [Equiv.addRight, dist_eq_norm])

/-- The point reflection `x ↦ v - x` as an isometry equivalence. -/
noncomputable def reflIso (v : Plane) : Plane ≃ᵢ Plane where
  toEquiv := (Equiv.neg Plane).trans (Equiv.addRight v)
  isometry_toFun := Isometry.of_dist_eq (by
    intro x y
    show dist (-x + v) (-y + v) = dist x y
    rw [dist_eq_norm, dist_eq_norm, show -x + v - (-y + v) = -(x - y) by abel, norm_neg])

/-- **The upward cell is congruent to the tile.** -/
theorem cellUp_congruent (hindep : AffineIndependent ℝ ![A, B, C]) (i j : ℕ) :
    Tri.Congruent (⟨![A,B,C], hindep⟩ : Tri) (cellUp A B C hindep i j) :=
  ⟨transIso (P A B C i j - A), Equiv.refl _, by
    intro m
    have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
    rcases htri m with rfl | rfl | rfl
    · show A + (P A B C i j - A) = P A B C i j
      abel
    · show B + (P A B C i j - A) = P A B C (i+1) j
      simp only [P]; push_cast; module
    · show C + (P A B C i j - A) = P A B C i (j+1)
      simp only [P]; push_cast; module⟩

/-- **The downward cell is congruent to the tile.** -/
theorem cellDown_congruent (hindep : AffineIndependent ℝ ![A, B, C]) (i j : ℕ) :
    Tri.Congruent (⟨![A,B,C], hindep⟩ : Tri) (cellDown A B C hindep i j) :=
  ⟨reflIso (P A B C (i+1) (j+1) + A), Equiv.swap 0 2, by
    intro m
    have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
    have s0 : (Equiv.swap (0:Fin 3) 2) 0 = 2 := by decide
    have s1 : (Equiv.swap (0:Fin 3) 2) 1 = 1 := by decide
    have s2 : (Equiv.swap (0:Fin 3) 2) 2 = 0 := by decide
    rcases htri m with rfl | rfl | rfl
    · rw [s0]
      show -A + (P A B C (i+1) (j+1) + A) = P A B C (i+1) (j+1)
      abel
    · rw [s1]
      show -B + (P A B C (i+1) (j+1) + A) = P A B C i (j+1)
      simp only [P]; push_cast; module
    · rw [s2]
      show -C + (P A B C (i+1) (j+1) + A) = P A B C (i+1) j
      simp only [P]; push_cast; module⟩

/-- **(C4), per cell: an upward cell has the tile's area.** -/
theorem volume_cellUp (hindep : AffineIndependent ℝ ![A, B, C]) (i j : ℕ) :
    MeasureTheory.volume (cellUp A B C hindep i j).carrier
      = MeasureTheory.volume (⟨![A,B,C], hindep⟩ : Tri).carrier :=
  (Erdos634.CongruentArea.volume_congruent (cellUp_congruent A B C hindep i j)).symm

/-- **(C4), per cell: a downward cell has the tile's area.** -/
theorem volume_cellDown (hindep : AffineIndependent ℝ ![A, B, C]) (i j : ℕ) :
    MeasureTheory.volume (cellDown A B C hindep i j).carrier
      = MeasureTheory.volume (⟨![A,B,C], hindep⟩ : Tri).carrier :=
  (Erdos634.CongruentArea.volume_congruent (cellDown_congruent A B C hindep i j)).symm

end Erdos634.Subdivision
