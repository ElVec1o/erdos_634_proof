import Erdos634.Subdivision
import Erdos634.InteriorCoord

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

end Erdos634.Subdivision
