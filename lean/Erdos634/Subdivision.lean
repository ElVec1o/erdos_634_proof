import Mathlib
import Erdos634.Dissection

/-!
# The `k²` subdivision: the lattice and its two tile shapes

Erdős #634, the scale map's construction half.  `thm:ladder` says a triangle cut into `N` copies of
a tile gives `kT` cut into `k²N` copies; the input it needs is that `kT` itself is cut into `k²`
copies of `T`.

The lattice is `P i j = A + i·(B-A) + j·(C-A)`, and the small triangles are of two shapes: the
*upward* ones `P i j, P (i+1) j, P i (j+1)`, which are translates of `T`, and the *downward* ones
`P (i+1) j, P i (j+1), P (i+1) (j+1)`, which are not translates but have the same three side
lengths.  This file defines them and proves both shapes are congruent to `T` side for side.

What is not here is the covering: that the `k²` triangles fill `kT` with disjoint interiors.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Subdivision

open Erdos634.Geometry

variable (A B C : Plane)

/-- The subdivision lattice, anchored at `A` with steps `B - A` and `C - A`. -/
noncomputable def P (i j : ℕ) : Plane := A + (i : ℝ) • (B - A) + (j : ℝ) • (C - A)

theorem P_succ_left (i j : ℕ) : P A B C (i + 1) j = P A B C i j + (B - A) := by
  simp only [P]; push_cast; module

theorem P_succ_right (i j : ℕ) : P A B C i (j + 1) = P A B C i j + (C - A) := by
  simp only [P]; push_cast; module

/-- **The upward triangle's sides.**  `P i j, P (i+1) j, P i (j+1)` has the side lengths of
`A, B, C`. -/
theorem up_sides (i j : ℕ) :
    dist (P A B C i j) (P A B C (i + 1) j) = dist A B ∧
    dist (P A B C i j) (P A B C i (j + 1)) = dist A C ∧
    dist (P A B C (i + 1) j) (P A B C i (j + 1)) = dist B C := by
  refine ⟨?_, ?_, ?_⟩
  · rw [P_succ_left, dist_eq_norm, dist_eq_norm]
    congr 1
    abel_nf
  · rw [P_succ_right, dist_eq_norm, dist_eq_norm]
    congr 1
    abel_nf
  · rw [P_succ_left, P_succ_right, dist_eq_norm, dist_eq_norm]
    congr 1
    abel_nf

/-- **The downward triangle's sides.**  `P (i+1) j, P i (j+1), P (i+1) (j+1)` has the same three
lengths, in the order `BC`, `AB`, `AC`. -/
theorem down_sides (i j : ℕ) :
    dist (P A B C (i + 1) j) (P A B C i (j + 1)) = dist B C ∧
    dist (P A B C i (j + 1)) (P A B C (i + 1) (j + 1)) = dist A B ∧
    dist (P A B C (i + 1) j) (P A B C (i + 1) (j + 1)) = dist A C := by
  refine ⟨(up_sides A B C i j).2.2, ?_, ?_⟩
  · rw [P_succ_left, dist_eq_norm, dist_eq_norm]
    congr 1
    abel_nf
  · rw [P_succ_right, dist_eq_norm, dist_eq_norm]
    congr 1
    abel_nf

end Erdos634.Subdivision
