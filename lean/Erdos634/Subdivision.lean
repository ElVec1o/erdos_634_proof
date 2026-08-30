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

/-! ## The cell decomposition

Each unit cell of the lattice splits into the upward and downward triangle, and the split is by
`u + v ≤ 1` against `u + v ≥ 1`.  Both halves are exhibited as explicit convex combinations, which
is what the covering argument will consume. -/

/-- A convex combination of three points lies in their hull. -/
theorem combo_mem (p q r : Plane) (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    a • p + b • q + c • r ∈ convexHull ℝ ({p, q, r} : Set Plane) := by
  set S : Set Plane := {p, q, r} with hS
  have hcv := convex_convexHull ℝ S
  have hp : p ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [hS])
  have hq : q ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [hS])
  have hr : r ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [hS])
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ b + c by linarith) with h1 | h1
  · have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    have ha1 : a = 1 := by linarith
    simpa [ha1, hb0, hc0] using hp
  · have hmid : (b/(b+c)) • q + (c/(b+c)) • r ∈ convexHull ℝ S :=
      hcv hq hr (by positivity) (by positivity) (by field_simp)
    have hfin := hcv hp hmid ha (le_of_lt h1) (by linarith : a + (b + c) = 1)
    have heq : a • p + (b + c) • ((b/(b+c)) • q + (c/(b+c)) • r) = a • p + b • q + c • r := by
      rw [smul_add, smul_smul, smul_smul]
      rw [show (b + c) * (b/(b+c)) = b by field_simp, show (b + c) * (c/(b+c)) = c by field_simp]
      abel
    rwa [heq] at hfin

theorem P_succ_both (i j : ℕ) :
    P A B C (i + 1) (j + 1) = P A B C i j + (B - A) + (C - A) := by
  simp only [P]; push_cast; module

/-- **The lower half of a cell is the upward triangle.** -/
theorem mem_up (i j : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    P A B C i j + u • (B - A) + v • (C - A)
      ∈ convexHull ℝ ({P A B C i j, P A B C (i + 1) j, P A B C i (j + 1)} : Set Plane) := by
  have hpt : P A B C i j + u • (B - A) + v • (C - A)
      = (1 - u - v) • P A B C i j + u • P A B C (i + 1) j + v • P A B C i (j + 1) := by
    rw [P_succ_left, P_succ_right]; module
  rw [hpt]
  exact combo_mem _ _ _ (1 - u - v) u v (by linarith) hu hv (by ring)

/-- **The upper half of a cell is the downward triangle.** -/
theorem mem_down (i j : ℕ) (u v : ℝ) (hu1 : u ≤ 1) (hv1 : v ≤ 1) (huv : 1 ≤ u + v) :
    P A B C i j + u • (B - A) + v • (C - A)
      ∈ convexHull ℝ
        ({P A B C (i + 1) (j + 1), P A B C (i + 1) j, P A B C i (j + 1)} : Set Plane) := by
  have hpt : P A B C i j + u • (B - A) + v • (C - A)
      = (u + v - 1) • P A B C (i + 1) (j + 1) + (1 - v) • P A B C (i + 1) j
        + (1 - u) • P A B C i (j + 1) := by
    rw [P_succ_both, P_succ_left, P_succ_right]; module
  rw [hpt]
  exact combo_mem _ _ _ (u + v - 1) (1 - v) (1 - u) (by linarith) (by linarith) (by linarith)
    (by ring)

/-! ## Placing a point in a cell

The global half of the covering: a point of `kT`, written in the lattice coordinates `s, t ≥ 0`
with `s + t ≤ k`, sits in a cell `(i, j)` with `i + j ≤ k - 1`.  Taking floors works except when
both coordinates are integers summing to `k`, where the point is on the far edge and one index must
be lowered by one. -/

/-- **Every point of `kT` lies in a cell of the subdivision.** -/
theorem cell_index (k : ℕ) (hk : 1 ≤ k) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t ≤ (k : ℝ)) :
    ∃ i j : ℕ, i + j + 1 ≤ k ∧ (i : ℝ) ≤ s ∧ s ≤ (i : ℝ) + 1 ∧ (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 := by
  classical
  set i₀ := ⌊s⌋₊ with hi₀
  set j₀ := ⌊t⌋₊ with hj₀
  have hi₀s : (i₀ : ℝ) ≤ s := Nat.floor_le hs
  have hj₀t : (j₀ : ℝ) ≤ t := Nat.floor_le ht
  have hsi₀ : s < (i₀ : ℝ) + 1 := Nat.lt_floor_add_one s
  have htj₀ : t < (j₀ : ℝ) + 1 := Nat.lt_floor_add_one t
  rcases Nat.lt_or_ge k (i₀ + j₀ + 1) with hgt | hle
  · -- the floors already sum to `k`, so both coordinates are integers and `s + t = k`
    have hsum : (i₀ : ℝ) + (j₀ : ℝ) ≤ s + t := by linarith
    have hk' : (k : ℝ) ≤ (i₀ : ℝ) + (j₀ : ℝ) := by
      have : k ≤ i₀ + j₀ := by omega
      exact_mod_cast this
    have hseq : s = (i₀ : ℝ) := by linarith
    have hteq : t = (j₀ : ℝ) := by linarith
    have hij : i₀ + j₀ = k := by
      have h1 : (i₀ : ℝ) + (j₀ : ℝ) = (k : ℝ) := by linarith
      exact_mod_cast h1
    rcases Nat.eq_zero_or_pos i₀ with hi0 | hi0
    · refine ⟨0, j₀ - 1, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · simpa using hs
      · rw [hseq, hi0]; norm_num
      · have : ((j₀ - 1 : ℕ) : ℝ) = (j₀ : ℝ) - 1 := by
          have : 1 ≤ j₀ := by omega
          push_cast [Nat.cast_sub this]; ring
        rw [this, hteq]; linarith
      · have : ((j₀ - 1 : ℕ) : ℝ) = (j₀ : ℝ) - 1 := by
          have : 1 ≤ j₀ := by omega
          push_cast [Nat.cast_sub this]; ring
        rw [this, hteq]; linarith
    · refine ⟨i₀ - 1, j₀, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · have : ((i₀ - 1 : ℕ) : ℝ) = (i₀ : ℝ) - 1 := by
          push_cast [Nat.cast_sub hi0]; ring
        rw [this, hseq]; linarith
      · have : ((i₀ - 1 : ℕ) : ℝ) = (i₀ : ℝ) - 1 := by
          push_cast [Nat.cast_sub hi0]; ring
        rw [this, hseq]; linarith
      · rw [hteq]
      · rw [hteq]; linarith

  · exact ⟨i₀, j₀, hle, hi₀s, le_of_lt hsi₀, hj₀t, le_of_lt htj₀⟩
end Erdos634.Subdivision
