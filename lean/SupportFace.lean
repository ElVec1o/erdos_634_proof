-- SupportFace.lean — the geometric input to obligation G3 (`Dissection.HasEdgeChains`).
--
-- G3 says each side of the target is a finite union of whole tile edges. The step that makes that
-- true, and the one Mathlib does not supply, is: a tile lying inside the target meets a boundary
-- LINE of the target in a face of the tile, never in a partial edge. This file proves that.
--
-- Mechanism. A side of the target lies on a line where a linear functional `f` attains its maximum
-- `c` over the target, so `f ≤ c` on every tile. A point of a tile is a convex combination of its
-- vertices; if it attains `c`, then every vertex given positive weight must itself attain `c`,
-- because the deficits `c - f(vertex)` are nonnegative and sum to zero against the weights. So the
-- contact set is the convex hull of the vertices on the line: empty, a vertex, or a whole edge.
--
-- Per the project rule, `Dissection.lean` and `Interface.lean` were read first: neither carries
-- halfplane, face or support machinery, and Mathlib's `IsExtreme` API is about extreme sets rather
-- than about supporting functionals on a simplex, so this is not a restatement of either.

import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

namespace Erdos634.SupportFace

open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Points of a convex hull attaining the maximum of a linear functional come from the vertices
that attain it.** If `f ≤ c` on a finite set `s` and `x` in the convex hull of `s` has `f x = c`,
then `x` lies in the convex hull of `{v ∈ s | f v = c}`.

This is the support-face statement in the only form G3 needs. -/
theorem mem_convexHull_max (f : E →ₗ[ℝ] ℝ) (c : ℝ) (s : Finset E)
    (hle : ∀ v ∈ s, f v ≤ c) {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) (hfx : f x = c) :
    x ∈ convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) := by
  classical
  rw [Finset.convexHull_eq] at hx
  obtain ⟨w, hw0, hw1, hcm⟩ := hx
  have hcomb : ∑ v ∈ s, w v • v = x := by
    rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]; rfl
  -- the weighted deficit vanishes
  have hdef : ∑ v ∈ s, w v * (c - f v) = 0 := by
    have hfsum : ∑ v ∈ s, w v * f v = c := by
      have : f (∑ v ∈ s, w v • v) = ∑ v ∈ s, w v * f v := by
        rw [map_sum]; simp [map_smul, smul_eq_mul]
      rw [hcomb] at this; rw [← this, hfx]
    calc ∑ v ∈ s, w v * (c - f v)
        = (∑ v ∈ s, w v) * c - ∑ v ∈ s, w v * f v := by
          rw [Finset.sum_mul]; rw [← Finset.sum_sub_distrib]; ring_nf
          exact Finset.sum_congr rfl (fun v _ => by ring)
      _ = 0 := by rw [hw1, hfsum]; ring
  -- each term is nonnegative, so each vanishes
  have hterm : ∀ v ∈ s, w v * (c - f v) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hdef
    intro v hv
    exact mul_nonneg (hw0 v hv) (by linarith [hle v hv])
  -- so `w` is supported on the maximising vertices
  have hsupp : ∀ v ∈ s, w v ≠ 0 → f v = c := by
    intro v hv hne
    rcases mul_eq_zero.mp (hterm v hv) with h | h
    · exact absurd h hne
    · linarith
  -- `w` vanishes off the maximising vertices
  have hzero : ∀ v ∈ s, v ∉ s.filter (fun v => f v = c) → w v = 0 := by
    intro v hv hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hv, hsupp v hv hne⟩)
  have hsub : s.filter (fun v => f v = c) ⊆ s := Finset.filter_subset _ _
  have hsum1 : ∑ v ∈ s.filter (fun v => f v = c), w v = 1 := by
    rw [Finset.sum_subset hsub hzero]; exact hw1
  rw [Finset.convexHull_eq]
  refine ⟨w, ?_, hsum1, ?_⟩
  · intro v hv; exact hw0 v (Finset.mem_filter.mp hv).1
  · rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
    have : ∑ v ∈ s.filter (fun v => f v = c), w v • id v = ∑ v ∈ s, w v • v := by
      refine Finset.sum_subset hsub ?_
      intro v hv hnot; simp [hzero v hv hnot]
    rw [this]; exact hcomb

/-- **Contact with a supporting line is a face.** With `f ≤ c` on the hull, the set of hull points
where `f = c` is exactly the hull of the vertices where `f = c`. The inclusion proved above is the
substantial one; the reverse is monotonicity of the hull. -/
theorem contact_eq_face (f : E →ₗ[ℝ] ℝ) (c : ℝ) (s : Finset E)
    (hle : ∀ v ∈ s, f v ≤ c) :
    {x ∈ convexHull ℝ (s : Set E) | f x = c}
      = convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    exact mem_convexHull_max f c s hle hx hfx
  · intro hx
    have hsub : ((s.filter (fun v => f v = c) : Finset E) : Set E) ⊆ (s : Set E) := by
      intro v hv; exact (Finset.mem_filter.mp hv).1
    refine ⟨convexHull_mono hsub hx, ?_⟩
    -- `f = c` on the sub-hull, since it is affine and equals `c` on the generators
    have : convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) ⊆ {y | f y = c} := by
      refine convexHull_min ?_ ?_
      · intro v hv; exact (Finset.mem_filter.mp hv).2
      · intro a ha b hb ta tb hta htb htab
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul]
        linear_combination c * htab
    exact this hx

end Erdos634.SupportFace
