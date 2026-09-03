import Erdos634.ChordTraceReal

/-!
# Each straddler's own trace is a segment

Erdős #634. Continuing the chord-decomposition assembly. Item (2) of the plan recorded in
`PAPER_MAP.md`: a direct instantiation of `isSegment_of_convex_inter_hyperplane` to a single
straddling tile (rather than the whole target, as `ChordAssembly.chord_isSegment` does), using
`interior_on_line_straddles`'s converse direction (a straddler's trace is nonempty, since it has an
interior point) to supply the witness point the segment lemma needs.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **A straddling tile's trace is nonempty.** Pick vertices `i, j` with `f (T.pts i) < c` and
`c < f (T.pts j)`; the segment between them lies in `T.carrier` (convex), and `f` is affine along
it, so by the intermediate value theorem it hits `c` somewhere on the segment. -/
theorem straddle_trace_nonempty (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    {i j : Fin 3} (hi : f (T.pts i) < c) (hj : c < f (T.pts j)) :
    ∃ x ∈ T.carrier, f x = c := by
  set g : ℝ → Plane := fun t => AffineMap.lineMap (T.pts i) (T.pts j) t with hgdef
  have hgc : Continuous g := by
    have : g = fun t => AffineMap.lineMap (T.pts i) (T.pts j) t := hgdef
    fun_prop
  have hfg : Continuous (fun t => f (g t)) := f.continuous_of_finiteDimensional.comp hgc
  have h0 : f (g 0) < c := by simp [hgdef, hi]
  have h1 : c < f (g 1) := by simp [hgdef, hj]
  obtain ⟨t, ht01, htc⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hfg.continuousOn
    (show c ∈ Set.Icc (f (g 0)) (f (g 1)) from ⟨h0.le, h1.le⟩)
  refine ⟨g t, ?_, htc⟩
  have hseg : g t ∈ segment ℝ (T.pts i) (T.pts j) := by
    refine ⟨1 - t, t, by linarith [ht01.2], ht01.1, by ring, ?_⟩
    show (1 - t) • T.pts i + t • T.pts j = g t
    rw [hgdef]
    simp [AffineMap.lineMap_apply_module]
  exact T.convex.segment_subset (subset_convexHull ℝ _ ⟨i, rfl⟩)
    (subset_convexHull ℝ _ ⟨j, rfl⟩) hseg

/-- **A straddling tile's trace is a genuine segment**, between two of its own points. -/
theorem straddle_trace_isSegment (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {i j : Fin 3} (hi : f (T.pts i) < c) (hj : c < f (T.pts j)) :
    ∃ p q, p ∈ T.carrier ∩ {x | f x = c} ∧ q ∈ T.carrier ∩ {x | f x = c}
      ∧ T.carrier ∩ {x | f x = c} = segment ℝ p q := by
  obtain ⟨x0, hx0, hfx0⟩ := straddle_trace_nonempty T f c hi hj
  exact isSegment_of_convex_inter_hyperplane (Tri.convex_inter_hyperplane T f c)
    (Tri.isCompact_inter_hyperplane T f c) f hf c (fun _ hx => hx.2) x0 ⟨hx0, hfx0⟩

end Erdos634.ChordTraceReal
