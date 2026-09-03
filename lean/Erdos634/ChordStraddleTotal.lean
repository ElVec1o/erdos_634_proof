import Erdos634.ChordTraceReal

/-!
# The straddle total, additive

Erdős #634. Continuing the `ChordTrace` bridge (`ChordTraceReal.lean`): the paper's
`prop:chorddecomp` tracks a chord's "straddle total" (the combined length of every straddling
tile's crossing segment) as one of two separately-accounted quantities, because a naive sum over
*every* tile touching the chord double-counts a shared edge between two opposite-side flush
neighbors (recorded in `ChordTraceReal.lean`'s header). The straddle total itself has no such
issue: `ChordTraceReal.trace_disjoint_of_straddle` already shows any two tiles with at least one of
them straddling meet in at most one point, so the straddling tiles' own traces are pairwise
disjoint outright — restricting to them, length-additivity holds unconditionally, with no
one-sided convention needed.

`straddle_total_eq_sum` is exactly this: for any `Dissection`, any line `(f, c)` with `f ≠ 0`, the
one-dimensional Hausdorff measure of the union of every straddling tile's trace equals the sum of
their individual trace lengths.

This is not `prop:chorddecomp` itself (that also needs the flush total, tracked separately, and the
member-specific `(3,7)` numerics), but it is the general, member-independent form of exactly the
"straddle total" half of that proposition's own bookkeeping.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- A subsingleton set has zero one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_one_subsingleton_eq_zero {s : Set Plane} (hs : s.Subsingleton) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) s = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · rw [(Set.subsingleton_iff_singleton hx).1 hs]
    haveI := MeasureTheory.Measure.noAtoms_hausdorff Plane (show (0:ℝ) < 1 by norm_num)
    exact MeasureTheory.measure_singleton x

/-- **The set of tiles straddling a given line.** -/
noncomputable def straddlers {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter
    (fun i => (∃ a, f ((D.tile i).pts a) < c) ∧ (∃ b, c < f ((D.tile i).pts b)))

/-- **The straddle total is additive.** The straddling tiles' traces are pairwise disjoint
(`trace_disjoint_of_straddle`, needing just one of any pair to straddle — true of both here), so
the one-dimensional measure of their union is exactly the sum of their individual lengths. -/
theorem straddle_total_eq_sum {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        (⋃ i ∈ straddlers D f c, (D.tile i).carrier ∩ {x | f x = c})
      = ∑ i ∈ straddlers D f c,
          (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            ((D.tile i).carrier ∩ {x | f x = c}) := by
  classical
  have hmeas : ∀ b ∈ straddlers D f c,
      MeasurableSet ((D.tile b).carrier ∩ {x | f x = c}) := by
    intro b _
    exact ((D.tile b).measurableSet).inter (measurableSet_eq_fun
      (f.continuous_of_finiteDimensional.measurable) measurable_const)
  have hdisj : Set.Pairwise (↑(straddlers D f c) : Set (Fin N))
      (Function.onFun
        (MeasureTheory.AEDisjoint (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane))
        (fun i => (D.tile i).carrier ∩ {x | f x = c})) := by
    intro i hi j hj hij
    have hjval : j ∈ straddlers D f c := hj
    simp only [straddlers, Finset.mem_filter, Finset.mem_univ, true_and] at hjval
    have hsub := trace_disjoint_of_straddle D f c hij hjval.1 hjval.2
    show (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        (((D.tile i).carrier ∩ {x | f x = c}) ∩ ((D.tile j).carrier ∩ {x | f x = c})) = 0
    exact hausdorffMeasure_one_subsingleton_eq_zero hsub
  exact MeasureTheory.measure_biUnion_finset₀ hdisj
    (fun b hb => (hmeas b hb).nullMeasurableSet)

end Erdos634.ChordTraceReal
