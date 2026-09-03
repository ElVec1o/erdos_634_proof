import Erdos634.ChordDecompositionGap
import Erdos634.ChordEndpointsDistinct
import Erdos634.ChordStraddlerSegment
import Mathlib.Analysis.Convex.StrictConvexBetween

/-!
# Length additivity along a segment

Erdős #634. The general real-line fact the multi-straddler assembly needs to glue gap totals and
straddler totals into the whole chord's length: if `y` lies on `segment ℝ x z`, then
`segment ℝ x z` splits into `segment ℝ x y` and `segment ℝ y z`, and their `μH¹` lengths (each
exactly the Euclidean distance between endpoints, `MeasureTheory.hausdorffMeasure_segment`) add,
via the classical "triangle inequality is equality along a segment"
(`dist_add_dist_eq_iff`/`Wbtw`, needing `Plane`'s `StrictConvexSpace` instance).

With `chord_decomposition_of_gap` (the per-gap total) and `straddle_total_eq_sum` (the straddle
total) already built, this is the last general ingredient: for exactly one straddler, splitting
`[p, q]` at the straddler's own trace `[r, s]` twice (via this lemma) gives
`length[p,q] = length[p,r] + length[r,s] + length[s,q]`, matching a gap total, the straddle total,
and a second gap total — not yet assembled into that concrete two-gap theorem, nor generalized to
the full finite induction over an arbitrary number of straddlers.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **Length additivity along a segment.** If `y ∈ segment ℝ x z`, the whole segment's `μH¹`
length is the sum of the two sub-segments' lengths. -/
theorem hausdorff_segment_split {x y z : Plane} (hxy : y ∈ segment ℝ x z) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ x z)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ x y)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ y z) := by
  rw [MeasureTheory.hausdorffMeasure_segment, MeasureTheory.hausdorffMeasure_segment,
    MeasureTheory.hausdorffMeasure_segment]
  have hwbtw : Wbtw ℝ x y z := mem_segment_iff_wbtw.mp hxy
  have hdist : dist x y + dist y z = dist x z := dist_add_dist_eq_iff.mpr hwbtw
  rw [edist_dist, edist_dist, edist_dist, ← hdist]
  rw [ENNReal.ofReal_add dist_nonneg dist_nonneg]

end Erdos634.ChordTraceReal
