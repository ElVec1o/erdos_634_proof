import Erdos634.ChordDecompositionGapGeneral
import Erdos634.ChordLengthAdditivity

/-!
# The chord decomposition, prepending one straddler — unconditionally

Erdős #634. As `chord_decomposition_cons`, but built on `chord_decomposition_of_gap'` instead of
`chord_decomposition_of_gap`: no `p ≠ r` hypothesis is needed at all. A degenerate leading gap
(`p = r`, the current position already coinciding with the straddler's own near endpoint)
contributes exactly `0`, automatically — precisely the fix `chord_decomposition_of_chain`'s general
nondegeneracy requirement needs, since it removes the only place `chord_decomposition_cons` ever
needed `p ≠ r` in the first place.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, one straddler prepended — unconditionally.** As
`chord_decomposition_cons`, but `p = r` is allowed. -/
theorem chord_decomposition_cons' {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q r s : Plane}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hr : r ∈ D.target.carrier ∩ {x | f x = c})
    (hwbtw1 : Wbtw ℝ p r s) (hwbtw2 : Wbtw ℝ p s q)
    (hgap : ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r, y ∉ interior (D.tile k).carrier)
    (Trest : ENNReal)
    (hrest : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        (segment ℝ s q) = Trest) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p q)
      = (∑ e ∈ D.lineChain f c,
            (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
              ((D.tile e.1).edge e.2 ∩ segment ℝ p r))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r s)
        + Trest := by
  have h1 := chord_decomposition_of_gap' D f hf c hlo hhi hp hr hgap
  have hsplit1 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ p q)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p s)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ s q) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hwbtw2)
  have hsplit2 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ p s)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p r)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r s) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hwbtw1)
  rw [hsplit1, hsplit2, h1, hrest]

end Erdos634.ChordTraceReal
