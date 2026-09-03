import Erdos634.ChordDecompositionGap
import Erdos634.ChordLengthAdditivity

/-!
# The chord decomposition, prepending one straddler to an existing decomposition

Erdős #634. The genuine recursive step of the general finite induction over an arbitrary number of
straddlers (the piece `PAPER_MAP.md` records as "still not built" for the *whole* induction):
`chord_decomposition_one_straddler`, `_two_`, `_three_` each unroll this step by hand, a fixed
number of times. Stated once, taking whatever total already holds for the *rest* of the chord
`[s, q]` as a hypothesis (however that total was itself established — directly, by
`chord_decomposition_of_no_straddlers`, or by this same lemma applied again), prepending one more
straddler with leading gap `(p, r)` and trace `[r, s]` extends it to the whole chord `[p, q]`. A
`List`/`Finset` induction packaging an arbitrary straddler count would apply this lemma once per
list element; that packaging itself is not done here.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, one straddler prepended to an existing total.** Given the leading
gap `(p, r)`'s own total (via `chord_decomposition_of_gap`), the trace length `[r, s]`, and
whatever total `Trest` already holds for the rest of the chord `[s, q]`, the near-side chain's
total over the whole chord `[p, q]` is their sum. -/
theorem chord_decomposition_cons {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q r s : Plane} (hpr : p ≠ r)
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
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  have h1 := chord_decomposition_of_gap D f hf c ⟨i, hi⟩ ⟨j, hj⟩ hpr hp hr hgap
  have hprs : Wbtw ℝ p r s := hwbtw1
  have hsplit1 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ p q)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p s)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ s q) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hwbtw2)
  have hsplit2 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ p s)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p r)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r s) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hprs)
  rw [hsplit1, hsplit2, h1, hrest]

end Erdos634.ChordTraceReal
