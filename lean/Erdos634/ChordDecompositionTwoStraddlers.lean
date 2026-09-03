import Erdos634.ChordDecompositionGap
import Erdos634.ChordLengthAdditivity

/-!
# The chord decomposition, assembled in full for exactly two straddlers

Erdős #634. The next concrete instance beyond `ChordDecompositionOneStraddler`, on the way to the
fully general finite induction over an arbitrary number of straddlers: given two straddlers whose
own traces occupy consecutive stretches of the chord in the order `p, r₁, s₁, r₂, s₂, q`, the
near-side chain's total over the whole chord `[p, q]` splits into three gap totals
(`chord_decomposition_of_gap`, on `[p, r₁]`, `[s₁, r₂]`, `[s₂, q]`) plus the two straddlers' own
trace lengths — glued via `hausdorff_segment_split` applied four times.

As in the one-straddler theorem's first pass, the three gaps' "no tile straddles inside" conditions
are taken directly as hypotheses here, matching `chord_decomposition_of_gap`'s own style, rather
than derived from a single global "no other tile straddles anywhere" condition. Deriving that
reduction for the *middle* gap `[s₁, r₂]` needs one more step than the one-straddler case did (a
point there must be shown disjoint from *both* straddlers' traces, not just the adjacent one) —
recorded as the next small piece, not attempted here for the same reason
`ChordDecompositionOneStraddler`'s docstring gave.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, exactly two straddlers.** Given the chord's own endpoints `p, q`,
two straddlers' trace endpoints `r₁, s₁` and `r₂, s₂` occupying consecutive stretches of the chord
in the order `p, r₁, s₁, r₂, s₂, q`, and that no tile's interior meets any of the three open gaps
`(p, r₁)`, `(s₁, r₂)`, `(s₂, q)`, the near-side chain's total over the whole chord splits into the
three gap totals plus the two straddlers' own trace lengths. -/
theorem chord_decomposition_two_straddlers {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q r₁ s₁ r₂ s₂ : Plane} (hpr₁ : p ≠ r₁) (hs₁r₂ : s₁ ≠ r₂) (hs₂q : s₂ ≠ q)
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    (hr₁ : r₁ ∈ D.target.carrier ∩ {x | f x = c}) (hs₁ : s₁ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₂ : r₂ ∈ D.target.carrier ∩ {x | f x = c}) (hs₂ : s₂ ∈ D.target.carrier ∩ {x | f x = c})
    (hws1 : Wbtw ℝ p s₁ q) (hwr1 : Wbtw ℝ p r₁ s₁)
    (hwr2 : Wbtw ℝ s₁ r₂ q) (hws2 : Wbtw ℝ r₂ s₂ q)
    (hgap1 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r₁, y ∉ interior (D.tile k).carrier)
    (hgap2 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₁ r₂, y ∉ interior (D.tile k).carrier)
    (hgap3 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₂ q, y ∉ interior (D.tile k).carrier) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p q)
      = (∑ e ∈ D.lineChain f c,
            (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
              ((D.tile e.1).edge e.2 ∩ segment ℝ p r₁))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            (segment ℝ r₁ s₁)
        + (∑ e ∈ D.lineChain f c,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                ((D.tile e.1).edge e.2 ∩ segment ℝ s₁ r₂))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            (segment ℝ r₂ s₂)
        + (∑ e ∈ D.lineChain f c,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                ((D.tile e.1).edge e.2 ∩ segment ℝ s₂ q)) := by
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  have h1 := chord_decomposition_of_gap D f hf c ⟨i, hi⟩ ⟨j, hj⟩ hpr₁ hp hr₁ hgap1
  have h2 := chord_decomposition_of_gap D f hf c ⟨i, hi⟩ ⟨j, hj⟩ hs₁r₂ hs₁ hr₂ hgap2
  have h3 := chord_decomposition_of_gap D f hf c ⟨i, hi⟩ ⟨j, hj⟩ hs₂q hs₂ hq hgap3
  have hsplit1 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ p q)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p s₁)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ s₁ q) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hws1)
  have hsplit2 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ p s₁)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p r₁)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r₁ s₁) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hwr1)
  have hsplit3 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ s₁ q)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ s₁ r₂)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r₂ q) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hwr2)
  have hsplit4 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ r₂ q)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r₂ s₂)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ s₂ q) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hws2)
  rw [hsplit1, hsplit2, hsplit3, hsplit4, h1, h2, h3]
  ring

end Erdos634.ChordTraceReal
