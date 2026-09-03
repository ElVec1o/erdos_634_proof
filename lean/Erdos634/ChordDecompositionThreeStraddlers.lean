import Erdos634.ChordDecompositionGap
import Erdos634.ChordLengthAdditivity

/-!
# The chord decomposition, assembled in full for exactly three straddlers

Erdős #634. The next rung of the ladder beyond `ChordDecompositionTwoStraddlers`, on the way to the
fully general finite induction over an arbitrary number of straddlers: given three straddlers whose
own traces occupy consecutive stretches of the chord in the order
`p, r₁, s₁, r₂, s₂, r₃, s₃, q`, the near-side chain's total over the whole chord `[p, q]` splits
into four gap totals (`chord_decomposition_of_gap`, on `[p, r₁]`, `[s₁, r₂]`, `[s₂, r₃]`, `[s₃, q]`)
plus the three straddlers' own trace lengths — glued via `hausdorff_segment_split` applied six
times.

As with the two-straddler case's first pass, the four gaps' "no tile straddles inside" conditions
are taken directly as hypotheses here, matching `chord_decomposition_of_gap`'s own style. Deriving
them from a single global `hunique` condition is the same kind of work
`ChordDecompositionTwoStraddlersFinal` did for two straddlers, scaled up: the two *middle* gaps here
are each adjacent to their own flanking straddler on one side and reach across one more stretch to
a *non-adjacent* straddler on the other (needing the "far" lemma chained one hop further than the
two-straddler case ever needed) — not attempted in this pass.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, exactly three straddlers.** Given the chord's own endpoints `p, q`,
three straddlers' trace endpoints `r₁,s₁`, `r₂,s₂`, `r₃,s₃` occupying consecutive stretches of the
chord in the order `p, r₁, s₁, r₂, s₂, r₃, s₃, q`, and that no tile's interior meets any of the four
open gaps `(p, r₁)`, `(s₁, r₂)`, `(s₂, r₃)`, `(s₃, q)`, the near-side chain's total over the whole
chord splits into the four gap totals plus the three straddlers' own trace lengths. -/
theorem chord_decomposition_three_straddlers {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q r₁ s₁ r₂ s₂ r₃ s₃ : Plane}
    (hpr₁ : p ≠ r₁) (hs₁r₂ : s₁ ≠ r₂) (hs₂r₃ : s₂ ≠ r₃) (hs₃q : s₃ ≠ q)
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    (hr₁ : r₁ ∈ D.target.carrier ∩ {x | f x = c}) (hs₁ : s₁ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₂ : r₂ ∈ D.target.carrier ∩ {x | f x = c}) (hs₂ : s₂ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₃ : r₃ ∈ D.target.carrier ∩ {x | f x = c}) (hs₃ : s₃ ∈ D.target.carrier ∩ {x | f x = c})
    (hws1 : Wbtw ℝ p s₁ q) (hwr1 : Wbtw ℝ p r₁ s₁)
    (hwr2 : Wbtw ℝ s₁ r₂ q) (hws2 : Wbtw ℝ r₂ s₂ q)
    (hws3 : Wbtw ℝ s₂ s₃ q) (hwr3 : Wbtw ℝ s₂ r₃ s₃)
    (hgap1 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r₁, y ∉ interior (D.tile k).carrier)
    (hgap2 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₁ r₂, y ∉ interior (D.tile k).carrier)
    (hgap3 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₂ r₃, y ∉ interior (D.tile k).carrier)
    (hgap4 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₃ q, y ∉ interior (D.tile k).carrier) :
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
                ((D.tile e.1).edge e.2 ∩ segment ℝ s₂ r₃))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            (segment ℝ r₃ s₃)
        + (∑ e ∈ D.lineChain f c,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                ((D.tile e.1).edge e.2 ∩ segment ℝ s₃ q)) := by
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  have h1 := chord_decomposition_of_gap D f hf c ⟨i, hi⟩ ⟨j, hj⟩ hpr₁ hp hr₁ hgap1
  have h2 := chord_decomposition_of_gap D f hf c ⟨i, hi⟩ ⟨j, hj⟩ hs₁r₂ hs₁ hr₂ hgap2
  have h3 := chord_decomposition_of_gap D f hf c ⟨i, hi⟩ ⟨j, hj⟩ hs₂r₃ hs₂ hr₃ hgap3
  have h4 := chord_decomposition_of_gap D f hf c ⟨i, hi⟩ ⟨j, hj⟩ hs₃q hs₃ hq hgap4
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
  have hsplit5 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ s₂ q)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ s₂ s₃)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ s₃ q) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hws3)
  have hsplit6 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ s₂ s₃)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ s₂ r₃)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r₃ s₃) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hwr3)
  rw [hsplit1, hsplit2, hsplit3, hsplit4, hsplit5, hsplit6, h1, h2, h3, h4]
  ring

end Erdos634.ChordTraceReal
