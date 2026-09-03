import Erdos634.ChordDecompositionGap
import Erdos634.ChordLengthAdditivity
import Erdos634.ChordEndpointsDistinct
import Erdos634.ChordStraddlerSegment

/-!
# The chord decomposition, assembled in full for exactly one straddler

Erdős #634. The first genuinely complete multi-tile chord-decomposition theorem: exactly one tile
straddles the chord, and the near-side chain's total length over the *whole* chord `[p, q]` equals
the sum of two "gap" totals (`chord_decomposition_of_gap`, on `[p, r]` and `[s, q]`) plus the one
straddler's own trace length `[r, s]` — glued via `hausdorff_segment_split` applied twice. This is
the concrete instance the general induction generalizes.

The two gaps' "no tile straddles inside" hypotheses are taken directly (matching
`chord_decomposition_of_gap`'s own style): in a concrete situation these follow from the
betweenness order `p, r, s, q` plus "no other tile straddles anywhere", but deriving that reduction
internally needs its own collinear-monotonicity lemma (distance from `p` is monotone along
`p → r → s → q`) that is not yet built — recorded as the next small piece, not attempted here to
avoid a fragile ad hoc argument.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, exactly one straddler.** Given the chord's own endpoints `p, q`,
the one straddler `m`'s own trace endpoints `r, s`, and that no tile's interior meets either open
gap `(p, r)` or `(s, q)`, the near-side chain's total over the whole chord splits into the two gap
totals plus the straddler's own trace length. -/
theorem chord_decomposition_one_straddler {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q : Plane}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    {r s : Plane} (hpr : p ≠ r) (hsq : s ≠ q)
    (hr : r ∈ D.target.carrier ∩ {x | f x = c}) (hs : s ∈ D.target.carrier ∩ {x | f x = c})
    (hwbtw1 : Wbtw ℝ p r q) (hwbtw2 : Wbtw ℝ r s q)
    (hgap1 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r, y ∉ interior (D.tile k).carrier)
    (hgap2 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s q, y ∉ interior (D.tile k).carrier) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p q)
      = (∑ e ∈ D.lineChain f c,
            (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
              ((D.tile e.1).edge e.2 ∩ segment ℝ p r))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r s)
        + (∑ e ∈ D.lineChain f c,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                ((D.tile e.1).edge e.2 ∩ segment ℝ s q)) := by
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  have h1 := chord_decomposition_of_gap D f hf c ⟨i, hi⟩ ⟨j, hj⟩ hpr hp hr hgap1
  have h2 := chord_decomposition_of_gap D f hf c ⟨i, hi⟩ ⟨j, hj⟩ hsq hs hq hgap2
  have hsplit1 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ p q)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p r)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r q) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hwbtw1)
  have hsplit2 : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      (segment ℝ r q)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r s)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ s q) :=
    hausdorff_segment_split (mem_segment_iff_wbtw.mpr hwbtw2)
  rw [hsplit1, hsplit2, h1, h2]
  ring

end Erdos634.ChordTraceReal
