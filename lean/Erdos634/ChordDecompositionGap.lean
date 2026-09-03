import Erdos634.ChordDecompositionNoStraddle

/-!
# The chord decomposition, on any gap between two points of the chord

Erdős #634. Generalizes `chord_decomposition_of_no_straddlers` from the chord's own two extreme
points `p, q` to *any* two distinct points of the chord — exactly the building block the full
multi-straddler assembly needs: applied to two consecutive straddler-trace endpoints (a "gap" with
no straddler crossing strictly inside it), this gives that gap's own near-side-chain total, ready
to be summed against `straddle_total_eq_sum`'s own total over all the straddler traces.

The only change from `chord_decomposition_of_no_straddlers` is that `Tri.straddle_openSegment_interior`
never actually needed `p, q` to be the chord's own extreme points — any two points of
`D.target.carrier ∩ {f = c}` work, since the target still straddles regardless of which two chord
points are chosen. Likewise `hwall` only ever needs to hold on the *particular* open segment in
question, not globally across the whole chord.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, on a gap.** Given any two distinct points `u₁, u₂` of the chord
(not necessarily its own extreme points) between which no tile straddles, the near-side chain
covers `segment ℝ u₁ u₂` exactly, with lengths summing to its length. -/
theorem chord_decomposition_of_gap {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (h1 : u₁ ∈ D.target.carrier ∩ {x | f x = c}) (h2 : u₂ ∈ D.target.carrier ∩ {x | f x = c})
    (hgapstraddle : ∀ k : Fin N, ∀ y ∈ openSegment ℝ u₁ u₂, y ∉ interior (D.tile k).carrier) :
    ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          (segment ℝ u₁ u₂) := by
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  have hint : openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier := by
    rw [openSegment_eq_image_lineMap]
    rintro z ⟨s, ⟨hs0, hs1⟩, rfl⟩
    exact Tri.straddle_openSegment_interior D.target f c ⟨i, hi⟩ ⟨j, hj⟩
      h1.1 h1.2 h2.1 h2.2 hu hs0 hs1
  have hS : segment ℝ u₁ u₂ ⊆ {y | f y = c} := by
    have hsub : D.target.carrier ∩ {x | f x = c} ⊆ {x | f x = c} := Set.inter_subset_right
    have hseg_sub : segment ℝ u₁ u₂ ⊆ D.target.carrier ∩ {x | f x = c} :=
      Tri.convex_inter_hyperplane D.target f c |>.segment_subset h1 h2
    exact hseg_sub.trans hsub
  exact D.wall_partition f c hf hu hS hint (fun y hy k => hgapstraddle k y hy)

end Erdos634.ChordTraceReal
