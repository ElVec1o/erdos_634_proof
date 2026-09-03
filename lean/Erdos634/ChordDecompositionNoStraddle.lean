import Erdos634.ChordAssembly
import Erdos634.ChordOpenSegmentInterior
import Erdos634.ChordInteriorStraddle
import Erdos634.WallChain

/-!
# The chord decomposition, complete in the no-straddler case

Erdős #634. Every individual geometric fact the chord-decomposition assembly needs is now built;
this file assembles them for the first fully complete case: a target-straddling chord with **no
straddling tile at all** is covered exactly by its near-side chain, with lengths summing to the
chord's own length. This is a genuine standalone theorem, not merely an intermediate step: it is
the general, member-independent statement that `prop:chorddecomp`'s "flush total" reduces to when
no tile crosses the chord — realistic whenever the chord lies entirely along tile boundaries.

The assembly: given the chord's own segment `p, q` (`chord_isSegment`, `p ≠ q` since the target
genuinely straddles) and the target straddling, `Tri.straddle_openSegment_interior` (applied to the
target itself) puts every point of the open chord in the target's interior — `wall_cover`'s `hint`;
"no straddling tile" plus `interior_on_line_straddles`'s contrapositive gives `hwall` (no tile's
interior meets the open chord). `WallChain.wall_partition` then finishes it.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, no straddlers.** Given the chord's own two distinct endpoints
`p, q` (from `chord_isSegment`, with the target genuinely straddling the line at both), if no
*tile* of the dissection straddles, the near-side chain covers the whole chord exactly, with
lengths summing to the chord's own length. -/
theorem chord_decomposition_of_no_straddlers {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q : Plane} (hpq : p ≠ q)
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    (hseg : D.target.carrier ∩ {x | f x = c} = segment ℝ p q)
    (hnostraddle : ∀ i : Fin N,
      ¬ ((∃ a, f ((D.tile i).pts a) < c) ∧ (∃ b, c < f ((D.tile i).pts b)))) :
    ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ p q)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          (segment ℝ p q) := by
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  have hint : openSegment ℝ p q ⊆ interior D.target.carrier := by
    rw [openSegment_eq_image_lineMap]
    rintro z ⟨s, ⟨hs0, hs1⟩, rfl⟩
    exact Tri.straddle_openSegment_interior D.target f c ⟨i, hi⟩ ⟨j, hj⟩
      hp.1 hp.2 hq.1 hq.2 hpq hs0 hs1
  have hwall : ∀ y ∈ openSegment ℝ p q, ∀ k, y ∉ interior (D.tile k).carrier := by
    intro y hy k hyint
    have hyfc : f y = c := by
      have hyseg : y ∈ D.target.carrier ∩ {x | f x = c} := by
        rw [hseg]; exact openSegment_subset_segment ℝ p q hy
      exact hyseg.2
    exact hnostraddle k (interior_on_line_straddles (D.tile k) f hf c hyint hyfc)
  have hS : segment ℝ p q ⊆ {y | f y = c} := by rw [← hseg]; exact Set.inter_subset_right
  exact D.wall_partition f c hf hpq hS hint hwall

end Erdos634.ChordTraceReal
