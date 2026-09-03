import Erdos634.ChordStraddleTotal
import Erdos634.WallChain

/-!
# The two degenerate cases the `Finset` assembly needs

Erdős #634. The two edge cases `PAPER_MAP.md` flagged as blocking the final assembly, resolved: a
"gap" or chord between two *equal* points contributes nothing, on both sides of the ledger. Both
follow from `segment ℝ u u = {u}` being a subsingleton, hence carrying zero one-dimensional
Hausdorff measure — including the sum over the near-side chain, since each summand is a subset of
that same singleton.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **A degenerate chord has zero length.** -/
theorem hausdorff_segment_self (u : Plane) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ u u) = 0 := by
  rw [segment_same]
  exact hausdorffMeasure_one_subsingleton_eq_zero (Set.subsingleton_singleton)

/-- **A degenerate gap's near-side chain total is zero.** -/
theorem chord_decomposition_of_trivial_gap {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (u : Plane) :
    (∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u u))
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ u u) := by
  rw [hausdorff_segment_self]
  apply Finset.sum_eq_zero
  intro e _
  apply hausdorffMeasure_one_subsingleton_eq_zero
  rw [segment_same]
  exact Set.subsingleton_singleton.anti Set.inter_subset_right

end Erdos634.ChordTraceReal
