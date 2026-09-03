import Erdos634.ChordDecompositionOneStraddler
import Erdos634.ChordBetweennessDisjoint

/-!
# The chord decomposition, one straddler, from the natural hypothesis

Erdős #634. Wires `ChordBetweennessDisjoint.openSegment_disjoint_segment_of_wbtw` into
`chord_decomposition_one_straddler`, deriving its two `hgap` hypotheses from the natural
"no *other* tile straddles anywhere" condition plus the betweenness order, instead of requiring
them supplied directly.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, exactly one straddler, from the natural hypothesis.** As
`chord_decomposition_one_straddler`, but `hgap1`/`hgap2` are derived from `hunique` ("no tile
other than `m` straddles anywhere") instead of assumed directly. -/
theorem chord_decomposition_one_straddler' {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q : Plane}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    {m : Fin N} {r s : Plane} (hpr : p ≠ r) (hsq : s ≠ q)
    (hr : r ∈ D.target.carrier ∩ {x | f x = c}) (hs : s ∈ D.target.carrier ∩ {x | f x = c})
    (hmtrace : (D.tile m).carrier ∩ {x | f x = c} = segment ℝ r s)
    (hwbtw1 : Wbtw ℝ p r q) (hwbtw2 : Wbtw ℝ r s q)
    (hunique : ∀ k : Fin N, k ≠ m →
      ¬ ((∃ a, f ((D.tile k).pts a) < c) ∧ (∃ b, c < f ((D.tile k).pts b)))) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p q)
      = (∑ e ∈ D.lineChain f c,
            (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
              ((D.tile e.1).edge e.2 ∩ segment ℝ p r))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r s)
        + (∑ e ∈ D.lineChain f c,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                ((D.tile e.1).edge e.2 ∩ segment ℝ s q)) := by
  have hprs : Wbtw ℝ p r s := hwbtw1.trans_right_left hwbtw2
  have hqsr : Wbtw ℝ q s r := Wbtw.symm hwbtw2
  have hgap1 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r, y ∉ interior (D.tile k).carrier := by
    intro k y hy hyint
    have hyfc : f y = c := by
      have hyseg : y ∈ D.target.carrier ∩ {x | f x = c} :=
        Tri.convex_inter_hyperplane D.target f c |>.segment_subset hp hr
          (openSegment_subset_segment ℝ p r hy)
      exact hyseg.2
    have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
    by_cases hkm : k = m
    · subst hkm
      exfalso
      have hymem : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
      rw [hmtrace] at hymem
      exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw hpr hprs)) hy hymem
    · exact hunique k hkm hstr
  have hgap2 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s q, y ∉ interior (D.tile k).carrier := by
    intro k y hy hyint
    have hyfc : f y = c := by
      have hyseg : y ∈ D.target.carrier ∩ {x | f x = c} :=
        Tri.convex_inter_hyperplane D.target f c |>.segment_subset hs hq
          (openSegment_subset_segment ℝ s q hy)
      exact hyseg.2
    have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
    by_cases hkm : k = m
    · subst hkm
      exfalso
      have hymem : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
      rw [hmtrace] at hymem
      have hysq : y ∈ openSegment ℝ q s := by rw [openSegment_symm]; exact hy
      have hymem' : y ∈ segment ℝ s r := by rw [segment_symm]; exact hymem
      exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw (Ne.symm hsq) hqsr))
        hysq hymem'
    · exact hunique k hkm hstr
  exact chord_decomposition_one_straddler D f hf c hlo hhi hp hq hpr hsq hr hs
    hwbtw1 hwbtw2 hgap1 hgap2

end Erdos634.ChordTraceReal
