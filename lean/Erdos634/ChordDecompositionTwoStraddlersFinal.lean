import Erdos634.ChordDecompositionTwoStraddlers
import Erdos634.ChordBetweennessDisjointFar

/-!
# The chord decomposition, two straddlers, from the natural hypothesis

Erdős #634. Wires `ChordBetweennessDisjoint.openSegment_disjoint_segment_of_wbtw` and
`ChordBetweennessDisjointFar.openSegment_disjoint_segment_of_wbtw_far` into
`chord_decomposition_two_straddlers`, deriving its three `hgap` hypotheses from the natural
"no tile other than `m₁` or `m₂` straddles anywhere" condition, instead of requiring them supplied
directly. The two outer gaps each meet only one straddler's trace adjacently (the one-straddler
pattern); the middle gap `(s₁, r₂)` is adjacent to `m₂`'s trace on one side but reaches `m₁`'s trace
only across the whole `[r₁, s₁]` stretch, which is exactly what the "far" lemma is for.

One additional hypothesis beyond `chord_decomposition_two_straddlers`'s own is needed to make the
whole chain of betweenness facts derivable: `hw_r1s1r2 : Wbtw ℝ r₁ s₁ r₂`, i.e. that the two
straddlers' traces occupy their stretches in the stated order (not just each individually between
`p` and `q`). Two nondegeneracy hypotheses (`r₁ ≠ s₁`, `s₁ ≠ s₂`) rule out the straddler traces
collapsing to points, which the betweenness algebra otherwise cannot exclude.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, exactly two straddlers, from the natural hypothesis.** As
`chord_decomposition_two_straddlers`, but the three `hgap` hypotheses are derived from `hunique`
("no tile other than `m₁` or `m₂` straddles anywhere") and the betweenness order, instead of
assumed directly. -/
theorem chord_decomposition_two_straddlers' {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q : Plane}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    {m₁ m₂ : Fin N} (hm : m₁ ≠ m₂)
    {r₁ s₁ r₂ s₂ : Plane} (hpr₁ : p ≠ r₁) (hs₁r₂ : s₁ ≠ r₂) (hs₂q : s₂ ≠ q)
    (hr₁s₁ : r₁ ≠ s₁) (hs₁s₂ : s₁ ≠ s₂)
    (hr₁ : r₁ ∈ D.target.carrier ∩ {x | f x = c}) (hs₁ : s₁ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₂ : r₂ ∈ D.target.carrier ∩ {x | f x = c}) (hs₂ : s₂ ∈ D.target.carrier ∩ {x | f x = c})
    (hm₁trace : (D.tile m₁).carrier ∩ {x | f x = c} = segment ℝ r₁ s₁)
    (hm₂trace : (D.tile m₂).carrier ∩ {x | f x = c} = segment ℝ r₂ s₂)
    (hws1 : Wbtw ℝ p s₁ q) (hwr1 : Wbtw ℝ p r₁ s₁)
    (hwr2 : Wbtw ℝ s₁ r₂ q) (hws2 : Wbtw ℝ r₂ s₂ q)
    (hw_r1s1r2 : Wbtw ℝ r₁ s₁ r₂)
    (hunique : ∀ k : Fin N, k ≠ m₁ → k ≠ m₂ →
      ¬ ((∃ a, f ((D.tile k).pts a) < c) ∧ (∃ b, c < f ((D.tile k).pts b)))) :
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
  -- Chained betweenness facts derived once, used by several gaps below.
  have hs₁r₂s2 : Wbtw ℝ s₁ r₂ s₂ := hwr2.trans_right_left hws2
  have hs1s2q : Wbtw ℝ s₁ s₂ q := hwr2.trans_right hws2
  have hr1s1s2 : Wbtw ℝ r₁ s₁ s₂ := hw_r1s1r2.trans_expand_left hs₁r₂s2 hs₁r₂
  have hpr1r2 : Wbtw ℝ p r₁ r₂ := hwr1.trans_expand_left hw_r1s1r2 hr₁s₁
  have hr1r2s2 : Wbtw ℝ r₁ r₂ s₂ := hr1s1s2.trans_right hs₁r₂s2
  have hr1r2 : r₁ ≠ r₂ := by
    rintro rfl
    have heq : dist r₁ s₁ + dist s₁ r₁ = dist r₁ r₁ := dist_add_dist_eq_iff.mpr hw_r1s1r2
    have hself : dist r₁ r₁ = 0 := dist_self r₁
    have hsymm : dist s₁ r₁ = dist r₁ s₁ := dist_comm s₁ r₁
    have h0 : dist r₁ s₁ = 0 := by linarith
    exact hr₁s₁ (dist_eq_zero.mp h0)
  -- Gap 1: (p, r₁). Adjacent to m₁'s trace [r₁, s₁]; far from m₂'s trace [r₂, s₂].
  have hgap1 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r₁, y ∉ interior (D.tile k).carrier := by
    intro k y hy hyint
    have hyfc : f y = c := by
      have hyseg : y ∈ D.target.carrier ∩ {x | f x = c} :=
        Tri.convex_inter_hyperplane D.target f c |>.segment_subset hp hr₁
          (openSegment_subset_segment ℝ p r₁ hy)
      exact hyseg.2
    have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
    have hymem : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
    by_cases hkm1 : k = m₁
    · subst hkm1
      exfalso
      rw [hm₁trace] at hymem
      exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw hpr₁ hwr1)) hy hymem
    · by_cases hkm2 : k = m₂
      · subst hkm2
        exfalso
        rw [hm₂trace] at hymem
        exact (Set.disjoint_left.mp
          (openSegment_disjoint_segment_of_wbtw_far hpr₁ hr1r2 hpr1r2 hr1r2s2)) hy hymem
      · exact hunique k hkm1 hkm2 hstr
  -- Gap 2: (s₁, r₂). Adjacent to m₂'s trace [r₂, s₂]; far from m₁'s trace [r₁, s₁] (reversed).
  have hgap2 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₁ r₂, y ∉ interior (D.tile k).carrier := by
    intro k y hy hyint
    have hyfc : f y = c := by
      have hyseg : y ∈ D.target.carrier ∩ {x | f x = c} :=
        Tri.convex_inter_hyperplane D.target f c |>.segment_subset hs₁ hr₂
          (openSegment_subset_segment ℝ s₁ r₂ hy)
      exact hyseg.2
    have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
    have hymem : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
    by_cases hkm2 : k = m₂
    · subst hkm2
      exfalso
      rw [hm₂trace] at hymem
      exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw hs₁r₂ hs₁r₂s2)) hy hymem
    · by_cases hkm1 : k = m₁
      · subst hkm1
        exfalso
        rw [hm₁trace] at hymem
        have hy' : y ∈ openSegment ℝ r₂ s₁ := by rw [openSegment_symm]; exact hy
        have hymem' : y ∈ segment ℝ s₁ r₁ := by rw [segment_symm]; exact hymem
        exact (Set.disjoint_left.mp
          (openSegment_disjoint_segment_of_wbtw (Ne.symm hs₁r₂) hw_r1s1r2.symm)) hy' hymem'
      · exact hunique k hkm1 hkm2 hstr
  -- Gap 3: (s₂, q). Adjacent to m₂'s trace [r₂, s₂] (reversed); far from m₁'s trace (reversed).
  have hgap3 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₂ q, y ∉ interior (D.tile k).carrier := by
    intro k y hy hyint
    have hyfc : f y = c := by
      have hyseg : y ∈ D.target.carrier ∩ {x | f x = c} :=
        Tri.convex_inter_hyperplane D.target f c |>.segment_subset hs₂ hq
          (openSegment_subset_segment ℝ s₂ q hy)
      exact hyseg.2
    have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
    have hymem : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
    by_cases hkm2 : k = m₂
    · subst hkm2
      exfalso
      rw [hm₂trace] at hymem
      have hy' : y ∈ openSegment ℝ q s₂ := by rw [openSegment_symm]; exact hy
      have hymem' : y ∈ segment ℝ s₂ r₂ := by rw [segment_symm]; exact hymem
      exact (Set.disjoint_left.mp
        (openSegment_disjoint_segment_of_wbtw (Ne.symm hs₂q) hws2.symm)) hy' hymem'
    · by_cases hkm1 : k = m₁
      · subst hkm1
        exfalso
        rw [hm₁trace] at hymem
        have hy' : y ∈ openSegment ℝ q s₂ := by rw [openSegment_symm]; exact hy
        have hymem' : y ∈ segment ℝ s₁ r₁ := by rw [segment_symm]; exact hymem
        exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw_far
          (Ne.symm hs₂q) (Ne.symm hs₁s₂) hs1s2q.symm hr1s1s2.symm)) hy' hymem'
      · exact hunique k hkm1 hkm2 hstr
  exact chord_decomposition_two_straddlers D f hf c hlo hhi hpr₁ hs₁r₂ hs₂q hp hq hr₁ hs₁ hr₂ hs₂
    hws1 hwr1 hwr2 hws2 hgap1 hgap2 hgap3

end Erdos634.ChordTraceReal
