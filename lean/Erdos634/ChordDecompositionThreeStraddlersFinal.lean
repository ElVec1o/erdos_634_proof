import Erdos634.ChordDecompositionThreeStraddlers
import Erdos634.ChordBetweennessDisjointFar

/-!
# The chord decomposition, three straddlers, from the natural hypothesis

Erdős #634. Wires `openSegment_disjoint_segment_of_wbtw` and
`openSegment_disjoint_segment_of_wbtw_far` into `chord_decomposition_three_straddlers`, deriving
its four `hgap` hypotheses from the natural "no tile other than `m₁`, `m₂` or `m₃` straddles
anywhere" condition, instead of requiring them supplied directly. Confirms the pattern
`ChordDecompositionTwoStraddlersFinal` found: each gap is adjacent (plain lemma) to its immediately
flanking straddler(s) and reaches every other straddler only through the far lemma, chained across
however many intervening stretches lie between — here up to two hops (`gap₁` reaching `m₃`, and
`gap₄` reaching `m₁`), confirming the far lemma itself needed no change to reach further; only the
betweenness bookkeeping grows.

Two additional linking hypotheses beyond `chord_decomposition_three_straddlers`'s own are needed:
`hw_r1s1r2 : Wbtw ℝ r₁ s₁ r₂` and `hw_r2s2r3 : Wbtw ℝ r₂ s₂ r₃` (each pair of consecutive traces
occupies its stretch in the stated order), plus `hwr3q : Wbtw ℝ r₃ s₃ q` (mirroring `hwr2`'s own
reach to `q`, needed to link the third straddler's trace to the far end of the chord). Five
nondegeneracy hypotheses (`r₁≠s₁`, `r₂≠s₂`, `s₁≠s₂`, `s₂≠s₃`, `r₃≠s₃`) rule out collapsed traces.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, exactly three straddlers, from the natural hypothesis.** As
`chord_decomposition_three_straddlers`, but the four `hgap` hypotheses are derived from `hunique`
("no tile other than `m₁`, `m₂` or `m₃` straddles anywhere") and the betweenness order, instead of
assumed directly. -/
theorem chord_decomposition_three_straddlers' {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q : Plane}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    {m₁ m₂ m₃ : Fin N} (hm12 : m₁ ≠ m₂) (hm13 : m₁ ≠ m₃) (hm23 : m₂ ≠ m₃)
    {r₁ s₁ r₂ s₂ r₃ s₃ : Plane}
    (hpr₁ : p ≠ r₁) (hs₁r₂ : s₁ ≠ r₂) (hs₂r₃ : s₂ ≠ r₃) (hs₃q : s₃ ≠ q)
    (hr₁s₁ : r₁ ≠ s₁) (hr₂s₂ : r₂ ≠ s₂) (hs₁s₂ : s₁ ≠ s₂) (hs₂s₃ : s₂ ≠ s₃) (hr₃s₃ : r₃ ≠ s₃)
    (hr₁ : r₁ ∈ D.target.carrier ∩ {x | f x = c}) (hs₁ : s₁ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₂ : r₂ ∈ D.target.carrier ∩ {x | f x = c}) (hs₂ : s₂ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₃ : r₃ ∈ D.target.carrier ∩ {x | f x = c}) (hs₃ : s₃ ∈ D.target.carrier ∩ {x | f x = c})
    (hm₁trace : (D.tile m₁).carrier ∩ {x | f x = c} = segment ℝ r₁ s₁)
    (hm₂trace : (D.tile m₂).carrier ∩ {x | f x = c} = segment ℝ r₂ s₂)
    (hm₃trace : (D.tile m₃).carrier ∩ {x | f x = c} = segment ℝ r₃ s₃)
    (hws1 : Wbtw ℝ p s₁ q) (hwr1 : Wbtw ℝ p r₁ s₁)
    (hwr2 : Wbtw ℝ s₁ r₂ q) (hws2 : Wbtw ℝ r₂ s₂ q)
    (hwr3 : Wbtw ℝ s₂ r₃ s₃) (hwr3q : Wbtw ℝ r₃ s₃ q)
    (hw_r1s1r2 : Wbtw ℝ r₁ s₁ r₂) (hw_r2s2r3 : Wbtw ℝ r₂ s₂ r₃)
    (hunique : ∀ k : Fin N, k ≠ m₁ → k ≠ m₂ → k ≠ m₃ →
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
                ((D.tile e.1).edge e.2 ∩ segment ℝ s₂ r₃))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            (segment ℝ r₃ s₃)
        + (∑ e ∈ D.lineChain f c,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                ((D.tile e.1).edge e.2 ∩ segment ℝ s₃ q)) := by
  -- Level-1 chained facts (as in the two-straddler case).
  have hs1r2s2 : Wbtw ℝ s₁ r₂ s₂ := hwr2.trans_right_left hws2
  have hs1s2q : Wbtw ℝ s₁ s₂ q := hwr2.trans_right hws2
  have hr1s1s2 : Wbtw ℝ r₁ s₁ s₂ := hw_r1s1r2.trans_expand_left hs1r2s2 hs₁r₂
  have hpr1r2 : Wbtw ℝ p r₁ r₂ := hwr1.trans_expand_left hw_r1s1r2 hr₁s₁
  have hr1r2s2 : Wbtw ℝ r₁ r₂ s₂ := hr1s1s2.trans_right hs1r2s2
  have hr1r2 : r₁ ≠ r₂ := by
    rintro rfl
    have heq : dist r₁ s₁ + dist s₁ r₁ = dist r₁ r₁ := dist_add_dist_eq_iff.mpr hw_r1s1r2
    have hself : dist r₁ r₁ = 0 := dist_self r₁
    have hsymm : dist s₁ r₁ = dist r₁ s₁ := dist_comm s₁ r₁
    have h0 : dist r₁ s₁ = 0 := by linarith
    exact hr₁s₁ (dist_eq_zero.mp h0)
  -- Level-2 chained facts (mirroring level-1, one stretch further).
  have hs2s3q : Wbtw ℝ s₂ s₃ q := hwr3.trans_expand_right hwr3q hr₃s₃
  have hr2s2s3 : Wbtw ℝ r₂ s₂ s₃ := hw_r2s2r3.trans_expand_left hwr3 hs₂r₃
  have hr2r3s3 : Wbtw ℝ r₂ r₃ s₃ := hr2s2s3.trans_right hwr3
  have hr2r3 : r₂ ≠ r₃ := by
    rintro rfl
    have heq : dist r₂ s₂ + dist s₂ r₂ = dist r₂ r₂ := dist_add_dist_eq_iff.mpr hw_r2s2r3
    have hself : dist r₂ r₂ = 0 := dist_self r₂
    have hsymm : dist s₂ r₂ = dist r₂ s₂ := dist_comm s₂ r₂
    have h0 : dist r₂ s₂ = 0 := by linarith
    exact hr₂s₂ (dist_eq_zero.mp h0)
  -- Cross-level facts (linking straddler 1's stretch to straddler 3's, two hops apart).
  have hr1r2r3 : Wbtw ℝ r₁ r₂ r₃ := hr1r2s2.trans_expand_left hw_r2s2r3 hr₂s₂
  have hpr1r3 : Wbtw ℝ p r₁ r₃ := hpr1r2.trans_expand_left hr1r2r3 hr1r2
  have hr1r2s3 : Wbtw ℝ r₁ r₂ s₃ := hr1r2r3.trans_expand_left hr2r3s3 hr2r3
  have hr1r3s3 : Wbtw ℝ r₁ r₃ s₃ := hr1r2s3.trans_right hr2r3s3
  have hr1r3 : r₁ ≠ r₃ := by
    rintro rfl
    have heq : dist r₁ r₂ + dist r₂ r₁ = dist r₁ r₁ := dist_add_dist_eq_iff.mpr hr1r2r3
    have hself : dist r₁ r₁ = 0 := dist_self r₁
    have hsymm : dist r₂ r₁ = dist r₁ r₂ := dist_comm r₂ r₁
    have h0 : dist r₁ r₂ = 0 := by linarith
    exact hr1r2 (dist_eq_zero.mp h0)
  have hs1r2r3 : Wbtw ℝ s₁ r₂ r₃ := hs1r2s2.trans_expand_left hw_r2s2r3 hr₂s₂
  have hs1s2r3 : Wbtw ℝ s₁ s₂ r₃ := hs1r2r3.trans_right hw_r2s2r3
  have hs1s2s3 : Wbtw ℝ s₁ s₂ s₃ := hs1s2q.trans_right_left hs2s3q
  have hr1s1s3 : Wbtw ℝ r₁ s₁ s₃ := hr1s1s2.trans_expand_left hs1s2s3 hs₁s₂
  have hs1s3q : Wbtw ℝ s₁ s₃ q := hs1s2q.trans_right hs2s3q
  have hs1s3 : s₁ ≠ s₃ := by
    rintro rfl
    have heq : dist s₁ s₂ + dist s₂ s₁ = dist s₁ s₁ := dist_add_dist_eq_iff.mpr hs1s2s3
    have hself : dist s₁ s₁ = 0 := dist_self s₁
    have hsymm : dist s₂ s₁ = dist s₁ s₂ := dist_comm s₂ s₁
    have h0 : dist s₁ s₂ = 0 := by linarith
    exact hs₁s₂ (dist_eq_zero.mp h0)
  -- Membership-on-line helper, reused by every gap.
  have honline : ∀ {u v : Plane}, u ∈ D.target.carrier ∩ {x | f x = c} →
      v ∈ D.target.carrier ∩ {x | f x = c} → ∀ y ∈ openSegment ℝ u v, f y = c := by
    intro u v hu hv y hy
    have hyseg : y ∈ D.target.carrier ∩ {x | f x = c} :=
      Tri.convex_inter_hyperplane D.target f c |>.segment_subset hu hv
        (openSegment_subset_segment ℝ u v hy)
    exact hyseg.2
  -- Gap 1: (p, r₁).
  have hgap1 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r₁, y ∉ interior (D.tile k).carrier := by
    intro k y hy hyint
    have hyfc : f y = c := honline hp hr₁ y hy
    have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
    have hymem : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
    by_cases hkm1 : k = m₁
    · subst hkm1; exfalso; rw [hm₁trace] at hymem
      exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw hpr₁ hwr1)) hy hymem
    · by_cases hkm2 : k = m₂
      · subst hkm2; exfalso; rw [hm₂trace] at hymem
        exact (Set.disjoint_left.mp
          (openSegment_disjoint_segment_of_wbtw_far hpr₁ hr1r2 hpr1r2 hr1r2s2)) hy hymem
      · by_cases hkm3 : k = m₃
        · subst hkm3; exfalso; rw [hm₃trace] at hymem
          exact (Set.disjoint_left.mp
            (openSegment_disjoint_segment_of_wbtw_far hpr₁ hr1r3 hpr1r3 hr1r3s3)) hy hymem
        · exact hunique k hkm1 hkm2 hkm3 hstr
  -- Gap 2: (s₁, r₂).
  have hgap2 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₁ r₂, y ∉ interior (D.tile k).carrier := by
    intro k y hy hyint
    have hyfc : f y = c := honline hs₁ hr₂ y hy
    have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
    have hymem : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
    by_cases hkm2 : k = m₂
    · subst hkm2; exfalso; rw [hm₂trace] at hymem
      exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw hs₁r₂ hs1r2s2)) hy hymem
    · by_cases hkm1 : k = m₁
      · subst hkm1; exfalso; rw [hm₁trace] at hymem
        have hy' : y ∈ openSegment ℝ r₂ s₁ := by rw [openSegment_symm]; exact hy
        have hymem' : y ∈ segment ℝ s₁ r₁ := by rw [segment_symm]; exact hymem
        exact (Set.disjoint_left.mp
          (openSegment_disjoint_segment_of_wbtw (Ne.symm hs₁r₂) hw_r1s1r2.symm)) hy' hymem'
      · by_cases hkm3 : k = m₃
        · subst hkm3; exfalso; rw [hm₃trace] at hymem
          exact (Set.disjoint_left.mp
            (openSegment_disjoint_segment_of_wbtw_far hs₁r₂ hr2r3 hs1r2r3 hr2r3s3)) hy hymem
        · exact hunique k hkm1 hkm2 hkm3 hstr
  -- Gap 3: (s₂, r₃).
  have hgap3 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₂ r₃, y ∉ interior (D.tile k).carrier := by
    intro k y hy hyint
    have hyfc : f y = c := honline hs₂ hr₃ y hy
    have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
    have hymem : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
    by_cases hkm3 : k = m₃
    · subst hkm3; exfalso; rw [hm₃trace] at hymem
      exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw hs₂r₃ hwr3)) hy hymem
    · by_cases hkm2 : k = m₂
      · subst hkm2; exfalso; rw [hm₂trace] at hymem
        have hy' : y ∈ openSegment ℝ r₃ s₂ := by rw [openSegment_symm]; exact hy
        have hymem' : y ∈ segment ℝ s₂ r₂ := by rw [segment_symm]; exact hymem
        exact (Set.disjoint_left.mp
          (openSegment_disjoint_segment_of_wbtw (Ne.symm hs₂r₃) hw_r2s2r3.symm)) hy' hymem'
      · by_cases hkm1 : k = m₁
        · subst hkm1; exfalso; rw [hm₁trace] at hymem
          have hy' : y ∈ openSegment ℝ r₃ s₂ := by rw [openSegment_symm]; exact hy
          have hymem' : y ∈ segment ℝ s₁ r₁ := by rw [segment_symm]; exact hymem
          exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw_far
            (Ne.symm hs₂r₃) (Ne.symm hs₁s₂) hs1s2r3.symm hr1s1s2.symm)) hy' hymem'
        · exact hunique k hkm1 hkm2 hkm3 hstr
  -- Gap 4: (s₃, q).
  have hgap4 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₃ q, y ∉ interior (D.tile k).carrier := by
    intro k y hy hyint
    have hyfc : f y = c := honline hs₃ hq y hy
    have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
    have hymem : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
    by_cases hkm3 : k = m₃
    · subst hkm3; exfalso; rw [hm₃trace] at hymem
      have hy' : y ∈ openSegment ℝ q s₃ := by rw [openSegment_symm]; exact hy
      have hymem' : y ∈ segment ℝ s₃ r₃ := by rw [segment_symm]; exact hymem
      exact (Set.disjoint_left.mp
        (openSegment_disjoint_segment_of_wbtw (Ne.symm hs₃q) hwr3q.symm)) hy' hymem'
    · by_cases hkm2 : k = m₂
      · subst hkm2; exfalso; rw [hm₂trace] at hymem
        have hy' : y ∈ openSegment ℝ q s₃ := by rw [openSegment_symm]; exact hy
        have hymem' : y ∈ segment ℝ s₂ r₂ := by rw [segment_symm]; exact hymem
        exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw_far
          (Ne.symm hs₃q) (Ne.symm hs₂s₃) hs2s3q.symm hr2s2s3.symm)) hy' hymem'
      · by_cases hkm1 : k = m₁
        · subst hkm1; exfalso; rw [hm₁trace] at hymem
          have hy' : y ∈ openSegment ℝ q s₃ := by rw [openSegment_symm]; exact hy
          have hymem' : y ∈ segment ℝ s₁ r₁ := by rw [segment_symm]; exact hymem
          exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw_far
            (Ne.symm hs₃q) (Ne.symm hs1s3) hs1s3q.symm hr1s1s3.symm)) hy' hymem'
        · exact hunique k hkm1 hkm2 hkm3 hstr
  exact chord_decomposition_three_straddlers D f hf c hlo hhi hpr₁ hs₁r₂ hs₂r₃ hs₃q hp hq
    hr₁ hs₁ hr₂ hs₂ hr₃ hs₃ hws1 hwr1 hwr2 hws2 hs2s3q hwr3 hgap1 hgap2 hgap3 hgap4

end Erdos634.ChordTraceReal
