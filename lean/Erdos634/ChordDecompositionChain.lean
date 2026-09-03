import Erdos634.ChordDecompositionCons
import Erdos634.WbtwChain

/-!
# The chord decomposition, given a sorted chain of straddlers

Erdős #634. The "sum splits given a sorted chain" half of the general finite induction (the other
half — sorting a `Finset` of straddlers into this shape — is separate and not attempted here, per
`PAPER_MAP.md`'s precise split). Given the straddler data packaged as a point sequence
`g : ℕ → Plane` (`g 0 = p`, `g (2i+1), g (2i+2)` the `i`-th straddler's oriented trace, `g (2n+1) =
q`) with consecutive-triple `Wbtw` facts (`wbtw_chain_bounded`'s own hypothesis shape) and
gap-freedom for each of the `n+1` gaps, the near-side chain's total over `[p, q]` splits into the
`n` trace lengths plus the `n+1` gap totals — by induction on `n`, peeling one straddler off the
front at each step via `chord_decomposition_cons`.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition, given a sorted chain of straddlers.** -/
theorem chord_decomposition_of_chain {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j)) :
    ∀ (n : ℕ) (g : ℕ → Plane) (tiles : ℕ → Fin N),
      (∀ i, i + 2 ≤ 2 * n + 1 → Wbtw ℝ (g i) (g (i + 1)) (g (i + 2))) →
      (∀ i, i + 1 ≤ 2 * n + 1 → g i ≠ g (i + 1)) →
      (∀ a b, a ≤ 2 * n + 1 → b ≤ 2 * n + 1 → a ≠ b → g a ≠ g b) →
      (∀ i, i ≤ 2 * n + 1 → g i ∈ D.target.carrier ∩ {x | f x = c}) →
      (∀ i, i < n →
        (D.tile (tiles i)).carrier ∩ {x | f x = c} = segment ℝ (g (2 * i + 1)) (g (2 * i + 2))) →
      (∀ i, i ≤ n → ∀ k : Fin N, ∀ y ∈ openSegment ℝ (g (2 * i)) (g (2 * i + 1)),
        y ∉ interior (D.tile k).carrier) →
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          (segment ℝ (g 0) (g (2 * n + 1)))
        = (∑ i ∈ Finset.range n,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                (segment ℝ (g (2 * i + 1)) (g (2 * i + 2))))
          + ∑ i ∈ Finset.range (n + 1),
              ∑ e ∈ D.lineChain f c,
                (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                  ((D.tile e.1).edge e.2 ∩ segment ℝ (g (2 * i)) (g (2 * i + 1))) := by
  intro n
  induction n with
  | zero =>
    intro g tiles _ hne _ hpts _ hgap
    have h := chord_decomposition_of_gap D f hf c hlo hhi
      (hne 0 (by omega)) (hpts 0 (by omega)) (hpts 1 (by omega)) (hgap 0 (by omega))
    simp only [Finset.range_zero, Finset.sum_empty, Finset.range_one, Finset.sum_singleton,
      zero_add, Nat.mul_zero]
    simpa using h.symm
  | succ n ih =>
    intro g tiles hchain hne hinj hpts hmtrace hgap
    set g2 : ℕ → Plane := fun i => g (i + 2) with hg2def
    set tiles2 : ℕ → Fin N := fun i => tiles (i + 1) with htiles2def
    have hchain2 : ∀ i, i + 2 ≤ 2 * n + 1 → Wbtw ℝ (g2 i) (g2 (i + 1)) (g2 (i + 2)) := by
      intro i hi
      have := hchain (i + 2) (by omega)
      simpa [hg2def, show i + 2 + 1 = i + 1 + 2 from by omega,
        show i + 2 + 2 = i + 2 + 2 from rfl] using this
    have hne2 : ∀ i, i + 1 ≤ 2 * n + 1 → g2 i ≠ g2 (i + 1) := by
      intro i hi
      have := hne (i + 2) (by omega)
      simpa [hg2def] using this
    have hinj2 : ∀ a b, a ≤ 2 * n + 1 → b ≤ 2 * n + 1 → a ≠ b → g2 a ≠ g2 b := by
      intro a b ha hb hab
      exact hinj (a + 2) (b + 2) (by omega) (by omega) (by omega)
    have hpts2 : ∀ i, i ≤ 2 * n + 1 → g2 i ∈ D.target.carrier ∩ {x | f x = c} := by
      intro i hi
      exact hpts (i + 2) (by omega)
    have hmtrace2 : ∀ i, i < n →
        (D.tile (tiles2 i)).carrier ∩ {x | f x = c}
          = segment ℝ (g2 (2 * i + 1)) (g2 (2 * i + 2)) := by
      intro i hi
      have := hmtrace (i + 1) (by omega)
      simpa [hg2def, htiles2def, show 2 * i + 1 + 2 = 2 * (i + 1) + 1 from by ring,
        show 2 * i + 2 + 2 = 2 * (i + 1) + 2 from by ring] using this
    have hgap2 : ∀ i, i ≤ n → ∀ k : Fin N, ∀ y ∈ openSegment ℝ (g2 (2 * i)) (g2 (2 * i + 1)),
        y ∉ interior (D.tile k).carrier := by
      intro i hi k y hy
      have e1 : g2 (2 * i) = g (2 * (i + 1)) := by
        show g (2 * i + 2) = g (2 * (i + 1)); rw [show 2 * i + 2 = 2 * (i + 1) from by ring]
      have e2 : g2 (2 * i + 1) = g (2 * (i + 1) + 1) := by
        show g (2 * i + 1 + 2) = g (2 * (i + 1) + 1)
        rw [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 from by ring]
      rw [e1, e2] at hy
      exact hgap (i + 1) (by omega) k y hy
    have hrec := ih g2 tiles2 hchain2 hne2 hinj2 hpts2 hmtrace2 hgap2
    have hpr : g 0 ≠ g 1 := hne 0 (by omega)
    have hp0 : g 0 ∈ D.target.carrier ∩ {x | f x = c} := hpts 0 (by omega)
    have hr1 : g 1 ∈ D.target.carrier ∩ {x | f x = c} := hpts 1 (by omega)
    have hwbtw1 : Wbtw ℝ (g 0) (g 1) (g 2) := hchain 0 (by omega)
    have hwbtw2 : Wbtw ℝ (g 0) (g 2) (g (2 * (n + 1) + 1)) :=
      wbtw_chain_bounded (2 * (n + 1) + 1) hchain hne hinj 0 2 (2 * (n + 1) + 1)
        (by omega) (by omega) (le_refl _)
    have hgap0 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ (g 0) (g 1), y ∉ interior (D.tile k).carrier :=
      hgap 0 (by omega)
    have heqK : g2 (2 * n + 1) = g (2 * (n + 1) + 1) := by
      show g (2 * n + 1 + 2) = g (2 * (n + 1) + 1)
      rw [show 2 * n + 1 + 2 = 2 * (n + 1) + 1 from by ring]
    rw [heqK] at hrec
    have hcons := chord_decomposition_cons D f hf c hlo hhi hpr hp0 hr1 hwbtw1 hwbtw2 hgap0
      _ hrec
    rw [hcons]
    conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hshift1 : ∀ i, (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        (segment ℝ (g2 (2 * i + 1)) (g2 (2 * i + 2)))
        = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            (segment ℝ (g (2 * (i + 1) + 1)) (g (2 * (i + 1) + 2))) := by
      intro i
      have e1 : g2 (2 * i + 1) = g (2 * (i + 1) + 1) := by
        show g (2 * i + 1 + 2) = g (2 * (i + 1) + 1)
        rw [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 from by ring]
      have e2 : g2 (2 * i + 2) = g (2 * (i + 1) + 2) := by
        show g (2 * i + 2 + 2) = g (2 * (i + 1) + 2)
        rw [show 2 * i + 2 + 2 = 2 * (i + 1) + 2 from by ring]
      rw [e1, e2]
    have hshift2 : ∀ i, ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ (g2 (2 * i)) (g2 (2 * i + 1)))
        = ∑ e ∈ D.lineChain f c,
            (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
              ((D.tile e.1).edge e.2 ∩ segment ℝ (g (2 * (i + 1))) (g (2 * (i + 1) + 1))) := by
      intro i
      have e1 : g2 (2 * i) = g (2 * (i + 1)) := by
        show g (2 * i + 2) = g (2 * (i + 1))
        rw [show 2 * i + 2 = 2 * (i + 1) from by ring]
      have e2 : g2 (2 * i + 1) = g (2 * (i + 1) + 1) := by
        show g (2 * i + 1 + 2) = g (2 * (i + 1) + 1)
        rw [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 from by ring]
      rw [e1, e2]
    simp only [hshift1, hshift2]
    ring

end Erdos634.ChordTraceReal
