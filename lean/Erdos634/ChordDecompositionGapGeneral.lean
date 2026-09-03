import Erdos634.ChordDecompositionGap
import Erdos634.ChordFinsetDegenerate

/-!
# The chord decomposition on a gap, unconditionally (no `u₁ ≠ u₂` needed)

Erdős #634. Unifies `chord_decomposition_of_gap` (needs `u₁ ≠ u₂`) and
`chord_decomposition_of_trivial_gap` (the `u₁ = u₂` case, contributing `0`) into one lemma taking no
nondegeneracy hypothesis at all. This is the fix the general induction's own nondegeneracy
requirement (`chord_decomposition_of_chain`'s `hne`, needed at *every* consecutive pair) has been
pointing at: rebuilding `chord_decomposition_cons` (and hence `chord_decomposition_of_chain`) on top
of this instead removes the need to separately rule out any adjacent coincidence — degenerate gaps
already contribute exactly `0`, automatically.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord decomposition on a gap, unconditionally.** As `chord_decomposition_of_gap`, but
`u₁ = u₂` is allowed — that case contributes `0` on both sides, via
`chord_decomposition_of_trivial_gap`. -/
theorem chord_decomposition_of_gap' {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {u₁ u₂ : Plane}
    (h1 : u₁ ∈ D.target.carrier ∩ {x | f x = c}) (h2 : u₂ ∈ D.target.carrier ∩ {x | f x = c})
    (hgapstraddle : ∀ k : Fin N, ∀ y ∈ openSegment ℝ u₁ u₂, y ∉ interior (D.tile k).carrier) :
    ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          (segment ℝ u₁ u₂) := by
  by_cases hu : u₁ = u₂
  · subst hu
    exact chord_decomposition_of_trivial_gap D f c u₁
  · exact chord_decomposition_of_gap D f hf c hlo hhi hu h1 h2 hgapstraddle

end Erdos634.ChordTraceReal
