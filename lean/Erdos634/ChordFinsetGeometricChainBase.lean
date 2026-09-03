import Erdos634.ChordFinsetBaseCase
import Erdos634.ChordEndpointFrontierGeneral
import Erdos634.WbtwChain
import Erdos634.ChordInteriorStraddle

/-!
# The geometric chain's base case: no straddlers remain

Erdős #634. The `L = []` case of `exists_geometric_chain` (the geometric twin of
`exists_injective_chain`): if every straddling tile's far endpoint weakly precedes the current
position `bound`, no tile's interior meets `bound` itself. If it did, `bound` would have to equal
that tile's own far endpoint exactly (via `wbtw_global_of_local` placing it between the trace's own
extremes, then `wbtw_antisymm_of_wbtw` collapsing it against the exclusion bound) — but a trace's
own extreme point is never interior to its own tile (`chord_endpoint_not_interior'`), contradiction.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **No straddler's interior meets the current position, once all are excluded.** -/
theorem not_interior_of_all_excluded {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P bound : Plane}
    (R S : Fin N → Plane)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧ R k ≠ S k ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k))
    (hexcl : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (S k) bound)
    (hboundfc : f bound = c) :
    ∀ k : Fin N, bound ∉ interior (D.tile k).carrier := by
  intro k hbint
  have hstr := interior_on_line_straddles (D.tile k) f hf c hbint hboundfc
  obtain ⟨hgo, hne, hktrace⟩ := hglobal k hstr.1 hstr.2
  have hbmem : bound ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hbint, hboundfc⟩
  rw [hktrace] at hbmem
  have hlocal : Wbtw ℝ (R k) bound (S k) := mem_segment_iff_wbtw.mp hbmem
  have hSb : Wbtw ℝ P (S k) bound := hexcl k hstr.1 hstr.2
  have hbS : Wbtw ℝ P bound (S k) := (wbtw_global_of_local hgo hlocal).2
  have heq : S k = bound := wbtw_antisymm_of_wbtw hSb hbS
  have hnotint : S k ∉ interior (D.tile k).carrier := by
    have hseg : (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (S k) (R k) := by
      rw [hktrace, segment_symm]
    exact chord_endpoint_not_interior' f c hne.symm hseg
  rw [heq] at hnotint
  exact hnotint hbint

end Erdos634.ChordTraceReal
