import Erdos634.ChordFinsetBaseCase
import Erdos634.WbtwTraceInTarget
import Erdos634.ChordInteriorStraddle

/-!
# The base case, assembled: full gap-freedom when no straddler remains

Erdős #634. Assembles `not_mem_gap_of_far_precedes` into the actual gap-freedom fact
`chord_decomposition_of_gap` needs: with the corrected exclusion invariant holding for *every*
straddling tile, no tile's interior meets the open gap `(p, Q)` at all.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The base case, assembled.** Given the target's own chord `[P, Q]`, a position `p` weakly
between them with `p ≠ Q`, a global oriented-trace assignment, and every straddling tile's far
endpoint weakly preceding `p`, no tile's interior meets the open gap `(p, Q)`. -/
theorem gap_free_of_all_excluded {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q p : Plane} (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (hPp : Wbtw ℝ P p Q) (hpQ : p ≠ Q)
    (R S : Fin N → Plane)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k))
    (hexcl : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (S k) p) :
    ∀ k : Fin N, ∀ y ∈ openSegment ℝ p Q, y ∉ interior (D.tile k).carrier := by
  intro k y hy hyint
  have hpmem : p ∈ D.target.carrier ∩ {x | f x = c} := by
    rw [hPQ]; exact mem_segment_iff_wbtw.mpr hPp
  have hQmem : Q ∈ D.target.carrier ∩ {x | f x = c} := by
    rw [hPQ]; exact right_mem_segment ℝ P Q
  have hyfc : f y = c := by
    have hyseg : y ∈ D.target.carrier ∩ {x | f x = c} :=
      Tri.convex_inter_hyperplane D.target f c |>.segment_subset hpmem hQmem
        (openSegment_subset_segment ℝ p Q hy)
    exact hyseg.2
  have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
  have hymem0 : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
  have hyPQ : Wbtw ℝ P y Q := wbtw_of_mem_tile_trace D f c hPQ k hymem0
  obtain ⟨hgo, hktrace⟩ := hglobal k hstr.1 hstr.2
  have hlocal : Wbtw ℝ (R k) y (S k) := mem_segment_iff_wbtw.mp (hktrace ▸ hymem0)
  exact not_mem_gap_of_far_precedes hPp hpQ hgo (hexcl k hstr.1 hstr.2) hyPQ hlocal hy

end Erdos634.ChordTraceReal
