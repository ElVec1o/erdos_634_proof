import Erdos634.WbtwGapFreeOfMinimal
import Erdos634.WbtwDistCoord
import Erdos634.WbtwTraceInTarget

/-!
# The induction step's gap-freedom, from a global minimality comparison

Erdős #634. Assembles `gap_free_of_minimal` (stated with a *local* origin `p`) from the *global*
minimality comparison (`dist P (R m) ≤ dist P (R k)`, from `Finset.exists_min_image` on the
remaining straddler set) the `Finset`-sort construction actually produces. The conversion chains
`wbtw_iff_dist_le_of_wbtw` (dist comparison to `Wbtw`), `wbtw_global_of_local` (placing a trace
point into the global order), `wbtw_of_wbtw_wbtw` (global chain composition), and
`wbtw_middle_of_wbtw_wbtw` (global-to-local conversion) to produce exactly the local fact
`gap_free_of_minimal` needs.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The induction step's gap-freedom.** Given the target's own chord `[P, Q]`, a position `p`
weakly between `P` and the minimal remaining straddler `m`'s near endpoint `r := R m`, a global
oriented-trace assignment, and `m` minimal (in `dist P (R ·)`) among the remaining straddlers, no
tile's interior meets the open gap `(p, r)`. -/
theorem gap_free_of_finset_step {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q p r s : Plane} (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (hPp : Wbtw ℝ P p Q) (R S : Fin N → Plane) {m : Fin N}
    (hpr : p ≠ r)
    (hgom : Wbtw ℝ P r s) (ho : Wbtw ℝ p r s)
    (hle : Wbtw ℝ P p r)
    (hmtrace : (D.tile m).carrier ∩ {x | f x = c} = segment ℝ r s)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k))
    (hmin : ∀ k : Fin N,
      (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      dist P r ≤ dist P (R k)) :
    ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r, y ∉ interior (D.tile k).carrier := by
  have hpmem : p ∈ D.target.carrier ∩ {x | f x = c} := by
    rw [hPQ]; exact mem_segment_iff_wbtw.mpr hPp
  have hsmem : s ∈ (D.tile m).carrier ∩ {x | f x = c} := by
    rw [hmtrace]; exact right_mem_segment ℝ r s
  have hsQ : Wbtw ℝ P s Q := wbtw_of_mem_tile_trace D f c hPQ m hsmem
  have hrQ : Wbtw ℝ P r Q := wbtw_of_wbtw_wbtw hgom hsQ
  have hrmem : r ∈ D.target.carrier ∩ {x | f x = c} := by
    rw [hPQ]; exact mem_segment_iff_wbtw.mpr hrQ
  refine gap_free_of_minimal D f hf c (q := Q) hpmem hrmem hpr ho hmtrace ?_
  intro k _hkm hka hkb y hymem
  obtain ⟨hgoK, hktrace⟩ := hglobal k hka hkb
  have hRkQ : Wbtw ℝ P (R k) Q := wbtw_of_mem_tile_trace D f c hPQ k
    (by rw [hktrace]; exact left_mem_segment ℝ (R k) (S k))
  have hrRk : Wbtw ℝ P r (R k) :=
    (wbtw_iff_dist_le_of_wbtw hrQ hRkQ).mpr (hmin k hka hkb)
  have hlocal : Wbtw ℝ (R k) y (S k) := mem_segment_iff_wbtw.mp (hktrace ▸ hymem)
  have hRky : Wbtw ℝ P (R k) y := (wbtw_global_of_local hgoK hlocal).1
  have hry : Wbtw ℝ P r y := wbtw_of_wbtw_wbtw hrRk hRky
  exact wbtw_middle_of_wbtw_wbtw hle hry

end Erdos634.ChordTraceReal
