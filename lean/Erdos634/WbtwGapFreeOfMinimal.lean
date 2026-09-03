import Erdos634.WbtwChain
import Erdos634.ChordInteriorStraddle

/-!
# A minimal straddler's leading gap is free of every tile's interior

Erdős #634. The base-case fact the sort-and-recurse packaging of the general straddler induction
actually needs (the missing piece `chord_decomposition_cons`'s own `hgap` hypothesis calls for): if
a straddler `m` with oriented trace `[r, s]` is *first* among all straddlers — every point of every
*other* straddler's own trace is weakly farther from `p` than `r` — then no tile's interior meets
the open gap `(p, r)`. Any tile whose interior meets the gap must itself straddle
(`interior_on_line_straddles`); if it is `m`, `openSegment_disjoint_segment_of_wbtw` rules it out
directly; if it is some other straddler, minimality plus `wbtw_antisymm_of_wbtw` collapses the
point to `r` itself, contradicting the gap's own openness.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **A minimal straddler's leading gap is free of every tile's interior.** Given a straddler `m`
with oriented trace `[r, s]` (near endpoint first), such that every point of every *other*
straddling tile's own trace is weakly farther from `p` than `r`, no tile's interior meets the open
gap `(p, r)`. -/
theorem gap_free_of_minimal {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {p q r s : Plane} {m : Fin N}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hr : r ∈ D.target.carrier ∩ {x | f x = c})
    (hpr : p ≠ r) (ho : Wbtw ℝ p r s)
    (hmtrace : (D.tile m).carrier ∩ {x | f x = c} = segment ℝ r s)
    (hmin : ∀ k : Fin N, k ≠ m →
      (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      ∀ y ∈ (D.tile k).carrier ∩ {x | f x = c}, Wbtw ℝ p r y) :
    ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r, y ∉ interior (D.tile k).carrier := by
  intro k y hy hyint
  have hyfc : f y = c := by
    have hyseg : y ∈ D.target.carrier ∩ {x | f x = c} :=
      Tri.convex_inter_hyperplane D.target f c |>.segment_subset hp hr
        (openSegment_subset_segment ℝ p r hy)
    exact hyseg.2
  have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
  have hymem : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
  by_cases hkm : k = m
  · subst hkm
    exfalso
    rw [hmtrace] at hymem
    exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw hpr ho)) hy hymem
  · exfalso
    have hry : Wbtw ℝ p r y := hmin k hkm hstr.1 hstr.2 y hymem
    have hyr : Wbtw ℝ p y r := mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ p r hy)
    have heq : r = y := wbtw_antisymm_of_wbtw hry hyr
    have hyne : y ≠ r := by
      intro h
      rw [h] at hy
      exact hpr (right_mem_openSegment_iff.mp hy)
    exact hyne heq.symm

end Erdos634.ChordTraceReal
