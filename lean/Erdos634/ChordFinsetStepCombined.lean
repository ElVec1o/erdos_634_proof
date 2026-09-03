import Erdos634.ChordFinsetBaseCase
import Erdos634.WbtwDistCoord
import Erdos634.WbtwTraceInTarget
import Erdos634.ChordInteriorStraddle

/-!
# The induction step's gap-freedom, combining minimality and exclusion

Erdős #634. `gap_free_of_minimal` (and the `gap_free_of_finset_step` built on it) implicitly assumed
*no* straddler is yet excluded — its own `hmin` hypothesis is only satisfiable when every other
straddling tile is still a genuine competitor for "closest to `p`". Once the `Finset`-sort
recursion has advanced past its first step, some straddlers are already excluded (their whole trace
behind `p`), and those need the entirely different argument `not_mem_gap_of_far_precedes` supplies,
not a minimality comparison. This file builds the correctly combined gap-freedom fact directly,
casing on whether a straddler is the chosen minimal one, another still-remaining one, or already
excluded.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The induction step's gap-freedom, correctly combining minimality and exclusion.** Given the
target's own chord `[P, Q]`, a position `p` weakly between `P` and the minimal remaining
straddler `m`'s near endpoint `r := R m`, a global oriented-trace assignment, `m` minimal (in
`dist P (R ·)`) among the *remaining* straddlers `T`, and every already-excluded straddler's far
endpoint weakly preceding `p`, no tile's interior meets the open gap `(p, r)`. -/
theorem gap_free_of_finset_step' {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q p r s : Plane} (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (R S : Fin N → Plane) {m : Fin N} (T : Finset (Fin N))
    (hpr : p ≠ r)
    (hgom : Wbtw ℝ P r s) (ho : Wbtw ℝ p r s) (hle_m : Wbtw ℝ P p r)
    (hmtrace : (D.tile m).carrier ∩ {x | f x = c} = segment ℝ r s)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k))
    (hmin : ∀ k ∈ T,
      (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      dist P r ≤ dist P (R k))
    (hexcl : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      k ∉ T → Wbtw ℝ P (S k) p) :
    ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r, y ∉ interior (D.tile k).carrier := by
  -- Common setup: p, r both lie on the target's own chord.
  have hsmem : s ∈ (D.tile m).carrier ∩ {x | f x = c} := by
    rw [hmtrace]; exact right_mem_segment ℝ r s
  have hsQ : Wbtw ℝ P s Q := wbtw_of_mem_tile_trace D f c hPQ m hsmem
  have hrQ : Wbtw ℝ P r Q := wbtw_of_wbtw_wbtw hgom hsQ
  have hpQ : Wbtw ℝ P p Q := wbtw_of_wbtw_wbtw hle_m hrQ
  have hpmem : p ∈ D.target.carrier ∩ {x | f x = c} := by
    rw [hPQ]; exact mem_segment_iff_wbtw.mpr hpQ
  have hrmem : r ∈ D.target.carrier ∩ {x | f x = c} := by
    rw [hPQ]; exact mem_segment_iff_wbtw.mpr hrQ
  intro k y hy hyint
  have hyfc : f y = c := by
    have hyseg : y ∈ D.target.carrier ∩ {x | f x = c} :=
      Tri.convex_inter_hyperplane D.target f c |>.segment_subset hpmem hrmem
        (openSegment_subset_segment ℝ p r hy)
    exact hyseg.2
  have hstr := interior_on_line_straddles (D.tile k) f hf c hyint hyfc
  have hymem0 : y ∈ (D.tile k).carrier ∩ {x | f x = c} := ⟨interior_subset hyint, hyfc⟩
  by_cases hkm : k = m
  · subst hkm
    exfalso
    rw [hmtrace] at hymem0
    exact (Set.disjoint_left.mp (openSegment_disjoint_segment_of_wbtw hpr ho)) hy hymem0
  · obtain ⟨hgoK, hktrace⟩ := hglobal k hstr.1 hstr.2
    have hlocal : Wbtw ℝ (R k) y (S k) := mem_segment_iff_wbtw.mp (hktrace ▸ hymem0)
    by_cases hkT : k ∈ T
    · -- Still remaining: use the minimality argument.
      exfalso
      have hRkQ : Wbtw ℝ P (R k) Q := wbtw_of_mem_tile_trace D f c hPQ k
        (by rw [hktrace]; exact left_mem_segment ℝ (R k) (S k))
      have hrRk : Wbtw ℝ P r (R k) :=
        (wbtw_iff_dist_le_of_wbtw hrQ hRkQ).mpr (hmin k hkT hstr.1 hstr.2)
      have hRky : Wbtw ℝ P (R k) y := (wbtw_global_of_local hgoK hlocal).1
      have hry : Wbtw ℝ P r y := wbtw_of_wbtw_wbtw hrRk hRky
      have hlocal_p : Wbtw ℝ p r y := wbtw_middle_of_wbtw_wbtw hle_m hry
      have hyr : Wbtw ℝ p y r := mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ p r hy)
      have heq : r = y := wbtw_antisymm_of_wbtw hlocal_p hyr
      have hyne : y ≠ r := by
        intro h; rw [h] at hy; exact hpr (right_mem_openSegment_iff.mp hy)
      exact hyne heq.symm
    · -- Already excluded: use `not_mem_gap_of_far_precedes` directly, with `r` as the bound.
      have hyRQ : Wbtw ℝ P y r := by
        have hySk : Wbtw ℝ P y (S k) := (wbtw_global_of_local hgoK hlocal).2
        have hSkp : Wbtw ℝ P (S k) p := hexcl k hstr.1 hstr.2 hkT
        exact wbtw_of_wbtw_wbtw hySk (wbtw_of_wbtw_wbtw hSkp hle_m)
      exact absurd hy (not_mem_gap_of_far_precedes hle_m hpr hgoK
        (hexcl k hstr.1 hstr.2 hkT) hyRQ hlocal)

end Erdos634.ChordTraceReal
