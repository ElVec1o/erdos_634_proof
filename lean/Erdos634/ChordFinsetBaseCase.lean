import Erdos634.WbtwChain

/-!
# The base-case contradiction for the `Finset`-sort construction

Erdős #634. Isolated first: the pure order-theoretic contradiction the base case (no straddlers
remain) of the `Finset`-sort construction needs. If every straddler `k` not yet placed has its
*far* endpoint `S_k` weakly preceding the current position `p` (the corrected exclusion invariant —
see `PAPER_MAP.md`), then no point of `k`'s own trace can lie in the open gap `(p, Q)`.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **An excluded straddler's trace cannot reach into the current gap.** Given a fixed reference
`P`, the current position `p` weakly between `P` and `Q` (`p ≠ Q`), a straddler's oriented trace
`[R_k, S_k]` (`Wbtw P R_k S_k`) whose far endpoint weakly precedes `p` (`Wbtw P S_k p`), and any
point `y` of that trace (`Wbtw R_k y S_k`) that also satisfies the global bound `Wbtw P y Q`, `y`
cannot lie in the open gap `(p, Q)`. -/
theorem not_mem_gap_of_far_precedes {P p Q Rk Sk y : Plane}
    (hPp : Wbtw ℝ P p Q) (hpQ : p ≠ Q)
    (hgo : Wbtw ℝ P Rk Sk) (hSp : Wbtw ℝ P Sk p)
    (hyPQ : Wbtw ℝ P y Q) (hlocal : Wbtw ℝ Rk y Sk) :
    y ∉ openSegment ℝ p Q := by
  intro hy
  have hPyS : Wbtw ℝ P y Sk := hgo.trans_right hlocal
  have hpyQ : Wbtw ℝ p y Q := mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ p Q hy)
  have hPpy : Wbtw ℝ P p y := by
    have h1 : dist P p + dist p Q = dist P Q := dist_add_dist_eq_iff.mpr hPp
    have h2 : dist p y + dist y Q = dist p Q := dist_add_dist_eq_iff.mpr hpyQ
    have h3 : dist P y + dist y Q = dist P Q := dist_add_dist_eq_iff.mpr hyPQ
    exact dist_add_dist_eq_iff.mp (by linarith)
  have hSy : Wbtw ℝ P Sk y := wbtw_of_wbtw_wbtw hSp hPpy
  have heq1 : Sk = y := wbtw_antisymm_of_wbtw hSy hPyS
  have hyp : Wbtw ℝ P y p := heq1 ▸ hSp
  have heq2 : p = y := wbtw_antisymm_of_wbtw hPpy hyp
  have hyne : y ≠ p := by
    intro h
    rw [h] at hy
    exact hpQ (left_mem_openSegment_iff.mp hy)
  exact hyne heq2.symm

end Erdos634.ChordTraceReal
