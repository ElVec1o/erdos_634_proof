import Erdos634.WbtwChain

/-!
# Two straddlers' traces are entirely separated

Erdős #634. The combinatorial fact the sorted multi-straddler assembly needs: given two straddling
tiles' oriented traces `segment ℝ r₁ s₁` and `segment ℝ r₂ s₂` (each with near endpoint first, i.e.
`Wbtw ℝ p r₁ s₁` and `Wbtw ℝ p r₂ s₂`, and all four points weakly between the chord's own endpoints
`p` and `q`), known to meet in at most one point
(`ChordTraceReal.trace_disjoint_of_straddle`), one trace lies *entirely* before the other: either
`s₁`'s side finishes before `r₂`'s side starts, or vice versa. This is what lets the traces be
strictly ordered (not just their near endpoints) — the fact needed to place the gaps between
consecutive traces in a sorted straddler sequence.

Proved by cross-comparing near/far endpoints via `wbtw_trichotomy_of_wbtw` and
`wbtw_middle_of_wbtw_wbtw`: assuming neither separation holds produces, in each of four cases (by
comparing `r₁` vs `r₂` and `s₁` vs `s₂`), two points of both traces that the disjointness hypothesis
forces equal — contradicting either the assumed non-separation directly (via `Wbtw`'s reflexivity)
or the traces' own nondegeneracy.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **Two straddlers' traces are entirely separated.** Given two oriented traces (near endpoint
first, all four points weakly between the chord's own `p` and `q`) meeting in at most one point,
either the first trace's far endpoint weakly precedes the second's near endpoint, or vice versa. -/
theorem traces_separated_of_disjoint {p q r₁ s₁ r₂ s₂ : Plane}
    (hr1 : Wbtw ℝ p r₁ q) (hs1 : Wbtw ℝ p s₁ q) (hr2 : Wbtw ℝ p r₂ q) (hs2 : Wbtw ℝ p s₂ q)
    (hr1s1 : r₁ ≠ s₁) (hr2s2 : r₂ ≠ s₂)
    (ho1 : Wbtw ℝ p r₁ s₁) (ho2 : Wbtw ℝ p r₂ s₂)
    (hdisj : (segment ℝ r₁ s₁ ∩ segment ℝ r₂ s₂).Subsingleton) :
    Wbtw ℝ p s₁ r₂ ∨ Wbtw ℝ p s₂ r₁ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  have h1 : Wbtw ℝ p r₂ s₁ := (wbtw_trichotomy_of_wbtw hs1 hr2).resolve_left hn1
  have h2 : Wbtw ℝ p r₁ s₂ := (wbtw_trichotomy_of_wbtw hs2 hr1).resolve_left hn2
  rcases wbtw_trichotomy_of_wbtw hr1 hr2 with hcr | hcr <;>
    rcases wbtw_trichotomy_of_wbtw hs1 hs2 with hcs | hcs
  · -- r₁ ≤ r₂, s₁ ≤ s₂: r₂ and s₁ both land in both traces.
    have hr2T1 : r₂ ∈ segment ℝ r₁ s₁ := mem_segment_iff_wbtw.mpr (wbtw_middle_of_wbtw_wbtw hcr h1)
    have hr2T2 : r₂ ∈ segment ℝ r₂ s₂ := left_mem_segment ℝ r₂ s₂
    have hs1T2 : s₁ ∈ segment ℝ r₂ s₂ := mem_segment_iff_wbtw.mpr (wbtw_middle_of_wbtw_wbtw h1 hcs)
    have hs1T1 : s₁ ∈ segment ℝ r₁ s₁ := right_mem_segment ℝ r₁ s₁
    have heq : r₂ = s₁ := hdisj ⟨hr2T1, hr2T2⟩ ⟨hs1T1, hs1T2⟩
    apply hn1
    rw [heq]
    exact wbtw_self_right ℝ p s₁
  · -- r₁ ≤ r₂, s₂ ≤ s₁: r₂ and s₂ both land in both traces.
    have hr2T1 : r₂ ∈ segment ℝ r₁ s₁ := mem_segment_iff_wbtw.mpr (wbtw_middle_of_wbtw_wbtw hcr h1)
    have hr2T2 : r₂ ∈ segment ℝ r₂ s₂ := left_mem_segment ℝ r₂ s₂
    have hs2T1 : s₂ ∈ segment ℝ r₁ s₁ := mem_segment_iff_wbtw.mpr (wbtw_middle_of_wbtw_wbtw h2 hcs)
    have hs2T2 : s₂ ∈ segment ℝ r₂ s₂ := right_mem_segment ℝ r₂ s₂
    have heq : r₂ = s₂ := hdisj ⟨hr2T1, hr2T2⟩ ⟨hs2T1, hs2T2⟩
    exact hr2s2 heq
  · -- r₂ ≤ r₁, s₁ ≤ s₂: r₁ and s₁ both land in both traces.
    have hr1T2 : r₁ ∈ segment ℝ r₂ s₂ := mem_segment_iff_wbtw.mpr (wbtw_middle_of_wbtw_wbtw hcr h2)
    have hr1T1 : r₁ ∈ segment ℝ r₁ s₁ := left_mem_segment ℝ r₁ s₁
    have hs1T2 : s₁ ∈ segment ℝ r₂ s₂ := mem_segment_iff_wbtw.mpr (wbtw_middle_of_wbtw_wbtw h1 hcs)
    have hs1T1 : s₁ ∈ segment ℝ r₁ s₁ := right_mem_segment ℝ r₁ s₁
    have heq : r₁ = s₁ := hdisj ⟨hr1T1, hr1T2⟩ ⟨hs1T1, hs1T2⟩
    exact hr1s1 heq
  · -- r₂ ≤ r₁, s₂ ≤ s₁: r₁ and s₂ both land in both traces.
    have hr1T2 : r₁ ∈ segment ℝ r₂ s₂ := mem_segment_iff_wbtw.mpr (wbtw_middle_of_wbtw_wbtw hcr h2)
    have hr1T1 : r₁ ∈ segment ℝ r₁ s₁ := left_mem_segment ℝ r₁ s₁
    have hs2T1 : s₂ ∈ segment ℝ r₁ s₁ := mem_segment_iff_wbtw.mpr (wbtw_middle_of_wbtw_wbtw h2 hcs)
    have hs2T2 : s₂ ∈ segment ℝ r₂ s₂ := right_mem_segment ℝ r₂ s₂
    have heq : r₁ = s₂ := hdisj ⟨hr1T1, hr1T2⟩ ⟨hs2T1, hs2T2⟩
    apply hn2
    rw [← heq]
    exact wbtw_self_right ℝ p r₁

end Erdos634.ChordTraceReal
