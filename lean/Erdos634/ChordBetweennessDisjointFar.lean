import Erdos634.ChordBetweennessDisjoint

/-!
# A gap and a further-away segment meet only if they must

Erdős #634. Generalizes `ChordBetweennessDisjoint.openSegment_disjoint_segment_of_wbtw` from a far
segment `[r, s]` sharing its left endpoint with the gap's own right endpoint, to a far segment
`[u, v]` that merely starts *at or beyond* that point: if `r` is weakly between `p` and `u`
(`Wbtw ℝ p r u`), `u` is weakly between `r` and `v` (`Wbtw ℝ r u v`), and `r ≠ u`, the open segment
`(p, r)` and the closed segment `[u, v]` are disjoint. This is exactly the fact the *middle* gap in
a multi-straddler chord decomposition needs: the gap `(s₁, r₂)` sits strictly between two
straddlers' traces `[r₁, s₁]` and `[r₂, s₂]`, and this lemma (applied in each direction) rules out
both, where `ChordBetweennessDisjoint`'s original lemma alone only reaches an *adjacent* trace.

Same proof shape as the original: distance additivity along betweenness chains
(`dist_add_dist_eq_iff`/`Wbtw`), now needing `Wbtw.trans_expand_left` to fold the extra hop from `u`
back to `r` into a single `Wbtw p r y` fact.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **A gap and a further-away segment meet only if they must.** If `r` is weakly between `p` and
`u`, `u` is weakly between `r` and `v`, and `r ≠ u`, the open segment `(p, r)` and the closed
segment `[u, v]` are disjoint. -/
theorem openSegment_disjoint_segment_of_wbtw_far {p r u v : Plane} (hpr : p ≠ r) (hru : r ≠ u)
    (hpru : Wbtw ℝ p r u) (hruv : Wbtw ℝ r u v) :
    Disjoint (openSegment ℝ p r) (segment ℝ u v) := by
  rw [Set.disjoint_left]
  intro y hyopen hyseg
  have hyr : y ≠ r := by
    rintro rfl
    exact hpr (right_mem_openSegment_iff.mp hyopen)
  have hwbtw_y : Wbtw ℝ p y r := mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ p r hyopen)
  have hsum1 : dist p y + dist y r = dist p r := dist_add_dist_eq_iff.mpr hwbtw_y
  have hyr_pos : 0 < dist y r := dist_pos.mpr hyr
  have hy_lt : dist p y < dist p r := by linarith
  have hwbtw_uv : Wbtw ℝ u y v := mem_segment_iff_wbtw.mp hyseg
  have hwbtw_ruy : Wbtw ℝ r u y := hruv.trans_right_left hwbtw_uv
  have hwbtw_pry : Wbtw ℝ p r y := hpru.trans_expand_left hwbtw_ruy hru
  have hsum2 : dist p r + dist r y = dist p y := dist_add_dist_eq_iff.mpr hwbtw_pry
  have hy_ge : dist p r ≤ dist p y := by linarith [dist_nonneg (x := r) (y := y)]
  linarith

end Erdos634.ChordTraceReal
