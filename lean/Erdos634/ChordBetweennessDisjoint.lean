import Mathlib.Analysis.Convex.StrictConvexBetween
import Erdos634.ChordTraceReal

/-!
# Adjacent sub-segments of an ordered chain meet only at their shared endpoint

Erdős #634. The small lemma `chord_decomposition_one_straddler`'s docstring flagged as missing:
if `r` lies weakly between `p` and `s` (`Wbtw ℝ p r s`), the open segment `(p, r)` and the closed
segment `[r, s]` are disjoint — so a point interior to a tile with a trace exactly `[r, s]` can
never lie in the open gap `(p, r)`. This is what lets `chord_decomposition_one_straddler`'s two
`hgap` hypotheses be derived from "no *other* tile straddles anywhere" plus the betweenness order,
rather than assumed directly.

Proved via distance additivity along betweenness chains (`dist_add_dist_eq_iff`/`Wbtw`, the same
fact `ChordLengthAdditivity.hausdorff_segment_split` uses): a point of the open segment `(p, r)` is
strictly closer to `p` than `r` is, while a point of `[r, s]` is weakly farther from `p` than `r` is
(since `r` lies between `p` and that point too, by transitivity of betweenness).

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **Adjacent sub-segments meet only at their shared endpoint.** If `r` is weakly between `p` and
`s` and `p ≠ r`, the open segment `(p, r)` and the closed segment `[r, s]` are disjoint. -/
theorem openSegment_disjoint_segment_of_wbtw {p r s : Plane} (hpr : p ≠ r) (hprs : Wbtw ℝ p r s) :
    Disjoint (openSegment ℝ p r) (segment ℝ r s) := by
  rw [Set.disjoint_left]
  intro y hyopen hyseg
  have hyr : y ≠ r := by
    rintro rfl
    exact hpr (right_mem_openSegment_iff.mp hyopen)
  have hwbtw_y : Wbtw ℝ p y r := (mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ p r hyopen))
  have hsum1 : dist p y + dist y r = dist p r := dist_add_dist_eq_iff.mpr hwbtw_y
  have hyr_pos : 0 < dist y r := dist_pos.mpr hyr
  have hy_lt : dist p y < dist p r := by linarith
  have hwbtw_r : Wbtw ℝ r y s := mem_segment_iff_wbtw.mp hyseg
  have hwbtw_pry : Wbtw ℝ p r y := hprs.trans_right_left hwbtw_r
  have hsum2 : dist p r + dist r y = dist p y := dist_add_dist_eq_iff.mpr hwbtw_pry
  have hy_ge : dist p r ≤ dist p y := by linarith [dist_nonneg (x := r) (y := y)]
  linarith

end Erdos634.ChordTraceReal
