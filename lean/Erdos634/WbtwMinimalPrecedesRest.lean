import Erdos634.WbtwTracesSeparated
import Erdos634.ChordTraceReal

/-!
# A minimal straddler's far endpoint precedes every other straddler's near endpoint

Erdős #634. The fact needed to set up the recursive sub-chord `[s, q]` correctly in the general
straddler induction: given a straddler `m` with oriented trace `[r, s]` whose near endpoint `r` is
*first* (weakly nearer `p` than every other straddler's own near endpoint), and all traces
nondegenerate and pairwise meeting in at most one point (`trace_disjoint_of_straddle`), `m`'s *far*
endpoint `s` weakly precedes every *other* straddler's near endpoint — so the remaining straddlers'
traces lie entirely within `[s, q]`, exactly the set the recursive call needs.

Proved via `traces_separated_of_disjoint`: the other separation direction (the other straddler's
trace entirely precedes `m`'s) would force, combined with `m`'s own minimality, that straddler's
whole trace to collapse onto `r` itself — contradicting its nondegeneracy.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **A minimal straddler's far endpoint precedes every other straddler's near endpoint.** Given
two oriented, nondegenerate traces `[r, s]` and `[rk, sk]` (near endpoint first, all four points
weakly between `p` and `q`) meeting in at most one point, with `r` weakly nearer `p` than `rk`,
`s` weakly precedes `rk`. -/
theorem far_precedes_of_minimal {p q r s rk sk : Plane}
    (hr : Wbtw ℝ p r q) (hs : Wbtw ℝ p s q) (hrk : Wbtw ℝ p rk q) (hsk : Wbtw ℝ p sk q)
    (hrs : r ≠ s) (hrksk : rk ≠ sk)
    (ho : Wbtw ℝ p r s) (hok : Wbtw ℝ p rk sk)
    (hdisj : (segment ℝ r s ∩ segment ℝ rk sk).Subsingleton)
    (hmin : Wbtw ℝ p r rk) :
    Wbtw ℝ p s rk := by
  rcases traces_separated_of_disjoint hr hs hrk hsk hrs hrksk ho hok hdisj with h | h
  · exact h
  · -- h : Wbtw p sk r, the "other straddler entirely precedes m" branch.
    exfalso
    have hskr : Wbtw ℝ p sk r := h
    have hrkr : Wbtw ℝ p rk r := wbtw_of_wbtw_wbtw hok hskr
    -- Combined with hmin : Wbtw p r rk, antisymmetry collapses r = rk.
    have heq : r = rk := wbtw_antisymm_of_wbtw hmin hrkr
    -- Then rk ≤ sk ≤ r = rk forces sk = rk too, contradicting hrksk.
    have hskrk : Wbtw ℝ p sk rk := heq ▸ hskr
    have hrksk' : Wbtw ℝ p rk sk := hok
    exact hrksk (wbtw_antisymm_of_wbtw hrksk' hskrk)

end Erdos634.ChordTraceReal
