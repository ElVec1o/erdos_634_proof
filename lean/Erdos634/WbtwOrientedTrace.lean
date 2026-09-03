import Erdos634.WbtwChain

/-!
# Orienting a trace consistently with the chord's own direction

Erdős #634. `straddle_trace_isSegment` gives a straddling tile's trace as `segment ℝ r s` for two
of its own points `r, s`, in no particular order relative to the chord's own endpoints `p, q`. The
general multi-straddler assembly needs every trace *oriented* the same way — its "near" endpoint
(from `p`) named first — so that consecutive traces and gaps chain correctly into a `g : ℕ → Plane`
for `wbtw_chain_bounded`. This is exactly what `wbtw_trichotomy_of_wbtw` supplies: reorder `(r, s)`
using it, swapping via `segment_symm` when the given order is backwards.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **A trace can be oriented from `p`.** Given a trace `segment ℝ r s` with both endpoints weakly
between the chord's own endpoints `p` and `q`, it equals `segment ℝ r' s'` for a reordering `r', s'`
of `{r, s}` with `r'` weakly between `p` and `s'` — the canonical "near, far" orientation the
multi-straddler chain assembly needs. -/
theorem oriented_trace_of_wbtw {p q r s : Plane} (hr : Wbtw ℝ p r q) (hs : Wbtw ℝ p s q) :
    ∃ r' s', segment ℝ r s = segment ℝ r' s' ∧ Wbtw ℝ p r' s' := by
  rcases wbtw_trichotomy_of_wbtw hr hs with h | h
  · exact ⟨r, s, rfl, h⟩
  · exact ⟨s, r, segment_symm ℝ r s, h⟩

end Erdos634.ChordTraceReal
