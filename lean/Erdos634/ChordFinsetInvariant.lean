import Erdos634.WbtwMinimalPrecedesRest

/-!
# The exclusion invariant survives one induction step

Erdős #634. After peeling off the minimal remaining straddler `m` (trace `[r, s]`, `r = R m`,
`s = S m`) and advancing the current position from `p` to `s`, the exclusion invariant (every
already-excluded straddler's far endpoint weakly precedes the current position) still holds for
`m` itself (trivially) and for every previously-excluded straddler (by chaining the old bound
through `p` to the new position `s`).

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The exclusion invariant survives one induction step, for the newly-excluded straddler.**
Trivial: `m`'s own far endpoint `s` weakly precedes the new position `s`. -/
theorem excl_new_self {P s : Plane} : Wbtw ℝ P s s := wbtw_self_right ℝ P s

/-- **The exclusion invariant survives one induction step, for a previously-excluded straddler.**
Given the old bound (`Wbtw P (S k) p`) and the new position reached via `p ≤ r ≤ s` (`Wbtw P p r`,
`Wbtw P r s`), the old bound still weakly precedes the new position `s`. -/
theorem excl_carries_forward {P p r s Sk : Plane}
    (hold : Wbtw ℝ P Sk p) (hle : Wbtw ℝ P p r) (hrs : Wbtw ℝ P r s) :
    Wbtw ℝ P Sk s :=
  wbtw_of_wbtw_wbtw hold (wbtw_of_wbtw_wbtw hle hrs)

end Erdos634.ChordTraceReal
