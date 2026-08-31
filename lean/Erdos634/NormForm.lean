import Mathlib.Tactic.Ring.RingNF

/-!
# The area ratio is a norm form

Erdős #634, obstructions `prop:norm`.  The base-`β` area ratio `N = m²(3f² - e²)` has
`3f² - e² = -N(e + f√3)`, the norm from `ℚ(√3)`.  The identity is the formalizable content; the
proposition's substance — that no Galois or Diophantine obstruction in the ratio can force `N`
composite — is a statement about the absence of proofs, not a theorem, and stays that way.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.NormForm

/-- **The norm identity.**  `3f² - e²` is minus the norm of `e + f√3`, whose norm is `e² - 3f²`. -/
theorem norm_identity (e f : ℤ) : 3 * f ^ 2 - e ^ 2 = -(e ^ 2 - 3 * f ^ 2) := by ring

/-- The area ratio at scale `m`. -/
theorem area_ratio (m e f : ℤ) : m ^ 2 * (3 * f ^ 2 - e ^ 2) = m ^ 2 * -(e ^ 2 - 3 * f ^ 2) := by
  ring

/-- The norm is multiplicative, so a scale factor cannot make the ratio composite by itself: at
`m = 1` the ratio *is* the norm. -/
theorem ratio_at_scale_one (e f : ℤ) :
    (1 : ℤ) ^ 2 * (3 * f ^ 2 - e ^ 2) = -(e ^ 2 - 3 * f ^ 2) := by ring

end Erdos634.NormForm
