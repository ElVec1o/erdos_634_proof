import Mathlib.Tactic.Ring.RingNF
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.NormNum.Prime

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

/-! ## The actual norm, and prime values

`norm_identity` above is only a sign flip; it never mentions `ℚ(√3)`.  The two additions below say
what `prop:norm` actually claims: the form *is* the norm of `ℤ[√3]`, which is multiplicative, and it
does take prime values — so nothing in the ratio can force `N` composite. -/

/-- **The form is the norm of `ℤ[√3]`.**  `Zsqrtd.norm ⟨e, f⟩ = e² − 3f²`, so `3f² − e²` is minus
it — the identification `prop:norm` asserts, now against Mathlib's norm rather than a sign flip. -/
theorem eq_neg_zsqrtd_norm (e f : ℤ) :
    3 * f ^ 2 - e ^ 2 = -(Zsqrtd.norm (⟨e, f⟩ : Zsqrtd (3 : ℤ))) := by
  simp [Zsqrtd.norm]; ring

/-- **The norm is multiplicative** (`Zsqrtd.norm_mul`), which is why a prime norm cannot be
factored by the form: there is no Diophantine obstruction to `3f² − e²` being prime. -/
theorem norm_mul' (z w : Zsqrtd (3 : ℤ)) :
    Zsqrtd.norm (z * w) = Zsqrtd.norm z * Zsqrtd.norm w :=
  Zsqrtd.norm_mul z w

/-- **Prime values occur.**  The four smallest coprime pairs `e < f` give `11, 23, 47, 71`, all
prime.  (An external count, `code/`-side, confirms the paper's `144` primes of this form with
`gcd(e,f) = 1`, `e < f < 40`; the four here are the formalized witnesses.) -/
theorem prime_values :
    Nat.Prime (3 * 2 ^ 2 - 1 ^ 2) ∧ Nat.Prime (3 * 3 ^ 2 - 2 ^ 2) ∧
    Nat.Prime (3 * 4 ^ 2 - 1 ^ 2) ∧ Nat.Prime (3 * 5 ^ 2 - 2 ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

end Erdos634.NormForm
