import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

/-!
# The filler identity, general in `f`

`lem:filler` states two identities and says they hold "in `f`", machine-checked in
`W2Core.lean`.  `W2Core` is deliberately import-free — `decide` and `omega` only — and so proves
the load-bearing identity **per member**: `filler_b_f3`, `filler_b_f4`, `filler_b_f6`,
`filler_b_f8`, `filler_b_f12`.  Its own header says "kernel-checked per member"; the paper's
"identities in `f`" was the overclaim.

Here they are proved for all `f`, which is what the paper asserts.  Keeping them out of `W2Core`
preserves that file's no-import property.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.FillerGeneral

/-- **The filler `b`-side identity, for every `f`,** in the denominator-cleared form of `W2Core`:
`(f²-1)² + 4f⁶ - (3f²-1)² = 4f²(f²-1)²`.  Stated over an arbitrary commutative ring, so the
per-member `decide` checks in `W2Core` are all instances of it. -/
theorem filler_b_general {R : Type*} [CommRing R] (f : R) :
    (f ^ 2 - 1) ^ 2 + 4 * f ^ 6 - (3 * f ^ 2 - 1) ^ 2 = 4 * f ^ 2 * (f ^ 2 - 1) ^ 2 := by
  ring

/-- **The `c`-side identity**, which the header calls trivial: with the same `4f²` cleared,
`(3f²-1)² + (4f⁶ - (3f²-1)²) = 4f⁶ = 4f²·c²` for `c = f²`. -/
theorem filler_c_general {R : Type*} [CommRing R] (f : R) :
    (3 * f ^ 2 - 1) ^ 2 + (4 * f ^ 6 - (3 * f ^ 2 - 1) ^ 2) = 4 * f ^ 2 * (f ^ 2) ^ 2 := by
  ring

/-- **The two identities are consistent**, which is their point: the *same* value of `c² sin²β`
serves both.  Eliminating it between
`((3f²-1)/(2f))² + c² sin²β = f⁴` and `((f²-1)/(2f))² + c² sin²β = (f²-1)²`
leaves an identity in `f` alone, true for every `f ≠ 0`.  So the triangle
`(J_i, ap_i, ap_{i+1})` has sides exactly `c`, `b`, `a`. -/
theorem filler_consistent (f : ℝ) (hf : f ≠ 0) :
    ((f ^ 2 - 1) / (2 * f)) ^ 2 + (f ^ 4 - ((3 * f ^ 2 - 1) / (2 * f)) ^ 2) = (f ^ 2 - 1) ^ 2 := by
  field_simp
  ring

/-! ## The same identities, general in `(e, f)`  (added 2026-09-10)

`GeneralPillars.lean` is the `e ≥ 2` counterpart of `W2Core.lean`, and carried the *same* debt:
its pillar P2 is checked per member (`filler_b_e2f3`, `_e2f5`, `_e4f5`, `_e5f6`, `_e4f7`,
`_e2f9`, `_e4f9`) by `decide`, while the companion's §"The general base-β architecture" asserts
the filler-mesh identity as an identity in `(e, f)`.  It is one, and the three theorems below
prove it, so every one of those seven `decide` checks is an instance.  The `e = 1` versions above
are in turn the `e = 1` instances of these. -/

/-- **The filler `b`-side identity, general in `(e, f)`**, denominators cleared by `4f²`:
`e²(f²−e²)² + 4f⁶ − e²(3f²−e²)² = 4f²(f²−e²)²`.
Setting `e = 1` recovers `filler_b_general`. -/
theorem filler_b_general_ef {R : Type*} [CommRing R] (e f : R) :
    e ^ 2 * (f ^ 2 - e ^ 2) ^ 2 + 4 * f ^ 6 - e ^ 2 * (3 * f ^ 2 - e ^ 2) ^ 2
      = 4 * f ^ 2 * (f ^ 2 - e ^ 2) ^ 2 := by
  ring

/-- **The `c`-side identity, general in `(e, f)`**: `c = f²` and the cleared form is trivial. -/
theorem filler_c_general_ef {R : Type*} [CommRing R] (e f : R) :
    e ^ 2 * (3 * f ^ 2 - e ^ 2) ^ 2 + (4 * f ^ 6 - e ^ 2 * (3 * f ^ 2 - e ^ 2) ^ 2)
      = 4 * f ^ 2 * (f ^ 2) ^ 2 := by
  ring

/-- **Consistency, general in `(e, f)`**: the same `c² sin²β` serves both filler triangles.
Uncleared, with the junction offsets `e(f²−e²)/(2f)` and `e(3f²−e²)/(2f)`, the elimination
leaves an identity in `(e, f)` valid for every `f ≠ 0` — the `e = 1` case is
`filler_consistent`. -/
theorem filler_consistent_ef (e f : ℝ) (hf : f ≠ 0) :
    (e * (f ^ 2 - e ^ 2) / (2 * f)) ^ 2
        + (f ^ 4 - (e * (3 * f ^ 2 - e ^ 2) / (2 * f)) ^ 2)
      = (f ^ 2 - e ^ 2) ^ 2 := by
  field_simp
  ring

end Erdos634.FillerGeneral
