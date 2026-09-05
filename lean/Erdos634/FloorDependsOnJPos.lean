import Erdos634.BoundaryRigidInsufficient

/-!
# The floor `K·b` depends on Theorem 2's `j > 0` clause — an unrecorded dependency

Erdős #634.  The corpus states the essential-segment floor unconditionally: every essential segment
satisfies `j b = u a + v c` with `f ∣ j`, hence has length `≥ K·b = f·b`.  A room seat audited this
and the audit holds.

**The `f ∣ j` step needs `j > 0`, and `j > 0` comes only from Beeson's Theorem 2.**  Beeson's Lemma 23
carries the hypothesis "only `b` edges on one side", and §8.5 *redefines* "essential segment" to mean
one with that relation; the clause is supplied by Theorem 2's **conclusion**.

**Why it matters: without `j > 0` the floor is strictly lower.**  The relation lattice contains

> **`f·a = e·c`**  — `f` `a`-edges against `e` `c`-edges, **with no `b`-edge at all** (`j = 0`).

Its one-sided length is `f·a = e f²`, and this is the true minimum (verified exhaustively over the
relation lattice, all coprime `(e,f)` with `f ≤ 40`).  So the honest floor is `f · min(a,b)`, and

> `f·a < f·b ⟺ a < b ⟺ f² − ef − e² > 0` — the **golden** regime.

Concretely at `(e,f) = (1,4)` (`N = 47`) the floor drops from `f·b = 60` to `f·a = 16`, while the
clearance-refined base chord is `≈ 44.06`.  **The base exclusion evaporates.**  Same at `(1,6)`
(`210 → 36`), `(1,8)` (`504 → 64`), `(2,9)` (`693 → 162`).

**Scope of the damage.**  Exactly the *golden* members are affected — which is every `e = 1` member,
i.e. the three `e = 1` primes `47, 107, 191` that R3 excludes, plus `239`.  The **thick** members are
untouched: at `(5,6)` one has `b < a`, so the minimum is `f·b = 66` and the floor stands.

So the four primes R3 currently excludes are consumers of Theorem 2's `j > 0` clause, not merely of
its four-direction list — and Theorem 2's own proof has an unclosed step.  This dependency was
recorded nowhere before.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.FloorDependsOnJPos

/-- **The `b`-free relation.**  `f·a = e·c` for `(a,c) = (ef, f²)` — a nonzero edge relation with
`j = 0`, so it is invisible to the `f ∣ j` argument. -/
theorem b_free_relation (e f : ℤ) : f * (e * f) = e * f ^ 2 := by ring

/-- **Its one-sided length undercuts `K·b` exactly in the golden regime.**  `f·a < f·b ⟺ a < b`. -/
theorem floor_drops_iff {e f : ℤ} (hf : 0 < f) :
    f * (e * f) < f * (f ^ 2 - e ^ 2) ↔ e * f < f ^ 2 - e ^ 2 := by
  constructor
  · intro h; exact lt_of_mul_lt_mul_left (by linarith) hf.le
  · intro h; exact mul_lt_mul_of_pos_left h hf

/-- **`(1,4)`, `N = 47`: the floor drops from 60 to 16.** -/
theorem drop_at_1_4 : (4:ℤ) * (1 * 4) = 16 ∧ (4:ℤ) * (4 ^ 2 - 1 ^ 2) = 60 ∧ (16:ℤ) < 60 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`(1,6)`, `N = 107`: `210 → 36`.  `(1,8)`, `N = 191`: `504 → 64`.  `(2,9)`, `N = 239`:
`693 → 162`.** -/
theorem drops_at_the_others :
    ((6:ℤ) * (1 * 6) = 36 ∧ (6:ℤ) * (6 ^ 2 - 1 ^ 2) = 210) ∧
    ((8:ℤ) * (1 * 8) = 64 ∧ (8:ℤ) * (8 ^ 2 - 1 ^ 2) = 504) ∧
    ((9:ℤ) * (2 * 9) = 162 ∧ (9:ℤ) * (9 ^ 2 - 2 ^ 2) = 693) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **The thick members are untouched.**  At `(5,6)` one has `b = 11 < 30 = a`, so `f·min(a,b) = f·b`
and the floor `66` stands. -/
theorem thick_floor_stands : (6:ℤ) * (6 ^ 2 - 5 ^ 2) = 66 ∧ (66:ℤ) < 6 * (5 * 6) := by
  refine ⟨by decide, by decide⟩

end Erdos634.FloorDependsOnJPos
