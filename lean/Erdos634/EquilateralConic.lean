import Mathlib.Tactic

/-!
The equilateral `2π/3`- and `π/3`-tile *necessary conditions* as pure integer algebra
(Erdős #634 paper, "Equilateral admissibility" and "Conic form" propositions), proved here with
no tiling theory and no dependence on any preprint.

For a `2π/3` tile `(a,b,c)` tiling an equilateral triangle of side `S`, the invariant counts
`s = 3S/(c+a-b)`, `t = 3S/(c+b-a)` are positive integers with `s*t = 3N` and `(t-s)^2 + 16N = q^2`
for an integer `q`.  The two lemmas below reduce that square condition to a **factorization of
`16N^2`** (a difference of two squares), which is the elementary necessary side used to enumerate
the finitely many admissible instances per `N`.  The `π/3` companion is a one-line ring identity.
Every proof is `ring`/`linear_combination` over `ℤ`, so the file is axiom-clean.
-/

namespace Erdos634.EquilateralConic

/-- Step 1 (2π/3): the two invariant counts `s,t` with `s*t = 3N` and `(t-s)^2 + 16N = q^2`
force `(q*s)^2 = (s^2 + N)(s^2 + 9N)`.  Pure elimination of `t`. -/
theorem qs_sq (s t N q : ℤ) (hst : t * s = 3 * N) (hq : (t - s) ^ 2 + 16 * N = q ^ 2) :
    (q * s) ^ 2 = (s ^ 2 + N) * (s ^ 2 + 9 * N) := by
  linear_combination (-s ^ 2) * hq + (t * s + 3 * N - 2 * s ^ 2) * hst

/-- Step 2 (2π/3): completing the square turns `(q*s)^2 = (s^2+N)(s^2+9N)` into
`(s^2 + 5N)^2 - (q*s)^2 = 16N^2`. -/
theorem conic_2pi3 (s N q : ℤ) (h : (q * s) ^ 2 = (s ^ 2 + N) * (s ^ 2 + 9 * N)) :
    (s ^ 2 + 5 * N) ^ 2 - (q * s) ^ 2 = 16 * N ^ 2 := by
  linear_combination -h

/-- The `2π/3` necessary condition in its final form: an equilateral `2π/3`-tiling yields an
**explicit factorization of `16N^2`** as a product of two integers of equal parity, namely
`u = s^2 + 5N - q*s` and `v = s^2 + 5N + q*s`.  This is the divisor condition the enumeration uses. -/
theorem factor_2pi3 (s t N q : ℤ) (hst : t * s = 3 * N) (hq : (t - s) ^ 2 + 16 * N = q ^ 2) :
    (s ^ 2 + 5 * N - q * s) * (s ^ 2 + 5 * N + q * s) = 16 * N ^ 2 := by
  have h := qs_sq s t N q hst hq
  linear_combination -h

/-- The `π/3` companion (Beeson's square criterion, restated): the necessary datum
`(9N - M^2)(N - M^2)` being a perfect square is exactly a factorization of `16N^2`, since
`(5N - M^2)^2 - 16N^2 = (9N - M^2)(N - M^2)`.  A pure ring identity. -/
theorem conic_pi3 (N M : ℤ) :
    (5 * N - M ^ 2) ^ 2 - 16 * N ^ 2 = (9 * N - M ^ 2) * (N - M ^ 2) := by
  ring

/-! ## The converse direction

`qs_sq`, `conic_2pi3` and `factor_2pi3` all run one way: from the invariant counts to the
factorization.  `prop:conicform` asserts an *equivalence*, and the return trip was missing.  It is
an identity: multiplying the target by `s²` and using `ts = 3N`,
`s²((t-s)² + 16N) = s⁴ + 10Ns² + 9N² = (s²+N)(s²+9N) = (qs)²`, and `s ≠ 0` cancels. -/

/-- **The `2π/3` criterion is sufficient, not merely necessary.**  Given `s ≠ 0` with `ts = 3N` and
the factorization `(s² + 5N - qs)(s² + 5N + qs) = 16N²`, the original conic condition
`(t - s)² + 16N = q²` follows.  With `factor_2pi3` this makes the two criteria equivalent. -/
theorem factor_2pi3_conv (s t N q : ℤ) (hs : s ≠ 0) (hst : t * s = 3 * N)
    (hfac : (s ^ 2 + 5 * N - q * s) * (s ^ 2 + 5 * N + q * s) = 16 * N ^ 2) :
    (t - s) ^ 2 + 16 * N = q ^ 2 := by
  have hs2 : (s : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have key : s ^ 2 * ((t - s) ^ 2 + 16 * N) = s ^ 2 * q ^ 2 := by
    linear_combination hfac + (t * s + 3 * N - 2 * s ^ 2) * hst
  exact mul_left_cancel₀ hs2 key

/-- **The `2π/3` equivalence**, both directions together. -/
theorem factor_2pi3_iff (s t N q : ℤ) (hs : s ≠ 0) (hst : t * s = 3 * N) :
    ((t - s) ^ 2 + 16 * N = q ^ 2)
      ↔ ((s ^ 2 + 5 * N - q * s) * (s ^ 2 + 5 * N + q * s) = 16 * N ^ 2) :=
  ⟨fun h => factor_2pi3 s t N q hst h, fun h => factor_2pi3_conv s t N q hs hst h⟩

/-- **The `π/3` equivalence.**  `conic_pi3` is a ring identity, so it already runs both ways:
`(9N - M²)(N - M²)` is a square exactly when `16N²` factors with `(u+v)/2 = 5N - M²`. -/
theorem conic_pi3_iff (N M k : ℤ) :
    ((9 * N - M ^ 2) * (N - M ^ 2) = k ^ 2)
      ↔ ((5 * N - M ^ 2 - k) * (5 * N - M ^ 2 + k) = 16 * N ^ 2) := by
  constructor <;> intro h <;> linear_combination h

/-! ## `prop:conicform` as a package (citation gap closed)

`prop:conicform` (`paper/erdos-634.tex`) states the criterion in *divisor* form:

> a `2π/3` tile requires a factorization `uv = 16N²` with `u + v ≡ 0 (mod 2)` and
> `(u+v)/2 − 5N = s²` for a divisor `s` of `3N` with `s ≡ 3N/s ≡ N (mod 2)`; a `π/3` tile requires
> `uv = 16N²` with `(u+v)/2 = 5N − M²` for some `0 < M < √N`, `M ≡ N (mod 2)`.

The paper's row cited `EquilateralConic.*` generically, but no declaration stated the criterion in
that packaged shape: `factor_2pi3` gives the factorization with the *particular* `u`, `v` and says
nothing about `u+v`'s parity, the `(u+v)/2 − 5N = s²` clause, or `s ∣ 3N`.  The two theorems below
are exactly that packaging.  They are conditional on the arithmetic inputs `t*s = 3N` and
`(t−s)² + 16N = q²` (and carry the parity hypotheses through verbatim); the word *requires* — that
a real tiling supplies integers `s,t,q` with those parities — is `prop:eqspecint` and is **not**
discharged here.  So this closes the arithmetic half of the row's citation, not its blocker. -/

/-- **`prop:conicform`, `2π/3` half, packaged.**  From the invariant relations `t·s = 3N` and
`(t−s)² + 16N = q²` (with the parities `s ≡ t ≡ N (mod 2)` carried through unchanged), there is a
factorization `u·v = 16N²` with `u + v` even, `(u+v)/2 − 5N = s²`, and `s` a divisor of `3N`. -/
theorem conicform_2pi3 (s t N q : ℤ) (hst : t * s = 3 * N)
    (hq : (t - s) ^ 2 + 16 * N = q ^ 2) :
    ∃ u v : ℤ, u * v = 16 * N ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧ (u + v) / 2 - 5 * N = s ^ 2
      ∧ s ∣ 3 * N := by
  refine ⟨s ^ 2 + 5 * N - q * s, s ^ 2 + 5 * N + q * s, factor_2pi3 s t N q hst hq,
    ⟨s ^ 2 + 5 * N, by ring⟩, ?_, ⟨t, by linarith [hst]⟩⟩
  have h : (s ^ 2 + 5 * N - q * s) + (s ^ 2 + 5 * N + q * s) = 2 * (s ^ 2 + 5 * N) := by ring
  rw [h, Int.mul_ediv_cancel_left _ (by norm_num)]
  ring

/-- **`prop:conicform`, `π/3` half, packaged.**  Beeson's square criterion
`(9N − M²)(N − M²) = k²` is exactly a factorization `u·v = 16N²` whose half-sum is `5N − M²`. -/
theorem conicform_pi3 (N M k : ℤ) (h : (9 * N - M ^ 2) * (N - M ^ 2) = k ^ 2) :
    ∃ u v : ℤ, u * v = 16 * N ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧ (u + v) / 2 = 5 * N - M ^ 2 := by
  refine ⟨5 * N - M ^ 2 - k, 5 * N - M ^ 2 + k, (conic_pi3_iff N M k).mp h,
    ⟨5 * N - M ^ 2, by ring⟩, ?_⟩
  have h2 : (5 * N - M ^ 2 - k) + (5 * N - M ^ 2 + k) = 2 * (5 * N - M ^ 2) := by ring
  rw [h2, Int.mul_ediv_cancel_left _ (by norm_num)]

end Erdos634.EquilateralConic

#print axioms Erdos634.EquilateralConic.qs_sq
#print axioms Erdos634.EquilateralConic.conic_2pi3
#print axioms Erdos634.EquilateralConic.factor_2pi3
#print axioms Erdos634.EquilateralConic.conic_pi3
#print axioms Erdos634.EquilateralConic.conicform_2pi3
#print axioms Erdos634.EquilateralConic.conicform_pi3
