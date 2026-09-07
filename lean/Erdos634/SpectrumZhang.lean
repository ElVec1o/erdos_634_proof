import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# `thm:spectrum` — the admissible spectrum is Zhang's family (forward half)

Erdős #634, `paper/erdos-634.tex:1515`. Outcome-1 formalization debt (Rule 5).

For a primitive `120°`-triple `(a,b,c)` — `c² = a² + ab + b²` — write

    X = c + a − b,   Y = c + b − a,   b = d·e²  (`d` squarefree),   k = d·e·w,   N = d·w²·(a+2b).

The invariant conditions on the base-`α` isosceles target are (paper proof, `:1527`-`:1535`)

    X ∣ 3ak,  Y ∣ 3ak,  and with A = 3ak/X, B = 3ak/Y:  A ≡ B ≡ N  (mod 2).

`thm:spectrum` states the counts satisfying all of them are **exactly** Zhang's family
`N = m²·b·(a+2b)`, i.e. exactly those with `e ∣ w`.

## Scope, stated exactly

**Formalized here: the forward half** — every member of Zhang's family is admissible — together with
the two identities it rests on (`XY = 3ab`, and `c ≡ a + b + ab (mod 2)`).

**NOT formalized here: the converse** (`admissible → e ∣ w`), whose proof is a `p`-adic valuation
argument: `ω ≥ ε − min(x,y)`; `min(x,y) = 0` at odd `p` because a common prime of `X` and `Y`
divides `X+Y = 2c` and `Y−X = 2(b−a)`, forcing `3 ∣ c` or `p ∣ gcd(a,b)`, both impossible; and at
`p = 2`, `v₂(b) ≥ 3` with the parity clause excluding `ω = ε−1`. That is the remaining debt, and
until it is in Lean **`thm:spectrum` stays PROVED, not VERIFIED.**

Numerically re-verified before formalizing (`private/rs/spectrum2.rs`, Rust): over all **138**
primitive non-equilateral triples with `a,b < 400` — the exact range `rem:zhang` cites — the
conditions hold **iff** `e ∣ w`, with zero failures in either direction; and `(11,24,31)` with
`N = 354` reproduces the paper's stated behaviour (integrality passes, parity fails).
-/

namespace Erdos634.SpectrumZhang

/-- **The tile identity.** `X·Y = 3ab` for a `120°`-triple, since `XY = c² − (a−b)²`. -/
theorem XY_eq_three_mul (a b c : ℤ) (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c + a - b) * (c + b - a) = 3 * (a * b) := by linear_combination h

/-- **The parity of `c`.**  `c ≡ a + b + ab (mod 2)`: squaring is the identity mod 2, so
`c ≡ c² = a² + ab + b² ≡ a + ab + b`. -/
theorem c_parity (a b c : ℤ) (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ((c : ZMod 2)) = (a : ZMod 2) + (b : ZMod 2) + (a : ZMod 2) * (b : ZMod 2) := by
  have hz : ((c : ZMod 2)) ^ 2 = (a : ZMod 2) ^ 2 + (a : ZMod 2) * (b : ZMod 2) + (b : ZMod 2) ^ 2 := by
    have := congrArg (fun z : ℤ => (z : ZMod 2)) h; push_cast at this; exact this
  have sq : ∀ z : ZMod 2, z ^ 2 = z := by decide
  rw [sq, sq, sq] at hz
  linear_combination hz

/-- The parity core, decided over `ZMod 2`: if `C = A + B + A·B` then both `(C+B−A)·M` and
`(C+A−B)·M` equal `B·M²·(A+2B)`. -/
theorem zmod2_key : ∀ A B C M : ZMod 2, C = A + B + A * B →
    (C + B - A) * M = B * M ^ 2 * (A + 2 * B) ∧
    (C + A - B) * M = B * M ^ 2 * (A + 2 * B) := by decide

/-- **Forward half of `thm:spectrum`: every member of Zhang's family is admissible.**
With `w = e·m` we get `k = b·m`, hence `3ak = X·(Y·m) = Y·(X·m)`, so both integrality conditions
hold with `A = Y·m` and `B = X·m`; and both parity clauses hold. -/
theorem zhang_admissible
    (a b c d e m : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hb : b = d * e ^ 2) :
    3 * a * (d * e * (e * m)) = (c + a - b) * ((c + b - a) * m) ∧
    3 * a * (d * e * (e * m)) = (c + b - a) * ((c + a - b) * m) ∧
    ((((c + b - a) * m : ℤ)) : ZMod 2) = ((d * (e * m) ^ 2 * (a + 2 * b) : ℤ) : ZMod 2) ∧
    ((((c + a - b) * m : ℤ)) : ZMod 2) = ((d * (e * m) ^ 2 * (a + 2 * b) : ℤ) : ZMod 2) := by
  have hN : d * (e * m) ^ 2 * (a + 2 * b) = b * m ^ 2 * (a + 2 * b) := by rw [hb]; ring
  have hcp := c_parity a b c hc
  obtain ⟨p1, p2⟩ := zmod2_key (a : ZMod 2) (b : ZMod 2) (c : ZMod 2) (m : ZMod 2) hcp
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-3 * a * m) * hb - m * hc
  · linear_combination (-3 * a * m) * hb - m * hc
  · rw [hN]; push_cast; exact p1
  · rw [hN]; push_cast; exact p2

/-- Zhang's count in closed form: with `w = e·m` and `b = d·e²`, `N = m²·b·(a+2b)`. -/
theorem zhang_count (a b d e m : ℤ) (hb : b = d * e ^ 2) :
    d * (e * m) ^ 2 * (a + 2 * b) = m ^ 2 * b * (a + 2 * b) := by rw [hb]; ring

/-- Non-vacuity: the primitive triple `(3,5,7)` with `b = 5·1²`, `m = 1`. -/
theorem witness_357 : (7 : ℤ) ^ 2 = 3 ^ 2 + 3 * 5 + 5 ^ 2 ∧ (5 : ℤ) = 5 * 1 ^ 2 := by norm_num

end Erdos634.SpectrumZhang

#print axioms Erdos634.SpectrumZhang.XY_eq_three_mul
#print axioms Erdos634.SpectrumZhang.c_parity
#print axioms Erdos634.SpectrumZhang.zhang_admissible
