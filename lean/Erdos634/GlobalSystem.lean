import Mathlib.Tactic

/-!
# `prop:globalsys`: the global angle–Euler system admits prime solutions

Erdős #634, obstructions paper. With `n₁, n₂` the counts of the boundary non-corner figures
`(1,1,1)`, `(3,2,0)` and `v₁…v₄` those of the interior figures `(0,1,3)`, `(2,2,2)`, `(4,3,1)`,
`(6,4,0)`, and the corner fills fixed (one apex `(3,0,0)`, two base corners `(0,1,0)`), each of the
three corner types sums to `N`:

    α :  3 + n₁ + 3n₂ + 2v₂ + 4v₃ + 6v₄ = N
    β :  2 + n₁ + 2n₂ + v₁ + 2v₂ + 3v₃ + 4v₄ = N
    γ :       n₁ +      3v₁ + 2v₂ +  v₃      = N

with the Euler relation `N = 2I + B + 1`, `I = v₁+v₂+v₃+v₄`, `B = n₁+n₂`.

The proposition's point is that this system **admits solutions at prime `N`**, so it cannot exclude
a prime order. That is what is formalized here: an explicit solution at `N = 11`, and the system's
only congruence.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.GlobalSystem

/-- **The system's only congruence.**  From `N = 2I + B + 1`, `N` is odd exactly when `B` is even.
The proposition notes this holds for every prime, so the congruence excludes nothing. -/
theorem euler_parity (N I B : ℕ) (h : N = 2 * I + B + 1) : Odd N ↔ Even B := by
  constructor
  · intro hN; rcases Nat.even_or_odd B with hb | hb
    · exact hb
    · exfalso; obtain ⟨k, hk⟩ := hN; obtain ⟨m, hm⟩ := hb; omega
  · intro hB; obtain ⟨m, hm⟩ := hB; exact ⟨I + m, by omega⟩

/-- **A solution at `N = 11`.**  `n₁ = n₂ = 0`, `v₁ = 1`, `v₂ = 4`, `v₃ = v₄ = 0` satisfies all
three corner counts and the Euler relation. Since `11` is prime, the global system does not exclude
prime orders — the proposition's conclusion. -/
theorem solution_eleven :
    3 + 0 + 3 * 0 + 2 * 4 + 4 * 0 + 6 * 0 = 11 ∧
    2 + 0 + 2 * 0 + 1 + 2 * 4 + 3 * 0 + 4 * 0 = 11 ∧
    0 + 3 * 1 + 2 * 4 + 0 = 11 ∧
    11 = 2 * (1 + 4 + 0 + 0) + (0 + 0) + 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The system admits a solution at a prime order.**  Packaged as the existential the proposition
asserts: `11` is prime and the system is satisfiable there. -/
theorem prime_solution_exists :
    ∃ N n₁ n₂ v₁ v₂ v₃ v₄ : ℕ, Nat.Prime N ∧
      3 + n₁ + 3 * n₂ + 2 * v₂ + 4 * v₃ + 6 * v₄ = N ∧
      2 + n₁ + 2 * n₂ + v₁ + 2 * v₂ + 3 * v₃ + 4 * v₄ = N ∧
      n₁ + 3 * v₁ + 2 * v₂ + v₃ = N ∧
      N = 2 * (v₁ + v₂ + v₃ + v₄) + (n₁ + n₂) + 1 :=
  ⟨11, 0, 0, 1, 4, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Erdos634.GlobalSystem
