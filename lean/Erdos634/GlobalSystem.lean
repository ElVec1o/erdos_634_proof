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

/-! ## The `N = 47` solution count — kernel-verified, and it corrects the paper

The proposition's own text also states the *total number* of solutions at `N = 11, 23, 47`:
`17`, `172`, `1968`. `code/globalsys_count.py` (a from-scratch brute-force enumerator) found `2096`
at `N = 47`, not `1968` — a TENSION recorded in `PAPER_MAP.md` (2026-09-07). This settles it with a
kernel-checked count, via an independent reduction rather than re-running the same enumerator. -/

/-- **The system collapses to one equation.** A tuple `(n1,n2,v1,v2,v3,v4)` satisfies all three
corner-sum equations plus Euler at order `N` iff `v1` is pinned by the others
(`v1 = 1+n2+v3+2v4`) and `(n1,n2,v2,v3,v4)` satisfy the single equation
`n1+3n2+2v2+4v3+6v4+3 = N`. Pure arithmetic: `γ` and Euler are both consequences of `α` once `v1`
is eliminated via `α−β` — exactly the paper's own remark that "the Euler count and the angle count
give the same relation, no more," made precise as a proved equivalence rather than asserted. -/
theorem system_iff_reduced (N n1 n2 v1 v2 v3 v4 : ℕ) :
    (3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N ∧
     2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N ∧
     n1 + 3 * v1 + 2 * v2 + v3 = N ∧
     N = 2 * (v1 + v2 + v3 + v4) + (n1 + n2) + 1)
    ↔ (v1 = 1 + n2 + v3 + 2 * v4 ∧ n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 + 3 = N) := by
  constructor
  · rintro ⟨hα, hβ, _, _⟩
    refine ⟨by omega, by omega⟩
  · rintro ⟨hv1, hα⟩
    subst hv1
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- Count of nonneg-integer solutions to `n1+3n2+2v2+4v3+6v4 = target`. For each `(v4,v3,v2)` with
`6v4+4v3+2v2 ≤ target`, the remaining `rem = target−6v4−4v3−2v2` splits as `n1+3n2=rem`, which has
exactly `rem/3+1` nonneg solutions. By `system_iff_reduced`, this equals the number of full-system
solutions at `N = target+3` (each `(n1,n2,v2,v3,v4)` extends to exactly one full tuple, via the
`v1` formula, so no double-counting). -/
def solCount (target : Nat) : Nat :=
  ((List.range (target+1)).map fun v4 =>
    if 6*v4 > target then 0 else
    ((List.range (target+1)).map fun v3 =>
      if 6*v4+4*v3 > target then 0 else
      ((List.range (target+1)).map fun v2 =>
        if 6*v4+4*v3+2*v2 > target then 0 else
        (target - 6*v4 - 4*v3 - 2*v2) / 3 + 1
      ).sum
    ).sum
  ).sum

set_option maxRecDepth 2000 in
/-- **The paper's `N=11` and `N=23` counts are confirmed.** -/
theorem solCount_11 : solCount 8 = 17 := by decide

set_option maxRecDepth 2000 in
theorem solCount_23 : solCount 20 = 172 := by decide

set_option maxRecDepth 2000 in
/-- **The `N=47` count — kernel-verified, and it corrects the paper.** The proposition's own text
states `1968`; this proves `2096`. `paper/erdos-634-obstructions.tex` has been corrected to match
(2026-09-08). The proposition's substantive conclusion (a prime order is admitted, so this system
cannot exclude one) is untouched — it rests on `prime_solution_exists` alone. -/
theorem solCount_47 : solCount 44 = 2096 := by decide

end Erdos634.GlobalSystem
