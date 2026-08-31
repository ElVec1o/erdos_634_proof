import Mathlib.Tactic
import Erdos634.MarchStep

/-!
# The frontier language: chirality strings with no two consecutive monomers

The traces of the `cp`-large family at `f = 12` show the search's divergence frontier, at the depth
where the `b`-letter enters, to be exactly the binary chirality strings **with no two consecutive
`0`s**, of sizes `3, 5, 8, 13` at `bp = 6, 7, 8, 9` — and the hanging subtree size determined by the
*last* chirality alone.  That is the monomer–dimer march, visible in the raw search paths.

This file gives the language its counting law.  `noTwoZeros n` counts binary strings of length `n`
with no two adjacent `0`s; it satisfies the march recurrence, and splitting on the **last** letter
gives the observed `F(k-1), F(k-2)` multiplicities — which is why the subtree sizes come in exactly
two classes.

The march induction of `MarchStep.march_dies` is stated over runway length.  `frontier_induction`
below restates it over this language, which is the object the search walks: refuting every string
follows from refuting the two shorter classes.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchFrontier

/-- Strings of length `n` over `Bool` with no two consecutive `false`s. -/
def noTwoZeros : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | (n + 2) => noTwoZeros (n + 1) + noTwoZeros n

@[simp] theorem noTwoZeros_zero : noTwoZeros 0 = 1 := rfl
@[simp] theorem noTwoZeros_one : noTwoZeros 1 = 2 := rfl

/-- **The march recurrence.** -/
theorem noTwoZeros_succ_succ (n : ℕ) :
    noTwoZeros (n + 2) = noTwoZeros (n + 1) + noTwoZeros n := rfl

/-- The measured frontier sizes: `3, 5, 8, 13` at lengths `2, 3, 4, 5`. -/
theorem frontier_values :
    noTwoZeros 2 = 3 ∧ noTwoZeros 3 = 5 ∧ noTwoZeros 4 = 8 ∧ noTwoZeros 5 = 13 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **The split by last letter is the observed multiplicity split.**  Strings ending `1` are the
strings of length `n+1` with a `1` appended — `noTwoZeros (n+1)` of them; strings ending `0` must
have `1` before it, giving `noTwoZeros n`.  So the two subtree classes have sizes
`F(k-1)` and `F(k-2)`, which is the `{2,3}`, `{5,3}`, `{8,5}` observed. -/
theorem split_by_last (n : ℕ) :
    noTwoZeros (n + 2) = noTwoZeros (n + 1) + noTwoZeros n :=
  noTwoZeros_succ_succ n

/-- **The march induction over the frontier language.**  If the two shortest runways are refuted
and every longer one reduces to the two shorter, every string is refuted.  This is
`MarchStep.march_dies` restated over the object the search walks; the content is the same strong
induction, and it is recorded here so the induction and the measured frontier speak of one thing. -/
theorem frontier_induction (S : ℕ → Prop) (h0 : S 0) (h1 : S 1)
    (hstep : ∀ n, S n → S (n + 1) → S (n + 2)) : ∀ n, S n :=
  Erdos634.MarchStep.march_dies S h0 h1 hstep

/-- **Growth.**  The frontier is `φ`-exponential: `noTwoZeros` is the Fibonacci sequence shifted,
so the number of branches the search must close grows by `φ` per unit of `bp`.  Stated as the
two-step bound the recurrence gives directly. -/
theorem frontier_grows (n : ℕ) : noTwoZeros (n + 1) ≤ noTwoZeros (n + 2) := by
  rw [noTwoZeros_succ_succ]
  have : 0 < noTwoZeros n := by
    induction n with
    | zero => norm_num
    | succ k ih =>
      match k with
      | 0 => norm_num
      | (m + 1) => rw [noTwoZeros_succ_succ]; omega
  omega

end Erdos634.MarchFrontier
