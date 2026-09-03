import Mathlib.Tactic

/-!
# `prop:nogocensus`: the side census contributes one relation, and it is spent

Erdős #634, obstructions paper. On the side carrying `{γ,α,β}` junctions, write `x` for the number
of such junctions, `u` for those whose `γ` sits on a side tile with `β` opposite, and `A`, `B` for
the `α`- and `β`-slot totals at the `10 − x` junctions of type `{3α,2β}` (so `A + B = 2(10 − x)`).
The paper's two counting equations are

    (7 − u) + (x − 7) + A = 3        (α)
    u + (x − 7) + B = 10             (β)

and its claim is that **adding them gives the identity `13 = 13`**, so the two are dependent and the
census cannot pin `x`; both `x = 7` and `x = 10` occur.

That is what this file proves. The remaining clause `x ≥ 7` is *not* arithmetic — it is the junction
typing (`{3α,2β}` holds no `γ`, `{γ,α,β}` exactly one, so the seven `γ`s occupy seven distinct
junctions of the latter kind), and is recorded in `PAPER_MAP` as the geometric input, not proved here.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CensusSide

/-- **The two side-census equations sum to `13 = 13`.**  Given only the slot count
`A + B = 2(10 − x)`, the left-hand sides add to `13` whatever `x` and `u` are: the sum carries no
information, so the two equations are linearly dependent. -/
theorem side_equations_dependent (u x A B : ℤ) (hslots : A + B = 2 * (10 - x)) :
    ((7 - u) + (x - 7) + A) + (u + (x - 7) + B) = 13 := by linarith

/-- **`x = 10` occurs.**  Weights `u = 7`, `A = B = 0` satisfy both equations and the slot count. -/
theorem solution_x_ten :
    (0 : ℤ) + (0 : ℤ) = 2 * (10 - 10) ∧
    ((7 : ℤ) - 7) + (10 - 7) + 0 = 3 ∧
    (7 : ℤ) + (10 - 7) + 0 = 10 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **`x = 7` occurs.**  Weights `u = 4`, `A = 0`, `B = 6` satisfy both equations and the slot
count — as does `u = 4 + A` for any `A ≤ 3`, which is the paper's family. -/
theorem solution_x_seven :
    (0 : ℤ) + (6 : ℤ) = 2 * (10 - 7) ∧
    ((7 : ℤ) - 4) + (7 - 7) + 0 = 3 ∧
    (4 : ℤ) + (7 - 7) + 6 = 10 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The paper's family at `x = 7`.**  For every `A` with `0 ≤ A ≤ 3`, taking `u = 4 + A` and
`B = 6 − A` satisfies both equations and the slot count.  So the census leaves a one-parameter
family at `x = 7`, on top of admitting `x = 10`. -/
theorem solution_family_x_seven (A : ℤ) (hA : 0 ≤ A) (hA3 : A ≤ 3) :
    A + (6 - A) = 2 * (10 - 7) ∧
    ((7 : ℤ) - (4 + A)) + (7 - 7) + A = 3 ∧
    (4 + A) + (7 - 7) + (6 - A) = 10 := by
  refine ⟨by ring, by ring, by ring⟩

/-- **The census does not determine `x`.**  Two solutions with different `x` exist, so no function
of the two equations can pin `x` down — the proposition's conclusion. -/
theorem census_does_not_determine_x :
    ∃ x₁ x₂ : ℤ, x₁ ≠ x₂ ∧
      (∃ u A B : ℤ, A + B = 2 * (10 - x₁) ∧ (7 - u) + (x₁ - 7) + A = 3 ∧
        u + (x₁ - 7) + B = 10) ∧
      (∃ u A B : ℤ, A + B = 2 * (10 - x₂) ∧ (7 - u) + (x₂ - 7) + A = 3 ∧
        u + (x₂ - 7) + B = 10) :=
  ⟨7, 10, by norm_num, ⟨4, 0, 6, by norm_num, by norm_num, by norm_num⟩,
    ⟨7, 0, 0, by norm_num, by norm_num, by norm_num⟩⟩

end Erdos634.CensusSide
