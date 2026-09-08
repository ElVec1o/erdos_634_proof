import Mathlib.Tactic

/-!
# `prop:nogoauto` — the junction automaton's only forbidden pair (outcome-1/nogo debt)

Erdős #634, `paper/erdos-634-obstructions.tex:786`. A junction of an equal side carries a straight
(`π`) figure, which is one of exactly two multisets of angles: `{γ,α,β}` (one of each) or `{3α,2β}`
(three `α`'s, two `β`'s, no `γ`). A boundary edge's two flanking angles are read off this figure; the
"transition" at a junction between edge `i` (contributing its *top* angle `T`) and edge `i+1`
(contributing its *bottom* angle `B`) is *admissible* when the figure can supply both `T` and `B`
simultaneously — with multiplicity, if `T = B`.

The proposition: the only inadmissible pair is `(γ,γ)`. This file formalizes exactly that, as a pure
finite fact about the two figure multisets — no geometry, no real coordinates, no quantifier over a
dissection.

## Scope, stated exactly

**Formalized here: the finite combinatorial fact itself**, `only_forbidden_pair_is_gg`, decided over
the two explicit figure multisets.

**NOT formalized here: the specific corollary** — "over all 120 words `a⁷c⁴` ending in `c` and all
`2¹¹` orientations, exactly 10 560 configurations survive" — which is a member-specific
(`(e,f)=(3,7)`) enumeration over actual boundary words, not part of the general automaton fact. The
row's label stays PROVED for that reason: the corollary's count is a separate finite check this file
does not attempt.

Non-vacuity: both figures are exhibited as concrete `Finset`-with-multiplicity (`Multiset`) values,
and the `decide` below is checked against them directly, not against an abstract stand-in.
-/

namespace Erdos634.JunctionAutomaton

/-- The three angle kinds at a junction, as an abstract label — no real-number semantics needed for
this fact. -/
inductive Angle
  | alpha | beta | gamma
  deriving DecidableEq, Fintype, Repr

open Angle

/-- The two straight-figure multisets a junction can carry: `{γ,α,β}` (one of each) and `{3α,2β}`
(no `γ`). -/
def figGAB : Multiset Angle := {gamma, alpha, beta}
def figAAABB : Multiset Angle := {alpha, alpha, alpha, beta, beta}

/-- **A figure supplies the pair `(T,B)`** when it contains both — with multiplicity two if
`T = B`, multiplicity one each otherwise. Phrased directly as a sub-multiset test, which handles
both cases uniformly. -/
def supplies (fig : Multiset Angle) (T B : Angle) : Prop :=
  ({T, B} : Multiset Angle) ≤ fig

instance supplies.decidable (fig : Multiset Angle) (T B : Angle) :
    Decidable (supplies fig T B) :=
  inferInstanceAs (Decidable (({T, B} : Multiset Angle) ≤ fig))

/-- **A pair `(T,B)` is admissible** when *either* figure can supply it. -/
def admissible (T B : Angle) : Prop := supplies figGAB T B ∨ supplies figAAABB T B

instance admissible.decidable (T B : Angle) : Decidable (admissible T B) :=
  inferInstanceAs (Decidable (supplies figGAB T B ∨ supplies figAAABB T B))

/-- **`prop:nogoauto`, exactly.** The only inadmissible pair, over all nine pairs of angle kinds,
is `(γ,γ)`. Decided directly over the two explicit figures — a finite check, `9` cases. -/
theorem only_forbidden_pair_is_gg :
    ∀ T B : Angle, ¬ admissible T B ↔ (T = gamma ∧ B = gamma) := by
  decide

/-- Restated as the paper phrases it: every pair **other than** `(γ,γ)` is admissible. -/
theorem admissible_of_ne_gg {T B : Angle} (h : ¬ (T = gamma ∧ B = gamma)) : admissible T B := by
  by_contra hna
  exact h (only_forbidden_pair_is_gg T B |>.mp hna)

/-- `(γ,γ)` is genuinely inadmissible — not a vacuous edge case, since it is decided by the same
finite check. -/
theorem gg_inadmissible : ¬ admissible gamma gamma := by decide

/-- Non-vacuity witness: `(α,β)` — a pair not equal to `(γ,γ)` — is admissible, and via the
`{γ,α,β}` figure specifically (`(3α,2β)` also admits it, but this exhibits the first). -/
theorem witness_alpha_beta : admissible alpha beta := Or.inl (by decide)

/-- Non-vacuity witness on the other figure: `(α,α)` is admissible only via `{3α,2β}` (the
`{γ,α,β}` figure has just one `α`, so cannot supply the pair `(α,α)`). -/
theorem witness_alpha_alpha : admissible alpha alpha ∧ ¬ supplies figGAB alpha alpha := by
  constructor
  · exact Or.inr (by decide)
  · decide

end Erdos634.JunctionAutomaton

#print axioms Erdos634.JunctionAutomaton.only_forbidden_pair_is_gg
#print axioms Erdos634.JunctionAutomaton.gg_inadmissible
#print axioms Erdos634.JunctionAutomaton.witness_alpha_beta
#print axioms Erdos634.JunctionAutomaton.witness_alpha_alpha
