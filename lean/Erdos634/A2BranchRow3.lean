import Erdos634.BaseWordBlock
import Erdos634.OrderForcing

/-!
# `prop:a2branch` at row 3

`prop:a2branch` excludes the `A₂` branch of the row-`j` fork.  At row 1 it is complete.  At
row 3 its south cover's feet land on an interior floor rather than on the base, and
`thm:strippbound` records the consequence: "that step is incomplete as written, and the
structural claim of reach 4 is open pending its repair."

## The fan content is NOT the obstacle

An earlier version of this file claimed the remaining gap needed `n`-fold angular fan sums,
which Mathlib cannot express beyond two summands.  **That is wrong for these fans.**  The
project bypasses angular measure entirely: `BaseBetaE1.tile_alpha_irrational` proves `α/π`
irrational from Niven's theorem with no citation, hence `α/β` is irrational, hence every
angle has *at most one* representation `x·α + y·β`, and a vertex figure becomes an integer
system (`AngleArithmetic`):

  `α ↦ (1,0)`,  `β ↦ (0,1)`,  `γ = 2α+β ↦ (2,1)`,  `π = 3α+2β ↦ (3,2)`,
  figure of type `(X,Y)`:  `na + 2·ng = X`  and  `nb + ng = Y`.

Every lemma `prop:a2branch` cites is already formalized on that basis, in `OrderForcing`:
`straight_junction_cases`, `straight_junction_gamma_bound`, `east_cover_gap`,
`alpha_vertex_gap`, `anti_brick_side`.  So the fan half of the proposition is *done*, at
every row, and needs nothing from this file.

## What actually remains

Only the **descent**: that the south cover's feet, which at row 3 land on an interior floor,
reach the base at all.  That is a global structural fact about the strips below, not a local
angular one, and it is the single thing carried here as a hypothesis.

The combinatorial half is row-independent (`BaseWordBlock.no_f_plus_one_a`): the base is a
permutation of `(a^f, b, c)`, `f + 2` letters with exactly `f` of them `a`, so the closing
demand for `f + 1` `a`-edges is impossible *anywhere* in the word.
-/

namespace Erdos634.A2BranchRow3

open Finset

/-- **The `γ`-wedge dichotomy.**  The wedge below the floor at a junction of the south cover
is exactly `γ`, of type `(2,1)`.  Its vertex system `na + 2ng = 2`, `nb + ng = 1` has exactly
two solutions: `{α,α,β}` — the brick's mate — and `{γ}` — the direct `L = 0` filler, which is
`rem:straddler`'s straddler.  Same shape as `OrderForcing.straight_junction_cases`, one level
down. -/
theorem gamma_wedge_cases (na nb ng : ℕ) (h1 : na + 2 * ng = 2) (h2 : nb + ng = 1) :
    (na = 2 ∧ nb = 1 ∧ ng = 0) ∨ (na = 0 ∧ nb = 0 ∧ ng = 1) := by omega

/-- **No straddler ⟹ the fill is the mate.**  Excluding the `{γ}` branch leaves `{α,α,β}`,
which is the brick's mate: the fill that keeps the strip rigid. -/
theorem mate_forced (na nb ng : ℕ) (h1 : na + 2 * ng = 2) (h2 : nb + ng = 1)
    (no_straddler : ng = 0) : na = 2 ∧ nb = 1 := by omega

/-- **The `a`-filler dies, at any row.**  A filler laying its `a` along the brick's ray makes
that `a` the first element of the `b`-edge's east cover, leaving `f² − 1 − f`, which admits no
completion.  This is `OrderForcing.east_cover_gap` verbatim — no row enters it. -/
theorem a_filler_dies {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - 1 - f) : False :=
  Erdos634.OrderForcing.east_cover_gap hf h

/-- **The `b`-filler dies, at any straight junction.**  A whole `b` laid on the ray is the
brick's reflected partner and repeats `γ`, but a straight junction admits at most one `γ`.
This is `OrderForcing.straight_junction_gamma_bound` verbatim — no row enters it either. -/
theorem b_filler_dies (na nb ng : ℕ) (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) : ng ≤ 1 :=
  Erdos634.OrderForcing.straight_junction_gamma_bound na nb ng h1 h2

/-- **The `A₂` branch dies at row 3, given the descent.**

`f` whole `a`-edges in the south cover have `f + 1` endpoints; `foot` carries them injectively
to base slots, all `a`-junctions; and `thm:e1reduce` allows only `f` letters `a` in the entire
base word.  The descent hypotheses (`foot`, `foot_inj`, `foot_lt`, `foot_isA`) are the *only*
geometric input — the fan exclusions above are proved, not assumed — and nothing here depends
on where on the base the run sits, so row 1 and row 3 are the same argument. -/
theorem row_three_dies (f : ℕ) (isA : ℕ → Prop) [DecidablePred isA]
    (base_count : ((range (f + 2)).filter isA).card = f)
    (foot : ℕ → ℕ)
    (foot_inj : Set.InjOn foot (range (f + 1)))
    (foot_lt : ∀ i ∈ range (f + 1), foot i < f + 2)
    (foot_isA : ∀ i ∈ range (f + 1), isA (foot i)) :
    False := by
  refine BaseWordBlock.no_f_plus_one_a f isA base_count ((range (f + 1)).image foot)
    ?_ ?_ (le_of_eq ?_)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact mem_range.mpr (foot_lt i hi)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact foot_isA i hi
  · rw [card_image_of_injOn foot_inj, card_range]

/-- **The count that makes it work**, isolated: a south cover of `f` whole `a`-edges has
`f + 1` endpoints, one more than the base word can supply. -/
theorem endpoints_exceed_supply (f : ℕ) : f + 1 > f := Nat.lt_succ_self f

end Erdos634.A2BranchRow3
