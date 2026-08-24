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
angular one.

That description was, until `row_three_dies_of_span` below, an understatement of what the file
actually assumed: `row_three_dies` also carries `foot_isA`, that every landing foot sits on an
`a`-junction — which is close to the conclusion being sought.  `row_three_dies_of_span` deletes it.
The letters under the run are forced by the arithmetic of the three edge lengths alone
(`span_all_a`), so the descent now needs only to land, and the header's claim is true as written.

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

/-! ## `foot_isA` is removable: the span decides the letters by itself

`row_three_dies` carries four descent hypotheses.  `DescentUniform` discharged `foot_inj`.  Of the
rest, `foot_isA` — that every landing foot sits on an `a`-junction — is by far the strongest: it
asserts the very thing the `A₂` branch is trying to establish.  It is not needed.

The south cover is `f` whole `a`-edges, so its `f + 1` endpoints span a length of `f·a = f²`.  They
descend to `f + 1` distinct points of the base, and a tiling vertex on the base is a base-word
junction, no vertex of a tile being interior to a boundary edge.  So the base carries `f + 1`
junctions spanning `f²`, carving a run of `k ≥ f` whole letters — `k ≥ f` because `f + 1` distinct
junctions leave `f` gaps and each gap holds at least one letter.

Now the letters decide themselves.  Their lengths lie in `{f, f²-1, f²}` and total `f²`
(`span_all_a`): a single `c` would exhaust the length in **one** letter, leaving `k = 1 < f`; a `b`
would leave a remainder of `1`, below the shortest letter; so every letter is an `a` and `k = f`
exactly.  That is `f` consecutive `a`-letters, which `BaseWordBlock.no_a_block` refutes — the `f`
letters `a` are then all of them and form one block, while slots `0` and `f + 1` must both be `a`.

So the descent needs only to *land*.  What it lands on is forced by the arithmetic of the three edge
lengths, and the geometric residue of `prop:a2branch` at row 3 shrinks from "the feet reach the base
and land on `a`-junctions" to "the feet reach the base".  `row_three_dies_of_span` is the statement
with `foot_isA` deleted.

The `c`-alternative is worth naming, because it is where the strength went.  A run of length `f²`
covered by *one* `c`-edge is exactly the configuration in which the interior feet would be vertices
interior to a boundary edge — impossible — and it is also the only other way to make `f²` out of the
three lengths.  The two impossibilities are the same fact counted twice, which is why no separate
geometric input is required. -/

/-- **The span lemma.**  A base run of `k ≥ f` whole letters, of lengths `a = f`, `b = f² - 1`
(written `B`) and `c = f²`, whose total length is `f²`, consists of exactly `f` letters, all `a`. -/
theorem span_all_a (f B x y z : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f)
    (hsum : x * f + y * B + z * (B + 1) = B + 1)
    (hk : f ≤ x + y + z) : y = 0 ∧ z = 0 ∧ x = f := by
  have hBge : 8 ≤ B := by nlinarith
  have hz : z = 0 := by
    by_contra h
    have h1 : 0 < z := Nat.pos_of_ne_zero h
    have hzz : B + 1 ≤ z * (B + 1) := Nat.le_mul_of_pos_left _ h1
    have hx0 : x * f = 0 := by omega
    have hy0 : y * B = 0 := by omega
    have hzeq : z * (B + 1) = 1 * (B + 1) := by omega
    have hz1 : z = 1 := Nat.eq_of_mul_eq_mul_right (by omega) hzeq
    have hx : x = 0 := by rcases Nat.mul_eq_zero.mp hx0 with h' | h' <;> omega
    have hy : y = 0 := by rcases Nat.mul_eq_zero.mp hy0 with h' | h' <;> omega
    omega
  subst hz
  have hy : y = 0 := by
    by_contra h
    have h1 : 0 < y := Nat.pos_of_ne_zero h
    have hyy : B ≤ y * B := Nat.le_mul_of_pos_left _ h1
    have h2 : y * B ≤ B + 1 := by omega
    have hy1 : y = 1 := by
      by_contra hne
      have hy2 : 2 ≤ y := by omega
      have : 2 * B ≤ y * B := Nat.mul_le_mul_right _ hy2
      omega
    subst hy1
    have hx1 : x * f = 1 := by omega
    rcases Nat.eq_zero_or_pos x with h' | h'
    · subst h'; simp at hx1
    · have : f ≤ x * f := Nat.le_mul_of_pos_left _ h'
      omega
  subst hy
  refine ⟨rfl, rfl, ?_⟩
  have hxf : x * f = f * f := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) hxf

/-- **The `A₂` branch dies at row 3, given only that the descent lands.**  `foot_isA` is gone: the
run's letters are forced to be `a` by `span_all_a`, and `no_a_block` finishes. -/
theorem row_three_dies_of_span (f B x y z j : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f)
    (isA : ℕ → Prop) [DecidablePred isA]
    (base_count : ((range (f + 2)).filter isA).card = f)
    (h0 : isA 0) (hlast : isA (f + 1))
    (hspan : x * f + y * B + z * (B + 1) = B + 1)
    (hk : f ≤ x + y + z)
    (hfit : j + (x + y + z) ≤ f + 2)
    (hAcount : ((range (x + y + z)).filter (fun i => isA (j + i))).card = x) :
    False := by
  obtain ⟨hy, hz, hx⟩ := span_all_a f B x y z hf hB hspan hk
  subst hy; subst hz
  simp only [Nat.add_zero] at hAcount hfit hk
  rw [hx] at hAcount hfit
  have hall : ∀ i, i < f → isA (j + i) := by
    intro i hi
    by_contra hcon
    have hsub : (range f).filter (fun i => isA (j + i)) ⊂ range f := by
      refine ⟨filter_subset _ _, ?_⟩
      intro hcontra
      have : i ∈ (range f).filter (fun i => isA (j + i)) := hcontra (mem_range.mpr hi)
      exact hcon (mem_filter.mp this).2
    have := card_lt_card hsub
    rw [hAcount, card_range] at this
    omega
  exact BaseWordBlock.no_a_block f hf isA base_count h0 hlast j (by omega) hall

/-! ## The configuration `(bp, cp) = (4, 2)` has nowhere for the descent to land

`PincerLadder.first_failure_escapes` shows that at the first failing level `f = R + 2` the only
escaping configurations are `(4,2)` and its mirror, so `(4,2)` is the single obstruction standing
between the ladder and its next level.  It spells the base word

  `a c a b a^{f-2}`   (`f + 2` letters, exactly `f` of them `a`).

Its `a`-runs have lengths `1`, `1`, `f - 2`, so the longest is `f - 2 < f`: **the word carries no
block of `f` consecutive `a`-letters** (`word42_no_a_block`).

By `span_all_a` a base run of `k ≥ f` whole letters totalling `f²` must be `f` consecutive `a`s.
There is no such run here.  The only other way to make `f²` from `{f, f²-1, f²}` is a single `c`, and
a descent landing on one puts its `f - 1` interior feet interior to a boundary edge, which no tiling
vertex may be.  So in this configuration the south cover has **nowhere to land at all**.

That is the whole of `(4,2)`: it dies the moment the descent is known to reach the base, and it needs
nothing else — no reach step, no fan analysis, no case split on the row.  Combined with
`first_failure_escapes` and `kill_mirror`, discharging the single hypothesis "the feet reach the
base" advances the reach ladder by a level; three such advances, from `R = 4` to `R = 7`, reach
`N = 191`.

The three open steps of the prime hole's smallest member are therefore one step, applied three
times, and that step is now stated in its weakest form. -/

/-- The `(4,2)` base word `a c a b a^{f-2}`: slot `1` is the `c`, slot `3` is the `b`, the rest `a`. -/
def isA42 (i : ℕ) : Prop := i ≠ 1 ∧ i ≠ 3

instance : DecidablePred isA42 := fun i => inferInstanceAs (Decidable (i ≠ 1 ∧ i ≠ 3))

/-- **The `(4,2)` word carries no block of `f` consecutive `a`-letters**, for `f ≥ 3`: any block
inside a word of length `f + 2` starts at slot `0`, `1` or `2`, and each of those meets slot `1`
or slot `3`. -/
theorem word42_no_a_block (f : ℕ) (hf : 3 ≤ f) (j : ℕ) (hjb : j + f ≤ f + 2)
    (hblock : ∀ i, i < f → isA42 (j + i)) : False := by
  have hj : j ≤ 2 := by omega
  interval_cases j
  · exact (hblock 1 (by omega)).1 rfl
  · exact (hblock 0 (by omega)).1 rfl
  · exact (hblock 1 (by omega)).2 rfl

/-- **So the descent cannot land in the `(4,2)` configuration.**  A landing run of `k ≥ f` whole
letters of total length `f²` would have to be `f` consecutive `a`s, and the word has none. -/
theorem word42_no_landing (f B x y z j : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f)
    (hspan : x * f + y * B + z * (B + 1) = B + 1)
    (hk : f ≤ x + y + z)
    (hfit : j + (x + y + z) ≤ f + 2)
    (hletters : ∀ i, i < x + y + z → isA42 (j + i)) :
    False := by
  obtain ⟨hy, hz, hx⟩ := span_all_a f B x y z hf hB hspan hk
  subst hy; subst hz
  simp only [Nat.add_zero] at hletters hfit
  rw [hx] at hletters hfit
  exact word42_no_a_block f hf j hfit hletters

end Erdos634.A2BranchRow3
