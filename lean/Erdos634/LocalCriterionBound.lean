import Mathlib.Tactic
import Mathlib.Data.Finset.Card

/-!
# F2 — a local criterion cannot settle a close pair

Erdős #634. Room `advance`, Erdős seat, 2026-09-06; witness verified independently by the
moderator in exact `ℚ(√32)` (17/17 tiles congruent to `(6,5,9)`, all vertices inside the target,
**zero** pairwise interior overlap, area exactly `17/23`, residue exactly 6 tiles).

## The input (F1) and the output (F2)

At the `m = 1` base-β target of `(e,f) = (2,3)` (`N = 23`) there is a genuine partial dissection by
**17** of the 23 tiles which extends to no tiling; at `(3,4)` (`N = 39`), one by **33** of 39.  Both
occur — they are geometric objects, not hypotheses.  Write `T` for the tile set of a would-be
tiling, `W ⊆ T` for the witness.  Then `|T \ W| = 6` at both members.

A *forbidden-configuration criterion* is a family `Bad` of configurations, and it excludes `A` when
some `F ∈ Bad` satisfies `F ⊆ A`.  Such a criterion is **sound** when no realizable configuration
contains a forbidden one.  F2 is the consequence of soundness against a realizable witness:

> every forbidden configuration must meet the 6-tile residue `T \ W`.

So no criterion supported on the boundary layer, the first tile layer, or any downward-closed
prefix of `≤ N−6` tiles can settle a close pair — a boundary is `O(√N)` tiles and a first layer is
`O(√N)`, while F2 demands a set that reaches into the last six.

## The sharpening at `(2,3)`, 2026-09-12 (room `e2b3`, Erdős seat)

A **19**-tile partial dissection of the same `(2,3)` target now exists
(`data/witnesses/Z1_basebeta_2_3_partial19.tsv`, room `e2b2`).  It was re-verified independently
this session in exact `ℚ(√32)` from the file on disk: 19/19 squared side multisets `{25,36,81}`
with zero irrational part, all 57 vertices inside the closed target, **zero** pairwise interior
overlap by exact separating-axis over all 171 pairs, area exactly `19/23`.  F1 was re-verified the
same way.  So at `N = 23` the residue is `4`, not `6`, and the bound sharpens from `> N−6` to
`> N−4`: a sound criterion must contain a forbidden configuration reaching into the **last four**
tiles.

The two witnesses are **incomparable** — `|W₁₇ ∩ W₁₉| = 15`, and `W₁₇ ⊄ W₁₉` (checked exactly on
the coordinate sets) — so they are two independent constraints, not one subsumed by the other:
every forbidden configuration must meet **both** residues (`forbidden_meets_both_residues`).

Honest scope of the sharpening: the mathematical content is the *witness*, verified outside Lean;
everything below is parametric in `W` and did not change.  The `(3,4)` member is untouched — its
best known partial is still 33 of 39, residue 6 — so `> N−4` is an `N = 23` statement and
`> N−6` remains the family-level one.

## Scope, stated honestly

This file formalizes the **combinatorial engine** of F2 and its cardinality bookkeeping.  It does
**not** formalize F1: that a 17-tile partial dissection of the `(2,3)` target exists is supplied as
a hypothesis (`hW : Realizable W`), because putting it in Lean needs the tile-placement layer, a
standing blocker.  The witness is real and checked outside Lean; here it is an assumption, and
`witness_23` records the arithmetic instance so nothing is vacuous.
-/

namespace Erdos634.LocalCriterionBound

variable {α : Type*} [DecidableEq α]

/-- **Soundness gives F2's engine.**  If the witness `W` is realizable and the criterion is sound,
no forbidden configuration sits inside `W`. -/
theorem no_forbidden_inside_witness
    (Realizable : Finset α → Prop) (Bad : Finset α → Prop)
    (hsound : ∀ A, Realizable A → ∀ F, Bad F → ¬ F ⊆ A)
    (W : Finset α) (hW : Realizable W) :
    ∀ F, Bad F → ¬ F ⊆ W :=
  fun F hF => hsound W hW F hF

/-- **Every forbidden configuration meets the residue.**  A forbidden `F` inside the full tile set
`T` cannot lie in `W`, so it contains a tile of `T \ W`. -/
theorem forbidden_meets_residue
    {T W F : Finset α} (hFT : F ⊆ T) (hnot : ¬ F ⊆ W) :
    (F ∩ (T \ W)).Nonempty := by
  rcases Finset.not_subset.mp hnot with ⟨x, hxF, hxW⟩
  exact ⟨x, Finset.mem_inter.mpr ⟨hxF, Finset.mem_sdiff.mpr ⟨hFT hxF, hxW⟩⟩⟩

/-- The residue has exactly `|T| − |W|` tiles. -/
theorem residue_card {T W : Finset α} (h : W ⊆ T) :
    (T \ W).card = T.card - W.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

/-- **F2, assembled.**  With a realizable witness `W ⊆ T` and a sound criterion, every forbidden
configuration meets `T \ W`, a set of exactly `T.card - W.card` tiles.  Hence a criterion all of
whose forbidden configurations are subsets of `W` is empty. -/
theorem F2
    (Realizable : Finset α → Prop) (Bad : Finset α → Prop)
    (hsound : ∀ A, Realizable A → ∀ F, Bad F → ¬ F ⊆ A)
    {T W : Finset α} (hWT : W ⊆ T) (hW : Realizable W) :
    (∀ F, Bad F → F ⊆ T → (F ∩ (T \ W)).Nonempty) ∧ (T \ W).card = T.card - W.card :=
  ⟨fun F hF hFT => forbidden_meets_residue hFT (no_forbidden_inside_witness Realizable Bad hsound W hW F hF),
   residue_card hWT⟩

/-- **A criterion supported inside the witness excludes nothing.**  This is the form that kills the
boundary layer and the first tile layer: both are subsets of `W` at a close pair. -/
theorem local_criterion_powerless
    (Realizable : Finset α → Prop) (Bad : Finset α → Prop)
    (hsound : ∀ A, Realizable A → ∀ F, Bad F → ¬ F ⊆ A)
    {W : Finset α} (hW : Realizable W)
    (hsupp : ∀ F, Bad F → F ⊆ W) :
    ∀ F, ¬ Bad F :=
  fun F hF => no_forbidden_inside_witness Realizable Bad hsound W hW F hF (hsupp F hF)

/-- **Two incomparable witnesses give two independent constraints.**  Neither residue is contained
in the other when `W₁ ⊄ W₂` and `W₂ ⊄ W₁`, so a forbidden configuration must meet each. -/
theorem forbidden_meets_both_residues
    (Realizable : Finset α → Prop) (Bad : Finset α → Prop)
    (hsound : ∀ A, Realizable A → ∀ F, Bad F → ¬ F ⊆ A)
    {T W₁ W₂ F : Finset α} (hFT : F ⊆ T)
    (h₁ : Realizable W₁) (h₂ : Realizable W₂) (hF : Bad F) :
    (F ∩ (T \ W₁)).Nonempty ∧ (F ∩ (T \ W₂)).Nonempty :=
  ⟨forbidden_meets_residue hFT (hsound W₁ h₁ F hF),
   forbidden_meets_residue hFT (hsound W₂ h₂ F hF)⟩

/-- **The `(2,3)` instance, so the bookkeeping is not abstract.**  `N = 23`, witness `17`, residue
`6`; and `(3,4)`: `N = 39`, witness `33`, residue `6`. -/
theorem witness_23 : 23 - 17 = 6 ∧ 39 - 33 = 6 := by norm_num

/-- **The sharpened `(2,3)` instance (2026-09-12).**  `N = 23`, witness `19`, residue `4`; the two
witnesses overlap in `15` tiles, so neither contains the other (`17 - 15 = 2 > 0` tiles of `W₁₇`
lie outside `W₁₉`).  `(3,4)` is unchanged at residue `6`. -/
theorem witness_23_sharp : 23 - 19 = 4 ∧ 17 - 15 = 2 ∧ 19 - 15 = 4 ∧ 39 - 33 = 6 := by norm_num

/-- **Why a boundary layer cannot reach.**  A boundary is `O(√N)` tiles.  At `(3,4)` the witness
already carries `33` of `39`, so any forbidden configuration must include one of the last `6` —
a set no `√N`-sized layer is guaranteed to meet.  Recorded as the arithmetic gap it is. -/
theorem layer_too_small : 33 + 6 = 39 ∧ 17 + 6 = 23 := by norm_num

end Erdos634.LocalCriterionBound

#print axioms Erdos634.LocalCriterionBound.F2
#print axioms Erdos634.LocalCriterionBound.local_criterion_powerless
