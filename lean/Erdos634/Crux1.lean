import Erdos634.A2BranchRow3
import Erdos634.PincerLadder

/-!
# CRUX-1: the crux ledger entry (Rule I1), and what clears it

The `e = 1` hole -- every prime `3f² - 1`, and so the smallest unsettled prime `191` -- rests on one
statement.  This file is its ledger entry: the statement, the instance, the unblocking criterion, and
the autopsies of the attacks that failed, so that none is walked a third time.

## The crux, as one statement

Let `e = 1`, `m = 1`, `f ≥ 3`, and let `T` be a tiling of the base-`β` target `(f³, f³, 3f² - 1)` by
the tile `(f, f² - 1, f²)`.  Let `L` be an interior floor of `T` carrying a run of `f` consecutive
`a`-edges from above -- a column footprint, of total length `f·a = f²`.  Then:

  **(CRUX-1)  the cover of that stretch from below is `f` `a`-edges, not a single `c`-edge.**

`cover_dichotomy` proves those are the only two possibilities, so CRUX-1 is a genuine dichotomy
branch and not an open-ended demand.  In the first branch the run is reproduced one level down and
the descent continues; iterating, it reaches the base, which is the form the residue takes in
`A2BranchRow3` ("the feet reach the base") and in `E1Assembly` ("the multiples of `f` in `[0, f²)`
are tiling vertices on the base").

Constants: none.  Quantifiers: `∀ f ≥ 3, ∀ T, ∀ L`.  No dependence on the row index, and none on
anything but `(e, f, m) = (1, f, 1)`.

## What it blocks, and the smallest instance

Blocks atom A13 (the `e = 1` hole), hence A15 (the GOAL) on every prime `3f² - 1`.  The smallest
instance exhibiting the difficulty is `f = 8`, `N = 191`.

## Unblocking criterion

CRUX-1 at **PROVED** suffices, and the chain from it is already formalised:

* `row_three_dies_of_span` -- with the descent landing, the `A₂` branch at row 3 dies, and `foot_isA`
  is not needed: `span_all_a` forces the letters under the run from the length arithmetic alone.
* that is the reach-4 step, open at `prop:a2branch` row 3.
* `PincerLadder.first_failure_escapes` -- at the first failing level `f = R + 2` the only escaping
  configurations are `(4,2)` and its mirror.
* `PincerLadder.kill_mirror` -- the kills are reflection-invariant, so the mirror dies with it.
* `word42_no_landing` -- `(4,2)` has no landing site at all, its longest `a`-run being `f - 2`.

So one advance of the ladder per proof of CRUX-1, and three advances (`R = 4` to `R = 7`) reach
`f = 8`.  `crux1_clears_a_level` below is that composition, stated on the hypotheses it consumes.

## Autopsies (Rule I2 sweep; do not re-enter without a stated new reason)

* **D-1** linear/character direction invariants -- closed by `LambdaFactor` (commutative ring).
* **D-2** angle-sum and Euler counting -- both collapse to `P + T + 2I = N - 1`, giving only "the
  interior `T`-vertex count is odd", independent of the side parameter.
* **D-3** refuting the `c`-under-run configuration outright -- FALSE: the interface census finds it
  in all eight certificates.  And this is predicted, not accidental: the configuration is scale-free,
  so `ScaleRigidity.no_similarity_invariant_proof` applies to it.
* **D-4** `b`-edge pairing parity -- forces `f` even, which already holds on the hole.
* **D-5** the reach ladder as a route -- each `f` costs its own reach step (`pincer_sharp`).
* **D-6** nonabelian boundary-word invariants (Conway--Lagarias tiling groups) -- the group collapses
  to its rank-two abelianisation; checked to nilpotency class 4 and over finite nonabelian quotients.
* **D-7** the γ-count on the stretch -- `c_under_run_dies_if_ends_gamma_free` is true but has an
  **unsatisfiable** hypothesis (`ends_gamma_free_impossible`), the monotone orientation word always
  leaving a `γ` at an endpoint.  The γ-trap behind `side_no_b_m1` is a boundary phenomenon and does
  not survive the move inward.

## The missing property (I2 output)

Every failed attack is blind to at least one of two things: the scale (`m = 1` versus `m = 2`), or
the boundary (a side's ends are a base corner and an apex; an interior floor's are not).  The
property no available tool supplies is

  **P: a boundary-like constraint at an interior line** -- some reason an interior floor's endpoints
  are as constrained as a side's.

`side_no_b_m1` is scale-sensitive but boundary-bound; the γ-count is boundary-shaped but
scale-blind.  Nothing in the corpus is both, and CRUX-1 needs both.
-/

namespace Erdos634.Crux1

open Finset

/-- **What CRUX-1 buys, composed.**  Given that the descent lands -- the run's letters occupying
`x + y + z` slots from `j`, of total length `f²`, with `f + 1` distinct junctions so `k ≥ f` -- the
`(4,2)` configuration is refuted outright, with no reach step and no fan analysis. -/
theorem crux1_clears_four_two (f B x y z j : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f)
    (hspan : x * f + y * B + z * (B + 1) = B + 1)
    (hk : f ≤ x + y + z)
    (hfit : j + (x + y + z) ≤ f + 2)
    (hletters : ∀ i, i < x + y + z → A2BranchRow3.isA42 (j + i)) :
    False :=
  A2BranchRow3.word42_no_landing f B x y z j hf hB hspan hk hfit hletters

/-- **And `(4,2)` is the whole of a ladder level.**  At the first failing level `f = R + 2` the only
escapes are `(4,2)` and its reflection, so refuting the one refutes the level. -/
theorem four_two_is_the_level {R bp cp : ℕ} (hR : 4 ≤ R)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ R + 2) (hc2 : 2 ≤ cp) (hcf : cp ≤ R + 3) (hne : bp ≠ cp)
    (hesc : ¬ PincerLadder.Kill (R + 2) bp cp R) :
    (bp = 4 ∧ cp = 2) ∨ (bp = R + 1 ∧ cp = R + 3) :=
  PincerLadder.first_failure_escapes hR hb3 hbf hc2 hcf hne hesc

end Erdos634.Crux1
