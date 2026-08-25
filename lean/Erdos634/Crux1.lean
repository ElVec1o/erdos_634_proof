import Erdos634.A2BranchRow3
import Erdos634.PincerLadder
import Erdos634.ChordDecomp

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

## A first instance of P, and why it is not enough

`P` does have one instance already in the corpus, and it is worth recording where it lands.
`ChordDecomp.area_never_integral` says the area above an interior junction chord is never an integral
number of tiles: with `N` coprime to `f` and `1 ≤ m < f²`, `f⁴ ∤ N·m²`.  Take the chord to be a
horizontal **level line**.  The line at level `j` has height fraction `(f-j)/f`, i.e. `m = f(f-j)`,
and `1 ≤ f(f-j) < f²` exactly when `1 ≤ j ≤ f-1`.  So

  **every interior level line has non-integral area above it, and is therefore straddled**
  (`interior_level_straddled`).

Only `j = 0` (the base) and `j = f` (the apex) are clean.  That is a boundary-like constraint at an
interior line, which is what `P` asked for, and it costs nothing -- it is a corollary of a theorem
already proved for a different purpose.

It does not close CRUX-1, and the reason sharpens what is still missing.  The statement is about the
**line**: some tile straddles it somewhere.  The `c`-under-run configuration lives on a **stretch**,
a sub-segment of the line, and a straddler a long way off is entirely compatible with that stretch
being covered cleanly on both sides.  Localising the defect would need the fractional part
`u²/f²` (writing `u = f - j`) to be forced into the stretch, and nothing does that.

So `P` refines to:

  **P′: a boundary-like constraint at a POINT of an interior line**, not merely at the line.

The area defect is global by construction -- it is an area -- so it cannot supply `P′`.

## `P′` does not exist: the endpoint is unconstrained

And nothing else can supply it either, because there is nothing to supply.  Work the vertex systems
at the stretch's endpoint `P` directly, in the `AngleArithmetic` encoding
(`α ↦ (1,0)`, `β ↦ (0,1)`, `γ = 2α+β ↦ (2,1)`, `π = 3α+2β ↦ (3,2)`), where a figure of type `(X,Y)`
solves `n_α + 2n_γ = X`, `n_β + n_γ = Y`.

* **Above** `P` the tiles close at `π`, type `(3,2)`: solutions `{α,α,α,β,β}` and `{γ,α,β}`.
* **Below** `P` the blocking `c`-tile presents `α` or `β`, `c`'s flanking angles.
  * showing `α`: the rest is `π - α`, type `(2,2)`: solutions `{α,α,β,β}` and `{γ,β}`.
  * showing `β`: the rest is `π - β`, type `(3,1)`: solutions `{α,α,α,β}` and `{γ,α}`.

Every case has **two** solutions (`endpoint_systems_solvable`).  The half-figures above and below a
point of a line are independent -- each closes at `π` on its own side -- so no combination of them
contradicts, whichever angle the `c`-tile presents.  The endpoint of an interior stretch is not a
constrained point, and no local statement there can be true.

This is the fourth independent confirmation of the same theme: `prop:nogoauto` found the side's local
combinatorics almost unconstrained (`10 560` configurations surviving one forbidden adjacency),
`prop:nogocensus` found corner counting dependent, `D-7` found the `γ`-count tight, and now the
endpoint figures are solvable in every case.

## The descent is a bounded induction with a proved base case

One corollary, and it is only a corollary -- `HeightLadder.width_at_rung` already gives the target's
width at rung `j` as `Y(f-j)/f`, and `h_c = H/f²` already says the blocking `c`-tile stands `1/f` of
a level.  A column has footprint `f²`, so it fits at rung `j` only when `f² ≤ Y(f-j)/f`, i.e.

  `j ≤ f(2f²-1)/(3f²-1)`,  which is about `2f/3`  (`column_fits_bound`).

At `f = 8` that is `j ≤ 5`, against `9` rungs.  So the descent runs at most `⌊2f/3⌋` steps, and its
last step lands on the base, where the `c`-alternative is already dead -- the interior feet would be
vertices interior to a boundary edge.  CRUX-1 is therefore a **finite induction with a proved base
case**, of length about `2f/3`.

That does not close it: every step is the same open statement, so bounding the count buys nothing on
its own.  It is recorded because it says what shape a proof by induction would have, and because the
bound is small.

## What that leaves

`P` exists but is global (an area).  `P′` does not exist at all.  So a proof of CRUX-1 can be neither
local nor scale-blind, and the only remaining shape is the one the companion's chain already attempts:
**trace the forced column outward until it meets the boundary**, where the constraints do bite -- a
base corner carries one `β`-tile, the apex three `α`s.  Every other route in the sweep is now closed
by name.
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

/-- **Every interior level line is straddled.**  The level-`j` line has height fraction `(f-j)/f`,
so the area above it is the `m = f(f-j)` case of `ChordDecomp.area_never_integral`, and `m` lies in
`[1, f²)` exactly for `1 ≤ j ≤ f-1`.  Only the base and the apex are clean. -/
theorem interior_level_straddled {N f u : ℕ} (hf : 0 < f) (hcop : Nat.Coprime N f)
    (h1 : 1 ≤ u) (h2 : u < f) : ¬ (f ^ 4 ∣ N * (f * u) ^ 2) := by
  refine ChordDecomp.area_never_integral hf hcop ?_ ?_
  · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · have h : f * u < f * f := by nlinarith
    simpa [pow_two] using h

/-- **The endpoint of an interior stretch is unconstrained.**  Above closes at `π` (type `(3,2)`);
below, the `c`-tile shows `α` leaving `(2,2)`, or `β` leaving `(3,1)`.  All three systems are
solvable, so no local contradiction is available at the endpoint. -/
theorem endpoint_systems_solvable :
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 2) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 2 ∧ nb + ng = 2) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 1) :=
  ⟨⟨3, 2, 0, by omega, by omega⟩, ⟨2, 2, 0, by omega, by omega⟩, ⟨3, 1, 0, by omega, by omega⟩⟩

/-- Each of the three also has a second, `γ`-bearing solution, so the freedom is not an artefact of
picking the `γ`-free witness. -/
theorem endpoint_systems_solvable_gamma :
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 2 ∧ ng = 1) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 2 ∧ nb + ng = 2 ∧ ng = 1) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 1 ∧ ng = 1) :=
  ⟨⟨1, 1, 1, by omega, by omega, rfl⟩, ⟨0, 1, 1, by omega, by omega, rfl⟩,
   ⟨1, 0, 1, by omega, by omega, rfl⟩⟩

/-- **A column fits only in the lower part of the ladder.**  Footprint `f³ = f·f²` against the width
`Y(f-j)/f` at rung `j` (`HeightLadder.width_at_rung`) gives `f³ ≤ Y·u` with `u = f - j` and
`Y = 3f² - 1`; then `f ≤ 3u`, i.e. `j ≤ f - f/3`.  Stated additively so no truncated subtraction
appears. -/
theorem column_fits_bound (f u Y : ℕ) (hf : 3 ≤ f) (hY : Y + 1 = 3 * f ^ 2)
    (hfit : f ^ 3 ≤ Y * u) : f ≤ 3 * u := by
  by_contra h
  push_neg at h
  have h1 : 3 * u + 1 ≤ f := by omega
  nlinarith [hfit, hY, h1, hf]

end Erdos634.Crux1
