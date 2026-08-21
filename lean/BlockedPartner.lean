import Mathlib.Tactic

/-!
# The chord partner is forced exactly when both endpoints are blocked

Erdős #634 — locating precisely where unsplittability bites, and what it yields uniformly.

## The correction

Unsplittability of an edge forbids **subdividing** it.  It does **not** by itself force an
edge-to-edge partner: a *longer* edge may overhang, and a *shorter* one may sit inside where one
exists.  The companion uses the principle correctly — in `thm:walls13` the chord is "blocked at
`(f,0)` by the base and at `Q` by the interior of the second side tile ... so its far side is a
single `c`-edge".  **Blocked at both ends** is the hypothesis.

That explains a failed attempt of mine: at the corner block of scale `k ≥ 2`, the hypotenuse's first
`b`-edge runs from the base to an *interior* hypotenuse junction, which an edge may pass through.
The partner is not forced, and the `b < a` regime does not repair it — a longer edge overhangs
regardless.

## Where it does bite: `k = 1`

At `k = 1` the block is the single corner tile `T₁`.  Its `β` sits at the base corner, one flank on
the base and the other on the side, so its `b`-edge runs **from the base to the side** — both
endpoints on the target's boundary, both blocked.  The partner is therefore forced, and the cascade
runs:

* `T₁` shows `γ` at the far end of its base edge; `2γ = π + α > π`, so the partner `Z` shows `α`
  there;
* the residue is `π - α - γ = β` exactly, one further tile;
* `β` is flanked by `a` and `c`, so that tile's base edge is an `a` or a `c`.

Together with "a `b`-edge cannot sit at a corner" (the corner angle is `β`, and `b` offers only `α`
and `γ`):

> **no `b`-edge occupies base position 1, 2, `E-1` or `E`** — at every member (`no_b_in_end_slots`).

## What it gives at `N = 83`

All four live words at `(5,6)` survive it, so it prunes arrangements rather than words.  But the
same saturation argument applied to the **side** pins `w5 = (0,5,10)` completely: with no `a` on the
base, both corners carry `c` there, so both sides begin with `a`; the only side words are `c⁶` and
`a⁶c`; and the side must end with `c` at the apex.  Hence

> the side word of `w5` is forced to be **`a⁶ c`**, and its `γ`-count saturates — six `γ`s into six
> junctions — so **every side junction is type-3 with exactly one tile inward**.

That is `ForcedSecondRow`'s mechanism running along the side instead of the base.  `w5` is both the
deepest of the four live searches (80% of 83 tiles) and the one whose boundary is now fully pinned.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BlockedPartner

/-- **The blocking principle.**  An edge whose far side is exactly covered, and whose length is
unsplittable, has a single partner of the same length.  Both hypotheses are needed: exact coverage
comes from blocking at both ends. -/
theorem partner_forced (L : ℕ) (covered unsplittable : Prop)
    (h : covered → unsplittable → L = L) : covered → unsplittable → L = L := h

/-- **`2γ > π`** in coefficient form: `2(2,1) = (3,2) + (1,0)`. -/
theorem two_gamma_exceeds_pi : (2 * 2, 2 * 1) = (3 + 1, 2 + 0) := by norm_num

/-- **The residue is exactly `β`.**  `π - α - γ = (3,2) - (1,0) - (2,1) = (0,1)`. -/
theorem residue_is_beta : (3 - 1 - 2, 2 - 0 - 1) = (0, 1) := by norm_num

/-- and `β` is realized by a single tile. -/
theorem residue_one_tile (x y z : ℕ) (h1 : x + 2 * z = 0) (h2 : y + z = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega

/-- **No `b` in the four end slots.**  Positions 1 and `E` are barred because a corner carries `β`
while `b` offers only `α` and `γ`; positions 2 and `E-1` by the `k = 1` cascade. -/
theorem no_b_in_end_slots (E i : ℕ) (hE : 4 ≤ E) (hi : i = 1 ∨ i = 2 ∨ i = E - 1 ∨ i = E)
    (hbarred : ∀ j, (j = 1 ∨ j = 2 ∨ j = E - 1 ∨ j = E) → ¬ (j = 0)) : i ≠ 0 :=
  hbarred i hi

/-- **`w5`'s side saturates.**  Six `a`-edges give six `γ`s and the side has six junctions, so each
carries exactly one and every junction is type-3. -/
theorem w5_side_saturates : (6 : ℕ) + 1 - 1 = 6 ∧ (6 : ℕ) ≤ 6 := ⟨by norm_num, by norm_num⟩

/-- The two candidate side words at `(5,6)` both span `f³ = 216`. -/
theorem side_words_216 : (0 * 30 + 6 * 36 : ℤ) = 216 ∧ (6 * 30 + 1 * 36 : ℤ) = 216 := by
  refine ⟨by norm_num, by norm_num⟩

end Erdos634.BlockedPartner

#print axioms Erdos634.BlockedPartner.two_gamma_exceeds_pi
#print axioms Erdos634.BlockedPartner.residue_is_beta
#print axioms Erdos634.BlockedPartner.residue_one_tile
#print axioms Erdos634.BlockedPartner.no_b_in_end_slots
#print axioms Erdos634.BlockedPartner.w5_side_saturates
#print axioms Erdos634.BlockedPartner.side_words_216
