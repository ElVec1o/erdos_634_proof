import Mathlib

/-!
# The base word cannot carry a long `a`-run

At `e = 1`, `m = 1`, `thm:e1reduce` makes the base walk a permutation of `(a^f, b, c)`:
**`f + 2` letters, of which exactly `f` are `a`**, with the first and last letters `a`
(companion, line 537: "`n_a = f`, so the base is a permutation of `(a^f, b, c)` with
`n = f + 2` edges").

`prop:a2branch` ends by forcing base junctions at `(kf, 0)` for `k = 2, …, f+1` and
concluding "the first `f + 1` letters are all `a`".  That conclusion is phrased
positionally, which is why the proposition reads as if it needed the run to sit at the
*start* of the base — and hence as if it only worked on row 1, where the south cover's
feet land on the base itself.

It does not.  The base word has only `f` letters `a` in total, so `f + 1` of them cannot
exist **anywhere**.  The contradiction is a counting one, and counting is blind to
position.  That is `no_f_plus_one_a`.

Even the weaker conclusion — `f` *consecutive* `a`-edges, without any claim about where
they start — already contradicts, because the `f` letters `a` are then all of them and
they form one block, while the first and last of the `f + 2` slots must both be `a`; a
block of length `f` cannot meet both ends of a word of length `f + 2`.  That is
`no_a_block`.

## Scope

This settles the *combinatorial* half of `prop:a2branch`'s punchline, and shows it is
row-independent.  It does **not** repair the proposition: the geometric half — that the
south cover's feet at row 3 descend through the straddler-free rows 2 and 1 to junctions
on the base — is still unproved.  See the research log.
-/

namespace Erdos634.BaseWordBlock

open Finset

/-- **`f + 1` letters `a` cannot occur, anywhere in the base word.**

`isA` marks the `a`-positions of the base word, whose slots are `range (f + 2)` and which
carries exactly `f` of them.  No `f + 1` distinct slots can all be `a`.  Position plays no
role, so this applies at any row, not only where the feet land on the base itself. -/
theorem no_f_plus_one_a (f : ℕ) (isA : ℕ → Prop) [DecidablePred isA]
    (hcount : ((range (f + 2)).filter isA).card = f)
    (S : Finset ℕ) (hS : S ⊆ range (f + 2)) (hSA : ∀ x ∈ S, isA x)
    (hcard : f + 1 ≤ S.card) : False := by
  have hsub : S ⊆ (range (f + 2)).filter isA := fun x hx =>
    mem_filter.mpr ⟨hS hx, hSA x hx⟩
  have h := card_le_card hsub
  rw [hcount] at h
  omega

/-- **A block of `f` consecutive `a`-edges is already impossible.**

The `f` letters `a` are then all of them, so they are exactly the block; but slots `0` and
`f + 1` must both be `a`, and a block of length `f` cannot contain both ends of a word of
length `f + 2`. -/
theorem no_a_block (f : ℕ) (hf : 3 ≤ f) (isA : ℕ → Prop) [DecidablePred isA]
    (hcount : ((range (f + 2)).filter isA).card = f)
    (h0 : isA 0) (hlast : isA (f + 1))
    (j : ℕ) (hjb : j + f ≤ f + 2) (hblock : ∀ i, i < f → isA (j + i)) : False := by
  have hBcard : ((range f).image (fun i => j + i)).card = f := by
    rw [card_image_of_injective _ (add_right_injective j), card_range]
  have hBsub : (range f).image (fun i => j + i) ⊆ (range (f + 2)).filter isA := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [mem_range] at hi
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hblock i hi⟩
  have hEq : (range f).image (fun i => j + i) = (range (f + 2)).filter isA :=
    eq_of_subset_of_card_le hBsub (by omega)
  have h0f : (0 : ℕ) ∈ (range (f + 2)).filter isA :=
    mem_filter.mpr ⟨mem_range.mpr (by omega), h0⟩
  have hlf : (f + 1) ∈ (range (f + 2)).filter isA :=
    mem_filter.mpr ⟨mem_range.mpr (by omega), hlast⟩
  rw [← hEq, mem_image] at h0f hlf
  obtain ⟨i, hi, hi0⟩ := h0f
  obtain ⟨k, hk, hkf⟩ := hlf
  rw [mem_range] at hi hk
  omega

/-! ## What this file does NOT claim

Two neighbouring results were attempted here and both turned out to be already in the
corpus.  They are recorded so the ground is not walked a third time.

* `2γ > π` at `e = 1` via `cos γ = -1/(2f)`.  `ApexRigidity.two_gamma` already gives
  `2γ = π + α` outright from `3α + 2β = π` and `γ = 2α + β` — exact, every `e`, no
  arithmetic in `f`.  Strictly stronger.  Cite that.
* `lem:ladder`(i)'s horizontal advance `f·u_x + b|cos 2γ| = c` is the law of projections
  `c = a cos β + b cos α`.  True, and it does make the advance family-independent — but
  `ApexRigidity` line 69 already records the projection formula for this tile
  ("NOT NEW either"), and `StripRigid.shift_num`/`shift_over_a` already carry
  `S = 2c cos β = e N₀ / f` and `S/a = N₀/f²` for **every** `(e, f)`, not just `e = 1`.

The rigidity of a straddler-free strip is likewise not provable here.  `StripRigid`
proves the two pointwise exclusions and supplies `layer_induction` as the schema, and
states the blocker exactly: formalizing the *link* — that the exclusions give the
induction hypotheses for the geometric predicate "tile `j` is unreflected" — "needs a
formalization of tilings that this project does not have."  Reach 4 stays open on that
blocker, not on anything provable from the arithmetic.

What is new here is only the counting observation above.
-/

/-- **`prop:a2branch` at row 3, given the descent.**  If the south cover's feet deliver
`f + 1` distinct base junctions, all of them `a`-junctions, the proposition closes by the
counting contradiction — with no reference to where on the base the run sits.  The
descent itself is *not* supplied (see the blocker above). -/
theorem row_three_closes (f : ℕ) (isA : ℕ → Prop) [DecidablePred isA]
    (hcount : ((range (f + 2)).filter isA).card = f)
    (S : Finset ℕ) (hS : S ⊆ range (f + 2)) (hSA : ∀ x ∈ S, isA x)
    (hcard : S.card = f + 1) : False :=
  no_f_plus_one_a f isA hcount S hS hSA (le_of_eq hcard.symm)

end Erdos634.BaseWordBlock
