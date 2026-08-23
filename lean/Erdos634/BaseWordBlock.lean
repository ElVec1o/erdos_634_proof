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

/-! ## The `γ`-bound is already in the corpus

`prop:a2branch`'s third filler exclusion needs `2γ > π`.  An earlier draft of this file
proved that at `e = 1` via `cos γ = -1/(2f)`.  That is a **rediscovery in a weaker form**:
`ApexRigidity.two_gamma` already gives `2γ = π + α` outright, from `3α + 2β = π` and
`γ = 2α + β` alone — exact, valid for every `e`, and with no arithmetic in `f`.  The
`e = 1` cosine computation is therefore removed; cite `ApexRigidity.two_gamma`.

What survives from that computation, and is genuinely new, is its consequence for the
brick lattice: `2γ = π + α` forces `|cos 2γ| = cos α`, which turns `lem:ladder`(i)'s
horizontal-advance identity into the law of projections.  See `LatticeDescent`.
-/

end Erdos634.BaseWordBlock
