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

/-! ## The `γ`-bound, in closed form

`prop:a2branch`'s third filler exclusion says a whole `b` laid on the brick's ray "repeats
`γ` at the base junction (`straight_junction_gamma_bound`)".  That bound needs `2γ > π`,
so that two copies of `γ` overflow a *straight* junction (fan `π`).  At `e = 1` the
cosine rule gives this in closed form and with no case split at all:

  `cos γ = (a² + b² - c²) / (2ab) = (f² + (f²-1)² - f⁴) / (2f(f²-1)) = (1 - f²) / (2f(f²-1)) = -1/(2f)`

so `cos γ < 0` for every `f ≥ 2`, hence `γ > π/2` and `2γ > π`.  The exclusion therefore
holds at **any** straight junction, on the base or on an interior floor line — provided
the floor is edged there, which is exactly straddler-freeness.  Only the *first* filler
exclusion ("a filler laying `c` … exceeds the ray by `c - b = 1` past the base") is
genuinely tied to the base: at an interior floor that overshoot pokes into the row below
instead of leaving the target, and that poke is precisely the straddler of `rem:straddler`.
-/

/-- **`cos γ = -1/(2f)` at `e = 1`**, in cleared-denominator integer form:
`2f·(a² + b² - c²) + 2ab = 0` for `(a, b, c) = (f, f² - 1, f²)`. -/
theorem two_f_cos_gamma (f : ℤ) :
    2 * f * (f ^ 2 + (f ^ 2 - 1) ^ 2 - (f ^ 2) ^ 2) + 2 * (f * (f ^ 2 - 1)) = 0 := by
  ring

/-- **`γ` is obtuse for every `f ≥ 2`**: the numerator of `cos γ` is `1 - f² < 0`. -/
theorem gamma_obtuse (f : ℤ) (hf : 2 ≤ f) :
    f ^ 2 + (f ^ 2 - 1) ^ 2 - (f ^ 2) ^ 2 < 0 := by nlinarith

end Erdos634.BaseWordBlock
