import Erdos634.A2BranchRow3

/-!
# The `(4,2)` "nowhere to land" argument is not about `(4,2)`

`rem:word42` (companion) excludes the base word `(bp,cp) = (4,2)`, i.e. `a c a b a^{f-2}`, given
only that the `A₂` descent's feet reach the base: `A2BranchRow3.word42_no_landing`.  `rem:ladder`
then frames the route to `N = 191` as a **ladder** — "each `f` costs its own reach step", "three
such advances, `R = 4` to `R = 7`, reach `N = 191`" — because `PincerLadder.first_failure_escapes`
says the only escape at the first failing level is `(4,2)` and its mirror, and a *new* escape set
appears one level up (`(5,2)`, `(5,3)`, … at `f = 8`).

**That framing overstates the residue.**  The exclusion never used `(4,2)`.  What it used is
`prop:cornerpara`: in every admissible base word the `b` avoids the first two and last two
positions, `3 ≤ bp ≤ f`.  In `0`-indexed slots that is `bp - 1 ∈ [2, f-1]`, and a word of length
`f + 2` has exactly three windows of `f` consecutive slots — starting at `0`, `1`, `2` — each of
which contains the whole interval `[2, f-1]`.  So **no admissible base word, at any `f`, carries a
block of `f` consecutive `a`-letters**, and `A2BranchRow3.span_all_a`'s landing run therefore has
nowhere to sit in *any* configuration, not merely in `(4,2)`.

The consequence, stated exactly:

> The combinatorial half of the escape exclusion is uniform in `(bp, cp)` and in `f`.  The reach
> ladder is not needed to get from `f = 7` to `f = 8`; discharging the single hypothesis "the
> `A₂` descent's feet reach the base" kills every admissible configuration at every `f` at once.

This is **not** a proof that `N = 191` is not a tile count.  The geometric hypothesis — the
descent lands — is untouched, and the project's own ledger records it as equivalent in difficulty
to `conj:advance` at `e = 1` (`rem:straddler`, `rem:overrunshape`, `Crux1.lean`).  What changes is
the *measurement* of the residue: `rem:mirrorwindow`'s "seven configurations at today's reach,
three at reach 4" counts configurations that all die to one and the same argument, and
`rem:ladder`'s "three advances" is one advance.

## Prior art, cited rather than rediscovered

`BaseWordBlock.no_a_block` already proves the block-free statement for an arbitrary word with `f`
`a`s among `f + 2` slots and `a` at both ends, and `A2BranchRow3.row_three_dies_of_span` already
consumes it word-generically.  So the counting fact is in the corpus.  What is *not* in the corpus
is the identification of that general lemma with `rem:word42`'s per-configuration exclusion, and
hence the retirement of the ladder framing.  The mechanism here is also strictly sharper than
`no_a_block`'s: it needs only the `b`-position (`prop:cornerpara`), not the letter count and not
the both-ends-`a` condition, so it applies to a window even when the rest of the word is unknown.
-/

namespace Erdos634.EscapeNoLanding

open Erdos634

/-- **One non-`a` slot in `[2, f-1]` blocks every window.**  A word on slots `range (f + 2)` has
exactly three blocks of `f` consecutive slots, starting at `0`, `1` or `2`; each contains every
slot of `[2, f-1]`.  So a single non-`a` letter anywhere in that interval forbids all of them. -/
theorem no_a_block_of_interior_gap (f β j : ℕ) (hf : 3 ≤ f)
    (hβ0 : 2 ≤ β) (hβ1 : β + 1 ≤ f) (isA : ℕ → Prop)
    (hnot : ¬ isA β) (hjb : j + f ≤ f + 2)
    (hblock : ∀ i, i < f → isA (j + i)) : False := by
  have hj : j ≤ 2 := by omega
  refine hnot ?_
  have h := hblock (β - j) (by omega)
  rwa [Nat.add_sub_cancel' (by omega : j ≤ β)] at h

/-- The base word of the configuration `(bp, cp)`: positions are `1`-indexed, slots `0`-indexed,
so slot `i` carries position `i + 1`.  Every letter is an `a` except the `b` at position `bp` and
the `c` at position `cp`.  At `(bp, cp) = (4, 2)` this is `A2BranchRow3.isA42`. -/
def isAcfg (bp cp i : ℕ) : Prop := i + 1 ≠ bp ∧ i + 1 ≠ cp

instance (bp cp : ℕ) : DecidablePred (isAcfg bp cp) :=
  fun i => inferInstanceAs (Decidable (i + 1 ≠ bp ∧ i + 1 ≠ cp))

/-- Sanity: at `(4,2)` this is exactly the word `rem:word42` treats. -/
theorem isAcfg_four_two (i : ℕ) : isAcfg 4 2 i ↔ A2BranchRow3.isA42 i := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩

/-- **No admissible base word carries a block of `f` consecutive `a`-letters.**  Only
`prop:cornerpara`'s `3 ≤ bp ≤ f` is used; `cp` plays no role at all. -/
theorem admissible_no_a_block (f bp cp j : ℕ) (hf : 3 ≤ f)
    (hbp0 : 3 ≤ bp) (hbp1 : bp ≤ f)
    (hjb : j + f ≤ f + 2) (hblock : ∀ i, i < f → isAcfg bp cp (j + i)) : False := by
  refine no_a_block_of_interior_gap f (bp - 1) j hf (by omega) (by omega) (isAcfg bp cp)
    ?_ hjb hblock
  intro h
  exact h.1 (by omega)

/-- **The descent has nowhere to land in *any* admissible configuration.**  Verbatim
`A2BranchRow3.word42_no_landing` with `(4,2)` replaced by an arbitrary admissible `(bp, cp)`:
a landing run of `k ≥ f` whole letters of total length `f²` must, by `span_all_a`, be `f`
consecutive `a`s, and no admissible word has such a block. -/
theorem admissible_no_landing (f B bp cp x y z j : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f)
    (hbp0 : 3 ≤ bp) (hbp1 : bp ≤ f)
    (hspan : x * f + y * B + z * (B + 1) = B + 1)
    (hk : f ≤ x + y + z)
    (hfit : j + (x + y + z) ≤ f + 2)
    (hletters : ∀ i, i < x + y + z → isAcfg bp cp (j + i)) : False := by
  obtain ⟨hy, hz, hx⟩ := A2BranchRow3.span_all_a f B x y z hf hB hspan hk
  subst hy; subst hz
  simp only [Nat.add_zero] at hletters hfit
  rw [hx] at hletters hfit
  exact admissible_no_a_block f bp cp j hf hbp0 hbp1 hfit hletters

/-! ## Rule 2: the hypotheses are not vacuous

`admissible_no_landing` concludes `False`, so its hypotheses are jointly unsatisfiable — that is
the theorem.  The control that matters is that the contradiction comes from the *word* and not
from a degenerate arithmetic side: the span hypotheses alone, without `hletters`, are satisfiable,
by the intended run of `f` whole `a`-edges. -/

/-- The span hypotheses of `admissible_no_landing` are satisfiable on their own: `x = f`,
`y = z = 0`, `j = 0`.  So the contradiction is supplied by the base word, not by the arithmetic. -/
theorem span_hypotheses_satisfiable (f B : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f) :
    f * f + 0 * B + 0 * (B + 1) = B + 1 ∧ f ≤ f + 0 + 0 ∧ 0 + (f + 0 + 0) ≤ f + 2 := by
  refine ⟨by omega, by omega, by omega⟩

/-! ## Instantiation at `f = 8`, `N = 191`

`rem:mirrorwindow` lists the surviving configurations at `f = 8` — seven up to mirror at the
proved reach `3`, three at reach `4`.  Every one of them satisfies `3 ≤ bp ≤ 8`, so every one of
them is killed by `admissible_no_landing`, and so is every other entry of the admissible box.
`(4,2)` is not distinguished. -/

/-- The seven `f = 8` representatives of `rem:mirrorwindow` are all admissible in the only sense
`admissible_no_landing` needs. -/
theorem mirrorwindow_f8_admissible :
    ∀ p ∈ ([(4,2),(5,2),(5,3),(5,6),(5,7),(5,8),(5,9)] : List (ℕ × ℕ)),
      3 ≤ p.1 ∧ p.1 ≤ 8 := by decide

/-- The reach-`4` escapes at `f = 8` likewise. -/
theorem reach_four_f8_admissible :
    ∀ p ∈ ([(4,2),(5,2),(5,3),(6,8),(6,9),(7,9)] : List (ℕ × ℕ)),
      3 ≤ p.1 ∧ p.1 ≤ 8 := by decide

/-- **`N = 191`: the whole `f = 8` escape set dies to one argument.**  For every configuration in
the admissible box at `f = 8` — the seven of `rem:mirrorwindow` included — a landing run of
`k ≥ 8` whole letters of total length `64` is impossible. -/
theorem f8_no_landing (bp cp x y z j : ℕ) (hbp0 : 3 ≤ bp) (hbp1 : bp ≤ 8)
    (hspan : x * 8 + y * 63 + z * 64 = 64)
    (hk : 8 ≤ x + y + z)
    (hfit : j + (x + y + z) ≤ 10)
    (hletters : ∀ i, i < x + y + z → isAcfg bp cp (j + i)) : False :=
  admissible_no_landing 8 63 bp cp x y z j (by norm_num) (by norm_num) hbp0 hbp1
    hspan hk hfit hletters

end Erdos634.EscapeNoLanding
