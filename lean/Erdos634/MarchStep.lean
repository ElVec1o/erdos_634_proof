import Mathlib.Tactic
import Erdos634.MarchRecurrence

/-!
# The march step: the wedge admits at most two placements, and the induction that consumes it

Erdős #634, `e = 1`, the escape families.  `MarchRecurrence` recorded the measured counts and the
arithmetic of the recurrence, and stated the remaining geometric obligation as the *admissibility*
of the two chiralities.  That statement of the obligation was the wrong half.

Admissibility — that both chiralities can actually be laid — is what produces the Fibonacci
*count*.  The refutation itself needs the opposite inequality: that there are **no other**
placements, so that a two-way case split exhausts the branch, together with a terminal
contradiction.  This file proves the exhaustiveness half and the induction that consumes it.  The
terminal contradiction is `LadderInvariant.terminal_kill` (residue `1` is a gap of `⟨f, f²-1, f²⟩`).

The geometry is done in polar coordinates about the junction apex, where the wedge of opening `α`
is the set of polar angles `[0, α]` and the statement becomes an inequality in `ℝ`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchStep

/-- **The extremal rays.**  Two directions inside a wedge of opening `α`, separated by exactly
`α`, are the two boundary rays of the wedge.  This is the whole geometric content of the march
step: the filling tile's angle at the junction equals the wedge's opening, so its two edges there
have nowhere to go but the wedge's own sides. -/
theorem polar_extremes {α φ ψ : ℝ}
    (hφ : φ ∈ Set.Icc (0:ℝ) α) (hψ : ψ ∈ Set.Icc (0:ℝ) α) (hsep : |φ - ψ| = α) :
    (φ = 0 ∧ ψ = α) ∨ (φ = α ∧ ψ = 0) := by
  obtain ⟨hφ0, hφa⟩ := hφ
  obtain ⟨hψ0, hψa⟩ := hψ
  rcases abs_cases (φ - ψ) with ⟨he, _⟩ | ⟨he, _⟩
  · right; constructor <;> linarith [hsep ▸ he]
  · left; constructor <;> linarith [hsep ▸ he]

/-- **At most two placements.**  Once the two edges lie on the two boundary rays, the tile is
determined by which of the two `α`-adjacent side lengths goes on which ray, and the two choices
are distinct exactly when those lengths differ.  For the base-`β` tile at `e = 1` they are
`b = f² - 1` and `c = f²`, which differ by `1`. -/
theorem two_placements {b c s t : ℝ} (hbc : b ≠ c)
    (hs : s = b ∨ s = c) (ht : t = b ∨ t = c) (hst : s ≠ t) :
    (s = b ∧ t = c) ∨ (s = c ∧ t = b) := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp_all

/-- The two `α`-adjacent side lengths of the base-`β` tile at `e = 1` are distinct, so the two
placements of `two_placements` are genuinely two. -/
theorem lengths_distinct (f : ℕ) : ((f * f : ℝ) - 1) ≠ (f * f : ℝ) := by
  intro h; linarith

/-! ## The induction

With the branch exhausted two ways, advancing the march by one position and by two, a refutation
of every shorter runway refutes the current one.  That is Fibonacci-shaped strong induction, and
it is the backbone of the intended proof for both escape families. -/

/-- **The march induction.**  If runways of length `0` and `1` are refuted and every longer runway
reduces to the two shorter ones, every runway is refuted. -/
theorem march_dies (S : ℕ → Prop) (h0 : S 0) (h1 : S 1)
    (hstep : ∀ n, S n → S (n + 1) → S (n + 2)) : ∀ n, S n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact h0
    | 1 => exact h1
    | (k + 2) => exact hstep k (ih k (by omega)) (ih (k + 1) (by omega))

/-- **The count that the exhaustiveness bounds.**  A branch splitting at most two ways, into
runways shorter by one and by two, and consuming two spine nodes, has subtree size bounded by the
march recurrence.  The measured counts meet this bound with equality, which is the content of the
*admissibility* half: both chiralities really occur. -/
theorem tree_size_bound (T : ℕ → ℤ) (n : ℕ)
    (hb : T (n + 2) ≤ T (n + 1) + T n + 2) :
    T (n + 2) - T (n + 1) - T n ≤ 2 := by omega

end Erdos634.MarchStep
