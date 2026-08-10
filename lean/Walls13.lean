-- Walls13.lean — the terminal mechanism of `thm:walls13`, and the base-word bookkeeping it collides
-- with.
--
-- `thm:walls13` (companion) proves Hypothesis `hyp:walls` at the member `(1,3)`: no tiling of the
-- `(1,3)` target at `m = 1` carries an `a`-edge on an equal side, hence no `(1,3)`-tiling exists.
-- The proof is search-free and runs through a fork:
--
--   * `p = 1` is forced and the side word is `c a a a c`;
--   * the corner partner's `c`-chord is blocked at both ends, so `CChord.c_chord_dichotomy` splits
--     the argument into a single-`c` and a three-`a` branch;
--   * the branch fixes the base word: `a a b c a` or `a c b a a`;
--   * in each branch the cascade advances one cell and the vertex figure at the next base point is
--     left with exactly `β` — while the base word, already fixed at the fork, puts a `b`-edge there.
--
-- The last line is the same in both branches, and is what this file isolates: **a `β`-vertex has
-- flanks `{a, c}`, so a tile presenting `β` at a boundary point cannot lay a `b`-edge there.**
--
-- SCOPE. The geometry — which point the cascade reaches, and that the figure there is left with
-- exactly `β` — is NOT proved here. It is carried as the hypotheses of `advance_and_collide`, in the
-- style of `ChordInterface`: the obligation is named rather than hidden, and the corpus keeps its
-- zero-`sorry` property. What is proved here is the collision itself plus the arithmetic of the two
-- forced base words.
--
-- Per the project rule, the corpus was surveyed first: `CChord.lean` carries the dichotomy and the
-- slot fillers, `Interface.lean` the partner uniqueness, `OrderForcing.lean` the run kills. None of
-- them states the flank relation or the base-word arithmetic, so this is not a restatement.

import Mathlib.Tactic

namespace Erdos634.Walls13

/-- The three tile edges. -/
inductive Edge | a | b | c
  deriving DecidableEq, Repr

/-- The three tile angles. `α` is opposite `a`, `β` opposite `b`, `γ` opposite `c`. -/
inductive Angle | alpha | beta | gamma
  deriving DecidableEq, Repr

/-- The edge opposite an angle. -/
def opposite : Angle → Edge
  | .alpha => .a
  | .beta  => .b
  | .gamma => .c

/-- The two edges flanking an angle's vertex: every side except the one opposite it. -/
def flanks : Angle → Edge × Edge
  | .alpha => (.b, .c)
  | .beta  => (.a, .c)
  | .gamma => (.a, .b)

/-- **A flank is never the opposite edge.**  The vertex of an angle is incident to exactly the two
sides that are not opposite it. -/
theorem flank_ne_opposite (A : Angle) :
    (flanks A).1 ≠ opposite A ∧ (flanks A).2 ≠ opposite A := by
  cases A <;> exact ⟨by decide, by decide⟩

/-- **The advance-and-collide contradiction**, the terminal step of both branches of
`thm:walls13`.

`hslot` is the geometric input: the cascade has advanced, and the vertex figure at the base point in
question is left with exactly one angle `A`, so a single tile fills it and lays one of that angle's
flanks along the base there.  `hword` is the combinatorial input: the base word, already fixed at the
dichotomy fork, has the edge `opposite A` at that position.  The two cannot both hold.

In `thm:walls13` both branches instantiate this with `A = β`, at `(2f,0)` in the single-`c` branch
and at the trisection point `(12,0)` in the three-`a` branch. -/
theorem advance_and_collide {A : Angle} {E : Edge}
    (hslot : E = (flanks A).1 ∨ E = (flanks A).2)
    (hword : E = opposite A) : False := by
  rcases hslot with h | h
  · exact (flank_ne_opposite A).1 (h ▸ hword ▸ rfl)
  · exact (flank_ne_opposite A).2 (h ▸ hword ▸ rfl)

/-- Specialised to `β`, the form both branches use: a tile presenting `β` at a boundary point lays
`a` or `c` there, never `b`. -/
theorem beta_lays_no_b {E : Edge}
    (hslot : E = (flanks Angle.beta).1 ∨ E = (flanks Angle.beta).2) : E ≠ Edge.b := by
  intro h; exact advance_and_collide hslot (by simpa [opposite] using h)

/-! ## The two forced base words

At `(1,3)` the tile is `(a,b,c) = (3,8,9)` and the base has length `3f²−e² = 26`. The dichotomy fork
fixes the base word to one of two permutations of `(a,a,b,c,a)`, and both have total length `26`.
Recording them makes the collision positions checkable rather than asserted. -/

/-- The length of an edge at `(1,3)`. -/
def len : Edge → ℕ
  | .a => 3
  | .b => 8
  | .c => 9

/-- The single-`c` branch's base word, `a a b c a`. -/
def wordSingleC : List Edge := [.a, .a, .b, .c, .a]

/-- The three-`a` branch's base word, `a c b a a`. -/
def wordThreeA : List Edge := [.a, .c, .b, .a, .a]

/-- Both forced words have the base length `26 = 3f² − e²` at `(1,3)`. -/
theorem word_lengths :
    (wordSingleC.map len).sum = 26 ∧ (wordThreeA.map len).sum = 26 := by
  constructor <;> decide

/-- Both words are permutations of `(a^3, b, c)`, as `thm:e1reduce` requires at `e = 1`. -/
theorem words_are_permutations :
    wordSingleC.count Edge.a = 3 ∧ wordSingleC.count Edge.b = 1 ∧ wordSingleC.count Edge.c = 1
  ∧ wordThreeA.count Edge.a = 3 ∧ wordThreeA.count Edge.b = 1 ∧ wordThreeA.count Edge.c = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **The collision position in the single-`c` branch.**  The word is `a a b c a`, so the base point
at distance `2f = 6` is the junction after the second `a`, and the edge starting there is the `b`.
The cascade leaves that vertex with exactly `β`, and `beta_lays_no_b` closes the branch. -/
theorem singleC_b_at_six :
    ((wordSingleC.take 2).map len).sum = 6 ∧ wordSingleC[2]? = some Edge.b := by
  constructor <;> decide

/-- **The collision position in the three-`a` branch.**  The word is `a c b a a`, so the base point
at distance `12` is the junction after `a c`, and the edge starting there is again the `b`. -/
theorem threeA_b_at_twelve :
    ((wordThreeA.take 2).map len).sum = 12 ∧ wordThreeA[2]? = some Edge.b := by
  constructor <;> decide

end Erdos634.Walls13
