import Erdos634.BaseWordBlock

/-!
# At `e = 1`, Hypothesis (walls) is equivalent to its own conclusion

Erdős #634 — a soundness audit of the hypothesis gating `thm:fullprime`.

`hyp:walls` (companion, "Complete corner walls") asserts that in **any** tiling of the base-`β`
target at `m = 1`, neither base-corner structure is starved or broken: the west corner carries the
complete block, whose feet are `f` `a`-edges lying on the base.  Feet are consecutive and start at
the corner, so the hypothesis says in particular

  **the base word begins with `a^f`.**

`thm:e1reduce` is an *unconditional theorem*: at `e = 1`, `m = 1`, `f ≥ 3` the base walk of any
tiling is a permutation of `(a^f, b, c)` — `f + 2` letters, exactly `f` of them `a` — **beginning
and ending with `a`**.

These cannot both hold.  If the first `f` letters are `a` they exhaust the supply, so the last
letter is `b` or `c`, not `a`.  The clash is `BaseWordBlock.no_f_plus_one_a` applied to the `f + 1`
slots `{0, …, f-1} ∪ {f+1}`.

## The consequence, which is not the one previously drawn

`rem:wallsfix` already records an incompatibility, located at the *east* corner: the block form puts
`e` `c`-feet there, while `thm:e1reduce` ends the base with an `a`.  It resolves the clash by
retreating to a weakened, west-only reading, "`hyp:walls` is exactly `p = 0`".

That retreat is not available.  The clash proved here is at the **west** corner, which is the very
half the weakened reading keeps, and the west block is also the sole premise of the derivation of
`p = 0` (`rem:sidenoa`: "the complete west block is the tile scaled by `f`, so its far side — which
at `m = 1` is the whole equal side — is subdivided into exactly `f` `c`-edges").  A structure that
provably never occurs cannot support that derivation.

So at `e = 1`, `m = 1`, `f ≥ 3`:

* every tiling has a starved-or-broken west corner (`west_block_never_complete`);
* hence `hyp:walls` holds there **iff no tiling exists** (`walls_iff_no_tiling`).

The hypothesis is therefore not a structural regularity assumption at `e = 1`; it is the conclusion.
Any conditional exclusion of the `e = 1` members that cites `hyp:walls` is circular, and
`thm:fullprime` has **no `e = 1` content** beyond the vacuous.

This does not cost the development the `e = 1` members.  They are excluded by two routes that never
mention the hypothesis: the companion's unconditional theorem on the `e = 1` family for all even
`f`, and `E1Assembly`, which reduces every `f` to the single geometric fact that the multiples of
`f` in `[0, f²)` are tiling vertices on the base.  What is lost is only the appearance that
`hyp:walls` was doing work at `e = 1`.

For `e ≥ 2` nothing here applies: the base word there is `(a^f, b^e, c^e)` with `f + 2e` letters, an
`a^f` prefix costs no more than the `f` available `a`'s, and the last letter may still be a `c`-foot
of the east block.  The collapse is specific to `e = 1`, where the east block shrinks to a single
foot and the two corners compete for the same letters.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WallsCircular

open Finset

/-- **The counting clash.**  A base word on slots `range (f + 2)` carrying exactly `f` `a`'s cannot
both begin with `a^f` (slots `0, …, f-1`) and end with an `a` (slot `f + 1`): that exhibits `f + 1`
distinct `a`-slots. -/
theorem prefix_run_contradicts_last (f : ℕ) (isA : ℕ → Prop) [DecidablePred isA]
    (hcount : ((range (f + 2)).filter isA).card = f)
    (hpre : ∀ i, i < f → isA i) (hlast : isA (f + 1)) : False := by
  refine BaseWordBlock.no_f_plus_one_a f isA hcount (insert (f + 1) (range f)) ?_ ?_ ?_
  · intro x hx
    rcases mem_insert.mp hx with h | h
    · subst h; exact mem_range.mpr (by omega)
    · exact mem_range.mpr (by have := mem_range.mp h; omega)
  · intro x hx
    rcases mem_insert.mp hx with h | h
    · exact h ▸ hlast
    · exact hpre x (mem_range.mp h)
  · have hnm : (f + 1) ∉ range f := by simp
    rw [card_insert_of_notMem hnm, card_range]

/-- **The west block is never complete at `e = 1`.**  Stated on the two inputs it consumes: the
block form's `a^f` prefix, and `thm:e1reduce`'s letter count with a final `a`. -/
theorem west_block_never_complete (f : ℕ) (isA : ℕ → Prop) [DecidablePred isA]
    (e1reduce_count : ((range (f + 2)).filter isA).card = f)
    (e1reduce_last : isA (f + 1))
    (walls_west : ∀ i, i < f → isA i) : False :=
  prefix_run_contradicts_last f isA e1reduce_count walls_west e1reduce_last

/-- **The circularity.**  If no tiling can satisfy the hypothesis, then asserting the hypothesis of
every tiling is exactly asserting that there are none. -/
theorem walls_iff_no_tiling {Tiling : Type*} (WestComplete : Tiling → Prop)
    (never : ∀ T, ¬ WestComplete T) :
    (∀ T, WestComplete T) ↔ IsEmpty Tiling := by
  constructor
  · intro h
    exact ⟨fun T => never T (h T)⟩
  · intro h T
    exact (h.false T).elim

/-- **A conditional exclusion citing the hypothesis proves nothing new.**  From `hyp:walls` one
derives emptiness, so the implication `walls → no tiling` carries no content beyond `never`. -/
theorem conditional_is_vacuous {Tiling : Type*} (WestComplete : Tiling → Prop)
    (never : ∀ T, ¬ WestComplete T) (walls : ∀ T, WestComplete T) : IsEmpty Tiling :=
  (walls_iff_no_tiling WestComplete never).mp walls

/-! ## What the collapse buys: at `e = 1` every tiling contains a side-break

The companion's chain for `thm:e1family` runs, at each of the two base corners, on a dichotomy:
either the quadratic growth **completes** (`k = f`), or a **first break** occurs, and that break is
on the base or on a side.  A base-break forces the offending walk letter into `{a, c}`, and it is
the `c` that ends the run of feet; the companion's own parenthesis, "two base-breaks are
incompatible with the single `c` of `(f,1,1)`", is that a base-break consumes a `c`.

`west_block_never_complete` closes the completion branch at the west, and the same count closes it
at the east: the east block at `e = 1` asks for a single `c`-foot, i.e. a base word ending in `c`,
while `thm:e1reduce` ends it with an `a`.  So at `e = 1`:

* both corners break (`both_corners_break`);
* at most one break is on the base, since the base carries one `c` (`at_most_one_base_break`);
* hence **some corner breaks on a side** (`some_side_break`).

That last is not a hypothesis in the companion's chain -- it is the trigger for the forced
horizontal column of `f` tiles and its filler identity.  Before this file the completion branch had
to be carried along, and Hypothesis (walls) was exactly the assertion that it is the branch that
occurs.  It is in fact the branch that never occurs, and eliminating it makes the column
unconditional at `e = 1`.

The chain then reads: both corners break -> some break is on a side -> a column of `f` tiles is
forced -> *the column reaches the base* -> its apexes are walk junctions at consecutive multiples of
`f` -> the letters on `[0, f^2]` are `a^f` -> the walk ends in `b` or `c`, against the corner
forcing.  Only the fourth step is unproved, and it is the same step `E1Assembly` isolates from the
other side.  The `e = 1` subfamily is reduced to it and to nothing else. -/

/-- **Both corners break.**  Neither completion is available: the west asks for `f` `a`-feet and the
east for a `c` at the final slot, and the letter budget refuses both. -/
theorem both_corners_break {Corner : Type*} (Completes Breaks : Corner -> Prop)
    (dichotomy : forall K, Completes K \/ Breaks K)
    (never : forall K, ¬ Completes K) : forall K, Breaks K := by
  intro K
  rcases dichotomy K with h | h
  · exact absurd h (never K)
  · exact h

/-- **At most one break is on the base.**  A base-break consumes a `c`-letter, the base carries one,
and distinct corners consume distinct letters. -/
theorem at_most_one_base_break {Corner : Type*}
    (BaseBreak : Corner -> Prop) (cOf : Corner -> ℕ)
    (consumes : forall K, BaseBreak K -> cOf K = 0)
    (distinct : forall K L, K ≠ L -> BaseBreak K -> BaseBreak L -> cOf K ≠ cOf L)
    (K L : Corner) (hKL : K ≠ L) : ¬ (BaseBreak K ∧ BaseBreak L) := by
  rintro ⟨hK, hL⟩
  exact distinct K L hKL hK hL ((consumes K hK).trans (consumes L hL).symm)

/-- **Some corner breaks on a side.**  Both corners break, breaks are base-or-side, and two
base-breaks are unavailable. -/
theorem some_side_break {Corner : Type*} (Breaks BaseBreak SideBreak : Corner -> Prop)
    (K L : Corner)
    (breaks : forall M, Breaks M) (split : forall M, Breaks M -> BaseBreak M \/ SideBreak M)
    (notBoth : ¬ (BaseBreak K ∧ BaseBreak L)) :
    SideBreak K \/ SideBreak L := by
  rcases split K (breaks K) with hK | hK
  · rcases split L (breaks L) with hL | hL
    · exact absurd ⟨hK, hL⟩ notBoth
    · exact Or.inr hL
  · exact Or.inl hK

end Erdos634.WallsCircular

#print axioms Erdos634.WallsCircular.prefix_run_contradicts_last
#print axioms Erdos634.WallsCircular.west_block_never_complete
#print axioms Erdos634.WallsCircular.walls_iff_no_tiling
