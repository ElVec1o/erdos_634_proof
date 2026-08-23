import Erdos634.BaseWordBlock

/-!
# `prop:a2branch` at row 3, in the firewall style

`prop:a2branch` excludes the `A₂` branch of the row-`j` fork.  At row 1 it is complete.  At
row 3 its south cover's feet land on an interior floor rather than on the base, and the
companion records the consequence at `thm:strippbound`: "that step is incomplete as written,
and the structural claim of reach 4 is open pending its repair."

Two things are now known about that gap.

* Its **combinatorial half is row-independent**.  `thm:e1reduce` makes the base a permutation
  of `(a^f, b, c)` — `f + 2` letters, exactly `f` of them `a` — so the proposition's closing
  demand for `f + 1` `a`-edges is impossible *anywhere* in the word, not merely at its start.
  That is `BaseWordBlock.no_f_plus_one_a`, and it needs no hypothesis about which row the
  feet came from.
* Its **geometric half** is the descent: that the feet reach the base at all.  That is a fan
  argument, and `Dissection` lines 396–402 record that Mathlib cannot lift a mod-`2π` angle
  sum to a real-valued one beyond two summands, so an `n`-fold fan "must be built from
  scratch".

`Dissection` handles exactly this situation by *carrying* the angle facts rather than proving
them — `HasAngleSums` takes the angle function as a parameter.  This file does the same for
the descent, so that everything except the fan is discharged.

## What is carried, and what is proved

Carried (the geometry, one hypothesis each):

* `foot` — the descent map, sending the `i`-th endpoint of the south cover to its base
  abscissa.  Its existence is the descent.
* `foot_inj` — the descent is injective on the cover's endpoints.  For a rigid strip this is
  because descent is a translation (`layer_rigid_of_exclusions` gives the rigidity; the
  translation step is the fan-dependent part).
* `foot_lt`, `foot_isA` — the images are base slots, and are `a`-junctions.

Proved: everything else.  A south cover of `f` whole `a`-edges has `f + 1` endpoints; an
injective descent gives `f + 1` **distinct** base `a`-junctions; and a base word with only
`f` letters `a` cannot carry them.  No step below refers to *where* on the base the run sits,
so the argument is the same at row 1 and at row 3 — which is the whole point.
-/

namespace Erdos634.A2BranchRow3

open Finset

/-- **The `A₂` branch dies at row 3, given the descent.**

`f` whole `a`-edges in the south cover have `f + 1` endpoints; `foot` carries them
injectively to base slots, all of which are `a`-junctions; and `thm:e1reduce` allows only `f`
letters `a` in the whole base word.  The descent hypotheses are the only geometric input, and
nothing here depends on the position of the run. -/
theorem row_three_dies (f : ℕ) (isA : ℕ → Prop) [DecidablePred isA]
    (base_count : ((range (f + 2)).filter isA).card = f)
    (foot : ℕ → ℕ)
    (foot_inj : Set.InjOn foot (range (f + 1)))
    (foot_lt : ∀ i ∈ range (f + 1), foot i < f + 2)
    (foot_isA : ∀ i ∈ range (f + 1), isA (foot i)) :
    False := by
  refine BaseWordBlock.no_f_plus_one_a f isA base_count ((range (f + 1)).image foot)
    ?_ ?_ (le_of_eq ?_)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact mem_range.mpr (foot_lt i hi)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact foot_isA i hi
  · rw [card_image_of_injOn foot_inj, card_range]

/-- **The count that makes it work**, isolated: a south cover of `f` whole `a`-edges has
`f + 1` endpoints, one more than the base word can supply. -/
theorem endpoints_exceed_supply (f : ℕ) : f + 1 > f := Nat.lt_succ_self f

end Erdos634.A2BranchRow3
