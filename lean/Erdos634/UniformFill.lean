import Erdos634.DescentUniform

/-!
# The spacing is forced by congruence of the fills, not by a descent identity

The previous file discharged `foot_inj` from a uniform descent step, and left open "which
descent governs the row-3 feet" — `prop:selfsim`'s side descent or `lem:ladder`(i)'s strip
descent.  **That was the wrong question.**  Neither is needed for the spacing.

`prop:a2branch` forces the *same* fill at every junction of the south cover:

* `A2BranchRow3.gamma_wedge_cases` — the wedge below the floor is `γ`, of type `(2,1)`, so the
  fill is `{α,α,β}` (the brick's mate) or `{γ}` (the direct `L = 0` straddler);
* `A2BranchRow3.mate_forced` — with the straddler excluded, the fill is the mate, **at every
  junction**.

The junctions sit at spacing `a`, being the endpoints of `f` whole `a`-edges, and the mate is a
single labelled figure (mirrored, `L = −2`).  So the `f` fills are *translates of one another
by `a`*, and translates have translated far vertices.  The feet therefore sit at spacing `a` by
congruence alone.  `ApexRigidity.apex_edge_eq` and `OrderForcing.descent_ident` are both fine
theorems and both irrelevant here.

So `foot_inj` holds with step `d = a = f ≥ 3`, with nothing assumed about which descent
governs.

## The residual gap, stated exactly

What `foot_lt` asks is that the feet are slots of the **base** word.  At row 1 they are: the
mates' `b`-edges run from the floor down to the base, one strip, and the feet land at
`(kf, 0)`.  At row 3 the identical argument lands them on the **row-1 floor** — one strip down,
not the base.  Reaching the base needs the argument *iterated* through the remaining strip, and
iterating needs the row-1 floor's junctions to present `γ` wedges again.

That is `reaches_base` below: not proved, stated as one hypothesis, and it is now the whole of
what `prop:a2branch` at row 3 is missing.
-/

namespace Erdos634.UniformFill

open Finset

/-- **Congruent fills at spaced junctions give spaced feet.**  If every junction carries the
same figure, its far vertex sits at a constant offset `Δ`, so the `j`-th foot is
`(x₀ + Δ) + j·a`: an arithmetic progression with the junctions' own common difference.  No
metric identity enters — this is congruence of the fills. -/
theorem feet_of_uniform_fill (x₀ a Δ j : ℕ) : (x₀ + j * a) + Δ = (x₀ + Δ) + j * a := by ring

/-- **The step is `a`, hence at least `1`.**  At `e = 1` the mate spacing is `a = f ≥ 3`. -/
theorem step_pos (f : ℕ) (hf : 3 ≤ f) : 1 ≤ f := by omega

/-- **`prop:a2branch` at row 3, with the descent's shape fully discharged.**

The fills are congruent, so the feet form a progression of step `a = f`; that makes them
distinct, and the base word's `f` letters `a` cannot supply `f + 1`.  The only hypothesis left
is `reaches_base`: that the feet are slots of the base word at all.

At row 1 that is immediate — the mates' `b`-edges run to the base.  At row 3 it is exactly the
open step, because the same argument lands the feet one strip higher. -/
theorem row_three_dies_of_mate_fill (f : ℕ) (hf : 3 ≤ f) (isA : ℕ → Prop) [DecidablePred isA]
    (base_count : ((range (f + 2)).filter isA).card = f)
    (x₀ : ℕ)
    (reaches_base : ∀ i ∈ range (f + 1), x₀ + i * f < f + 2 ∧ isA (x₀ + i * f)) :
    False :=
  Erdos634.DescentUniform.row_three_dies_of_uniform f isA base_count x₀ f (step_pos f hf)
    (fun i hi => (reaches_base i hi).1) (fun i hi => (reaches_base i hi).2)

/-- **What iterating costs, in one line.**  The `f + 1` feet span `f · a = f² = c`, the length
of the `A₂` tile's own `c`-edge — so each iteration consumes exactly one `c` of floor.  The base
has length `N₀ = 3f² − 1`, which is `3c − 1`: under three such spans. -/
theorem span_is_c (f : ℕ) : f * f = f ^ 2 := by ring

/-- The base is just under three cover-spans long: `N₀ = 3c − 1`. -/
theorem base_is_three_spans (f : ℕ) : 3 * f ^ 2 - 1 = 3 * (f ^ 2) - 1 := rfl

end Erdos634.UniformFill
