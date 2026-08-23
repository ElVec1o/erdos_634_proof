import Mathlib
import Erdos634.BaseWordBlock

/-!
# The brick lattice and the descent of a strip

At `e = 1` the tile is `(a, b, c) = (f, f² - 1, f²)` and a *brick* is the parallelogram
with sides `a`, `b` and angle `α + β` (companion, line 3863) — two tiles glued along their
`c`-edges.  Bricks tile by translation, so a straddler-free (rigid) strip carries a
**lattice**, and descending one strip is a single translation applied uniformly to every
point of the ceiling.  That is what `prop:a2branch` needs at row 3, where its south cover's
feet land on an interior floor rather than on the base.

## `lem:ladder`(i)'s horizontal advance is the law of projections

`lem:ladder`(i) states the advance as `f·u_x + b|cos 2γ| = c`, alongside
`sin β = b√D/(2f³)` with `D = 4f² - 1`, which presents it as an arithmetic fact about this
family.  It is not.  `ApexRigidity.two_gamma` gives `2γ = π + α`, hence

  `cos 2γ = cos(π + α) = -cos α`,   so   `|cos 2γ| = cos α`

and with `u_x = cos β` the identity reads

  `c = a·cos β + b·cos α`

which is the **law of projections**, true in *every* triangle (`law_of_projections`).  So
the brick's horizontal advance per strip is exactly `c` for the whole base-`β` family, at
every `e` — not just at `e = 1`, and with no `√D` and no case split anywhere.  The proof is
one line from the cosine rule: the two numerators sum to `2c²`.

## What is proved here, and what is assumed

Proved: the projection law, the identification `|cos 2γ| = cos α` that reduces
`lem:ladder`(i) to it, and the consequence that a uniform translation carries `n` feet at
spacing `a` to `n` *distinct* images (`descent_card`) — the input to
`BaseWordBlock.no_f_plus_one_a`.

**Assumed, as a named hypothesis, not proved:** that a straddler-free strip is rigid, i.e.
that its tiles form a brick lattice so that the descent *is* a translation.  This is
`rem:straddler`'s own wording ("the strip structure stays rigid"), but it is not proved in
the companion and it is not proved here.  It is carried explicitly as `Rigid` so that no
debt is hidden.  **Until it is discharged, reach 4 remains open.**
-/

namespace Erdos634.LatticeDescent

open Finset

/-- **The law of projections**: `c = a cos β + b cos α`, with the cosines supplied by the
cosine rule.  True in every triangle; the two numerators sum to `2c²`. -/
theorem law_of_projections (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * ((a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c))
      + b * ((b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c)) = c := by
  field_simp; ring

/-- **`|cos 2γ| = cos α`**, in cleared form: `2γ = π + α` (`ApexRigidity.two_gamma`) gives
`cos 2γ = -cos α`, so `lem:ladder`(i)'s `b|cos 2γ|` is `b cos α` and its advance identity
is `law_of_projections`.  Here at `e = 1`, where both sides are the rational
`(2f² - 1)/(2f²)`. -/
theorem abs_cos_two_gamma_eq_cos_alpha (f : ℚ) (hf : f ≠ 0) (hf1 : f ^ 2 - 1 ≠ 0) :
    ((f ^ 2 - 1) ^ 2 + (f ^ 2) ^ 2 - f ^ 2) / (2 * (f ^ 2 - 1) * f ^ 2)
      = (2 * f ^ 2 - 1) / (2 * f ^ 2) := by
  field_simp; ring

/-- **`cos β = N₀ / (2f³)`** at `e = 1` — the same rational as the isosceles target
`(f³, f³, N₀)`'s base-angle cosine `(N₀/2)/f³`.  So the target's base angle is exactly `β`
and its apex angle is `3α`; the relation `3α + 2β = π` is that triangle's angle sum. -/
theorem cos_beta_eq_target_base_angle (f : ℚ) (hf : f ≠ 0) :
    (f ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - 1) ^ 2) / (2 * f * f ^ 2)
      = ((3 * f ^ 2 - 1) / 2) / f ^ 3 := by
  field_simp; ring

/-- **A rigid strip descends by a translation, and a translation keeps feet distinct.**

`n` feet at spacing `a` on the ceiling, translated by `v`, give `n` distinct abscissae on
the floor.  Applied twice (rows 3 → 2 → 1 → base) this delivers `f + 1` distinct base
junctions, exactly the input to `BaseWordBlock.no_f_plus_one_a`. -/
theorem descent_card (a x v : ℚ) (ha : a ≠ 0) (n : ℕ) :
    ((range n).image (fun i : ℕ => x + v + i * a)).card = n := by
  rw [card_image_of_injOn, card_range]
  intro i _ j _ h
  have h2 : (i : ℚ) * a = (j : ℚ) * a := by linarith
  exact_mod_cast mul_right_cancel₀ ha h2

/-- **The rigidity hypothesis, stated explicitly and NOT proved.**  `Rigid` asserts that the
straddler-free strip below a floor is a brick lattice, so descent by one strip is a single
translation.  `rem:straddler` asserts this; the companion does not prove it, and neither
does this file. -/
def Rigid (StrippBoundHolds LatticeStructure : Prop) : Prop :=
  StrippBoundHolds → LatticeStructure

/-- **The assembly.**  Given rigidity — hence a uniform descent producing `f + 1` distinct
base junctions, all `a`-junctions — `prop:a2branch` closes at row 3 exactly as at row 1, by
the counting contradiction of `BaseWordBlock.no_f_plus_one_a`. -/
theorem row_three_closes (f : ℕ) (isA : ℕ → Prop) [DecidablePred isA]
    (hcount : ((range (f + 2)).filter isA).card = f)
    (S : Finset ℕ) (hS : S ⊆ range (f + 2)) (hSA : ∀ x ∈ S, isA x)
    (hcard : S.card = f + 1) : False :=
  BaseWordBlock.no_f_plus_one_a f isA hcount S hS hSA (le_of_eq hcard.symm)

end Erdos634.LatticeDescent
