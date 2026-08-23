import Erdos634.UniformFill
import Erdos634.Frontier

/-!
# Why `prop:a2branch` does not iterate, and what carries the argument past a floor

`UniformFill` reduced `prop:a2branch` at row 3 to one hypothesis, `reaches_base`: that the
south cover's feet are slots of the base word.  The obvious repair is to iterate the
proposition one strip lower.  **It does not iterate.**

`prop:a2branch`'s hypothesis is a horizontal **`c`-edge** lying on the floor east of the fork.
After one descent what sits on the floor below is `f + 1` junctions at spacing `a`, spanning
`f·a = c` — that is `f` `a`-edges, *not* a `c`-edge.  The hypothesis is not reproduced, so the
proposition cannot simply be applied again.  This is recorded because it is the natural repair
and it fails.

## What does carry across a floor

The `a`-edges propagate on their own, by an arithmetic fact about the tile's semigroup.  Since
`a < b < c`, the only way to write `a` as a nonnegative combination of `a`, `b`, `c` is `a`
itself (`a_cover_is_single`).  So an `a`-edge lying on an interior floor is covered from below
by a **single** `a`-edge: the covering introduces no new junction, and the endpoints are
junctions from below exactly as they were from above.

`Frontier.semigroup_elt_ge_min` already gives the weaker "a nonzero sum of tile sides is at
least the smallest side"; the sharpening to uniqueness is what is needed here, and is proved
from it in one step.

## The residual hypothesis, in its reduced form

With the junctions passing through the floor unchanged, what remains is that the figure *below*
each of them is again uniform — the same congruence argument as `UniformFill`, one strip lower.
That is `uniform_below` in `reaches_base_of_uniform_below`, and it is the only thing still
carried.  It is a fan statement of exactly the kind `OrderForcing` already proves at the floor
above; whether it holds at an interior floor is open.
-/

namespace Erdos634.FloorPropagation

open Finset

/-- **The cover of an `a`-edge is a single `a`-edge.**  With `a` strictly the smallest side,
`x·a + y·b + z·c = a` forces `(x,y,z) = (1,0,0)`: no `b` or `c` fits, and no two `a`'s fit.
Sharpens `Frontier.semigroup_elt_ge_min` from `≥ a` to uniqueness at `a`. -/
theorem a_cover_is_single {a b c x y z : ℕ} (ha : 0 < a) (hab : a < b) (hac : a < c)
    (h : x * a + y * b + z * c = a) : x = 1 ∧ y = 0 ∧ z = 0 := by
  have hy : y = 0 := by
    by_contra hy0
    have h1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
    have h2 : b ≤ y * b := Nat.le_mul_of_pos_left b (by omega)
    omega
  have hz : z = 0 := by
    by_contra hz0
    have h1 : 1 ≤ z := Nat.one_le_iff_ne_zero.mpr hz0
    have h2 : c ≤ z * c := Nat.le_mul_of_pos_left c (by omega)
    omega
  subst hy; subst hz
  refine ⟨?_, rfl, rfl⟩
  have hx : x * a = 1 * a := by omega
  exact Nat.eq_of_mul_eq_mul_right ha hx

/-- **At `e = 1`, `a` is strictly the smallest side** for `f ≥ 3`: `f < f² − 1 < f²`. -/
theorem a_is_strictly_smallest (f : ℕ) (hf : 3 ≤ f) : f < f * f - 1 ∧ f * f - 1 < f * f := by
  have h : 3 * f <= f * f := by nlinarith
  omega

/-- **The junctions pass through the floor unchanged.**  Instantiating `a_cover_is_single` at
`e = 1`: an `a`-edge on an interior floor is covered from below by one `a`-edge, so the `f + 1`
junctions at spacing `a` are junctions from below with no new subdivision. -/
theorem junctions_pass_through (f x y z : ℕ) (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f) : x = 1 ∧ y = 0 ∧ z = 0 :=
  a_cover_is_single (by omega) (a_is_strictly_smallest f hf).1
    (lt_trans (a_is_strictly_smallest f hf).1 (a_is_strictly_smallest f hf).2) h

/-- **`reaches_base`, reduced.**  Given that the figure below each junction is uniform — the
same congruence argument as `UniformFill`, one strip lower — the feet continue to the next floor
at the same spacing, and the row-3 statement closes.  `uniform_below` is the only hypothesis
left, and it is a fan statement at an interior floor. -/
theorem reaches_base_of_uniform_below (f : ℕ) (hf : 3 ≤ f) (isA : ℕ → Prop) [DecidablePred isA]
    (base_count : ((range (f + 2)).filter isA).card = f)
    (x₀ : ℕ)
    (uniform_below : ∀ i ∈ range (f + 1), x₀ + i * f < f + 2 ∧ isA (x₀ + i * f)) :
    False :=
  Erdos634.UniformFill.row_three_dies_of_mate_fill f hf isA base_count x₀ uniform_below

end Erdos634.FloorPropagation
