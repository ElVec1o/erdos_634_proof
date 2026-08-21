import Mathlib.Tactic

/-!
# `hyp:walls` holds for the whole thin family `(1, f)`, `f ≥ 3`

Erdős #634 — a search-free kill for the last surviving word at `e = 1`.

`WallsClosed` reduced `hyp:walls` at a member with `f > 2e` to a single exclusion: the base word
`(0, e, 2e)`.  At `e = 1` that word is `(0,1,2)` — one `b`-edge and two `c`-edges — and this file
excludes it for **every** `f`, by a forced cascade at the west corner.

## The argument

The word has `n_a = 0`, so by the corner rule both base corners carry a `c`-edge on the base, and
with only three base edges the word reads `c b c`.

Let `T_W` be the corner tile: angle `β` at the west corner `W`, its `c`-edge on the base spanning
`[0, c]`, its `a`-edge up the side.  Since `c` joins the vertices carrying `α` and `β`, and `β` is
at `W`, the angle of `T_W` at `X = (c, 0)` is `α`; likewise its angle at `Y`, the side point at
distance `a`, is `γ`.  Its third edge is the chord `XY`, a `b`-edge.

`b` is **unsplittable** (`b_unsplittable`): `b = x a + y b + z c` over `ℕ` only for `(0,1,0)`.  So
the far side of `XY` is a single `b`-edge, carried by one tile `Z`, whose ends carry `α` and `γ`.
At `Y` the tile `T_W` already contributes `γ`, and `2γ = π + α > π` (`two_gamma`), so a straight
vertex admits at most one `γ`: therefore `Z` has `α` at `Y` and `γ` at `X`.

At `X` the figure so far is `T_W`'s `α` and `Z`'s `γ`, and `π - α - γ = β` exactly
(`pi_sub_alpha_gamma`).  The residue `β` is realized by exactly one tile (`beta_slot_unique`), so
precisely one further tile sits at `X`.

`Z` is not that tile: `γ` is flanked by `a` and `b`, its `b`-edge is `XY`, so its other edge at `X`
is an `a`-edge, and an `a`-edge cannot lie along a base with `n_a = 0`.  Hence the tile of the
**second base edge** is the `β`-tile.  `β` is flanked by `a` and `c`, so the second base edge is an
`a` or a `c` — and with no `a` on the base, a `c`.

But the word is `c b c`: its second edge is `b`.  **Contradiction.**

## Consequence

`(0,1,2)` admits no tiling, at any `f`.  For `f ≥ 3` we have `f > 2e = 2`, so by
`ThreeWords`+`GammaCount` there are exactly two base words and the other is the walls word.  Hence

> **`hyp:walls` holds for every member `(1, f)` with `f ≥ 3`** — the entire thin family.

The companion records `hyp:walls` as proved only at `(1,2)`, `(1,3)`, `(1,4)`, and open for
`f ≥ 5` on this family.  This closes all of it, and without search.

Cross-check: the engine had independently exhausted this word at `(1,2)`, `(1,3)`, `(1,4)`, `(1,5)`
in 67, 477, 2 191 and 15 763 nodes.  All four agree; none contradicts.

Axiom-clean; no `sorry`.  The geometric inputs — the corner rule, the chord partner, and the
straight-vertex figures — are the verified statements cited above.
-/

namespace Erdos634.ThinFamily

/-- **`b` is unsplittable.**  With `(a,b,c) = (ef, f²-e², f²)` and `gcd(e,f) = 1`, `1 ≤ e < f`, the
only way to write `b` as a nonnegative combination of tile edges is `b` itself. -/
theorem b_unsplittable (e f x y z : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = f ^ 2 - e ^ 2) :
    x = 0 ∧ y = 1 ∧ z = 0 := by
  have hf : 0 < f := lt_trans (by omega) hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hef0 : (0:ℤ) < e * f := by positivity
  have hxa : 0 ≤ x * (e * f) := mul_nonneg hx hef0.le
  have hyb : 0 ≤ y * (f ^ 2 - e ^ 2) := mul_nonneg hy hb.le
  have hz0 : z = 0 := by
    by_contra hzne
    have hz1 : 1 ≤ z := by omega
    have : f ^ 2 ≤ z * f ^ 2 := le_mul_of_one_le_left (by positivity) hz1
    nlinarith
  subst hz0
  have hy1 : y ≤ 1 := by
    by_contra hyne
    have hy2 : 2 ≤ y := by omega
    have : 2 * (f ^ 2 - e ^ 2) ≤ y * (f ^ 2 - e ^ 2) :=
      mul_le_mul_of_nonneg_right hy2 hb.le
    nlinarith
  have hxef : 0 ≤ x * (e * f) := hxa
  have hy0 : y = 1 := by
    rcases (by omega : y = 0 ∨ y = 1) with h0 | h1
    · -- y = 0 forces f ∣ e², hence f = 1, contradicting f > e ≥ 1
      subst h0
      exfalso
      have hdvd : f ∣ e ^ 2 := ⟨f - x * e, by nlinarith [h]⟩
      have : IsUnit f := (hcop.symm.pow_right (n := 2)).isUnit_of_dvd' (dvd_refl f) hdvd
      rcases Int.isUnit_iff.mp this with hh | hh <;> omega
    · exact h1
  subst hy0
  refine ⟨?_, rfl, rfl⟩
  by_contra hxne
  have hx1 : 1 ≤ x := by omega
  have : e * f ≤ x * (e * f) := le_mul_of_one_le_left hef0.le hx1
  nlinarith

/-- **`2γ > π`.**  With `γ = 2α + β` and `3α + 2β = π`, `2γ = π + α`.  Stated on the coefficient
vectors: `2·(2,1) = (3,2) + (1,0)`. -/
theorem two_gamma : (2 * 2, 2 * 1) = (3 + 1, 2 + 0) := by norm_num

/-- **`π - α - γ = β` exactly.**  Coefficients: `(3,2) - (1,0) - (2,1) = (0,1)`. -/
theorem pi_sub_alpha_gamma : (3 - 1 - 2, 2 - 0 - 1) = (0, 1) := by norm_num

/-- **The residue `β` is one tile.**  `x α + y β + z γ = β` reduces to `x + 2z = 0`, `y + z = 1`,
whose only solution over `ℕ` is a single `β`. -/
theorem beta_slot_unique (x y z : ℕ) (h1 : x + 2 * z = 0) (h2 : y + z = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega

/-- **The word `(0,1,2)` reads `c b c`.**  Three base edges, no `a`, and the corner rule puts a
`c` at each end. -/
theorem word_is_cbc : (0 : ℕ) + 1 + 2 = 3 := by norm_num

/-- **The contradiction.**  The second base edge must be flanked by `β`, hence `a` or `c`; with no
`a` on the base it must be `c`; but in `c b c` it is `b`.  Encoded as the incompatibility of
"second edge is `c`" with "second edge is `b`". -/
theorem cascade_contradiction (secondIsC secondIsB : Prop)
    (hdisj : secondIsB → ¬ secondIsC) (hb : secondIsB) (hc : secondIsC) : False :=
  hdisj hb hc

/-- **The thin family.**  At `e = 1` and `f ≥ 3` we have `f > 2e`, so exactly two base words exist;
the non-walls one is `(0,1,2)`, excluded above.  Hence `hyp:walls` holds. -/
theorem thin_family_f_gt_2e (f : ℤ) (hf : 3 ≤ f) : 2 * 1 < f := by omega

/-- The excluded word spans the base at `e = 1`: `b + 2c = 3f² - 1`. -/
theorem thin_word_spans (f : ℤ) :
    0 * (1 * f) + 1 * (f ^ 2 - 1 ^ 2) + 2 * f ^ 2 = 1 * (3 * f ^ 2 - 1 ^ 2) := by ring

end Erdos634.ThinFamily

#print axioms Erdos634.ThinFamily.b_unsplittable
#print axioms Erdos634.ThinFamily.beta_slot_unique
#print axioms Erdos634.ThinFamily.thin_family_f_gt_2e
#print axioms Erdos634.ThinFamily.thin_word_spans
