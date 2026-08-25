import Mathlib.Tactic

/-!
# A quantitative crossing bound for the corner lines

Erdős #634 — answering the request of `rem:straddle`.

`rem:straddle` records that the blanket no-straddle hypothesis is false — at `m ≥ 2`, tiles
straddle lines through `b`-edges routinely (19, 30 and 64 of the 44, 44 and 99 `b`-edge lines of
the three certified tilings) — and concludes:

> the missing ingredient is not a prohibition but a **quantitative** bound: a description of the
> set in which a straddling tile's crossing points must lie.

This file supplies a bound of that kind for the corner lines `L_k`, by area rather than by
position.

## The setup

For `1 ≤ k < f` let `L_k` be the `b`-direction line from the base point `(kf, 0)` to the side point
`k·c·u`.  The region `W_k` west of it is the triangle with sides `k·a`, `k·b`, `k·c` — **similar to
the tile, at scale `k`** — so

  `area(W_k) = k² · A`,   `A` the tile's area.

The other two sides of `W_k` lie on the target's base and side, which no tile crosses.  A tile of
the tiling therefore meets `∂W_k` only through `L_k`, and is either wholly inside `W_k`, wholly
outside, or crossed by `L_k`.

## The bound

Writing `n` for the number of tiles wholly inside and `φ₁, …, φ_r` for the areas that the `r`
crossed tiles contribute to `W_k`, each strictly between `0` and `A`,

  `k² A = n A + Σ φᵢ`,  so  `Σ φᵢ = (k² − n) A`  with  `0 < k² − n < r`.

`k² − n` is an integer, so it is at least `1`, and therefore

  **`r ≥ 2`: if any tile crosses `L_k`, at least two do.**

`crossing_count_ge_two` is that statement, in the normalised form where areas are measured in units
of `A`.  Its content is the impossibility of a single crossing: one crossed tile would have to
donate an integer multiple of `A` to `W_k` while donating strictly between `0` and `A`.

## What it gives

It is the first constraint on crossings that does not assume they are absent, so it applies exactly
where `rem:straddle` says the blanket hypothesis fails.  In a route-1 configuration
`a^i c a^j b a^{k'}` the base `c`-edge forces a crossing of `L_k` for every `i < k < f` — the point
`(kf, 0)` is then strictly interior to that `c`-edge — so this lemma says each such line carries a
**second** crossing tile, elsewhere along it.  That is a fact about the interior of the
configuration obtained from the boundary word alone.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CrossingCount

/-- **No single crossing.**  If `r` reals, each strictly between `0` and `1`, sum to a positive
integer `m`, then `r ≥ 2`: the sum is `< r`, so `r > m ≥ 1`.

Areas are normalised by the tile's area `A`; `m = k² − n` is the integer deficit of `W_k` and each
`φᵢ / A` lies strictly in `(0,1)`. -/
theorem crossing_count_ge_two (r m : ℕ) (φ : Fin r → ℝ)
    (hlt : ∀ i, φ i < 1) (hm : 1 ≤ m) (hsum : ∑ i, φ i = (m : ℝ)) :
    2 ≤ r := by
  by_contra hcon
  push_neg at hcon
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  interval_cases r
  · -- no crossing tile: the sum is empty, so `m = 0`, contradicting `m ≥ 1`
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    linarith
  · -- one crossing tile: its donation is `< 1`, but must equal `m ≥ 1`
    rw [Fin.sum_univ_one] at hsum
    have := hlt 0
    linarith

/-- **The area identity behind it.**  `W_k` is similar to the tile at scale `k`, so its area is
`k²` tile-areas; the whole tiles inside contribute `n`, the crossed ones the rest. -/
theorem area_identity (k n : ℕ) (S : ℝ) (h : (k : ℝ) ^ 2 = n + S) : S = (k : ℝ) ^ 2 - n := by
  linarith

/-- **`W_k` is a scaled tile.**  Its three sides are `k` times the tile's, so its area is `k²`
times the tile's — recorded as the side identity at `e = 1`, where `(a,b,c) = (f, f²-1, f²)`. -/
-- CONTENT-FREE (code/trivia_audit.py, 2026-08-25): this statement asserts nothing --
-- reflexivity: both sides are the same triple.
-- Kept for its docstring's exposition; it carries no mathematical content and must not be
-- cited as evidence that the surrounding claim is established.
theorem west_region_similar (f k : ℤ) :
    (k * f, k * (f ^ 2 - 1), k * f ^ 2) = (k * f, k * (f ^ 2 - 1), k * f ^ 2) := rfl

/-- **In a route-1 word the base point of `L_k` is interior to the `c`-edge, for every `k > i`.**
The `c`-edge runs from `i f` to `i f + f²`, and `i f < k f < i f + f²` reduces to `0 < k - i < f`,
which holds since `1 ≤ i < k < f`. -/
theorem base_point_interior (f i k : ℤ) (hi : 1 ≤ i) (hik : i < k) (hkf : k < f) :
    i * f < k * f ∧ k * f < i * f + f ^ 2 := by
  constructor
  · nlinarith
  · nlinarith

end Erdos634.CrossingCount

#print axioms Erdos634.CrossingCount.crossing_count_ge_two
#print axioms Erdos634.CrossingCount.area_identity
#print axioms Erdos634.CrossingCount.base_point_interior
